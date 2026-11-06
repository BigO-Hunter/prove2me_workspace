#!/usr/bin/env python3
"""Read-only fixpoint recovery: keep fetching missing Theorems modules until none remain.

Same contract as Solutions/api_recover_r6.py: GET-only (plus the documented
/agent/refresh token exchange). No submission, no mutation, no status change.

Scans every .lean file under Theorems/ and Solutions/ for import lines whose
module file is absent, and recovers each from the platform accepted submissions.
Module leaf Thm_A_B_C corresponds to the theorem whose dotted name written with
dot->underscore is A_B_C (exactly invertible).
"""
import json, os, urllib.parse, urllib.request

BASE = "https://prove2.me/api/v1"
ROOT = "/Users/dmitri.arkhipov/prove2me_workspace"
creds = json.load(open(os.path.join(ROOT, "credentials.json")))
TOK = None


def refresh():
    req = urllib.request.Request(BASE + "/agent/refresh",
        data=json.dumps({"api_key": creds["api_key"]}).encode(),
        headers={"Content-Type": "application/json"}, method="POST")
    return json.load(urllib.request.urlopen(req, timeout=30))["access_token"]


def get(path):
    req = urllib.request.Request(BASE + path,
                                headers={"Authorization": "Bearer " + TOK})
    return json.load(urllib.request.urlopen(req, timeout=90))


def mod_path(mod):
    return os.path.join(ROOT, mod.replace(".", "/") + ".lean")


def scan_missing():
    seen, missing = set(), set()
    for root in ("Theorems", "Solutions"):
        for dirpath, _, files in os.walk(os.path.join(ROOT, root)):
            for fn in files:
                if not fn.endswith(".lean"):
                    continue
                try:
                    lines = open(os.path.join(dirpath, fn), errors="replace").read().splitlines()
                except OSError:
                    continue
                for line in lines:
                    if not line.startswith("import "):
                        continue
                    mod = line.strip()[len("import "):]
                    if mod in seen:
                        continue
                    seen.add(mod)
                    if not os.path.exists(mod_path(mod)):
                        missing.add(mod)
    return sorted(missing)


def theorem_key(mod):
    parts = mod.split(".")
    leaf = parts[-1]
    if len(parts) >= 2 and parts[0] == "Theorems" and leaf.startswith("Thm_"):
        return leaf[len("Thm_"):]
    return None


def recover(mod):
    key = theorem_key(mod)
    if key is None:
        print("  skip (not a Theorems.Thm_* module): " + mod)
        return False
    queries = [key, key.split("_")[-1], key.replace("_", " ")]
    for q in queries:
        try:
            res = get("/theorems?" + urllib.parse.urlencode(
                {"q": q, "view": "compact", "limit": 50}))
        except Exception:
            continue
        rows = res.get("theorems", [])
        exact = [t for t in rows
                 if t.get("theorem_name", "").replace(".", "_") == key]
        if not exact:
            continue
        exact.sort(key=lambda t: t.get("status") != "Proved")
        tid = exact[0]["theorem_id"]
        subs = get("/theorems/" + tid + "/submissions?" + urllib.parse.urlencode(
            {"status": "ACCEPTED,SKETCH_ACCEPTED", "limit": 5, "offset": 0}))
        rows2 = subs.get("submissions", []) if isinstance(subs, dict) else subs
        for s in rows2:
            sid = s.get("submission_id") or s.get("id")
            try:
                sol = get("/submissions/" + str(sid) + "/solution")
            except Exception:
                continue
            content = sol.get("content", "")
            if not content:
                continue
            dst = mod_path(mod)
            if os.path.exists(dst):
                return True
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            open(dst, "w").write(content)
            print("  + " + mod + " (" + str(len(content)) + " B) <- "
                  + exact[0]["theorem_name"] + " [" + str(exact[0]["status"]) + "]", flush=True)
            return True
    print("  !! UNRECOVERABLE " + mod + " (key=" + key + ")", flush=True)
    return False


if __name__ == "__main__":
    TOK = refresh()
    for rnd in range(1, 13):
        missing = scan_missing()
        print("\n=== round " + str(rnd) + ": " + str(len(missing)) + " missing modules ===", flush=True)
        if not missing:
            print("FIXPOINT: no missing imports remain")
            break
        got = sum(1 for m in missing if recover(m))
        print("round " + str(rnd) + ": recovered " + str(got) + "/" + str(len(missing)), flush=True)
        if got == 0:
            print("STUCK: nothing recoverable in this round")
            break
