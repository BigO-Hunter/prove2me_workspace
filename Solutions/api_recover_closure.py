#!/usr/bin/env python3
"""Read-only recursive recovery of missing Theorems modules.

Same contract as Solutions/api_recover_r6.py: GET-only (plus the documented
/agent/refresh token exchange). No submission, no mutation, no status change.
Writes recovered accepted sources into Theorems/ ONLY where the module is absent.

Usage: python3 Solutions/api_recover_closure.py <Module.Path> [...]
"""
import json, os, sys, urllib.parse, urllib.request

BASE = "https://prove2.me/api/v1"
ROOT = "/Users/dmitri.arkhipov/prove2me_workspace"
creds = json.load(open(os.path.join(ROOT, "credentials.json")))


def refresh():
    req = urllib.request.Request(BASE + "/agent/refresh",
        data=json.dumps({"api_key": creds["api_key"]}).encode(),
        headers={"Content-Type": "application/json"}, method="POST")
    with urllib.request.urlopen(req, timeout=30) as r:
        return json.load(r).get("access_token")


TOK = None


def get(path):
    req = urllib.request.Request(BASE + path, headers={"Authorization": "Bearer " + TOK})
    with urllib.request.urlopen(req, timeout=90) as r:
        return json.load(r)


def mod_path(mod):
    return os.path.join(ROOT, mod.replace(".", "/") + ".lean")


def missing_imports(path):
    out = []
    for line in open(path):
        if line.startswith("import "):
            mod = line.strip()[len("import "):]
            if not os.path.exists(mod_path(mod)):
                out.append(mod)
    return out


def theorem_key(mod):
    """Theorems.Thm_A_B_C -> A_B_C, the module leaf with the Thm_ prefix stripped.

    The module naming is exactly invertible: a theorem's dotted name written with
    every '.' replaced by '_' IS the module leaf. Do not try to re-derive the dots
    -- identifiers like `rowUCC_of` contain underscores of their own.
    """
    leaf = mod.split(".")[-1]
    return leaf[len("Thm_"):] if leaf.startswith("Thm_") else leaf


def recover(mod):
    """Find the platform theorem for a module and write its accepted solution."""
    key = theorem_key(mod)
    leaf = key.split("_")[-1]
    # candidate search phrasings, most specific first
    queries = [key, leaf, "IntMul.Kappa.R6 " + leaf]
    cand = None
    for q in queries:
        try:
            res = get("/theorems?" + urllib.parse.urlencode(
                {"q": q, "view": "compact", "limit": 50}))
        except Exception as e:
            print(f"  search error {q!r}: {e}")
            continue
        rows = res.get("theorems", [])
        exact = [t for t in rows
                 if t.get("theorem_name", "").replace(".", "_") == key]
        if exact:
            exact.sort(key=lambda t: t.get("status") != "Proved")
            cand = exact[0]
            break
    if cand is None:
        print(f"  !! {mod}: no theorem with name ending .{leaf}")
        return False
    tid = cand["theorem_id"]
    print(f"  -> {tid} {cand['status']} {cand['theorem_name']}")
    subs = get(f"/theorems/{tid}/submissions?" + urllib.parse.urlencode(
        {"status": "ACCEPTED,SKETCH_ACCEPTED", "limit": 5, "offset": 0}))
    rows = subs.get("submissions", []) if isinstance(subs, dict) else subs
    for s in rows:
        sid = s.get("submission_id") or s.get("id")
        try:
            sol = get(f"/submissions/{sid}/solution")
        except Exception as e:
            print(f"     {str(sid)[:8]}: {e}")
            continue
        content = sol.get("content", "")
        if not content:
            continue
        dst = mod_path(mod)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        if os.path.exists(dst):
            print(f"     exists, skip {dst}")
            return True
        open(dst, "w").write(content)
        print(f"     wrote {os.path.relpath(dst, ROOT)} "
              f"({len(content)} bytes, {content.count(chr(10))} lines)")
        return True
    print(f"  !! {mod}: no accepted submission with content")
    return False


def closure(seeds, depth=4):
    TOK_GLOBAL = None
    todo = list(seeds)
    seen = set()
    for _ in range(depth):
        nxt = []
        for mod in todo:
            if mod in seen:
                continue
            seen.add(mod)
            print(f"[{mod}]")
            if not recover(mod):
                continue
            p = mod_path(mod)
            if os.path.exists(p):
                for m in missing_imports(p):
                    if m not in seen:
                        nxt.append(m)
        if not nxt:
            print("closure complete: no further missing imports")
            return
        todo = nxt
    print("depth limit reached; still missing:")
    for m in todo:
        print("  " + m)


if __name__ == "__main__":
    TOK = refresh()
    closure(sys.argv[1:])
