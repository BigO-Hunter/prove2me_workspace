#!/usr/bin/env python3
"""Read-only recovery of accepted sources for the subtracted R6 machinery.

GET-only (plus the documented /agent/refresh token exchange). No submission,
no mutation. Sources land in Solutions/recovered/.
"""
import json, os, urllib.parse, urllib.request

BASE = "https://prove2.me/api/v1"
ROOT = "/Users/dmitri.arkhipov/prove2me_workspace"
OUT = os.path.join(ROOT, "Solutions", "recovered")
os.makedirs(OUT, exist_ok=True)
creds = json.load(open(os.path.join(ROOT, "credentials.json")))


def refresh():
    req = urllib.request.Request(BASE + "/agent/refresh",
        data=json.dumps({"api_key": creds["api_key"]}).encode(),
        headers={"Content-Type": "application/json"}, method="POST")
    with urllib.request.urlopen(req, timeout=30) as r:
        return json.load(r).get("access_token")


def get(path, token):
    req = urllib.request.Request(BASE + path, headers={"Authorization": "Bearer " + token})
    with urllib.request.urlopen(req, timeout=90) as r:
        return json.load(r)


TARGETS = {
    "r6_normalize": "07692ff8",
    "rG_normalize": "a8b367da",
    "p14Need6_all": "7d2bd1d2",
    "p14NeedG_all": "2f863fbf",
    "kappaBound_of_machine6": "6fd48450",
    "kappa_final6": "6a4a68e3",
    "kappa_final6_at": "d1e95d20",
    "bitNetR7_mom": "e27d1a90",
}
FULL = {}
tok = refresh()

# resolve full ids via keyword search (search returns 8-char prefixes above)
for label, pre in TARGETS.items():
    res = get("/theorems?" + urllib.parse.urlencode(
        {"q": "IntMul.Kappa.R6 " + label, "view": "compact", "limit": 40}), tok)
    cand = [t for t in res.get("theorems", [])
            if t.get("theorem_id", "").startswith(pre)]
    if not cand:
        print(f"!! {label}: no theorem matching prefix {pre}")
        continue
    FULL[label] = cand[0]["theorem_id"]
    print(f"{label}: {cand[0]['theorem_id']} {cand[0]['status']} {cand[0]['theorem_name']}")

for label, tid in FULL.items():
    # statement
    th = get(f"/theorems/{tid}", tok)
    open(os.path.join(OUT, f"{label}.statement.lean"), "w").write(
        "-- " + json.dumps({k: th.get(k) for k in
                            ("theorem_id", "theorem_name", "status", "preamble")},
                           ensure_ascii=False) + "\n"
        + (th.get("formal_statement") or "") + "\n")
    try:
        subs = get(f"/theorems/{tid}/submissions?"
                   + urllib.parse.urlencode({"status": "ACCEPTED,SKETCH_ACCEPTED",
                                             "limit": 5, "offset": 0}), tok)
    except Exception as e:
        print(f"!! {label}: submissions error {e}")
        continue
    rows = subs.get("submissions", []) if isinstance(subs, dict) else subs
    print(f"{label}: {len(rows)} accepted submission(s)")
    for s in rows[:2]:
        sid = s.get("submission_id") or s.get("id")
        try:
            sol = get(f"/submissions/{sid}/solution", tok)
        except Exception as e:
            print(f"   - {sid[:8]}: solution error {e}")
            continue
        content = sol.get("content", "")
        path = os.path.join(OUT, f"{label}.{str(sid)[:8]}.lean")
        open(path, "w").write(content)
        print(f"   - {sid[:8]} -> {os.path.relpath(path, ROOT)} ({len(content)} bytes, "
              f"{content.count(chr(10))} lines)")
