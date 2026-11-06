#!/usr/bin/env python3
"""Read-only: keyword-search platform theorems for the missing R6/R7 machinery.

GET-only (plus the documented /agent/refresh token exchange). Nothing is submitted.
"""
import json, sys, urllib.parse, urllib.request

BASE = "https://prove2.me/api/v1"
creds = json.load(open("/Users/dmitri.arkhipov/prove2me_workspace/credentials.json"))


def refresh():
    req = urllib.request.Request(BASE + "/agent/refresh",
        data=json.dumps({"api_key": creds["api_key"]}).encode(),
        headers={"Content-Type": "application/json"}, method="POST")
    with urllib.request.urlopen(req, timeout=30) as r:
        return json.load(r).get("access_token")


def get(path, token):
    req = urllib.request.Request(BASE + path, headers={"Authorization": "Bearer " + token})
    with urllib.request.urlopen(req, timeout=60) as r:
        return json.load(r)


tok = refresh()
for q in sys.argv[1:]:
    p = "/theorems?" + urllib.parse.urlencode({"q": q, "view": "compact", "limit": 40})
    try:
        res = get(p, tok)
    except Exception as e:
        print(f"== {q!r}: ERROR {e}")
        continue
    rows = res.get("theorems", [])
    print(f"== {q!r}: {res.get('total')} total, showing {len(rows)}")
    for t in rows:
        print(f"   {t.get('theorem_id','?')[:8]} {str(t.get('status')):12} {t.get('theorem_name','')[:95]}")
