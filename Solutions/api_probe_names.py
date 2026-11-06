#!/usr/bin/env python3
"""Read-only probe: find published theorems by identifier substring. GET-only."""
import json, sys, urllib.parse, urllib.request

BASE = "https://prove2.me/api/v1"
creds = json.load(open("credentials.json"))
req = urllib.request.Request(BASE + "/agent/refresh",
    data=json.dumps({"api_key": creds["api_key"]}).encode(),
    headers={"Content-Type": "application/json"}, method="POST")
tok = json.load(urllib.request.urlopen(req, timeout=30))["access_token"]


def get(p):
    r = urllib.request.Request(BASE + p, headers={"Authorization": "Bearer " + tok})
    return json.load(urllib.request.urlopen(r, timeout=90))


for q in sys.argv[1:]:
    try:
        res = get("/theorems?" + urllib.parse.urlencode(
            {"q": q, "view": "compact", "limit": 20}))
    except Exception as e:
        print(q, "ERR", e)
        continue
    rows = res.get("theorems", [])
    print(f"{q} -> {len(rows)} hits")
    for t in rows[:10]:
        print("   ", t.get("theorem_id", "")[:8], t.get("status"), t.get("theorem_name"))
