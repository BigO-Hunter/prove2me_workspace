#!/usr/bin/env python3
"""Read-only: list all theorems of the Jain round-eight mission (51a41d26...)."""
import json, urllib.request

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
    with urllib.request.urlopen(req, timeout=30) as r:
        return json.load(r)

tok = refresh()
MID = "51a41d26-9435-4580-bdce-b7bab34f1b4c"
for off in (0, 50, 100):
    res = get(f"/missions/{MID}/theorems?limit=50&offset={off}", tok)
    items = res.get("items") if isinstance(res, dict) else res
    if not items:
        break
    for t in items:
        st = t.get("status")
        name = (t.get("name") or "")[:60]
        print(f"{t.get('id','?')[:8]} {st:12} {name}")
    if len(items) < 50:
        break
