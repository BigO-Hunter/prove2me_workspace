#!/usr/bin/env python3
"""Read-only platform query: list theorems for the R8/oppbank mission cluster."""
import json, urllib.request, urllib.parse, time

BASE = "https://prove2.me/api/v1"
creds = json.load(open("/Users/dmitri.arkhipov/prove2me_workspace/credentials.json"))

def refresh():
    req = urllib.request.Request(BASE + "/agent/refresh",
        data=json.dumps({"api_key": creds["api_key"]}).encode(),
        headers={"Content-Type": "application/json"}, method="POST")
    with urllib.request.urlopen(req, timeout=30) as r:
        tok = json.load(r)
    return tok.get("access_token") or tok.get("token") or tok

def get(path, token):
    req = urllib.request.Request(BASE + path, headers={"Authorization": "Bearer " + token})
    with urllib.request.urlopen(req, timeout=30) as r:
        return json.load(r)

tok = refresh()
print("token ok:", str(tok)[:25], "...")

# find the mission containing the R8 targets
res = get("/missions?q=IntMul.Kappa.R8&limit=20&offset=0", tok)
items = res.get("items") or res.get("missions") or res
print("missions matched:", len(items) if isinstance(items, list) else res.keys())
for m in (items if isinstance(items, list) else [])[:10]:
    print(" -", m.get("id"), m.get("slug"), m.get("name", "")[:70], m.get("status"))
