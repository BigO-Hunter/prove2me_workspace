#!/usr/bin/env python3
"""Read-only: open-leaves frontier of the R8 mission main theorem + graph."""
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
m = get(f"/missions/{MID}", tok)
mt = m.get("main_theorem") or {}
tid = mt.get("theorem_id") or m.get("main_theorem_id")
print("main theorem:", tid, (mt.get("name") or m.get("name", ""))[:70], "status:", mt.get("status"))

res = get(f"/theorems/{tid}/open-leaves?limit=40&offset=0", tok)
items = res.get("items") if isinstance(res, dict) else res
total = res.get("total", "?") if isinstance(res, dict) else "?"
print(f"open leaves: {len(items) if items else 0} (total {total})")
for t in (items or []):
    print(f"  {t.get('id','?')[:8]} close={t.get('closability','?'):>2} {(t.get('name') or '')[:72]}")
