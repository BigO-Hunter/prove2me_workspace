#!/usr/bin/env python3
"""Read-only: enumerate R7 / PR#62 mission theorems + their submission statuses.

Read-only in the strict sense: only GET requests (plus the documented
`/agent/refresh` token exchange, which mutates nothing). No submissions.
"""
import json, sys, urllib.request

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
MISSIONS = {
    "07a39c83-e65b-47a1-b829-8cfb18ed46c4": "Jain round seven",
    "534241e5-3742-47b2-9c87-b482c1fa54f3": "community PR #62",
    "51a41d26-9435-4580-bdce-b7bab34f1b4c": "Jain round eight",
}
for MID, label in MISSIONS.items():
    print(f"===== {label} ({MID}) =====")
    for off in range(0, 400, 50):
        res = get(f"/missions/{MID}/theorems?limit=50&offset={off}", tok)
        items = res.get("items") if isinstance(res, dict) else res
        if not items:
            break
        for t in items:
            print(f"  {t.get('id','?')[:8]} {str(t.get('status')):16} {(t.get('name') or '')[:80]}")
        if len(items) < 50:
            break
