#!/usr/bin/env python3
"""Structured search: dTPP(10,10,10) in SL2(5) with exact potential LP.

Pool = conjugacy-canonical coset-union families + random right-translations.
Distinctness |A*B|=100 via batched sort trick:
  P[a,b] = |A_a * A_b| == 100        (covers X=S*T and, via inversion
           bijectivity, Z: |U^-1 S^-1|=|(S U)^-1| -> P[si,ui])
  Q[a,b] = |inv(A_a) * A_b| == 100   (covers Y=T^-1*U -> Q[ti,ui])
Surviving triples -> dtpp.analyze (junk) -> dtpp.lp_verdict if njunk <= cap.
"""
import itertools, json, random, sys, time
from collections import Counter

import numpy as np

import dtpp

T0 = time.time()
DEADLINE = T0 + float(sys.argv[sys.argv.index("--deadline-sec") + 1])
LOG = open("/tmp/matmul-lane/results.jsonl", "a")
NJUNK_LP_CAP = int(sys.argv[sys.argv.index("--njunk-cap") + 1]) if "--njunk-cap" in sys.argv else 1500
LP_MAX = int(sys.argv[sys.argv.index("--lp-max") + 1]) if "--lp-max" in sys.argv else 4000
CAP_PER_FAM = int(sys.argv[sys.argv.index("--cap-fam") + 1]) if "--cap-fam" in sys.argv else 500
SEED = int(sys.argv[sys.argv.index("--seed") + 1]) if "--seed" in sys.argv else 1


def log(rec):
    rec["t"] = round(time.time() - T0, 1)
    LOG.write(json.dumps(rec, default=str) + "\n")
    LOG.flush()
    print(json.dumps(rec, default=str)[:300], flush=True)


def tl():
    return DEADLINE - time.time()


def main():
    rng = random.Random(SEED)
    els, idx, Mt, inv, n = dtpp.build_sl2(5)
    ID = idx[(1, 0, 0, 1)]   # identity index (NOT 0: els is lexicographic)
    log({"event": "start", "n": n, "identity_index": ID})
    orders = {}
    for g in range(n):
        x, o = g, 1
        while x != ID:
            x = int(Mt[x, g]); o += 1
        orders[g] = o

    def cyclic_subgroups(k):
        subs = set()
        for g in range(n):
            if orders[g] == k:
                e, x = set(), g
                while x not in e:
                    e.add(x); x = int(Mt[x, g])
                subs.add(frozenset(e))
        return [set(s) for s in subs]

    def left_cosets(H):
        seen, cos = set(), []
        for g in range(n):
            c = frozenset(int(Mt[g, h]) for h in H)
            if c not in seen:
                seen.add(c); cos.append(frozenset(c))
        return cos

    c5, c6, c4 = cyclic_subgroups(5), cyclic_subgroups(6), cyclic_subgroups(4)
    e2 = [g for g in range(n) if orders[g] == 2]
    H2 = {ID, e2[0]} if e2 else None
    log({"event": "subgroups", "c5": len(c5), "c6": len(c6), "c4": len(c4), "center2": bool(e2)})

    fam = {k: set() for k in ("2xC5", "C5xC5cross", "C6+C4", "C6+2Z2", "5Z2")}
    cos5 = [left_cosets(H) for H in c5]
    for cs in cos5:
        for a, b in itertools.combinations(range(len(cs)), 2):
            fam["2xC5"].add(cs[a] | cs[b])
    for h1, h2 in itertools.combinations(range(len(cos5)), 2):
        for a in cos5[h1]:
            for b in cos5[h2]:
                u = a | b
                if len(u) == 10:
                    fam["C5xC5cross"].add(u)
    for H6 in c6:
        for c6c in left_cosets(H6):
            for H4 in c4:
                for c4c in left_cosets(H4):
                    u = c6c | c4c
                    if len(u) == 10:
                        fam["C6+C4"].add(u)
    if H2:
        zc = left_cosets(H2)
        nz = len(zc)
        for H6 in c6:
            for c6c in left_cosets(H6):
                for a, b in itertools.combinations(range(nz), 2):
                    u = c6c | zc[a] | zc[b]
                    if len(u) == 10:
                        fam["C6+2Z2"].add(u)
        for _ in range(20000):
            combo = rng.sample(range(nz), 5)
            u = frozenset().union(*(zc[ci] for ci in combo))
            if len(u) == 10:
                fam["5Z2"].add(u)
    log({"event": "families-raw", **{k: len(v) for k, v in fam.items()}})

    # conjugation table: C[g,x] = g x g^-1
    C = Mt[Mt[:, :][:, :], :]  # placeholder; build properly below
    C = np.zeros((n, n), dtype=np.int64)
    for g in range(n):
        gi = int(inv[g])
        C[g] = Mt[Mt[g, :], gi]

    def canon_key(s_list):
        imgs = np.sort(C[:, list(s_list)], axis=1)
        best = None
        for r in imgs:
            t = r.tobytes()
            if best is None or t < best:
                best = t
        return best

    canon, fam_of = {}, {}
    for name, ss in fam.items():
        lst = sorted(ss)
        if len(lst) > CAP_PER_FAM:
            lst = rng.sample(lst, CAP_PER_FAM)
        kept = 0
        for s in lst:
            k = canon_key(s)
            if k not in canon:
                canon[k] = sorted(s)
                fam_of[k] = name
                kept += 1
        log({"event": "canon", "family": name, "sampled": len(lst), "new_classes": kept})

    base_keys = list(canon.keys())
    extra = 0
    for k in base_keys:
        if tl() < 0.85 * (DEADLINE - T0) * -1 + DEADLINE - T0:  # keep simple below
            pass
        if extra >= 600 or tl() < 1000:
            break
        s = canon[k]
        for _ in range(2):
            a = rng.randrange(n)
            t = sorted(int(Mt[x, a]) for x in s)
            k2 = canon_key(t)
            if k2 not in canon:
                canon[k2] = t
                fam_of[k2] = fam_of[k] + "+tr"
                extra += 1
    set_masks = list(canon.values())
    K = len(set_masks)
    log({"event": "pool", "K": K, "translations_added": extra})
    E = np.array(set_masks)             # (K,10)
    Einv = inv[E]                       # (K,10)

    # P[a,b]: |A_a * A_b| == 100 ; Q[a,b]: |inv(A_a) * A_b| == 100
    def build_PQ(rowsrc):
        Pm = np.zeros((K, K), dtype=bool)
        for si in range(K):
            V = Mt[rowsrc[si]][:, E]              # (10,K,10)
            V2 = np.transpose(V, (1, 0, 2)).reshape(K, 100)
            S = np.sort(V2, axis=1)
            Pm[si] = np.all(np.diff(S, axis=1) != 0, axis=1)
        return Pm

    t0 = time.time()
    P = build_PQ(E)
    Q = build_PQ(Einv)
    log({"event": "PQ-done", "secs": round(time.time() - t0, 1),
         "P_density": round(float(P.mean()), 4), "Q_density": round(float(Q.mean()), 4)})

    pairs = np.argwhere(P)
    log({"event": "pairs-ST", "count": len(pairs)})
    order = np.random.default_rng(SEED).permutation(len(pairs))

    ntrip = nlp = 0
    njunks = []
    verdicts = Counter()
    margins = []
    pairs_covered = 0
    for oi in order:
        if tl() < 240 or nlp >= LP_MAX:
            break
        si, ti = int(pairs[oi, 0]), int(pairs[oi, 1])
        pairs_covered += 1
        ucand = np.nonzero(P[si] & Q[ti])[0]
        for ui in ucand:
            if tl() < 240 or nlp >= LP_MAX:
                break
            ui = int(ui)
            ntrip += 1
            r = dtpp.analyze(Mt, inv, n, set_masks[si], set_masks[ti], set_masks[ui])
            if not r["ok"]:
                continue
            njunks.append(r["njunk"])
            if r["njunk"] <= NJUNK_LP_CAP:
                nlp += 1
                v, marg, w = dtpp.lp_verdict(n, r)
                verdicts[v] += 1
                margins.append((round(marg, 6), v, si, ti, ui, r["njunk"]))
                if v.startswith("FEASIBLE"):
                    log({"event": "FEASIBLE!!!", "verdict": v, "margin": marg,
                         "S": set_masks[si], "T": set_masks[ti], "U": set_masks[ui],
                         "njunk": r["njunk"], "fams": [fam_of.get(canon_key(x), "?") for x in
                                 (set_masks[si], set_masks[ti], set_masks[ui])]})
            if ntrip and ntrip % 3000 == 0:
                log({"event": "trip-progress", "ntrip": ntrip, "nlp": nlp,
                     "njunk_min": min(njunks) if njunks else None})
    njunks.sort()
    log({"event": "done", "pairs_total": len(pairs), "pairs_covered": pairs_covered,
         "trips_distinct": ntrip, "lps": nlp, "verdicts": dict(verdicts),
         "njunk_dist": {"n": len(njunks), "min10": njunks[:10],
                        "med": njunks[len(njunks)//2] if njunks else None,
                        "max": njunks[-1] if njunks else None},
         "min_margins": sorted(margins)[:10]})


if __name__ == "__main__":
    try:
        main()
    except BaseException:
        import traceback
        tb = traceback.format_exc()
        log({"event": "CRASH", "tb": tb[-3000:]})
        raise
