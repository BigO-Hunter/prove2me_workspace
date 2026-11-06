#!/usr/bin/env python3
"""dTPP search for SL2(5) at (10,10,10) — bounded probe of fringewidth's open target.

Framework (Cohn-Umans + fringewidth part-2 dTPP definition):
  S,T,U subsets of G. x_{ij}=s_i t_j, y_{jk}=t_j^-1 u_k, z_{ki}=u_k^-1 s_i^-1.
  x_ij y_jk z_ki = 1 (matmul triples); other index combos with x y z = 1 are junk.
  dTPP potential: w: G -> Z with
    (E) w(x_ij)+w(y_jk)+w(z_ki) = 0   for all i,j,k
    (J) w(x)+w(y)+w(z) >= 1           for every junk triple
  => eps-degeneration of group-algebra tensor (rank |G|) limits to <a,b,c>
  => border rank <= |G|. Square (n,n,n): n^omega <= |G|. For (10,10,10) in
  SL2(5): 10^omega <= 120 => omega <= 2.0792 < 9/4.
  Requires pair-injectivity (distinctness of X, Y, Z images).

LP: HiGHS in w-space (rational polytope => rational vertices). FEASIBLE claims
get exact Fraction verification (propose & dispose). INFEASIBLE gets a phase-1
margin s* (>0 = every w violates some junk row by >= s* after uniform shift).
"""
import itertools, json, random, sys, time
from collections import Counter
from fractions import Fraction

import numpy as np
from scipy.optimize import linprog

T0 = time.time()
DEADLINE = T0 + (float(sys.argv[sys.argv.index("--deadline-sec") + 1])
                 if "--deadline-sec" in sys.argv else 2100)
OUT = open("/tmp/matmul-lane/results.jsonl", "a")


def log(rec):
    rec["t"] = round(time.time() - T0, 1)
    OUT.write(json.dumps(rec, default=str) + "\n")
    OUT.flush()
    print(json.dumps(rec, default=str)[:300], flush=True)


def time_left():
    return DEADLINE - time.time()


def build_sl2(q=5):
    els = [(a, b, c, d) for a in range(q) for b in range(q) for c in range(q) for d in range(q)
           if (a * d - b * c) % q == 1]
    idx = {e: i for i, e in enumerate(els)}
    n = len(els)
    M = np.zeros((n, n), dtype=np.int64)
    inv = np.zeros(n, dtype=np.int64)
    for i, (a, b, c, d) in enumerate(els):
        inv[i] = idx[(d % q, (-b) % q, (-c) % q, a % q)]
        for j, (e, f, g, h) in enumerate(els):
            M[i, j] = idx[((a * e + b * g) % q, (a * f + b * h) % q,
                            (c * e + d * g) % q, (c * f + d * h) % q)]
    return els, idx, M, inv, n


def analyze(M, inv, n, S, T, U):
    S = np.asarray(S); T = np.asarray(T); U = np.asarray(U)
    sa, tb, uc = len(S), len(T), len(U)
    X = M[S[:, None], T[None, :]]
    Y = M[inv[T][:, None], U[None, :]]
    Z = M[inv[U][:, None], inv[S][None, :]]
    Xf, Yf, Zf = X.reshape(-1), Y.reshape(-1), Z.reshape(-1)
    res = {"sa": sa, "tb": tb, "uc": uc, "ok": False}
    if len(set(Xf.tolist())) != sa * tb or len(set(Yf.tolist())) != tb * uc \
       or len(set(Zf.tolist())) != uc * sa:
        return res
    res["ok"] = True
    zl = np.full(n, -1, dtype=np.int64)
    zl[Zf] = np.arange(uc * sa)
    P = M[Xf[:, None], Yf[None, :]]
    C = zl[inv[P]]
    a_idx, b_idx = np.nonzero(C >= 0)
    c_idx = C[a_idx, b_idx]
    i_, j_ = a_idx // tb, a_idx % tb
    j2, k_ = b_idx // uc, b_idx % uc
    k2, i2 = c_idx // sa, c_idx % sa
    jm = (j2 != j_) | (k2 != k_) | (i2 != i_)
    res["junk"] = (Xf[a_idx[jm]], Yf[b_idx[jm]], Zf[c_idx[jm]])
    res["njunk"] = int(jm.sum())
    I, J, K = np.meshgrid(np.arange(sa), np.arange(tb), np.arange(uc), indexing="ij")
    res["eq"] = (X[I, J].reshape(-1), Y[J, K].reshape(-1), Z[K, I].reshape(-1))
    return res


def _eq_matrix(n, res):
    eqx, eqy, eqz = res["eq"]
    m = len(eqx)
    rows = {}
    for a in range(m):
        key = (int(eqx[a]), int(eqy[a]), int(eqz[a]))
        rows.setdefault(key, []).append(a)
    uniq = sorted(rows)
    E = np.zeros((len(uniq), n))
    for r, (x, y, z) in enumerate(uniq):
        E[r, x] += 1.0; E[r, y] += 1.0; E[r, z] += 1.0
    return np.unique(E, axis=0)


def lp_verdict(n, res, exact=True):
    """Returns (verdict, margin, w_exact_Fraction_list_or_None)."""
    E = _eq_matrix(n, res)
    if res["njunk"] == 0:
        return ("FEASIBLE-nojunk", 1.0, [Fraction(0)] * n)
    jx, jy, jz = res["junk"]
    m = len(jx)
    J = np.zeros((m, n))
    J[np.arange(m), jx] += 1.0
    J[np.arange(m), jy] += 1.0
    J[np.arange(m), jz] += 1.0
    free = [(None, None)] * n
    # feasibility: E w = 0, J w >= 1  <=>  -J w <= -1
    r = linprog(np.zeros(n), A_ub=-J, b_ub=-np.ones(m), A_eq=E, b_eq=np.zeros(len(E)),
                bounds=free, method="highs")
    if r.status == 0:
        w = r.x
        if exact:
            wF = [Fraction(float(v)).limit_denominator(10**12) for v in w]
            eqx, eqy, eqz = res["eq"]
            eqs_ok = all(wF[eqx[a]] + wF[eqy[a]] + wF[eqz[a]] == 0 for a in range(len(eqx)))
            jsums = [wF[jx[t]] + wF[jy[t]] + wF[jz[t]] for t in range(m)]
            mn = min(jsums) if jsums else Fraction(1)
            if eqs_ok and mn > 0:
                wF = [v / mn for v in wF]     # junk sums >= 1, equalities still 0
                return ("FEASIBLE-EXACT", float(mn), wF)
        return ("FEASIBLE-float", 0.0, None)
    if r.status == 2:  # infeasible -> phase-1 margin: min s, Jw + s >= 1, Ew = 0, s >= 0
        A_ub = np.hstack([-J, -np.ones((m, 1))])
        b_ub = -np.ones(m)
        c = np.zeros(n + 1); c[-1] = 1.0
        r2 = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=np.hstack([E, np.zeros((len(E), 1))]),
                     b_eq=np.zeros(len(E)), bounds=free + [(0, None)], method="highs")
        s_star = float(r2.x[-1]) if r2.status == 0 else float("nan")
        return ("INFEASIBLE", s_star, None)
    return ("LP-ERROR-status%d" % r.status, 0.0, None)


def validate():
    out = {}
    els = [(a, b, c) for a in range(3) for b in range(3) for c in range(3)]
    idx = {e: i for i, e in enumerate(els)}
    n = 27
    M = np.zeros((n, n), dtype=np.int64); inv = np.zeros(n, dtype=np.int64)
    for i, (a, b, c) in enumerate(els):
        inv[i] = idx[(-a % 3, -b % 3, -c % 3)]
        for j, (d, e, f) in enumerate(els):
            M[i, j] = idx[((a + d) % 3, (b + e) % 3, (c + f) % 3)]
    S = [idx[(a, 0, 0)] for a in range(3)]
    T = [idx[(0, b, 0)] for b in range(3)]
    U = [idx[(0, 0, c)] for c in range(3)]
    r = analyze(M, inv, n, S, T, U)
    out["p1_genuine_tpp_z33"] = {"ok": r["ok"], "njunk": r.get("njunk"),
                                 "verdict": lp_verdict(n, r)[0] if r["ok"] else None}
    rr = {"njunk": 1, "junk": (np.array([0]), np.array([1]), np.array([2])),
          "eq": (np.array([0]), np.array([1]), np.array([2])), "ok": True}
    v = lp_verdict(4, rr)
    out["p3_infeasible_unit"] = {"verdict": v[0], "margin": round(v[1], 4)}  # want INFEASIBLE 1.0
    rr2 = {"njunk": 1, "junk": (np.array([0]), np.array([1]), np.array([3])),
           "eq": (np.array([0]), np.array([1]), np.array([2])), "ok": True}
    v2 = lp_verdict(4, rr2)
    out["p2_feasible_unit"] = {"verdict": v2[0], "margin": round(v2[1], 6)}  # want FEASIBLE-EXACT
    # p4: real SL2(5) 3x3x3 probe -> exercises analyze on 120-group
    _, _, M5, inv5, n5 = build_sl2(5)
    rng = random.Random(7)
    tries = 0
    while tries < 5000:
        tries += 1
        S = rng.sample(range(n5), 3); T = rng.sample(range(n5), 3); U = rng.sample(range(n5), 3)
        r4 = analyze(M5, inv5, n5, S, T, U)
        if r4["ok"]:
            v4 = lp_verdict(n5, r4)
            out["p4_sl25_333_sample"] = {"tries": tries, "njunk": r4["njunk"], "verdict": v4[0]}
            break
    log({"event": "validation", **out})


def greedy_triple(M, inv, n, rng, size=10):
    """Build (S,T,U) with pair-injectivity by incremental greedy choice."""
    S = rng.sample(range(n), size)
    Sarr = np.array(S)
    T, xseen = [], set()
    order = list(range(n)); rng.shuffle(order)
    for t in order:
        prods = M[Sarr, t]
        if not (set(prods.tolist()) & xseen):
            T.append(t); xseen |= set(prods.tolist())
            if len(T) == size: break
    if len(T) < size: return None
    Tarr = np.array(T)
    invT = inv[Tarr]
    U, yseen, zseen = [], set(), set()
    invS = inv[Sarr]
    order2 = list(range(n)); rng.shuffle(order2)
    for u in order2:
        ys = M[invT, u]
        zs = M[inv[u], invS]
        if not (set(ys.tolist()) & yseen) and not (set(zs.tolist()) & zseen):
            U.append(u); yseen |= set(ys.tolist()); zseen |= set(zs.tolist())
            if len(U) == size: break
    if len(U) < size: return None
    return S, T, U


def main():
    els, idx, M, inv, n = build_sl2(5)
    assert n == 120
    ID = idx[(1, 0, 0, 1)]
    orders = {}
    for g in range(n):
        x, o = g, 1
        while x != ID:
            x = int(M[x, g]); o += 1
        orders[g] = o
    log({"event": "group", "n": n, "order_counts": dict(sorted(Counter(orders.values()).items())),
         "cert_if_found": "10^omega<=120 => omega<=2.0792"})

    def subgroups_of_order(k):
        subs = set()
        for g in range(n):
            if orders[g] == k or (k % orders[g] == 0 and orders[g] > 1):
                elems, x = set(), g
                while x not in elems:
                    elems.add(x); x = int(M[x, g])
                if len(elems) == k:
                    subs.add(frozenset(elems))
        return [set(s) for s in subs]

    def left_cosets(H):
        seen, cos = set(), []
        for g in range(n):
            c = frozenset(int(M[g, h]) for h in H)
            if c not in seen:
                seen.add(c); cos.append(sorted(c))
        return cos

    def conj_canon(fset):
        best = None
        for g in range(n):
            gi = int(inv[g])
            t = tuple(sorted(int(M[M[g, x], gi]) for x in fset))
            if best is None or t < best:
                best = t
        return best

    c5 = subgroups_of_order(5)
    c6 = subgroups_of_order(6)
    c4 = subgroups_of_order(4)
    e2 = [g for g in range(n) if orders[g] == 2]
    fams = {}
    sets = set()
    for H in c5:
        cs = left_cosets(H)
        for a, b in itertools.combinations(range(len(cs)), 2):
            sets.add(frozenset(cs[a] + cs[b]))
    fams["2xC5coset"] = sets
    sets2 = set()
    for H6 in c6:
        for c6c in left_cosets(H6):
            for H4 in c4:
                for c4c in left_cosets(H4):
                    if not (set(c6c) & set(c4c)):
                        sets2.add(frozenset(c6c + c4c))
    fams["C6+C4coset"] = sets2
    sets3 = set()
    if e2:
        H2 = {0, e2[0]}
        zcos = left_cosets(H2)
        for H6 in c6:
            for c6c in left_cosets(H6):
                for a, b in itertools.combinations(range(len(zcos)), 2):
                    u = set(c6c) | set(zcos[a]) | set(zcos[b])
                    if len(u) == 10:
                        sets3.add(frozenset(u))
    fams["C6+2xZ2coset"] = sets3
    log({"event": "subgroups", "c5": len(c5), "c6": len(c6), "c4": len(c4), "e2": len(e2),
         "fam_raw": {k: len(v) for k, v in fams.items()}})

    canon = {}
    for name, ss in fams.items():
        for s in ss:
            canon.setdefault(conj_canon(s), sorted(s))
    allsets = list(canon.values())
    K = len(allsets)
    log({"event": "search-start", "canon_sets": K})

    # stage 1: structured (S,T,U) over canonical coset-family sets
    npairs = ntrip = nlp = 0
    verdicts = Counter(); margins = []; best = []
    A = [np.array(s) for s in allsets]
    covered_si = 0
    for si in range(K):
        if time_left() < 420: break
        covered_si = si + 1
        S = A[si]
        for ti in range(K):
            if time_left() < 420: break
            T = A[ti]
            X = M[S[:, None], T[None, :]]
            if len(set(X.reshape(-1).tolist())) != 100:
                continue
            npairs += 1
            invT = inv[T]
            for ui in range(K):
                if time_left() < 420: break
                U = A[ui]
                Y = M[invT[:, None], U[None, :]]
                if len(set(Y.reshape(-1).tolist())) != 100: continue
                Z = M[inv[U][:, None], inv[S][None, :]]
                if len(set(Z.reshape(-1).tolist())) != 100: continue
                ntrip += 1
                r = analyze(M, inv, n, S, T, U)
                best.append((r["njunk"], si, ti, ui))
                if r["njunk"] <= 1500 and nlp < 3000 and time_left() > 480:
                    nlp += 1
                    v, marg, w = lp_verdict(n, r)
                    verdicts[v] += 1
                    margins.append((round(marg, 6), v, si, ti, ui, r["njunk"]))
                    if v.startswith("FEASIBLE"):
                        log({"event": "FEASIBLE!!!", "verdict": v, "margin": marg,
                             "S": allsets[si], "T": allsets[ti], "U": allsets[ui],
                             "njunk": r["njunk"]})
    best.sort()
    log({"event": "done-structured", "covered_S_sets": covered_si, "of": K,
         "pairs_ST_distinct": npairs, "trips_distinct": ntrip, "lps_run": nlp,
         "verdicts": dict(verdicts), "min_njunk_top5": best[:5],
         "min_infeas_margin_top5": sorted(margins)[:5]})

    # stage 2: greedy-random
    rng = random.Random(12345)
    samples = built = nlp2 = 0
    v2 = Counter(); marg2 = []
    while time_left() > 45 and samples < 200000:
        samples += 1
        trip = greedy_triple(M, inv, n, rng, 10)
        if trip is None: continue
        built += 1
        S, T, U = trip
        r = analyze(M, inv, n, S, T, U)
        if not r["ok"]: continue
        if r["njunk"] <= 1500 and time_left() > 60 and nlp2 < 1500:
            nlp2 += 1
            v, marg, w = lp_verdict(n, r)
            v2[v] += 1
            marg2.append((round(marg, 6), v, r["njunk"]))
            if v.startswith("FEASIBLE"):
                log({"event": "FEASIBLE-random!!!", "verdict": v, "S": S, "T": T, "U": U,
                     "njunk": r["njunk"]})
    log({"event": "done-random", "samples": samples, "greedy_built": built,
         "lps_run": nlp2, "verdicts": dict(v2),
         "min_infeas_margin_top5": sorted(marg2)[:5]})


if __name__ == "__main__":
    validate()
    main()
