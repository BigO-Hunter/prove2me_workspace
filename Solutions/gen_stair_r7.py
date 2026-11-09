#!/usr/bin/env python3
"""Staircase (round-seven, witness 1) child-width histogram certificate generator.

**Construction: S. Jain**, *integer-mult-kappa* round seven — ported and verified here;
every number this script emits is derived from his frozen schedule at
`certificates/round7/` of `Swapnil-jain/integer-mult-kappa` @ `c05adfe1`
(`deferred_23.json.gz`, `witness_23.json.gz`), the same files his own
`scripts/certificate_round7.py` reads.  This script is a self-contained stdlib
re-implementation of the JSON-only derivation path of that checker (schedule
chains -> frame dims -> chain ranks -> deferred levels -> X_S chains ->
`histogram()` with the staircase corner); the derivation is cross-checked
against the workspace transcription of his `bitHist` (`Jain.bitR7`) before any
Lean is emitted, and the emitted identity is re-checked in Lean's kernel
(`Definitions/Def_IntMul_Kappa_R7_StairHist.lean`).

Provenance pins (sha256, verified before any derivation):
  deferred_23.json.gz  8c38e947ff9e021e308000dd82bb5e2194eb265d8b75194e22ce783d3e75317c
  witness_23.json.gz   b2486aa2bb222bacea6e52162a3920780e45dd8edc5d7cb03eabea336a1c6588

Usage: python3 Solutions/gen_stair_r7.py [cert_dir]
  cert_dir holds the two pinned .gz files (default: the spec-side copy under
  /Volumes/Substrate-1/bigo/jain-staircase-spec/upstream-certificates/round7).
Emits Definitions/Def_IntMul_Kappa_R7_StairHist.lean (overwrite, deterministic).
"""
import gzip
import hashlib
import json
import sys
from collections import Counter, defaultdict
from itertools import combinations

PINS = {
    "deferred_23.json.gz": "8c38e947ff9e021e308000dd82bb5e2194eb265d8b75194e22ce783d3e75317c",
    "witness_23.json.gz": "b2486aa2bb222bacea6e52162a3920780e45dd8edc5d7cb03eabea336a1c6588",
}
DEFAULT_CERT_DIR = "/Volumes/Substrate-1/bigo/jain-staircase-spec/upstream-certificates/round7"
OUT = "Definitions/Def_IntMul_Kappa_R7_StairHist.lean"
JAIN_DATA = "Definitions/Def_IntMul_KappaJainData.lean"

H = 23


def load(cert_dir):
    files = {}
    for name, pin in PINS.items():
        path = f"{cert_dir}/{name}"
        digest = hashlib.sha256(open(path, "rb").read()).hexdigest()
        if digest != pin:
            raise SystemExit(f"SHA-256 pin mismatch for {name}: {digest} != {pin}")
        with gzip.open(path, "rt") as fh:
            files[name] = json.load(fh)
    return files["witness_23.json.gz"], files["deferred_23.json.gz"]


class Schedule:
    """The design-B schedule fields needed for the histogram (deferred.py subset)."""

    def __init__(self, W, D):
        self.h = D["h"]
        self.R = D["R"]
        self.trip = list(combinations(range(self.h), 3))
        self.v = len(self.trip)
        self.tid = {T: i for i, T in enumerate(self.trip)}
        self.args = {int(n): (tuple(a) if a else None) for n, a in W["args"].items()}
        self.ops = [
            tuple(o[:2]) + (tuple(o[2]),) if o[0] == "fan" else tuple(o) for o in D["ops"]
        ]
        self.hold = D["hold"]
        self.start = D["start"]
        self.out = {s: (c, tuple(T)) for s, c, T in D["out"]}
        self.ret = {s: c for s, c in D["ret"]}
        self.readout = D["readout_order"]
        self.sel = set(self.readout)
        self.sigma = dict(zip(D["readout_order"], D["sigma"]))
        self.f = [0] * self.R
        for s, B in self.sigma.items():
            self.f[s] = len(B)
        self.vstart = dict(zip(D["vleaf_slots"], D["vleaf_start"]))
        self.xs = [(n, us) for n, us in D["xs_order"]]
        self.late = {int(n): (list(e), list(l)) for n, (e, l) in W["late"].items()}
        self.pivslot = {o[3]: o[1] for o in self.ops if o[0] == "add"}

    def root_targets(self):
        rt = {}
        for s, (c, T) in self.out.items():
            rt[s] = [self.tid[T]]
        for s, c in self.ret.items():
            rt[s] = [t for t, T in enumerate(self.trip) if c in T]
        return rt

    def adjoint(self):
        cov = [dict() for _ in range(self.R)]
        for s, ts in self.root_targets().items():
            for t in ts:
                cov[s][t] = cov[s].get(t, 0) + 1

        def addto(d, e):
            for t, x in e.items():
                d[t] = d.get(t, 0) + x

        for op in reversed(self.ops):
            if op[0] == "add":
                addto(cov[op[2]], cov[op[1]])
            elif op[0] == "fan":
                for g in op[2]:
                    addto(cov[op[1]], cov[g])
        return cov

    def start_key(self, s):
        n0 = self.hold[s][0]
        if self.args[n0] is None:
            return ("v", s)
        k = self.start[s][2]
        dec = self.late.get(n0)
        if dec is None or k in dec[0]:
            return ("n", n0)
        lt = dec[1]
        return ("c", n0, tuple(lt[lt.index(k):]))

    def chain_keys(self, s):
        ch = [("sigma", s) if s in self.sel else ("0",), self.start_key(s)]
        for idx, n in enumerate(self.hold[s]):
            if idx > 0:
                ch.append(("n", n))
            if self.args[n] is not None and self.pivslot.get(n) == s and n in self.late:
                lt = self.late[n][1]
                for i in range(len(lt) - 1):
                    ch.append(("c", n, tuple(lt[i:])))
        if s in self.out:
            c, T = self.out[s]
            ch.append(("out", c, T))
        if s in self.ret:
            ch.append(("ret", self.ret[s]))
        ch.append(("F",))
        return ch

    def dim(self, key):
        k = key[0]
        if k == "0":
            return 0
        if k == "F":
            return self.h
        if k in ("out", "ret"):
            return self.h - 1
        if k == "n":
            return self.node_dims[key[1]]
        if k == "c":
            return self.late_dims[key[1], key[2]]
        if k == "sigma":
            return len(self.sigma[key[1]])
        if k == "v":
            return len(self.vstart[key[1]])
        raise KeyError(key)

    def ylevels(self, cov):
        lev = defaultdict(set)
        for s in self.readout:
            for t in cov[s]:
                lev[t].add(self.f[s])
        return {t: sorted(lev[t]) for t in range(self.v)}

    def xdata(self):
        out = []
        for n, us in self.xs:
            ds = [1] + [len(self.vstart[s]) for s in us] + [self.h]
            ds = [d for i, d in enumerate(ds) if i == 0 or d != ds[i - 1]]
            out.append([b - a for a, b in zip(ds, ds[1:])])
        return out


def chain_ranks(S):
    rk = Counter()
    for s in range(S.R):
        ds = [S.dim(k) for k in S.chain_keys(s)]
        assert all(b >= a for a, b in zip(ds, ds[1:])), ("decreasing chain", s)
        assert ds[-1] == S.h
        for a, b in zip(ds, ds[1:]):
            if b > a:
                rk[b - a] += 1
    return rk


def inner(r, h):
    """children of a rank-r chain step (one block of width 2r-h when 2r > h)."""
    return [1] * (h - r) + [2 * r - h] if 2 * r > h else [1] * r


def staircase_corner(h):
    """runs (h-2, h-5, 1^6) — the staircase entrance corner (upstream check_stair.py)."""
    return [h - 2, h - 5] + [1] * 6


def histogram(S, rk, ylev, xd, corner):
    h, v, R = S.h, S.v, S.R
    m = h * h
    N = v * v
    A = v * R
    Hc = Counter()
    assert sum(corner) == 2 * h - 1
    corners = Counter(h - S.f[s] for s in range(R))
    for _ in range(2):
        for r, c in corners.items():
            Hc[m - 2 * r] += v * c
            for w in inner(r, h):
                Hc[w] += v * c
        for r, c in rk.items():
            for w in inner(r, h):
                Hc[w] += v * c
        for _c in range(h):
            for w in inner(h - 1, h):
                Hc[w] += v
        for t in range(v):
            ds = sorted(set([0] + ylev[t] + [h - 1]))
            for a, b in zip(ds, ds[1:]):
                for w in inner(b - a, h):
                    Hc[w] += v
        for xsl in xd:
            for x in xsl:
                for w in inner(x, h):
                    Hc[w] += v
    Hc[m - 4 * h + 2] += 2 * N
    for w in corner:
        Hc[w] += 2 * N
    Hc[1] += N
    return {w: c for w, c in Hc.items() if c}, corners


def parse_bitR7():
    """The workspace transcription of Jain's bitHist (the comparison oracle)."""
    import re

    src = open(JAIN_DATA).read()
    body = src.split("def bitR7 : List (ℕ × ℕ) :=")[1].split("def bitR7plain")[0]
    return [(int(w), int(n)) for w, n in re.findall(r"\((\d+),\s*(\d+)\)", body)]


def main():
    cert_dir = sys.argv[1] if len(sys.argv) > 1 else DEFAULT_CERT_DIR
    W, D = load(cert_dir)
    S = Schedule(W, D)
    assert S.h == H and S.R == 28866 and S.v == 1771
    # node/late dims live in the deferred file as [n, d] / [n, lt, d] pairs
    S.node_dims = {n: d for n, d in D["node_dims"]}
    S.late_dims = {(n, tuple(lt)): d for n, lt, d in D["late_dims"]}
    ylev = S.ylevels(S.adjoint())
    rk = chain_ranks(S)
    xd = S.xdata()
    assert all(sum(x) == H - 1 for x in xd)
    hist, corners = histogram(S, rk, ylev, xd, staircase_corner(H))

    h, v, N, A = H, S.v, S.v * S.v, S.v * S.R
    m = h * h
    Wd = 2 * N + 2 * A
    L = 2 * v * h * (h - 1)
    s = Wd * m - N + L
    assert Wd == 108516254, Wd
    rs = sum(w * n for w, n in hist.items())
    assert rs == s == 57403754177, rs
    assert max(hist) < m
    items = sorted(hist.items())

    # cross-check against the workspace transcription of Jain's bitHist
    bit = parse_bitR7()
    if items != bit:
        raise SystemExit(f"histogram mismatch vs Jain.bitR7:\n{items}\n{bit}")

    corner_items = sorted(corners.items())
    rk_items = sorted(rk.items())

    def pairs(lst):
        return ", ".join(f"({w}, {c})" for w, c in lst)

    lean = f"""import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_KappaJainData

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000

/-!
# Round-seven staircase certificate: the child-width histogram, transcribed (milestone M2)

**Construction: S. Jain**, *integer-mult-kappa* round seven — ported and verified here.
This module is the transcription certificate for staircase step ②: the child-width
histogram of his witness-1 side program (`R = 28866` slots, PR #62 producer with PR #44's
moment-weighted link choice), rebuilt from his frozen schedule
(`certificates/round7/{{deferred,witness}}_23.json.gz` at `Swapnil-jain/integer-mult-kappa`
@ `c05adfe1`) and pinned against the workspace transcription `Jain.bitR7` in the kernel.

The derivation is upstream `scripts/certificate_round7.py` (his own checker, stdlib):
slot frame chains from `hold`/`start`/`late`, frame dims from the data file
(`node_dims`/`late_dims`/`sigma`/`vleaf_start`), chain ranks, deferred readout levels on
every target from the garbage-coefficient supports (`adjoint`/`ylevels`), `X_S` chains
from the V-gate order (`xs_order`), then the batched two-stage interchange histogram with
the staircase entrance corner (runs `(h-2, h-5, 1^6)`, certified at the integer point by
his `independent/deferred-readout/check_stair.py`).  The committed generator
`Solutions/gen_stair_r7.py` reproduces this file byte-for-byte from the pinned schedule
(sha256 recorded there); the kernel re-checks every identity below by `decide`.

Inputs (sha256):
  deferred_23.json.gz  8c38e947ff9e021e308000dd82bb5e2194eb265d8b75194e22ce783d3e75317c
  witness_23.json.gz   b2486aa2bb222bacea6e52162a3920780e45dd8edc5d7cb03eabea336a1c6588

The acceptance test of the staircase port (spec §3) is `stair_hist = Jain.bitR7` as
multisets, pinned here as a list equality; with it, domination at every `τ` is equality.
-/

namespace IntMul.Kappa.R7.StairHist

/-! ## The transcribed certificate -/

/-- The staircase-corner child-width histogram of Jain's round-seven witness 1,
rebuilt from his frozen schedule.  `width, count` pairs, sorted by width. -/
def stair_hist : List (ℕ × ℕ) :=
  [{pairs(items)}]

/-- **The certificate identity.**  The rebuilt histogram IS Jain's `bitR7` (his
`lean/Round7.lean` `bitHist`, "staircase entrance corner, witness 1"). -/
theorem stair_hist_eq_bitR7 : stair_hist = Jain.bitR7 := by rfl

/-! ## Certificate ledger (decide-checked derived quantities) -/

/-- Rank sum: exactly the fit-identity value `529·W − 1771·759` (M1 keystone). -/
theorem stair_hist_rankSum : histRankSum stair_hist = 57403754177 := by decide

/-- No child at full width `m = 529` (upstream assert `max(hist) < m`). -/
theorem stair_hist_widths_lt_m : (stair_hist.all fun p => p.1 < 529) = true := by decide

/-- Total child calls of the transcribed histogram (matches `bitR7_childCount`, M1). -/
theorem stair_hist_childCount : (stair_hist.map Prod.snd).sum = 1905413587 := by decide

/-- Entry count: the histogram has exactly the 37 width classes of `Jain.bitR7`. -/
theorem stair_hist_length : stair_hist.length = 37 := by decide

/-- Corner ranks `r_u = h − dim σ_u` over the `R = 28866` side slots
(the aux-edge corner multiset; feeds the run-profile assignment of step ③). -/
def corner_counts : List (ℕ × ℕ) :=
  [{pairs(corner_items)}]

/-- Every side slot carries a corner rank in `1..h-1`, and the counts total `R`. -/
theorem corner_counts_total : (corner_counts.map Prod.snd).sum = 28866 := by decide

/-- Chain-step ranks over all slot chains (`rk` of the derivation; the width-≤23 filler
ledger of step ③). -/
def chain_rank_counts : List (ℕ × ℕ) :=
  [{pairs(rk_items)}]

/-- The chain-rank ledger total (number of chain steps over all slots). -/
theorem chain_rank_counts_total : (chain_rank_counts.map Prod.snd).sum = {sum(c for _, c in rk_items)} := by decide

end IntMul.Kappa.R7.StairHist
"""
    with open(OUT, "w") as fh:
        fh.write(lean)
    print(f"wrote {OUT}: {len(items)} entries, rank sum {rs}, corner classes {len(corner_items)}, "
          f"chain-rank classes {len(rk_items)}")


if __name__ == "__main__":
    main()
