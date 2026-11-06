#!/usr/bin/env python3
"""Exact replication of NB.cs1/cs2 chunk-move rank histograms (per pass).

Parses the packed Nat tables (packL = 65536-bit little-endian limbs) directly
from the Lean definition files, rebuilds W1F/W2F instruction lists, runs the
genF fold with dicts, and histograms rkC(oldCode, newCode) over all moves.
Cross-checked against Lean's own #eval of W1F.length = 237921 and
touch-total = 536840.
"""
import re, sys
from collections import Counter

DEFS = "/Users/dmitri.arkhipov/prove2me_workspace/Definitions/"

def parse_packl(path, name):
    src = open(path).read()
    m = re.search(r"def %s : Nat :=\s*\n?\s*packL\s*\[(.*?)\]" % name, src, re.S)
    if not m:
        raise SystemExit(f"table {name} not found in {path}")
    limbs = [int(h, 16) for h in re.findall(r"0x[0-9a-fA-F]+", m.group(1))]
    # packL l = foldr lor (shiftLeft acc 65536) — little-endian 65536-bit limbs
    LIMB = 1 << 65536
    v = 0
    for limb in reversed(limbs):  # foldr: last limb is most significant
        v = (v << 65536) | limb
    return v

def field_of(X, w, i):
    return (X >> (w * i)) & ((1 << w) - 1)

# ---- tables ----
TPTS = parse_packl(DEFS + "Def_IntMul_Kappa_R8_Data_BitOppbankLocSlots.lean", "TPTS")
INJ  = parse_packl(DEFS + "Def_IntMul_Kappa_R8_Data_BitOppbankLocSlots.lean", "INJ")
RETS = parse_packl(DEFS + "Def_IntMul_Kappa_R8_Data_BitOppbankLocSlots.lean", "RETS")
RETN = parse_packl(DEFS + "Def_IntMul_Kappa_R8_Data_BitOppbankLocSlots.lean", "RETN")
SRC  = parse_packl(DEFS + "Def_IntMul_Kappa_R8_Data_BitOppbankLocSlots.lean", "SRC")
DIMT = parse_packl(DEFS + "Def_IntMul_Kappa_R8_Data_BitOppbankChkBitArg.lean", "DIMT")
SG1_0 = parse_packl(DEFS + "Def_IntMul_Kappa_R8_Data_BitOppbankGenData_0.lean", "SG1_0")
SG2_0 = parse_packl(DEFS + "Def_IntMul_Kappa_R8_Data_BitOppbankGenData_2.lean", "SG2_0")

# GREC: List Nat (not packL) — list of 16-bit-field limbs? read the file
def parse_listnat(path, name):
    src = open(path).read()
    m = re.search(r"def %s : List [ℕN] :=\s*\n?\s*\[(.*?)\]" % name, src, re.S)
    if not m:
        raise SystemExit(f"list {name} not found in {path}")
    return [int(h, 16) for h in re.findall(r"0x[0-9a-fA-F]+", m.group(1))]

# GREC might be packL or List — check LocGrecDense source
gsrc = open(DEFS + "Def_IntMul_Kappa_R8_Data_BitOppbankLocGrecDense.lean").read()
m = re.search(r"def GREC : List [ℕN] :=\s*\n?\s*\[", gsrc)
if "List" in m.group(0):
    GREC = parse_listnat(DEFS + "Def_IntMul_Kappa_R8_Data_BitOppbankLocGrecDense.lean", "GREC")
else:
    GREC = parse_packl(DEFS + "Def_IntMul_Kappa_R8_Data_BitOppbankLocGrecDense.lean", "GREC")
print("GREC limbs:", len(GREC), file=sys.stderr)

# ---- constants ----
h_ = 23; v = 1771; NR = 27794; N = 3136441; W = 104719230
wEnt = 3542; wAuxEnd = 31336; NL = 31359
def wX(t): return t
def wY(T): return v + T
def wS(q): return wEnt + q
def wT(c): return wAuxEnd + c
def wU(s): return NL + s

cLOW, cHIGH = 0, 1
def cPT(T): return 2 + T
def cND(n): return 1773 + n

def pts(T, k): return field_of(TPTS, 5, 3*T + k)
def injS(T, k): return field_of(INJ, 16, 3*T + k)
def retS(c): return field_of(RETS, 16, c)
def retN(c): return field_of(RETN, 16, c)
def srcS(t): return field_of(SRC, 16, t)

def dimF(n): return field_of(DIMT, 5, n)
def dimCF(c):
    if c == 0: return 0
    if c == 1: return 23
    if c < 1773: return 22
    return dimF(c - 1773)
def rkC(a, b):
    a1, b1 = dimCF(a), dimCF(b)
    return b1 - a1 if a1 < b1 else a1 - b1

# ---- GREC decode (chunkDec) ----
def chunk_dec(X):
    cnt = X & 65535
    p = X >> 16
    recs = []
    for _ in range(cnt):
        n = p & 65535; p >>= 16
        piv = p & 65535; p >>= 16
        bp = p & 65535; p >>= 16
        ne = p & 255; p >>= 8
        ex = []
        for _ in range(ne):
            ex.append(p & 65535); p >>= 16
        recs.append((n, piv, bp, ex))
    return recs

recs = []
for X in GREC:
    recs.extend(chunk_dec(X))
print("recs:", len(recs), file=sys.stderr)
assert len(recs) == 54290, "recs mismatch vs Lean #eval 54290"

def blk_recs(a, b):
    out = []
    for X in GREC[a:b]:
        out.extend(chunk_dec(X))
    return out

def rec_el(r):
    n, piv, bp, ex = r
    pair = [] if bp == 0 else [(wS(piv), wS(bp - 1))]
    return pair + [(wS(o), wS(piv)) for o in ex]

def touch(el): return [x for p in el for x in p]

def mk(c, el): return (c, touch(el), el)
def scat_el(rd, T): return [(wY(T), rd(pts(T, k))) for k in (0, 1, 2)]
def rdS(c): return wS(retS(c))

# ---- W1F / W2F ----
def mixF(code): return [mk(code(r[0]), rec_el(r)) for r in recs]
def mixI(code): return [mk(code(r[0]), list(reversed(rec_el(r)))) for r in reversed(recs)]
def mixFB(a, b, code): return [mk(code(r[0]), rec_el(r)) for r in blk_recs(a, b)]
def scat(rd, code): return [mk(code(T), scat_el(rd, T)) for T in range(v)]
def injo(code): return [mk(code(T), [(wY(T), wS(injS(T, k))) for k in (0, 1, 2)]) for T in range(v)]
def copyo(code): return [mk(code(t), [(wS(srcS(t)), wX(t))]) for t in range(v)]
tcopy = [mk(cND(retN(c)), [(wT(c), wS(retS(c)))]) for c in range(23)]
scatT = tcopy + scat(wT, lambda _: cLOW)
def revI(op): return [(c, ts, list(reversed(el))) for (c, ts, el) in reversed(op)]
def sweepR(a, b, f): return [(f, [wS(q)], []) for q in range(a, b)]

W1F = (mixF(lambda _: cLOW) + scat(rdS, lambda _: cLOW) + injo(lambda _: cLOW)
       + mixI(lambda _: cLOW)
       + copyo(lambda t: cND(t + 1))
       + mixFB(0, 12, cND) + mixFB(12, 24, cND) + mixFB(24, 48, cND) + mixFB(48, 72, cND)
       + mixFB(72, 96, cND) + mixFB(96, 120, cND) + mixFB(120, 143, cND)
       + scatT + injo(cPT)
       + sweepR(0, 20000, cHIGH) + sweepR(20000, NR, cHIGH)
       + mixI(lambda _: cHIGH) + copyo(lambda _: cHIGH))

W2F = (revI(copyo(lambda _: cHIGH)) + revI(mixI(lambda _: cHIGH))
       + revI(injo(cPT)) + revI(scatT)
       + revI(mixFB(120, 143, cND)) + revI(mixFB(96, 120, cND))
       + revI(mixFB(72, 96, cND)) + revI(mixFB(48, 72, cND))
       + revI(mixFB(24, 48, cND)) + revI(mixFB(12, 24, cND))
       + revI(mixFB(0, 12, cND)) + revI(copyo(lambda t: cND(t + 1)))
       + sweepR(0, 20000, cLOW) + sweepR(20000, NR, cLOW)
       + revI(mixI(lambda _: cLOW)) + revI(injo(lambda _: cLOW))
       + revI(scat(rdS, lambda _: cLOW)) + revI(mixF(lambda _: cLOW)))

print("W1F len:", len(W1F), " (Lean #eval: 237921)", file=sys.stderr)
print("W1F touch:", sum(len(ts) for _, ts, _ in W1F), " (Lean #eval: 536840)", file=sys.stderr)
assert len(W1F) == 237921 and sum(len(ts) for _, ts, _ in W1F) == 536840

def code_of(S, w): return (S >> (16 * w)) & 65535

def genf(seed, Winstr):
    f = {}  # sparse; default seed value lookup
    def getf(w):
        return f[w] if w in f else code_of(seed, w)
    chunks = []
    for (c, ts, el) in Winstr:
        mvs = []
        for w in ts:
            if getf(w) == c:
                continue
            mvs.append((w, getf(w)))
            f[w] = c
        chunks.append((c, list(reversed(mvs)), el))
    return chunks

cs1 = genf(SG1_0, W1F)
cs2 = genf(SG2_0, W2F)

def ranks(cs):
    out = []
    for (c, mvs, el) in cs:
        for (w, o) in mvs:
            out.append(rkC(o, c))
    return out

r1 = ranks(cs1)
r2 = ranks(cs2)
print("cs1 chunks:", len(cs1), " moves:", len(r1), file=sys.stderr)
print("cs2 chunks:", len(cs2), " moves:", len(r2), file=sys.stderr)
c1 = Counter(r1); c2 = Counter(r2)
print("DC1 =,", [(r, c1.get(r, 0)) for r in range(0, 30) if c1.get(r, 0)])
print("DC2 =,", [(r, c2.get(r, 0)) for r in range(0, 30) if c2.get(r, 0)])
print("DC1 total:", len(r1), " runs:", sum(r * n for r, n in c1.items()))
print("DC2 total:", len(r2), " runs:", sum(r * n for r, n in c2.items()))
