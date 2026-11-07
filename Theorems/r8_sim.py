#!/usr/bin/env python3
"""Faithful Python replication of the R8 oppbank net0Pnd child-width histogram (v2).

Mirrors Def_IntMul_Kappa_R8_Data_BitOppbank{QHNet,Pnd,Hist,LocSlots,ChkBitArg,GenData_0/2}.lean.
Exact per-edge child multisets from the SPECS (SideR/DataR/AuxR) + faithful program
simulation (genF/mvF machine over real GREC/INJ/RETS/RETN/SRC/TPTS data).
"""
import re, sys
from collections import Counter

WS = "/Users/dmitri.arkhipov/prove2me_workspace/Definitions/"

def read(fn): return open(WS + fn).read()

def packL_from(text, decl):
    i = text.index(decl); j = text.index("]", i)
    hexes = [int(h, 16) for h in re.findall(r"0x([0-9a-fA-F]+)", text[i:j])]
    out = 0; shift = 0
    for h in hexes:
        out |= h << shift; shift += 65536
    return out

def single_list_from(text, decl):
    # def X : List Nat := [ ... ]  (GREC: each element a standalone Nat)
    i = text.index(decl); j = text.index("]", i)
    return [int(h, 16) for h in re.findall(r"0x([0-9a-fA-F]+)", text[i:j])]

v, NR, wEnt, wAuxEnd, NL, m = 1771, 27794, 3542, 31336, 31359, 529
codeBound = 64251

slotst = read("Def_IntMul_Kappa_R8_Data_BitOppbankLocSlots.lean")
chk = read("Def_IntMul_Kappa_R8_Data_BitOppbankChkBitArg.lean")
gd0 = read("Def_IntMul_Kappa_R8_Data_BitOppbankGenData_0.lean")
gd2 = read("Def_IntMul_Kappa_R8_Data_BitOppbankGenData_2.lean")
grecl = read("Def_IntMul_Kappa_R8_Data_BitOppbankLocGrecDense.lean")

TPTS = packL_from(slotst, "def TPTS")
INJ = packL_from(slotst, "def INJ")
RETS = packL_from(slotst, "def RETS")
RETN = packL_from(slotst, "def RETN")
SRC = packL_from(slotst, "def SRC")
DIMT = packL_from(chk, "def DIMT")
SG1_0 = packL_from(gd0, "def SG1_0")
SG2_0 = packL_from(gd2, "def SG2_0")
GREC = single_list_from(grecl, "def GREC")

def fieldOf(X, w, i): return (X >> (w * i)) & ((1 << w) - 1)
dimF = lambda n: fieldOf(DIMT, 5, n)
def dimCF(c):
    if c == 0: return 0
    if c == 1: return 23
    if c < 1773: return 22
    return dimF(c - 1773)
rkC = lambda a, b: abs(dimCF(a) - dimCF(b))

pts = lambda T, k: fieldOf(TPTS, 5, 3*T + k)
injS = lambda T, k: fieldOf(INJ, 16, 3*T + k)
retS = lambda c: fieldOf(RETS, 16, c)
retN = lambda c: fieldOf(RETN, 16, c)
srcS = lambda t: fieldOf(SRC, 16, t)

def chunkDec(X):
    cnt = X & 0xFFFF; p = X >> 16; recs = []
    for _ in range(cnt):
        n = p & 0xFFFF; piv = (p >> 16) & 0xFFFF; ne = (p >> 48) & 0xFF
        rest = p >> 56
        ex = []
        for _ in range(ne):
            ex.append(rest & 0xFFFF); rest >>= 16
        recs.append((n, piv, ex)); p = rest
    return recs

RECS = [r for X in GREC for r in chunkDec(X)]
sys.stderr.write(f"GREC={len(GREC)} recs={len(RECS)}\n")

cLOW, cHIGH = 0, 1
cPT = lambda T: 2 + T
cND = lambda n: 1773 + n
wS = lambda q: wEnt + q
wX = lambda t: t
wY = lambda T: v + T
wT = lambda c: wAuxEnd + c
rdS = lambda c: wS(retS(c))

def recEl(r):
    n, piv, ex = r
    out = []
    if piv != 0: out.append((wS(piv), wS(piv - 1)))
    out += [(wS(o), wS(n)) for o in ex]
    return out

def mk(c, el):
    wires = []
    for (a, b) in el: wires += [a, b]
    return (c, wires, el)

def mix(codef, recs, rev=False):
    rs = list(reversed(recs)) if rev else recs
    return [mk(codef(r), recEl(r)) for r in rs]

def blkRecs(a, b): return [r for X in GREC[a:b] for r in chunkDec(X)]
def scat(rd, codef): return [mk(codef(T), [(wY(T), rd(pts(T, k))) for k in (0,1,2)]) for T in range(v)]
def injo(codef): return [mk(codef(T), [(wY(T), wS(injS(T, k))) for k in (0,1,2)]) for T in range(v)]
def copyo(codef): return [mk(codef(t), [(wS(srcS(t)), wX(t))]) for t in range(v)]
def tcopyf(): return [mk(cND(retN(c)), [(wT(c), wS(retS(c)))]) for c in range(23)]
def sweepR(a, b, f): return [(f, [wS(q)], []) for q in range(a, b)]
def revI(op): return [(i[0], list(reversed(i[1])), list(reversed(i[2]))) for i in reversed(op)]

def genStepF(acc, instr):
    c, wires, _ = instr
    code, chunks = acc
    moves = []
    for w in wires:
        old = code.get(w, 0)
        if old == c: continue
        code[w] = c
        moves.append((w, old))
    moves.reverse()
    return (code, [(c, moves, None)] + chunks)

def genF(f0, W):
    code = {x: f0(x) for x in range(NL)}
    acc = (code, [])
    for instr in W: acc = genStepF(acc, instr)
    return list(reversed(acc[1]))

FB = [(0,12),(12,24),(24,48),(48,72),(72,96),(96,120),(120,143)]
W1 = (mix(lambda r: cLOW, RECS) + scat(rdS, lambda T: cLOW) + injo(lambda T: cLOW)
      + mix(lambda r: cLOW, RECS, rev=True) + copyo(lambda t: cND(t + 1))
      + [i for a, b in FB for i in mix(lambda r: cND(r[0]), blkRecs(a, b))]
      + tcopyf() + scat(rdS, lambda T: cLOW) + injo(cPT)
      + sweepR(0, 20000, cHIGH) + sweepR(20000, NR, cHIGH)
      + mix(lambda r: cHIGH, RECS, rev=True) + copyo(lambda t: cHIGH))
W2 = (revI(copyo(lambda t: cHIGH)) + revI(mix(lambda r: cHIGH, RECS)) + revI(injo(cPT))
      + revI(scat(rdS, lambda T: cLOW)) + revI(tcopyf() + scat(rdS, lambda T: cLOW))
      + [i for a, b in reversed(FB) for i in revI(mix(lambda r: cND(r[0]), blkRecs(a, b)))]
      + revI(copyo(lambda t: cND(t + 1)))
      + sweepR(0, 20000, cLOW) + sweepR(20000, NR, cLOW)
      + revI(mix(lambda r: cLOW, RECS, rev=True)) + revI(injo(lambda T: cLOW))
      + revI(scat(rdS, lambda T: cLOW)) + revI(mix(lambda r: cLOW, RECS)))

cs1 = genF(lambda w: fieldOf(SG1_0, 16, w), W1)
cs2 = genF(lambda w: fieldOf(SG2_0, 16, w), W2)
sys.stderr.write(f"chunks cs1={len(cs1)} cs2={len(cs2)}\n")

# SideR r: EXACTLY r children: r>=12 -> one @ 2r-23 + (23-r) @ 1 ; r<=11 -> r @ 1
def side_children(r):
    if r >= 12:
        c = Counter({2*r - 23: 1, 1: 23 - r})
    else:
        c = Counter({1: r})
    return c

hist = Counter()
aux_edge = Counter({23: 1, 483: 1})
data_edge = Counter({439: 1, 21: 1, 1: 24})
n_ex = v * NR
n_ei = v * (wAuxEnd - wEnt)
n_en = v * wEnt
n_ec = v * v * 3
for _ in range(n_ex): hist += aux_edge
for _ in range(n_ei): hist += aux_edge
for _ in range(n_en): hist += data_edge
for _ in range(n_ec): hist += Counter({1: 1})

def chunk_children(cs):
    h = Counter(); nedges = 0
    for (c, moves, _) in cs:
        for (w, old) in moves:
            h += side_children(rkC(old, c)); nedges += 1
    return h, nedges

h1, e1 = chunk_children(cs1)
h2, e2 = chunk_children(cs2)
for _ in range(v): hist += h1 + h2
sys.stderr.write(f"chunk edges/block: s1={e1} s2={e2}\n")

struct = n_ex*2 + n_ei*2 + n_en*26 + n_ec
total = sum(hist.values())
OPP = opp = [(1, 221936407), (2, 259926128), (3, 38728228), (4, 49343602), (5, 24609816), (6, 8068676), (7, 3818276), (8, 4785242), (9, 2992990), (10, 1211364), (11, 1445136), (12, 1331792), (13, 1080310), (14, 669438), (15, 2755676), (16, 3860780), (17, 1933932), (18, 364826), (19, 13388760), (20, 587972), (21, 1771000), (22, 116886), (484, 6272882), (506, 59760624), (507, 453376), (508, 173558), (509, 421498), (510, 233772), (511, 205436), (512, 226688), (513, 340032), (514, 602140), (515, 173558), (516, 357742), (517, 283360), (518, 690690), (519, 389620), (520, 102718), (521, 184184), (522, 584430), (523, 350658), (524, 3021326), (525, 13448974), (526, 4558554), (527, 5649490), (528, 6233920)]

print(f"oppbank childCount = {sum(n for _, n in opp)} rankSum = {sum(w*n for w, n in opp)}")
print(f"net0Pnd children = {total} (structural-only {struct}); rankSum = {sum(w*n for w, n in hist.items())}")

print(f"CHECK oppbank childCount={sum(n for _,n in opp)} (expect 749446467) rankSum={sum(w*n for w,n in opp)} (expect 55395128481)")
