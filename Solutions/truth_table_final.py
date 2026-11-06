#!/usr/bin/env python3
"""DEFINITIVE domination truth table with ground-truth DC histograms.

Ground truth (this session, verified against Lean #eval on sizes):
  W1F touch = 536840 = Lean; recs = 54290 = Lean; W1F len = 237921 = Lean.
  DC1 = DC2 (identical per-pass rank histograms):
  r:  0     1      2      3     4     5    6    7    8    9    10   11
     13016 25510  25258   2987 10042  3871 2463 2257 1427 5371 1114 1660
  r: 12   13   14   15   16   17   18   19  20   21    22    23
      941  482  715  296  331  347  851  512   7  4915  4184 10705
  total moves/pass = 119262, total runs/pass = sum r*DC = 774109.

net0P structure (per b in stage 1, per a in stage 2; v = 1771):
  chunk edges: rank r -> SideR r edge: widths [2r-23] + (23-r)*[1] (12<=r<=23),
               r*[1] (1<=r<=11), none (r=0); r>23 impossible (max rank 23 here).
  blk1: NR=27794 ex edges (AuxR: widths 23,483)
  entI per a: 3542 en edges (DataR: 439, 21, 24x1) + 27794 ei (AuxR: 23,483)
  corrI per a: 1771 ec edges (SideR 1: [1])
"""
from fractions import Fraction

DC = {0:13016, 1:25510, 2:25258, 3:2987, 4:10042, 5:3871, 6:2463, 7:2257,
      8:1427, 9:5371, 10:1114, 11:1660, 12:941, 13:482, 14:715, 15:296,
      16:331, 17:347, 18:851, 19:512, 20:7, 21:4915, 22:4184, 23:10705}
assert sum(DC.values()) == 119262
assert sum(r * DC[r] for r in DC) == 774109

v = 1771
net = {}
def add(w, c): net[w] = net.get(w, 0) + c

nData = 3542 * v
nAux = 2 * 27794 * v   # ei (per a) + ex (per b)
nEc = v * v
add(439, nData); add(21, nData); add(1, 24 * nData)
add(23, nAux); add(483, nAux)
add(1, nEc)
for r in range(1, 24):
    tot = 2 * DC[r] * v   # stage1 (per b) + stage2 (per a), each over v passes
    if tot == 0: continue
    if r <= 11:
        add(1, r * tot)
    else:
        add(2 * r - 23, tot)
        add(1, (23 - r) * tot)

widths = sorted(net)
print("== net0P.hist (ground truth) ==")
for w in widths:
    print(f"  ({w}, {net[w]})")
tot_children = sum(net.values())
rank_sum = sum(w * net[w] for w in widths)
print("net0P total children:", tot_children)
print("net0P rank sum      :", rank_sum)

bitR8 = [(1, 221936407), (2, 259926128), (3, 38728228), (4, 49343602), (5, 24609816), (6, 8068676), (7, 3818276), (8, 4785242), (9, 2992990), (10, 1211364), (11, 1445136), (12, 1331792), (13, 1080310), (14, 669438), (15, 2755676), (16, 3860780), (17, 1933932), (18, 364826), (19, 13388760), (20, 587972), (21, 1771000), (22, 116886), (484, 6272882), (506, 59760624), (507, 453376), (508, 173558), (509, 421498), (510, 233772), (511, 205436), (512, 226688), (513, 340032), (514, 602140), (515, 173558), (516, 357742), (517, 283360), (518, 690690), (519, 389620), (520, 102718), (521, 184184), (522, 584430), (523, 350658), (524, 3021326), (525, 13448974), (526, 4558554), (527, 5649490), (528, 6233920)]
bitR7plain = [(1, 1456218305), (3, 4381934), (5, 354200), (7, 3580962), (9, 1526602), (11, 5093396), (13, 2164162), (15, 7948248), (17, 8476006), (18, 6272882), (19, 1639946), (21, 6906900), (23, 61280142), (439, 6272882), (483, 61280142), (485, 545468), (487, 173558), (489, 293986), (491, 580888), (493, 14168), (495, 322322), (497, 17710), (499, 1129898), (501, 127512), (503, 410872), (505, 99176), (507, 1186570), (509, 340032), (511, 322322), (513, 106260), (515, 1583274), (517, 626934), (519, 2854852), (521, 13711082), (523, 4629394), (525, 5653032), (527, 6233920)]

def total(h): return sum(c for _, c in h)
def rsum(h): return sum(w * c for w, c in h)
def mom(h, tau): return sum(c * (w / 529.0) ** tau for w, c in h)

print(f"\nbitR8     : total={total(bitR8)}  rankSum={rsum(bitR8)}")
print(f"bitR7plain: total={total(bitR7plain)}  rankSum={rsum(bitR7plain)}")

for name, tgt in [("bitR8", bitR8), ("bitR7plain", bitR7plain)]:
    print(f"\n===== net0P vs {name} =====")
    print(f"count arm : net {tot_children} <= tgt {total(tgt)} ? {tot_children <= total(tgt)}")
    print(f"rank  arm : net {rank_sum} <= tgt {rsum(tgt)} ? {rank_sum <= rsum(tgt)}")
    print(f"tau=1     : net {rank_sum/529} vs tgt {rsum(tgt)/529}")
    lo, hi, bad = None, None, 0
    first_bad = None
    for i in range(1, 1000):
        tau = i / 1000
        d = mom(net.items(), tau) - mom(tgt, tau)
        if d > 0:
            bad += 1
            if first_bad is None: first_bad = (tau, d)
    print(f"tau in (0,1) sampled 1000 pts: net-tgt > 0 at {bad} pts"
          + (f", first at tau={first_bad[0]} diff={first_bad[1]:.3f}" if first_bad else ""))

# Also: compare the fixed+side components only, and bitR8 vs bitR7plain check with exact basis
# Verify bitR8 moment basis q=0,1 against the json oracle
import json
basis = json.load(open("/Users/dmitri.arkhipov/prove2me_workspace/bitR8_moment_basis.json"))
print("\noracle check bitR8: q0 =", basis["0"], "computed", total(bitR8),
      "OK" == "" if int(basis["0"]) != total(bitR8) else "OK")
print("oracle check bitR8: q1 =", basis["1"], "computed", rsum(bitR8),
      "OK" if int(basis["1"]) == rsum(bitR8) else "MISMATCH")

# where does net0P stand relative to bitR7plain at tau=1?
print("\nnet0P rank sum per 529:", rank_sum / 529)
print("bitR8  rank sum per 529:", rsum(bitR8) / 529)
print("excess runs (children):", tot_children - total(bitR8))
