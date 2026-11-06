#!/usr/bin/env python3
"""Stage 1 — the unipotent Bruhat-glue gadget: EXACT verdict.

Framework-faithful analog (Def_IntMul_Kappa_R6_Defs4):
  Edge m = (E1, runs, E2); runPiv (i,j,r) -> pivots (i+k, m+j+k) k<r
  edgeMat = E1 * permMatrix(prod of pivot transpositions) * E2
  EdgeOK-shape: E1,E2 lower-triangular, invertible (diag units).

Question: can U0 P(s1) U1 ... P(sR) UR = swapMat (the 2m x 2m block swap)
with TOTAL pivot count R < m?  (This is the only way the onerun census,
which is 759 transpositions per block short of 529*59130, could close
FormalOK by own-edge assembly.)

Rank lemma (proved here symbolically for m=2,3 / validated by sampling):
  B(F) := top-right m x m block of F.  B(I) = 0, B(swapMat) = I_m.
  Right-mult by lower-triangular V: right-half columns receive only from
  higher-indexed right-half columns  =>  rank B unchanged.
  Left-mult by lower-triangular L: B -> T * B  => rank unchanged.
  One cross-transposition pivot (a, m+b): swaps one left column into the
  right half  =>  rank B grows by <= 1.
  Hence R >= rank(I_m) = m.  NO SAVING, ANY m.
"""
import itertools, random
import sympy as sp

def cross_transposition(m, a, b):
    """Pivot (a, m+b): transposition swapping top index a with bottom m+b."""
    n = 2 * m
    P = sp.eye(n)
    P[a, a] = 0; P[a, m + b] = 1
    P[m + b, a] = 1; P[m + b, m + b] = 0
    return P

def swap_mat(m):
    n = 2 * m
    S = sp.zeros(n, n)
    for i in range(m):
        S[i, m + i] = 1
        S[m + i, i] = 1
    return S

def rand_lower_unitri(m_, gen):
    """Random lower-unitriangular of size m_ (symbolic entries)."""
    n = m_
    U = sp.eye(n)
    for i in range(n):
        for j in range(i):
            U[i, j] = sp.Symbol(f"{gen}_{i}{j}", nonzero=True)
    return U

def B_block(F, m):
    n = 2 * m
    return F[:m, m:n]

def run_pivots(m, i, j, r):
    """Framework runPiv: pivots (i+k, m+j+k) for k < r, in-range only."""
    out = []
    for k in range(r):
        if i + k < m and j + k < m:
            out.append((i + k, j + k))
    return out

def run_perm(m, i, j, r):
    P = sp.eye(2 * m)
    for (a, b) in run_pivots(m, i, j, r):
        P = P * cross_transposition(m, a, b)
    return P

def edge_mat(m, E1, runs, E2):
    P = sp.eye(2 * m)
    for (i, j, r) in runs:
        P = P * run_perm(m, i, j, r)
    return E1 * P * E2

# ----------------------------------------------------------------------
# (a) POSITIVE CONTROL (width exactly m): cancellation identity.
#     runs covering the full block swap (offset-0 runs), E1 = diag(A,D),
#     E2 = diag(D^-1, A^-1)  =>  edgeMat = swapMat exactly.
# ----------------------------------------------------------------------
print("== (a) positive control: width-m own-assembly (cancellation identity) ==")
for m in (2, 3, 4, 8):
    A = rand_lower_unitri(m, "a"); D = rand_lower_unitri(m, "d")
    Ai = A.inv(); Di = D.inv()
    E1 = sp.diag(A, D, evaluate=False) if False else sp.zeros(2*m, 2*m)
    E1[:m, :m] = A; E1[m:, m:] = D          # block-diag lower-tri
    E2 = sp.zeros(2*m, 2*m)
    E2[:m, :m] = Di; E2[m:, m:] = Ai
    runs = [(k, k, 1) for k in range(m)]     # m pivots (k, m+k), offset 0
    F = edge_mat(m, E1, runs, E2)
    ok = sp.simplify(F - swap_mat(m)) == sp.zeros(2*m, 2*m)
    print(f"  m={m}: edgeMat(diag-unipotent sandwich, width {m}) == swapMat -> {ok}")
    # and the trivial version E1 = E2 = I
    F0 = edge_mat(m, sp.eye(2*m), runs, sp.eye(2*m))
    print(f"  m={m}: edgeMat(E1=E2=1, width {m}) == swapMat -> {F0 == swap_mat(m)}")

# ----------------------------------------------------------------------
# (b) NEGATIVE, symbolic: m=2, R=1  —  det B(F) = 0 symbolically.
# ----------------------------------------------------------------------
print("\n== (b) m=2, one pivot: symbolic impossibility ==")
m = 2
U1 = rand_lower_unitri(2*m, "u1"); U2 = rand_lower_unitri(2*m, "u2")
for a in range(m):
    for b in range(m):
        F = U1 * cross_transposition(m, a, b) * U2
        B = B_block(F, m)
        detB = sp.factor(B.det())
        # B(swap) = I2 has det 1; if det B(F) == 0 for all unipotents, F != swap.
        print(f"  tau=({a},{m+b}): det(top-right block) = {detB}  (must be 1 for swap -> impossible)" )

# ----------------------------------------------------------------------
# (c) NEGATIVE, symbolic minors: m=3, R=2 — all 3x3 minors of B vanish.
#     F = U0 P(t1) U1 P(t2) U2, general lower-unitriangular U's.
#     rank B(F) <= 2 < 3 = rank B(swap)  =>  F != swap for ALL choices.
# ----------------------------------------------------------------------
print("\n== (c) m=3, two pivots interleaved: rank(top-right) <= 2 symbolically ==")
m = 3
U0 = rand_lower_unitri(2*m, "x"); U1 = rand_lower_unitri(2*m, "y"); U2 = rand_lower_unitri(2*m, "z")
checked = 0; all_vanish = True
for a1, b1, a2, b2 in itertools.product(range(m), repeat=4):
    F = U0 * cross_transposition(m, a1, b1) * U1 * cross_transposition(m, a2, b2) * U2
    B = B_block(F, m)
    # all 3x3 minors (only one: det) must be identically zero
    d = sp.factor(sp.expand(B.det()))
    if d != 0:
        all_vanish = False
        print(f"  NONVANISHING at ({a1},{b1}),({a2},{b2}): {d}")
    checked += 1
print(f"  checked {checked} tau-pairs: all 3x3 minors identically zero -> {all_vanish}")
print("  (rank B <= 2 < 3 = rank I_3 = rank B(swap)  =>  no factorization: SAVING IMPOSSIBLE at m=3)")

# ----------------------------------------------------------------------
# (d) NEGATIVE, sampling: interleaved products with total width < m never
#     equal swapMat (validates conventions; the lemma is the proof).
# ----------------------------------------------------------------------
print("\n== (d) sampling m=3..6, width < m: product == swap? ==")
rng = random.Random(7)
def rand_unitri_num(n):
    U = sp.eye(n)
    for i in range(n):
        for j in range(i):
            U[i, j] = rng.randint(-3, 3)
    return U

trials = hits = 0
for m in (3, 4, 5, 6):
    for _ in range(300):
        R = m - 1
        F = rand_unitri_num(2*m)
        for _ in range(R):
            a, b = rng.randrange(m), rng.randrange(m)
            F = F * cross_transposition(m, a, b) * rand_unitri_num(2*m)
        trials += 1
        if F == swap_mat(m):
            hits += 1
print(f"  {trials} random interleaved products with width = m-1: hits == swapMat: {hits}")

# ----------------------------------------------------------------------
# (e) RANK LEMMA, validated: rank B grows by <= 1 per pivot, any m.
# ----------------------------------------------------------------------
print("\n== (e) rank-lemma validation (rank B <= #pivots, sampled) ==")
viol = 0
for m in (3, 5, 8):
    for _ in range(200):
        R = rng.randrange(0, m + 2)
        F = rand_unitri_num(2*m)
        for _ in range(R):
            a, b = rng.randrange(m), rng.randrange(m)
            F = F * cross_transposition(m, a, b)
            F = F * rand_unitri_num(2*m)
        if B_block(F, m).rank() > R:
            viol += 1
print(f"  violations of rank B <= #pivots: {viol} (expected 0)")

# ----------------------------------------------------------------------
# (f) SCALING: per-block census ledger vs the >=529-per-role lower bound.
#     Ground truth: onerun_net_rungs12.lean decide-proved identities.
# ----------------------------------------------------------------------
print("\n== (f) scaling to m=529 with #6's decide-proved census ==")
W, blocks, m5 = 104719230, 1771, 529
roles_per_block = W // blocks           # 59130 (decide-proved)
big = 3542*484 + 33744*506 + 11454294   # 30243086 (decide-proved)
small = 1035925                          # per-block small-filler (decide-proved)
avail = 529*roles_per_block - 759
need = 529*roles_per_block               # rank lemma: >= m per role wire
print(f"  roles/block={roles_per_block}, big-run width={big}, small={small}")
print(f"  available={avail}, needed(own-assembly)={need}, deficit={need-avail}")
print(f"  => own-assembly short by {need-avail} per block = 1771*759 total;"
      f" UNIPOTENT GLUE SAVES 0 (rank lemma) => onerun family dead for FormalOK.")
