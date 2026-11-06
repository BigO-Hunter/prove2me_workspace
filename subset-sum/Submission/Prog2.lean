import Submission.Program
import Submission.ProgFacts
set_option autoImplicit true

/-!
# Prog2: the α = 1/2 machine (R2125607749 Lane 1)

`prog2` replaces `prog`'s Phase B (per-subset bit extraction + binary search,
`Θ(n·2^(n/2))` — the ACTUAL poly source; Phase A's doubling merge is already
`Θ(2^(n/2))` by its proven budget `12 + 44·(2^(n/2)−1) + 24·(n/2)`) with:

1. `canon`  — canonicalize `S₁` (sorted first-half sums, `2^h` values) into
   `ARR1 = 3n+25`, copying from `ARR2` when Phase A's final swap left it
   there; `cell 22 := ARR1` becomes the scan's fixed `S₁` base.
   `≤ 6·2^h + 11` steps.
2. `phaseA2` — the SAME doubling-merge machine run on the second half
   `a_{h+1}..a_n` (`m = n − h` elements), producing sorted
   `S₂ = halfSums (instA x ∘ (h+·)) m` (`2^m` values) at base `B2`/`B3`:
   `B2 := ARR1 + 2^h + 1` (the old `ARR2` slot, extended to `2^m` cells),
   `B3 := B2 + 2^m + 1`.  On exit `[rSRC]` = S₂ base, `[rL] = 2^m`.
   `Θ(2^(n−n/2))` steps.
3. `scanB` — two-pointer walk over the two sorted arrays replacing Phase B:
   `s := S₁[i] + S₂[j]` (no wrap: `s ≤ Σa < 2^w` by Fit), compare with `t`,
   `i++` on `s < t` (then no `j' ≤ j` can pair with `i`), `j--` on `s > t`
   (then no `i' ≤ i` can pair with `j`), accept on equality, reject on
   exhaustion.  `≤ 10·(2^h + 2^m) + O(1)` steps.  NO subtraction — the
   wrapped-complement refutation machinery is unnecessary for `prog2`.

Total `≤ C·2^(n/2) + O(n)`, b-INDEPENDENT (every instruction, including the
`blt` word compares, costs 1 step for any `b`), so `T(n)² ≤ K·2^n` — the
α = 1/2 shape.  (A 2-pass LSD radix on `n/2`-bit digits, as the campaign
charter proposed, sorts only values `< 2^n`; half-sums reach `n·2^b` with
`b ≤ n^c`, and covering `w` bits needs `Θ(b/n)` passes — worse than the
merge.  See the Lane-1 interim rider on R2125607749.)

Register additions (cells freed by the prologue, dead on the big-n path):
`[4] = m` (phaseA2 round bound), `[5] = H = 2^h` (scan's `i` bound),
`[22] = ARR1` (scan's S₁ base).  Cells 1, 2 (the `jmp` constants) and
7, 8 (`n`, `RELOC`) are never written after the prologue.

Layout extension (minimal; the prologue's cell-8 setup is untouched):
big cells now run through `B3 + 2^m − 1 = 3n + 26 + 2^(n/2) + 2·2^(n−n/2)`.
The exec-walk hypotheses need `haddr` widened to
`∀ c ≤ 3n + 27 + 2^(n/2) + 2·2^(n−n/2), c < 2^w` (pro_addr_lt variant:
`3·m + 27 + 2^(m/2) + 2·2^(m−m/2) < 2^(2m)`, same induction) and `AReg n`'s
second disjunct widened to the same ceiling.

Resolved pc map (`resolve prog2Lines`, 301 instructions — dumped by
`Prog2Bench.lean`): prologue `0–85` and phaseA `86–147` are PC-IDENTICAL
to `prog` (same prefix): LROUND=98 LMERGE=103 LHAVEJ=105 LBOTH=107
LTAKEJ=114 LTAKEL=118 LSTEP=121 LDRAINI=123 LDILOOP=125 LDRAINJ=LDJLOOP=133
LSWAP=141.  New segments: canon entry=148 (LCANCH=154, LCANLOOP=155,
LPHASEA2=161) · phaseA2 161–223 (LROUND2=173 LMERGE2=179 LHAVEJ2=181
LBOTH2=183 LTAKEJ2=190 LTAKEL2=194 LSTEP2=197 LDRAINI2=199 LDILOOP2=201
LDRAINJ2=LDJLOOP2=209 LSWAP2=217, round guard 223, falls through at 224) ·
scanB 224–243 (setup 224–228, LSCAN=229, accept=236, LSCANLESS=237–239,
LSCANGTR=240–241, LSCANDEC=242, `jmp LSCAN`=243) · smallN 244–300
(LSMALL=244, unchanged).  Every physical exit halts or jumps — smallN is
reachable only via the prologue's LSMALL dispatch.

Empirical status (Lane 1, this workspace): rock battery 69/69 Lean
(`Prog2Rocks.lean`: 15 targeted edges + 8 dup-heavy + 20 LCG seed 20261031 +
10 parity-supplement LCG + 10 odd-n explicit + 3 huge-b + 3 n=12 pipeline)
and 77/77 Python (`sim_l1.py`, includes n=16/20 full pipeline; simulator
validated against Lean execMem verdict-by-verdict, step semantics pinned by
minimal-fuel bisection in `StepCheck.lean`: 480/870/1241 exact matches).
Measured worst-case (miss-path) steps track `C·2^(n/2)`: ratio 64–78 over
n=8..24 (sup 77.6 at n=8, asymptote ≈ 64); old `prog` on the same instances
grows as `Θ(n·2^(n/2))` (ratio/2^(n/2): 146 → 292 over n=8..24).  Fit for
Lane 4: `T(n) = 256·2^(n/2) + D·n` covers the measurement with ≥3x margin
(analytic bound from the proven per-segment budgets: ≤ 230·2^(n/2) + O(n)).
-/

namespace SubsetSum.MITM

open BigOSpeedrun.SubsetSum

/-- Labels for `canon` / `phaseA2` / `scanB` (70+; disjoint from
Phase A's 10–21, Phase B's 30–40, smallN's 50–64, prologue's 2–3). -/
def LCANCH    : Nat := 70
def LCANLOOP  : Nat := 71
def LROUND2   : Nat := 72
def LMERGE2   : Nat := 73
def LHAVEJ2   : Nat := 74
def LBOTH2    : Nat := 75
def LTAKEJ2   : Nat := 76
def LTAKEL2   : Nat := 77
def LSTEP2    : Nat := 78
def LDRAINI2  : Nat := 79
def LDILOOP2  : Nat := 80
def LDJLOOP2  : Nat := 81
def LSWAP2    : Nat := 82
def LDRAINJ2  : Nat := 83
def LSCAN     : Nat := 84
def LSCANLESS : Nat := 85
def LSCANGTR  : Nat := 86
def LSCANDEC  : Nat := 87
def LPHASEA2  : Nat := 88

/-- Canonicalize: `[22] := ARR1 = RELOC + n + 2`; if Phase A left `S₁` in
`ARR2` (`ARR1 < [rSRC]`), copy `[rSRC .. +[rL])` down to `ARR1`.  Falls
through to `phaseA2` on either path. -/
def canon : List Line :=
  [ .raw (.add rT1 rRE rN)
  , .raw (.add rT1 rT1 rONE)
  , .raw (.add rT1 rT1 rONE)        -- t1 := RELOC + n + 2 = 3n+25 = ARR1
  , .raw (.add rT3 rT1 rZER)        -- [22] := ARR1 (the scan's S₁ base)
  , .jblt rT1 rSRC LCANCH           -- ARR1 < bd ⟹ bd = ARR2: copy
  , jmp LPHASEA2
  , .mark LCANCH
  , .raw (.sub rI rI rI)            -- i := 0
  , .mark LCANLOOP
  , .raw (.add rT2 rSRC rI)
  , .raw (.load rVI rT2)            -- v := bd[i]
  , .raw (.add rT2 rT1 rI)
  , .raw (.store rT2 rVI)           -- ARR1[i] := v
  , .raw (.add rI rI rONE)
  , .jblt rI rL LCANLOOP
  , .mark LPHASEA2
  ]

/-- Phase A₂: the doubling-merge machine on the second half.  Entry state:
`[rH] = h`, `[rL] = H = 2^h`, `[rT3] = ARR1` (S₁ canonical), `[rN] = n`,
`[rRE] = RELOC`, `[1] = 1`, `[2] = 0`.  Round `k` merges `S₂_{k-1}` at
`[rSRC]` (length `[rL] = 2^(k-1)`) with its `+a_{h+k}` copy into `[rDST]`,
`a_{h+k} = mem[RELOC + h + k]`.  Exit: `[rSRC]` = S₂ base (`B2` or `B3`),
`[rL] = 2^m`, `[4] = m`, `[5] = H`. -/
def phaseA2 : List Line :=
  [ .raw (.add rIDX rL rZER)        -- [5] := H = 2^h (scan's i-bound)
  , .raw (.sub rBND rN rH)          -- [4] := m = n − h
  , .raw (.add rT1 rONE rZER)       -- t1 := 1
  , .raw (.shl rT1 rT1 rBND)        -- t1 := M = 2^m
  , .raw (.add rSRC rT3 rL)
  , .raw (.add rSRC rSRC rONE)      -- B2 := ARR1 + H + 1
  , .raw (.add rDST rSRC rT1)
  , .raw (.add rDST rDST rONE)      -- B3 := B2 + M + 1
  , .raw (.add rL rONE rZER)        -- L := 1
  , .raw (.add rT1 rSRC rZER)
  , .raw (.store rT1 rZER)          -- S₂₀ := [0] at B2
  , .raw (.add rK rONE rZER)        -- k := 1
  , .mark LROUND2
  , .raw (.add rT1 rRE rH)
  , .raw (.add rT1 rT1 rK)
  , .raw (.load rAK rT1)            -- a_{h+k} := mem[RELOC + h + k]
  , .raw (.sub rI rI rI)
  , .raw (.sub rJ rJ rJ)
  , .raw (.sub rW rW rW)
  , .mark LMERGE2
  , .jblt rJ rL LHAVEJ2
  , jmp LDRAINI2
  , .mark LHAVEJ2
  , .jblt rI rL LBOTH2
  , jmp LDRAINJ2
  , .mark LBOTH2
  , .raw (.add rT1 rSRC rI)
  , .raw (.load rVI rT1)
  , .raw (.add rT2 rSRC rJ)
  , .raw (.load rVJ rT2)
  , .raw (.add rVJ rVJ rAK)
  , .jblt rVJ rVI LTAKEJ2
  , jmp LTAKEL2
  , .mark LTAKEJ2
  , .raw (.add rT1 rDST rW)
  , .raw (.store rT1 rVJ)
  , .raw (.add rJ rJ rONE)
  , jmp LSTEP2
  , .mark LTAKEL2
  , .raw (.add rT1 rDST rW)
  , .raw (.store rT1 rVI)
  , .raw (.add rI rI rONE)
  , .mark LSTEP2
  , .raw (.add rW rW rONE)
  , jmp LMERGE2
  , .mark LDRAINI2
  , .jblt rI rL LDILOOP2
  , jmp LSWAP2
  , .mark LDILOOP2
  , .raw (.add rT1 rSRC rI)
  , .raw (.load rVI rT1)
  , .raw (.add rT2 rDST rW)
  , .raw (.store rT2 rVI)
  , .raw (.add rI rI rONE)
  , .raw (.add rW rW rONE)
  , .jblt rI rL LDILOOP2
  , jmp LSWAP2
  , .mark LDRAINJ2
  , .mark LDJLOOP2
  , .raw (.add rT2 rSRC rJ)
  , .raw (.load rVJ rT2)
  , .raw (.add rVJ rVJ rAK)
  , .raw (.add rT1 rDST rW)
  , .raw (.store rT1 rVJ)
  , .raw (.add rJ rJ rONE)
  , .raw (.add rW rW rONE)
  , .jblt rJ rL LDJLOOP2
  , .mark LSWAP2
  , .raw (.add rL rL rL)            -- L := 2L
  , .raw (.add rT1 rSRC rZER)       -- swap src/dst
  , .raw (.add rSRC rDST rZER)
  , .raw (.add rDST rT1 rZER)
  , .raw (.add rK rK rONE)
  , .raw (.add rT2 rBND rONE)
  , .jblt rK rT2 LROUND2
  ]

/-- Phase B₂: the two-pointer scan.  Entry: S₁ sorted ascending at `[rT3]`
(`H = [rIDX]` values), S₂ sorted ascending at `[rSRC]` (`[rL] = 2^m`
values), `t` at `mem[RELOC + n + 1]`, `[1] = 1`, `[2] = 0`, `[7] = n`,
`[8] = RELOC`.  Invariant at `LSCAN`: no pair `(i', j')` with `i' < [rI]`
or (`i' = [rI]` and `j' > [rJ]`) sums to `t`.  Accept on `S₁[i]+S₂[j] = t`;
reject when `i` exhausts `H` (no `j` pairs with the remaining `i`… the full
monotone-skip argument is Lane 2's scan invariant) or `j` hits 0 with
`s > t`. -/
def scanB : List Line :=
  [ .raw (.add rT1 rRE rN)
  , .raw (.add rT1 rT1 rONE)
  , .raw (.load rAK rT1)            -- t := mem[RELOC + n + 1]
  , .raw (.sub rI rI rI)            -- i := 0
  , .raw (.sub rJ rL rONE)          -- j := 2^m − 1
  , .mark LSCAN
  , .raw (.add rT1 rT3 rI)
  , .raw (.load rVI rT1)            -- v1 := S₁[i]
  , .raw (.add rT2 rSRC rJ)
  , .raw (.load rVJ rT2)            -- v2 := S₂[j]
  , .raw (.add rW rVI rVJ)          -- s := v1 + v2   (≤ Σa < 2^w: no wrap)
  , .jblt rW rAK LSCANLESS          -- s < t
  , .jblt rAK rW LSCANGTR           -- t < s
  , .raw (.accept)                  -- s = t: HIT
  , .mark LSCANLESS
  , .raw (.add rI rI rONE)
  , .jblt rI rIDX LSCAN             -- i < H
  , .raw (.reject)                  -- S₁ exhausted
  , .mark LSCANGTR
  , .jblt rZER rJ LSCANDEC          -- 0 < j
  , .raw (.reject)                  -- S₂ exhausted (j = 0, s > t)
  , .mark LSCANDEC
  , .raw (.sub rJ rJ rONE)
  , jmp LSCAN
  ]

/-- The α = 1/2 assembly: prologue (+ small-n split) + Phase A (unchanged)
+ canonicalization + Phase A₂ + the two-pointer scan + small-n verdict. -/
def prog2Lines : List Line :=
  prologue ++ phaseA ++ canon ++ phaseA2 ++ scanB ++ smallN

def prog2 : List Instr := resolve prog2Lines

set_option maxRecDepth 10000 in
/-- `prog2` contains no `rand` instruction (so Det.lean's
`correct_of_det` applies verbatim). -/
theorem prog2_no_rand : NoRand prog2 := by
  intro p hp i he
  have hall : prog2.all (fun q => !isRandInstr q) = true := by decide
  have h1 : (!isRandInstr p) = true := List.all_eq_true.mp hall p hp
  rw [he] at h1
  simp [isRandInstr] at h1

end SubsetSum.MITM
