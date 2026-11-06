import Submission.Prologue
import Submission.Sort
import Submission.Fit
set_option autoImplicit true

/-!
# Phase A: the doubling-merge mountain (R2125607414)

At `LROUND` (pc 98) of round `k`, the source array at `[rSRC]` (cells
`[rSRC .. +2^(k-1))`) is exactly `halfSums (instA x) (k-1)` (Sort.lean's
contract array).  Round `k` loads `a_k`, merges the array with its `+a_k`
copy into `[rDST]` (the program's `blt`-merge IS `mmerge`), doubles `L`,
swaps the pointers.  After round `h = n/2` the loop falls through to
Phase B (pc 148) with `halfSums (instA x) h` at `[rSRC]`.

Resolved program map (from `resolve (prologue ++ phaseA ++ …)`):
`86` Phase A entry · `98` LROUND · `103` LMERGE · `105` LHAVEJ ·
`107` LBOTH · `114` LTAKEJ · `118` LTAKEL · `121` LSTEP · `123` LDRAINI ·
`125` LDILOOP · `133` LDRAINJ = LDJLOOP · `141` LSWAP · `148` Phase B entry.

The merge loop's key invariant needs NO sortedness: the "merge path"
equation `out.drop (i+j) = mmerge (sl.drop i) (M.drop j)` follows the
`mmerge` recursion, which consumes heads by the same comparison the
program makes.  Sortedness arrives free from `halfSums_sorted`.

Entry is an explicit hypothesis bundle (the prologue walk discharges it
elsewhere); `ARR1 = RELOC + n + 2 = 3n+25`, `ARR2 = ARR1 + 2^h + 1`.

## STATUS (mind 4, 2026-10-31) — GREEN through §4.1

Proven: §0 vocab (`arrAt`/`arrL`/`Pres`, `up_fit`, `arrL_take_up`,
`getD_arrL`) · §1 lists (`dropCons`, `dropSucc`, `getDDrop`, `takeSucc`,
`takeAll`, `dropMap`, `mmerge_nil_r`, the merge-path `mmerge_stepL/J`) ·
§2 fit (`halfSumsLe`, `arrLtPow`, `halfSumAddFit`) · §3 `init_exec` (pc 86→98, 12 steps) · §4.1 `diLoop_exec` (pc 125→141, drain-i
body loop) · §4.2 `djLoop_exec` (pc 133→141, drain-j do-while; body writes
21:=(b+j); 16:=sl j; 16:=+ak; 20:=(d+wq); (d+wq):=sl j+ak; 13:=j+1;
14:=wq+1; guard at 140; `getD_map_add` shuttles map-reads).
Zero admits, standard axioms.

REMAINING: (a) DONE as djLoop_exec; (b) drainI entry (pc 123→125/141: guard `blt 12 11 125` then diLoop,
≤ 8N + 11 total; base `i = L` forces `L = 0` via drop-length); (c)
`merge_exec` (pc 103→141, induction on N with `(L-i)+(L-j) ≤ N`; the
both-sides iteration is 14 steps: 103→105→107-111→112→114-116/113→118-
120→121→122→103, using `mmerge_stepL/J` for the drop-invariant and
`arrL_take_up` + `takeSucc` for the take-invariant); (d) `round_exec`
(pc 98→147/148: 5-step setup 98-102 — `20 := RELOC+k; 17 := inF x k =
instA x (k-1); 12,13,14 := 0` — then merge_exec from (0,0,0) where the
take/drop invariants are rfl-trivial, then LSWAP tail 141-147: `11 :=
2L; 20 := b; 18 := d; 19 := b; 10 := k+1; 21 := h+1; blt 10 21 98`);
(e) `lround_exec` (fuel induction on `h + 1 - k`, exit falls to 148);
(f) `phaseA_exec` (init + lround at k=1; entry bundle from the prologue
walk — NOT YET WRITTEN, see Prologue.lean's planned `prologue_exec`).

DISCIPLINES that made this compile (all paid for):
- `have`-defs are OPAQUE: spell up-chains (generate them in python).
- `rw [step (by omega) (show prog.getD pc .reject = ... by rfl)]` —
  the getD fact MUST be `show ... by rfl` with ALL args explicit
  (`by decide` fails: no DecidableEq Instr in this toolchain).
- Normalize EVERY intermediate read inline right after its step rw —
  never let raw chains nest.
- Value facts (`show STATE cell = v`) reference the exact state the
  instruction READS; walks peel OUTSIDE-IN in write order.
- up_eq/up_ne side conditions: `(show (9:Nat) ≠ 18 by omega)` (i ≠ c).
- Horizons: end each chain with `simp only [Nat.sub_sub, Nat.reduceAdd]`,
  then omega-prove horizon equations (`S - 6 - 1 = S - 7`) and rw them.
- `MReg_dst` for array writes; `Or.inl rfl`-chains for register cells
  (12/13/14/15/16/20/21 at depths 0-6 of the MReg disjunction).
- Lists: this core has NO drop_succ/drop_map/take_all_of_le — use the
  §1 lemmas; `List.drop_cons` has a `0 < n` side-goal — avoid, use
  defeq `show` instead.
- diLoop's invariant is `wq = L + i` (NOT `wq + i = 2L` — that was a
  3-arrorithmic trap; wq − i stays L through the drain).
-/

namespace SubsetSum.MITM

open BigOSpeedrun.SubsetSum SubsetSum.MITM.Spec

/-! ## §0. Array vocabulary -/

/-- Cell `i` of the array at base `b` in state `f`. -/
def arrAt (f : Nat → Nat) (b i : Nat) : Nat := f (b + i)

/-- The array at base `b`, length `L`, as a list. -/
def arrL (f : Nat → Nat) (b L : Nat) : List Nat := (List.range L).map (arrAt f b)

/-- `g` differs from `f` only at cells satisfying `P`. -/
def Pres (P : Nat → Prop) (f g : Nat → Nat) : Prop := ∀ x, ¬ P x → g x = f x

theorem up_fit {f : Nat → Nat} {c v w : Nat} (hfit : ∀ q, f q < 2 ^ w)
    (hv : v < 2 ^ w) : ∀ q, (up f c v) q < 2 ^ w := by
  intro q
  by_cases h : q = c <;> simp [h, up, hfit, hv]

theorem pres_up {P : Nat → Prop} {f : Nat → Nat} {c v : Nat} (h : P c) :
    Pres P f (up f c v) := by
  intro x hx
  by_cases hxc : x = c
  · exact absurd (by rw [hxc]; exact h) hx
  · exact up_ne hxc

theorem pres_trans {P : Nat → Prop} {f g k : Nat → Nat}
    (h1 : Pres P f g) (h2 : Pres P g k) : Pres P f k := by
  intro x hx
  rw [h2 x hx]
  exact h1 x hx

theorem pres_mono {P Q : Nat → Prop} {f g : Nat → Nat} (hsub : ∀ x, P x → Q x)
    (h : Pres P f g) : Pres Q f g := by
  intro x hx
  exact h x (fun hpq => hx (hsub x hpq))

theorem arrL_congr {f g : Nat → Nat} {b L : Nat}
    (h : ∀ i, i < L → f (b + i) = g (b + i)) : arrL f b L = arrL g b L := by
  unfold arrL
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

theorem arrL_up_out {f : Nat → Nat} {b L c v : Nat}
    (h : ∀ i, i < L → c ≠ b + i) : arrL (up f c v) b L = arrL f b L := by
  refine arrL_congr fun i hi => ?_
  exact up_ne (Ne.symm (h i hi))

/-- Helper: `take (wq+1)` of a map over `range L` is the map over
`range (wq+1)` (valid for `wq + 1 ≤ L`). -/
theorem take_map_range {g : Nat → Nat} {L wq : Nat} (h : wq + 1 ≤ L) :
    ((List.range L).map g).take (wq + 1) = (List.range (wq + 1)).map g := by
  rw [← List.map_take, List.take_range, Nat.min_eq_left h]

/-- Writing at array index `wq` (the next unwritten slot) extends the
written prefix by exactly one cell. -/
theorem arrL_take_up {f : Nat → Nat} {b L wq v : Nat} (hwq : wq < L) :
    (arrL (up f (b + wq) v) b L).take (wq + 1)
      = (arrL f b L).take wq ++ [v] := by
  rw [show arrL (up f (b + wq) v) b L
        = (List.range L).map (fun i => (up f (b + wq) v) (b + i)) from rfl,
    take_map_range (by omega), List.range_succ, List.map_append,
    List.map_singleton, up_eq,
    show arrL f b L = (List.range L).map (fun i => f (b + i)) from rfl,
    ← List.map_take, List.take_range, Nat.min_eq_left (by omega : wq ≤ L)]
  have hmap : (List.range wq).map (fun i => (up f (b + wq) v) (b + i))
      = (List.range wq).map (fun i => f (b + i)) :=
    List.map_congr_left fun i hi => up_ne (by have := List.mem_range.mp hi; omega)
  rw [hmap]

theorem getD_arrL {f : Nat → Nat} {b L q : Nat} (h : q < L) :
    (arrL f b L).getD q 0 = f (b + q) := by
  unfold arrL arrAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  simp

/-! ## §1. List infrastructure: drops, takes, the merge path -/

/-- `drop i` of a nonempty suffix is a cons. -/
theorem dropCons {l : List Nat} {i : Nat} (h : i < l.length) :
    l.drop i = l.getD i 0 :: l.drop (i + 1) := by
  induction i generalizing l with
  | zero =>
    cases l with
    | nil => exact absurd h (by simp)
    | cons a t => rfl
  | succ i ih =>
    cases l with
    | nil => exact absurd h (by simp)
    | cons a t =>
        have hi : i < t.length := by simpa using h
        show List.drop i t = (a :: t).getD (i + 1) 0 :: List.drop (i + 1) t
        rw [ih hi, List.getD_cons_succ]

/-- One more drop is dropping the head of the suffix. -/
theorem dropSucc (l : List Nat) (n : Nat) : l.drop (n + 1) = (l.drop n).drop 1 :=
  (List.drop_drop (l := l) (i := 1) (j := n)).symm

/-- Element `i` read through the drop at `i`. -/
theorem getDDrop (l : List Nat) (i : Nat) : (l.drop i).getD 0 0 = l.getD i 0 := by
  by_cases h : i < l.length
  · rw [dropCons h]; rfl
  · cases hd : l.drop i with
    | nil =>
      have hle : l.length ≤ i := by
        have hlen : (l.drop i).length = l.length - i := List.length_drop
        rw [hd] at hlen
        have h0 : ([] : List Nat).length = 0 := rfl
        omega
      have hz : l.getD i 0 = 0 := by
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_eq_none_iff.mpr hle]
        rfl
      rw [hz]
      rfl
    | cons x r =>
      exact absurd (by
        have hlen : (l.drop i).length = l.length - i := List.length_drop
        rw [hd] at hlen
        have h0 : (x :: r).length = r.length + 1 := rfl
        omega) h

/-- `take (i+1)` adds element `i` to `take i`. -/
theorem takeSucc {l : List Nat} {i : Nat} (h : i < l.length) :
    l.take (i + 1) = l.take i ++ [l.getD i 0] := by
  induction l generalizing i with
  | nil => exact absurd h (by simp)
  | cons a t ih =>
    cases i with
    | zero => rfl
    | succ i =>
        have hi : i < t.length := by simpa using h
        show a :: List.take (i + 1) t = (a :: List.take i t) ++ [(a :: t).getD (i + 1) 0]
        rw [ih hi, List.getD_cons_succ]
        rfl

/-- Taking at least the whole list. -/
theorem takeAll {l : List Nat} {n : Nat} (h : l.length ≤ n) : l.take n = l := by
  induction l generalizing n with
  | nil => simp
  | cons a t ih =>
    have hl : t.length + 1 ≤ n := by simpa using h
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    show a :: List.take m t = a :: t
    exact congrArg _ (ih (by simpa using hl))

/-- Drop and map commute. -/
theorem dropMap (g : Nat → Nat) (l : List Nat) (i : Nat) :
    (l.map g).drop i = (l.drop i).map g := by
  induction i generalizing l with
  | zero => rfl
  | succ i ih =>
    cases l with
    | nil => simp
    | cons a t =>
      show List.drop i (t.map g) = (List.drop i t).map g
      exact ih t

theorem mmerge_nil_r (l : List Nat) : mmerge l [] = l := by
  cases l <;> simp [mmerge]

/-! The merge-path steps: from the invariant `out.drop (i+j) = mmerge
(sl.drop i) (M.drop j)`, one program comparison moves it one cell. -/

/-- The program took the left source (`¬ VJ < VI`): head is `sl i`. -/
theorem mmerge_stepL (sl M : List Nat) (i j : Nat) (hi : i < sl.length)
    (hj : j < M.length) (h : ¬ M.getD j 0 < sl.getD i 0)
    (hB : (mmerge sl M).drop (i + j) = mmerge (sl.drop i) (M.drop j)) :
    (mmerge sl M).getD (i + j) 0 = sl.getD i 0 ∧
      (mmerge sl M).drop (i + j + 1) = mmerge (sl.drop (i + 1)) (M.drop j) := by
  have e1 : sl.drop i = sl.getD i 0 :: sl.drop (i + 1) := dropCons hi
  have e2 : M.drop j = M.getD j 0 :: M.drop (j + 1) := dropCons hj
  have hu : mmerge (sl.drop i) (M.drop j)
      = sl.getD i 0 :: mmerge (sl.drop (i + 1)) (M.drop j) := by
    rw [e1, e2, mmerge, if_neg h]
  constructor
  · rw [← getDDrop, hB, hu]
    rfl
  · rw [dropSucc, hB, hu]
    rfl

/-- The program took the right source (`VJ < VI`): head is `M j`. -/
theorem mmerge_stepJ (sl M : List Nat) (i j : Nat) (hi : i < sl.length)
    (hj : j < M.length) (h : M.getD j 0 < sl.getD i 0)
    (hB : (mmerge sl M).drop (i + j) = mmerge (sl.drop i) (M.drop j)) :
    (mmerge sl M).getD (i + j) 0 = M.getD j 0 ∧
      (mmerge sl M).drop (i + j + 1) = mmerge (sl.drop i) (M.drop (j + 1)) := by
  have e1 : sl.drop i = sl.getD i 0 :: sl.drop (i + 1) := dropCons hi
  have e2 : M.drop j = M.getD j 0 :: M.drop (j + 1) := dropCons hj
  have hu : mmerge (sl.drop i) (M.drop j)
      = M.getD j 0 :: mmerge (sl.drop i) (M.drop (j + 1)) := by
    rw [e1, e2, mmerge, if_pos h]
  constructor
  · rw [← getDDrop, hB, hu]
    rfl
  · rw [dropSucc, hB, hu]
    rfl

/-! ## §2. Value and address fit -/

theorem memLeSum {l : List Nat} {v : Nat} (h : v ∈ l) : v ≤ l.sum := by
  induction l with
  | nil => cases h
  | cons a t ih =>
    rcases List.mem_cons.mp h with h | h
    · rw [h]
      simp only [List.sum_cons]
      omega
    · have := ih h
      simp only [List.sum_cons]
      omega

theorem sumRangeSucc (a : Nat → Nat) (k : Nat) :
    ((List.range (k + 1)).map a).sum = ((List.range k).map a).sum + a k := by
  rw [List.range_succ, List.map_append, List.map_singleton, List.sum_append,
    List.sum_singleton]

theorem sumRangeMono (a : Nat → Nat) {k n : Nat} (h : k ≤ n) :
    ((List.range k).map a).sum ≤ ((List.range n).map a).sum := by
  induction n with
  | zero =>
    have hk : k = 0 := Nat.le_zero.mp h
    subst hk
    exact Nat.le_refl _
  | succ n ih =>
    by_cases hk : k ≤ n
    · rw [sumRangeSucc]
      omega
    · have hk1 : k = n + 1 := by omega
      subst hk1
      rw [sumRangeSucc]
      omega

/-- Every half-sum is bounded by the total of the family. -/
theorem halfSumsLe (a : Nat → Nat) (k v : Nat) (hv : v ∈ halfSums a k) :
    v ≤ ((List.range k).map a).sum := by
  induction k generalizing v with
  | zero =>
    rw [halfSums] at hv
    simp at hv
    subst hv
    simp
  | succ k ih =>
    rw [halfSums, mem_mmerge] at hv
    rcases hv with h | h
    · have hle := ih v h
      rw [sumRangeSucc]
      omega
    · rw [List.mem_map] at h
      obtain ⟨y, hy, hyv⟩ := h
      have hyv' : y + a k = v := hyv
      have hle := ih y hy
      rw [← hyv', sumRangeSucc]
      omega

/-- The phase-A address ceiling fits below `2^(2n)`. -/
theorem arrLtPow (m : Nat) (hm : 4 ≤ m) :
    3 * m + 25 + 2 * 2 ^ (m / 2) < 2 ^ (2 * m) := by
  have hbase : ∀ q ∈ [4, 5], 3 * q + 25 + 2 * 2 ^ (q / 2) < 2 ^ (2 * q) := by decide
  induction m with
  | zero => omega
  | succ k ih =>
    by_cases hk : 4 ≤ k
    · have ihm := ih hk
      have h1 : (k + 1) / 2 ≤ k / 2 + 1 := by omega
      have h2 : 2 ^ ((k + 1) / 2) ≤ 2 ^ (k / 2 + 1) :=
        Nat.pow_le_pow_right (n := 2) (by omega) h1
      have h3 : (2 : Nat) ^ (k / 2 + 1) = 2 * 2 ^ (k / 2) := by
        rw [Nat.pow_succ]
        exact Nat.mul_comm _ _
      rw [h3] at h2
      have h4 : (2 : Nat) ^ (2 * k + 2) = 2 ^ (2 * k) * 4 := by
        rw [Nat.pow_add 2 (2 * k) 2, show (2 : Nat) ^ 2 = 4 from rfl]
      have hconv : 2 * (k + 1) = 2 * k + 2 := by omega
      rw [hconv, h4]
      have hpos : 1 ≤ 2 ^ (k / 2) := Nat.one_le_two_pow
      omega
    · have h41 : k + 1 = 4 := by omega
      rw [h41]
      exact hbase 4 (by simp)

/-- Every half-sum plus its addend fits in a word. -/
theorem halfSumAddFit {n w : Nat} {x : Instance n} (hn : 2 ≤ n)
    (hw : wordLength n x.bits ≤ w) (q : Nat) (hq : q < n)
    (v : Nat) (hv : v ∈ halfSums (instA x) q) :
    v + instA x q < 2 ^ w := by
  have hsum : 2 * ((List.range n).map (instA x)).sum
      < 2 ^ (wordLength n x.bits) := two_sum_lt_pow_wordLength x hn
  have hvle : v ≤ ((List.range q).map (instA x)).sum := halfSumsLe _ _ _ hv
  have hqle : ((List.range q).map (instA x)).sum ≤ ((List.range n).map (instA x)).sum :=
    sumRangeMono _ (by omega)
  have hmem : instA x q ∈ (List.range n).map (instA x) := by
    refine List.mem_map.mpr ⟨q, List.mem_range.mpr hq, rfl⟩
  have := memLeSum hmem
  have hpow : 2 ^ (wordLength n x.bits) ≤ 2 ^ w :=
    Nat.pow_le_pow_right (n := 2) (by omega) hw
  omega


/-! ## §3. Exec layer: the Phase A init segment (pc 86 → 98) -/

/-- The phase-A write region: registers (cells ≤ 22) plus both array strips. -/
def AReg (n : Nat) (c : Nat) : Prop :=
  c ≤ 22 ∨ (3 * n + 25 ≤ c ∧ c < 3 * n + 25 + 2 ^ (n / 2 + 1) + 1)

/-- 12 steps: `h := n/2`, `ARR1 := RELOC + n + 2 = 3n+25`,
`ARR2 := ARR1 + 2^h + 1`, `L := 1`, `S₀ := [0]` at `ARR1`, `k := 1`. -/
theorem init_exec {w n : Nat} (ρ : Nat → BitVec w)
    (f0 : Nat → Nat) (r S : Nat)
    (hfit : ∀ q, f0 q < 2 ^ w)
    (h1 : f0 1 = 1) (h2 : f0 2 = 0) (h7 : f0 7 = n) (h8 : f0 8 = 2 * n + 23)
    (haddr : ∀ c, c ≤ 3 * n + 26 + 2 * 2 ^ (n / 2) → c < 2 ^ w)
    (hS : 12 ≤ S) :
    ∃ f1, exec prog ρ S 86 r (memOf w f0) = exec prog ρ (S - 12) 98 r (memOf w f1) ∧
      (∀ q, f1 q < 2 ^ w) ∧
      f1 9 = n / 2 ∧ f1 18 = 3 * n + 25 ∧ f1 19 = 3 * n + 25 + 2 ^ (n / 2) + 1 ∧
      f1 10 = 1 ∧ f1 11 = 1 ∧
      f1 1 = 1 ∧ f1 2 = 0 ∧ f1 7 = n ∧ f1 8 = 2 * n + 23 ∧
      arrL f1 (3 * n + 25) 1 = [0] ∧
      Pres (AReg n) f0 f1 := by
  have hw1 : (1:Nat) ≤ 2 ^ w := Nat.one_le_two_pow
  have hA : (1:Nat) ≤ 2 ^ (n / 2) := Nat.one_le_two_pow
  have h2p : 2 ^ (n / 2) < 2 ^ w := haddr _ (by omega)
  have e86 : f0 7 / 2 ^ f0 1 = n / 2 := by rw [h7, h1, Nat.pow_one]
  have e87 : (up f0 9 (n / 2)) 8 + (up f0 9 (n / 2)) 7 = 3 * n + 23 := by
    rw [up_ne (show (8:Nat) ≠ 9 by omega), up_ne (show (7:Nat) ≠ 9 by omega),
      h8, h7]
    omega
  have e88 : (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 + (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 1 = 3 * n + 24 := by
    rw [up_eq, up_ne (show (1:Nat) ≠ 18 by omega),
      up_ne (show (1:Nat) ≠ 9 by omega), h1]
  have e89 : (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 + (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 1 = 3 * n + 25 := by
    rw [up_eq, up_ne (show (1:Nat) ≠ 18 by omega),
      up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 9 by omega), h1]
  have e90 : (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 1 + (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 2 = 1 := by
    rw [up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega),
      up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega),
      up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega),
      up_ne (show (1:Nat) ≠ 9 by omega), up_ne (show (2:Nat) ≠ 9 by omega), h1, h2]
  have e91 : (up (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 20 (1)) 20 * 2 ^ (up (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 20 (1)) 9 = 2 ^ (n / 2) := by
    rw [up_eq, up_ne (show (9:Nat) ≠ 20 by omega),
      up_ne (show (9:Nat) ≠ 18 by omega), up_ne (show (9:Nat) ≠ 18 by omega),
      up_ne (show (9:Nat) ≠ 18 by omega), up_eq, Nat.one_mul]
  have e92 : (up (up (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 20 (1)) 20 (2 ^ (n / 2))) 18 + (up (up (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 20 (1)) 20 (2 ^ (n / 2))) 20 = 3 * n + 25 + 2 ^ (n / 2) := by
    rw [up_ne (show (18:Nat) ≠ 20 by omega), up_eq,
      up_ne (show (18:Nat) ≠ 20 by omega), up_eq]
  have e93 : (up (up (up (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 20 (1)) 20 (2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2))) 19 + (up (up (up (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 20 (1)) 20 (2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2))) 1 = 3 * n + 25 + 2 ^ (n / 2) + 1 := by
    rw [up_eq, up_ne (show (1:Nat) ≠ 19 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega), up_ne (show (1:Nat) ≠ 20 by omega),
      up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 18 by omega),
      up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 9 by omega), h1]
  have e94 : (up (up (up (up (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 20 (1)) 20 (2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2) + 1)) 1 + (up (up (up (up (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 20 (1)) 20 (2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2) + 1)) 2 = 1 := by
    rw [up_ne (show (1:Nat) ≠ 19 by omega), up_ne (show (2:Nat) ≠ 19 by omega),
      up_ne (show (1:Nat) ≠ 19 by omega), up_ne (show (2:Nat) ≠ 19 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega), up_ne (show (2:Nat) ≠ 20 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega), up_ne (show (2:Nat) ≠ 20 by omega),
      up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega),
      up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega),
      up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega),
      up_ne (show (1:Nat) ≠ 9 by omega), up_ne (show (2:Nat) ≠ 9 by omega), h1, h2]
  have e95 : (up (up (up (up (up (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 20 (1)) 20 (2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2) + 1)) 11 (1)) 18 + (up (up (up (up (up (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 20 (1)) 20 (2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2) + 1)) 11 (1)) 2 = 3 * n + 25 := by
    rw [up_ne (show (18:Nat) ≠ 11 by omega), up_ne (show (18:Nat) ≠ 19 by omega),
      up_ne (show (18:Nat) ≠ 19 by omega), up_ne (show (18:Nat) ≠ 20 by omega),
      up_ne (show (18:Nat) ≠ 20 by omega), up_eq,
      up_ne (show (2:Nat) ≠ 11 by omega), up_ne (show (2:Nat) ≠ 19 by omega),
      up_ne (show (2:Nat) ≠ 19 by omega), up_ne (show (2:Nat) ≠ 20 by omega),
      up_ne (show (2:Nat) ≠ 20 by omega), up_ne (show (2:Nat) ≠ 18 by omega),
      up_ne (show (2:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega),
      up_ne (show (2:Nat) ≠ 9 by omega), h2, Nat.add_zero]
  have e96a : (up (up (up (up (up (up (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 20 (1)) 20 (2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2) + 1)) 11 (1)) 20 (3 * n + 25)) 20 = 3 * n + 25 := by rfl
  have e96b : (up (up (up (up (up (up (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 20 (1)) 20 (2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2) + 1)) 11 (1)) 20 (3 * n + 25)) 2 = 0 := by
    rw [up_ne (show (2:Nat) ≠ 20 by omega),
      up_ne (show (2:Nat) ≠ 11 by omega), up_ne (show (2:Nat) ≠ 19 by omega),
      up_ne (show (2:Nat) ≠ 19 by omega), up_ne (show (2:Nat) ≠ 20 by omega),
      up_ne (show (2:Nat) ≠ 20 by omega), up_ne (show (2:Nat) ≠ 18 by omega),
      up_ne (show (2:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega),
      up_ne (show (2:Nat) ≠ 9 by omega), h2]
  have e97 : (up (up (up (up (up (up (up (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 20 (1)) 20 (2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2) + 1)) 11 (1)) 20 (3 * n + 25)) (3 * n + 25) (0)) 1 + (up (up (up (up (up (up (up (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 20 (1)) 20 (2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2) + 1)) 11 (1)) 20 (3 * n + 25)) (3 * n + 25) (0)) 2 = 1 := by
    rw [up_ne (show (1:Nat) ≠ 3 * n + 25 by omega),
      up_ne (show (2:Nat) ≠ 3 * n + 25 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega), up_ne (show (2:Nat) ≠ 20 by omega),
      up_ne (show (1:Nat) ≠ 11 by omega), up_ne (show (2:Nat) ≠ 11 by omega),
      up_ne (show (1:Nat) ≠ 19 by omega), up_ne (show (2:Nat) ≠ 19 by omega),
      up_ne (show (1:Nat) ≠ 19 by omega), up_ne (show (2:Nat) ≠ 19 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega), up_ne (show (2:Nat) ≠ 20 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega), up_ne (show (2:Nat) ≠ 20 by omega),
      up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega),
      up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega),
      up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega),
      up_ne (show (1:Nat) ≠ 9 by omega), up_ne (show (2:Nat) ≠ 9 by omega), h1, h2]
  have f1f : ∀ q, (up f0 9 (n / 2)) q < 2 ^ w := up_fit hfit (haddr _ (by omega))
  have f2f : ∀ q, (up (up f0 9 (n / 2)) 18 (3 * n + 23)) q < 2 ^ w := up_fit f1f (haddr _ (by omega))
  have f3f : ∀ q, (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) q < 2 ^ w := up_fit f2f (haddr _ (by omega))
  have f4f : ∀ q, (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) q < 2 ^ w := up_fit f3f (haddr _ (by omega))
  have f5f : ∀ q, (up (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 20 (1)) q < 2 ^ w := up_fit f4f (by omega)
  have f6f : ∀ q, (up (up (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 20 (1)) 20 (2 ^ (n / 2))) q < 2 ^ w := up_fit f5f h2p
  have f7f : ∀ q, (up (up (up (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 20 (1)) 20 (2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2))) q < 2 ^ w := up_fit f6f (haddr _ (by omega))
  have f8f : ∀ q, (up (up (up (up (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 20 (1)) 20 (2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2) + 1)) q < 2 ^ w := up_fit f7f (haddr _ (by omega))
  have f9f : ∀ q, (up (up (up (up (up (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 20 (1)) 20 (2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2) + 1)) 11 (1)) q < 2 ^ w := up_fit f8f (by omega)
  have f10f : ∀ q, (up (up (up (up (up (up (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 20 (1)) 20 (2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2) + 1)) 11 (1)) 20 (3 * n + 25)) q < 2 ^ w := up_fit f9f (haddr _ (by omega))
  have f11f : ∀ q, (up (up (up (up (up (up (up (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 20 (1)) 20 (2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2) + 1)) 11 (1)) 20 (3 * n + 25)) (3 * n + 25) (0)) q < 2 ^ w := up_fit f10f (haddr _ (by omega))
  refine ⟨(up (up (up (up (up (up (up (up (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 20 (1)) 20 (2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2) + 1)) 11 (1)) 20 (3 * n + 25)) (3 * n + 25) (0)) 10 (1)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [exec_shr_step (by omega)
        (show prog.getD 86 Instr.reject = Instr.shr 9 7 1 by rfl) hfit, e86,
      exec_add_step (by omega)
        (show prog.getD 87 Instr.reject = Instr.add 18 8 7 by rfl), e87,
      exec_add_step (by omega)
        (show prog.getD 88 Instr.reject = Instr.add 18 18 1 by rfl), e88,
      exec_add_step (by omega)
        (show prog.getD 89 Instr.reject = Instr.add 18 18 1 by rfl), e89,
      exec_add_step (by omega)
        (show prog.getD 90 Instr.reject = Instr.add 20 1 2 by rfl), e90,
      exec_shl_step (by omega)
        (show prog.getD 91 Instr.reject = Instr.shl 20 20 9 by rfl) f5f
        (by rw [e91]; exact h2p), e91,
      exec_add_step (by omega)
        (show prog.getD 92 Instr.reject = Instr.add 19 18 20 by rfl), e92,
      exec_add_step (by omega)
        (show prog.getD 93 Instr.reject = Instr.add 19 19 1 by rfl), e93,
      exec_add_step (by omega)
        (show prog.getD 94 Instr.reject = Instr.add 11 1 2 by rfl), e94,
      exec_add_step (by omega)
        (show prog.getD 95 Instr.reject = Instr.add 20 18 2 by rfl), e95,
      exec_store_step (by omega)
        (show prog.getD 96 Instr.reject = Instr.store 20 2 by rfl) f10f,
      e96a, e96b,
      exec_add_step (by omega)
        (show prog.getD 97 Instr.reject = Instr.add 10 1 2 by rfl), e97]
    simp only [Nat.sub_sub, Nat.reduceAdd]
  · exact up_fit f11f (by omega)
  · rw [up_ne (show (9:Nat) ≠ 10 by omega),
      up_ne (show (9:Nat) ≠ 3 * n + 25 by omega),
      up_ne (show (9:Nat) ≠ 20 by omega), up_ne (show (9:Nat) ≠ 11 by omega),
      up_ne (show (9:Nat) ≠ 19 by omega), up_ne (show (9:Nat) ≠ 19 by omega),
      up_ne (show (9:Nat) ≠ 20 by omega), up_ne (show (9:Nat) ≠ 20 by omega),
      up_ne (show (9:Nat) ≠ 18 by omega), up_ne (show (9:Nat) ≠ 18 by omega),
      up_ne (show (9:Nat) ≠ 18 by omega), up_eq]
  · rw [up_ne (show (18:Nat) ≠ 10 by omega),
      up_ne (show (18:Nat) ≠ 3 * n + 25 by omega),
      up_ne (show (18:Nat) ≠ 20 by omega), up_ne (show (18:Nat) ≠ 11 by omega),
      up_ne (show (18:Nat) ≠ 19 by omega), up_ne (show (18:Nat) ≠ 19 by omega),
      up_ne (show (18:Nat) ≠ 20 by omega), up_ne (show (18:Nat) ≠ 20 by omega),
      up_eq]
  · rw [up_ne (show (19:Nat) ≠ 10 by omega),
      up_ne (show (19:Nat) ≠ 3 * n + 25 by omega),
      up_ne (show (19:Nat) ≠ 20 by omega), up_ne (show (19:Nat) ≠ 11 by omega),
      up_eq]
  · exact up_eq _ _ _
  · rw [up_ne (show (11:Nat) ≠ 10 by omega),
      up_ne (show (11:Nat) ≠ 3 * n + 25 by omega),
      up_ne (show (11:Nat) ≠ 20 by omega), up_eq]
  · rw [up_ne (show (1:Nat) ≠ 10 by omega),
      up_ne (show (1:Nat) ≠ 3 * n + 25 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega),
      up_ne (show (1:Nat) ≠ 11 by omega),
      up_ne (show (1:Nat) ≠ 19 by omega),
      up_ne (show (1:Nat) ≠ 19 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega),
      up_ne (show (1:Nat) ≠ 18 by omega),
      up_ne (show (1:Nat) ≠ 18 by omega),
      up_ne (show (1:Nat) ≠ 18 by omega),
      up_ne (show (1:Nat) ≠ 9 by omega),
      h1]
  · rw [up_ne (show (2:Nat) ≠ 10 by omega),
      up_ne (show (2:Nat) ≠ 3 * n + 25 by omega),
      up_ne (show (2:Nat) ≠ 20 by omega),
      up_ne (show (2:Nat) ≠ 11 by omega),
      up_ne (show (2:Nat) ≠ 19 by omega),
      up_ne (show (2:Nat) ≠ 19 by omega),
      up_ne (show (2:Nat) ≠ 20 by omega),
      up_ne (show (2:Nat) ≠ 20 by omega),
      up_ne (show (2:Nat) ≠ 18 by omega),
      up_ne (show (2:Nat) ≠ 18 by omega),
      up_ne (show (2:Nat) ≠ 18 by omega),
      up_ne (show (2:Nat) ≠ 9 by omega),
      h2]
  · rw [up_ne (show (7:Nat) ≠ 10 by omega),
      up_ne (show (7:Nat) ≠ 3 * n + 25 by omega),
      up_ne (show (7:Nat) ≠ 20 by omega),
      up_ne (show (7:Nat) ≠ 11 by omega),
      up_ne (show (7:Nat) ≠ 19 by omega),
      up_ne (show (7:Nat) ≠ 19 by omega),
      up_ne (show (7:Nat) ≠ 20 by omega),
      up_ne (show (7:Nat) ≠ 20 by omega),
      up_ne (show (7:Nat) ≠ 18 by omega),
      up_ne (show (7:Nat) ≠ 18 by omega),
      up_ne (show (7:Nat) ≠ 18 by omega),
      up_ne (show (7:Nat) ≠ 9 by omega),
      h7]
  · rw [up_ne (show (8:Nat) ≠ 10 by omega),
      up_ne (show (8:Nat) ≠ 3 * n + 25 by omega),
      up_ne (show (8:Nat) ≠ 20 by omega),
      up_ne (show (8:Nat) ≠ 11 by omega),
      up_ne (show (8:Nat) ≠ 19 by omega),
      up_ne (show (8:Nat) ≠ 19 by omega),
      up_ne (show (8:Nat) ≠ 20 by omega),
      up_ne (show (8:Nat) ≠ 20 by omega),
      up_ne (show (8:Nat) ≠ 18 by omega),
      up_ne (show (8:Nat) ≠ 18 by omega),
      up_ne (show (8:Nat) ≠ 18 by omega),
      up_ne (show (8:Nat) ≠ 9 by omega),
      h8]
  · show [(up (up (up (up (up (up (up (up (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 20 (1)) 20 (2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2) + 1)) 11 (1)) 20 (3 * n + 25)) (3 * n + 25) (0)) 10 (1)) (3 * n + 25 + 0)] = [0]
    rw [Nat.add_zero, up_ne (show 3 * n + 25 ≠ 10 by omega), up_eq]
  · have hR : (1:Nat) ≤ 2 ^ (n / 2 + 1) := Nat.one_le_two_pow
    have hRA : AReg n (3 * n + 25) :=
      Or.inr ⟨Nat.le_refl (3 * n + 25), by omega⟩
    have q1 : Pres (AReg n) f0 (up f0 9 (n / 2)) := pres_up (Or.inl (show (9:Nat) ≤ 22 by omega))
    have q2 : Pres (AReg n) (up f0 9 (n / 2)) (up (up f0 9 (n / 2)) 18 (3 * n + 23)) := pres_up (Or.inl (show (18:Nat) ≤ 22 by omega))
    have q3 : Pres (AReg n) (up (up f0 9 (n / 2)) 18 (3 * n + 23)) (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) := pres_up (Or.inl (show (18:Nat) ≤ 22 by omega))
    have q4 : Pres (AReg n) (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) := pres_up (Or.inl (show (18:Nat) ≤ 22 by omega))
    have q5 : Pres (AReg n) (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) (up (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 20 (1)) := pres_up (Or.inl (show (20:Nat) ≤ 22 by omega))
    have q6 : Pres (AReg n) (up (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 20 (1)) (up (up (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 20 (1)) 20 (2 ^ (n / 2))) := pres_up (Or.inl (show (20:Nat) ≤ 22 by omega))
    have q7 : Pres (AReg n) (up (up (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 20 (1)) 20 (2 ^ (n / 2))) (up (up (up (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 20 (1)) 20 (2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2))) := pres_up (Or.inl (show (19:Nat) ≤ 22 by omega))
    have q8 : Pres (AReg n) (up (up (up (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 20 (1)) 20 (2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2))) (up (up (up (up (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 20 (1)) 20 (2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2) + 1)) := pres_up (Or.inl (show (19:Nat) ≤ 22 by omega))
    have q9 : Pres (AReg n) (up (up (up (up (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 20 (1)) 20 (2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2) + 1)) (up (up (up (up (up (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 20 (1)) 20 (2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2) + 1)) 11 (1)) := pres_up (Or.inl (show (11:Nat) ≤ 22 by omega))
    have q10 : Pres (AReg n) (up (up (up (up (up (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 20 (1)) 20 (2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2) + 1)) 11 (1)) (up (up (up (up (up (up (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 20 (1)) 20 (2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2) + 1)) 11 (1)) 20 (3 * n + 25)) := pres_up (Or.inl (show (20:Nat) ≤ 22 by omega))
    have q11 : Pres (AReg n) (up (up (up (up (up (up (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 20 (1)) 20 (2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2) + 1)) 11 (1)) 20 (3 * n + 25)) (up (up (up (up (up (up (up (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 20 (1)) 20 (2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2) + 1)) 11 (1)) 20 (3 * n + 25)) (3 * n + 25) (0)) := pres_up (hRA)
    have q12 : Pres (AReg n) (up (up (up (up (up (up (up (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 20 (1)) 20 (2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2) + 1)) 11 (1)) 20 (3 * n + 25)) (3 * n + 25) (0)) (up (up (up (up (up (up (up (up (up (up (up (up f0 9 (n / 2)) 18 (3 * n + 23)) 18 (3 * n + 24)) 18 (3 * n + 25)) 20 (1)) 20 (2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2))) 19 (3 * n + 25 + 2 ^ (n / 2) + 1)) 11 (1)) 20 (3 * n + 25)) (3 * n + 25) (0)) 10 (1)) := pres_up (Or.inl (show (10:Nat) ≤ 22 by omega))
    exact pres_trans q1 (pres_trans q2 (pres_trans q3 (pres_trans q4 (pres_trans q5 (pres_trans q6 (pres_trans q7 (pres_trans q8 (pres_trans q9 (pres_trans q10 (pres_trans q11 (q12)))))))))))

/-! ## §4. The merge loops -/

/-- `getD` of a `(+ak)`-shifted map. -/
theorem getD_map_add (sl : List Nat) (ak : Nat) (j : Nat) (hj : j < sl.length) :
    (sl.map (fun z => z + ak)).getD j 0 = sl.getD j 0 + ak := by
  induction sl generalizing j with
  | nil => exact absurd hj (by simp)
  | cons a t ih =>
    cases j with
    | zero => rfl
    | succ j =>
      rw [List.getD_cons_succ, List.map_cons, List.getD_cons_succ]
      apply ih
      simpa using hj

/-- The merge-loop write region. -/
def MReg (d L : Nat) (c : Nat) : Prop :=
  c = 12 ∨ c = 13 ∨ c = 14 ∨ c = 15 ∨ c = 16 ∨ c = 20 ∨ c = 21 ∨ (d ≤ c ∧ c < d + 2 * L)

/-- `getD i` of a list is a member when `i < length`. -/
theorem mem_getD {l : List Nat} {i : Nat} (h : i < l.length) : l.getD i 0 ∈ l := by
  induction l generalizing i with
  | nil => exact absurd h (by simp)
  | cons a t ihl =>
    cases i with
    | zero => simp
    | succ i => exact List.mem_cons_of_mem _ (ihl (by simpa using h))

/-- Array view ignores register writes below the base. -/
theorem arrL_up_regs {f : Nat → Nat} {d L c v : Nat} (hd : d + 2 * L ≤ c ∨ c < d)
    (hfit : ∀ q, f q < 2 ^ w) : True := trivial

theorem MReg_dst {d L : Nat} {c : Nat} (h1 : d ≤ c) (h2 : c < d + 2 * L) :
    MReg d L c := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩))))))

/-- Drain-i body loop (pc 125 → 141). -/
theorem diLoop_exec {w : Nat} (ρ : Nat → BitVec w) :
    ∀ (N L b d : Nat) (sl out : List Nat) (f : Nat → Nat) (i wq S r : Nat),
    sl.length = L →
    i < L → wq = L + i → f 12 = i → f 14 = wq → f 11 = L →
    f 18 = b → f 19 = d → f 1 = 1 → f 2 = 0 →
    (∀ q, q < L → f (b + q) = sl.getD q 0) →
    (∀ v ∈ sl, v < 2 ^ w) →
    (out.take wq = (arrL f d (2 * L)).take wq) →
    out.drop wq = sl.drop i →
    (∀ q, f q < 2 ^ w) → b + L < 2 ^ w → d + 2 * L < 2 ^ w → 2 * L < 2 ^ w →
    33 ≤ b → 33 ≤ d → (∀ p q, p < 2 * L → q < L → d + p ≠ b + q) →
    L - i ≤ N → 8 * N + 9 ≤ S →
    ∃ c f', c ≤ 8 * N + 9 ∧
      exec prog ρ S 125 r (memOf w f) = exec prog ρ (S - c) 141 r (memOf w f') ∧
      arrL f' d (2 * L) = out ∧ f' 12 = L ∧ f' 14 = 2 * L ∧
      (∀ q, f' q < 2 ^ w) ∧ Pres (MReg d L) f f' := by
  intro N
  induction N with
  | zero =>
    intro L b d sl out f i wq S r hsL hiL hwi hf12 hf14 hf11 hf18 hf19 h1 h2
      hsrc hvfit htake hdrop hfit hbL hdL h2L hb33 hd33 hdisj hN hS
    omega
  | succ N ih =>
    intro L b d sl out f i wq S r hsL hiL hwi hf12 hf14 hf11 hf18 hf19 h1 h2
      hsrc hvfit htake hdrop hfit hbL hdL h2L hb33 hd33 hdisj hN hS
    have hvsl : sl.getD i 0 < 2 ^ w := hvfit _ (mem_getD (by omega))
    have fi1 : ∀ q, (up f 20 (b + i)) q < 2 ^ w := up_fit hfit (by have := hbL; omega)
    have fi2 : ∀ q, (up (up f 20 (b + i)) 15 (sl.getD i 0)) q < 2 ^ w := up_fit fi1 (by omega)
    have fi3 : ∀ q, (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) q < 2 ^ w := up_fit fi2 (by have := hdL; omega)
    have fi4 : ∀ q, (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) q < 2 ^ w := up_fit fi3 (by omega)
    have fi5 : ∀ q, (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) q < 2 ^ w := up_fit fi4 (by omega)
    have fi6 : ∀ q, (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) q < 2 ^ w := up_fit fi5 (by omega)
    -- array views
    have hA2 : arrL (up (up f 20 (b + i)) 15 (sl.getD i 0)) d (2 * L) = arrL f d (2 * L) := by
      rw [show arrL (up (up f 20 (b + i)) 15 (sl.getD i 0)) d (2 * L) = arrL (up f 20 (b + i)) d (2 * L) from
          arrL_up_out (fun q _ => show (15:Nat) ≠ d + q by omega),
        show arrL (up f 20 (b + i)) d (2 * L) = arrL f d (2 * L) from
          arrL_up_out (fun q _ => show (20:Nat) ≠ d + q by omega)]
    have hA3 : arrL (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) d (2 * L) = arrL f d (2 * L) := by
      rw [show arrL (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) d (2 * L) = arrL (up (up f 20 (b + i)) 15 (sl.getD i 0)) d (2 * L) from
          arrL_up_out (fun q _ => show (21:Nat) ≠ d + q by omega), hA2]
    have hA6 : arrL (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) d (2 * L) = arrL (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) d (2 * L) := by
      rw [show arrL (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) d (2 * L) = arrL (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) d (2 * L) from
          arrL_up_out (fun q _ => show (14:Nat) ≠ d + q by omega),
        show arrL (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) d (2 * L) = arrL (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) d (2 * L) from
          arrL_up_out (fun q _ => show (12:Nat) ≠ d + q by omega)]
    have hleno : out.length = 2 * L := by
      have h1l := List.length_drop (l := out) (i := wq)
      rw [hdrop, List.length_drop (l := sl) (i := i)] at h1l
      omega
    -- list facts
    have hisl : i < sl.length := by omega
    have hwqo : wq < out.length := by omega
    have hwq2L : wq < 2 * L := by omega
    have htake1 : out.take (wq + 1) = (arrL (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) d (2 * L)).take (wq + 1) := by
      rw [hA6, arrL_take_up hwq2L, hA3, ← htake, takeSucc hwqo]
      congr 1
      rw [← getDDrop, hdrop, dropCons hisl]
      simp
    have hdrop1 : out.drop (wq + 1) = sl.drop (i + 1) := by
      rw [dropSucc, hdrop, dropCons hisl]
      simp
    -- G6 register facts
    have e12g : (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 12 = i + 1 := by
      rw [up_ne (show (12:Nat) ≠ 14 by omega), up_eq]
    have e14g : (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 14 = wq + 1 := up_eq _ _ _
    have e11g : (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 11 = L := by rw [up_ne (show (11:Nat) ≠ 14 by omega), up_ne (show (11:Nat) ≠ 12 by omega), up_ne (show (11:Nat) ≠ d + wq by omega), up_ne (show (11:Nat) ≠ 21 by omega), up_ne (show (11:Nat) ≠ 15 by omega), up_ne (show (11:Nat) ≠ 20 by omega), hf11]
    have e18g : (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 18 = b := by rw [up_ne (show (18:Nat) ≠ 14 by omega), up_ne (show (18:Nat) ≠ 12 by omega), up_ne (show (18:Nat) ≠ d + wq by omega), up_ne (show (18:Nat) ≠ 21 by omega), up_ne (show (18:Nat) ≠ 15 by omega), up_ne (show (18:Nat) ≠ 20 by omega), hf18]
    have e19g : (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 19 = d := by rw [up_ne (show (19:Nat) ≠ 14 by omega), up_ne (show (19:Nat) ≠ 12 by omega), up_ne (show (19:Nat) ≠ d + wq by omega), up_ne (show (19:Nat) ≠ 21 by omega), up_ne (show (19:Nat) ≠ 15 by omega), up_ne (show (19:Nat) ≠ 20 by omega), hf19]
    have e1g : (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 1 = 1 := by rw [up_ne (show (1:Nat) ≠ 14 by omega), up_ne (show (1:Nat) ≠ 12 by omega), up_ne (show (1:Nat) ≠ d + wq by omega), up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (1:Nat) ≠ 15 by omega), up_ne (show (1:Nat) ≠ 20 by omega), h1]
    have e2g : (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 2 = 0 := by rw [up_ne (show (2:Nat) ≠ 14 by omega), up_ne (show (2:Nat) ≠ 12 by omega), up_ne (show (2:Nat) ≠ d + wq by omega), up_ne (show (2:Nat) ≠ 21 by omega), up_ne (show (2:Nat) ≠ 15 by omega), up_ne (show (2:Nat) ≠ 20 by omega), h2]
    have esrcg : ∀ q, q < L → (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) (b + q) = sl.getD q 0 := by
      intro q hq
      rw [up_ne (show b + q ≠ 14 by omega),
        up_ne (show b + q ≠ 12 by omega),
        up_ne (Ne.symm (hdisj wq q (by omega) hq)),
        up_ne (show b + q ≠ 21 by omega),
        up_ne (show b + q ≠ 15 by omega), up_ne (show b + q ≠ 20 by omega)]
      exact hsrc q hq
    -- the shared 7-step prefix (125..130) with inline normalization
    have hsteps : exec prog ρ S 125 r (memOf w f)
        = exec prog ρ (S - 6) 131 r (memOf w (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1))) := by
      rw [exec_add_step (by omega)
          (show prog.getD 125 Instr.reject = Instr.add 20 18 12 by rfl),
          show f 18 + f 12 = b + i from by rw [hf18, hf12],
        exec_load_step (by omega)
          (show prog.getD 126 Instr.reject = Instr.load 15 20 by rfl) fi1,
          up_eq, up_ne (show b + i ≠ 20 by omega), hsrc i hiL,
        exec_add_step (by omega)
          (show prog.getD 127 Instr.reject = Instr.add 21 19 14 by rfl),
          show (up (up f 20 (b + i)) 15 (sl.getD i 0)) 19 + (up (up f 20 (b + i)) 15 (sl.getD i 0)) 14 = d + wq from by
            rw [up_ne (show (19:Nat) ≠ 15 by omega),
              up_ne (show (14:Nat) ≠ 15 by omega),
              up_ne (show (19:Nat) ≠ 20 by omega),
              up_ne (show (14:Nat) ≠ 20 by omega), hf19, hf14],
        exec_store_step (by omega)
          (show prog.getD 128 Instr.reject = Instr.store 21 15 by rfl) fi3,
          up_eq, up_ne (show (15:Nat) ≠ 21 by omega), up_eq,
        exec_add_step (by omega)
          (show prog.getD 129 Instr.reject = Instr.add 12 12 1 by rfl),
          show (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 + (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 1 = i + 1 from by
            rw [up_ne (show (12:Nat) ≠ d + wq by omega),
              up_ne (show (12:Nat) ≠ 21 by omega), up_ne (show (12:Nat) ≠ 15 by omega),
              up_ne (show (12:Nat) ≠ 20 by omega), hf12,
              up_ne (show (1:Nat) ≠ d + wq by omega),
              up_ne (show (1:Nat) ≠ 21 by omega),
              up_ne (show (1:Nat) ≠ 15 by omega),
              up_ne (show (1:Nat) ≠ 20 by omega), h1],
        exec_add_step (by omega)
          (show prog.getD 130 Instr.reject = Instr.add 14 14 1 by rfl),
          show (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 + (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 1 = wq + 1 from by
            rw [up_ne (show (14:Nat) ≠ 12 by omega),
              up_ne (show (14:Nat) ≠ d + wq by omega),
              up_ne (show (14:Nat) ≠ 21 by omega),
              up_ne (show (14:Nat) ≠ 15 by omega),
              up_ne (show (14:Nat) ≠ 20 by omega), hf14,
              up_ne (show (1:Nat) ≠ 12 by omega),
              up_ne (show (1:Nat) ≠ d + wq by omega),
              up_ne (show (1:Nat) ≠ 21 by omega),
              up_ne (show (1:Nat) ≠ 15 by omega),
              up_ne (show (1:Nat) ≠ 20 by omega), h1]]
      simp only [Nat.sub_sub, Nat.reduceAdd]
    by_cases hnext : i + 1 < L
    · have h131 : (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 12 < (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 11 := by

        rw [e12g, e11g]
        exact hnext
      rw [hsteps, exec_blt_lt_step (by omega)
        (show prog.getD 131 Instr.reject = Instr.blt 12 11 125 by rfl) fi6 h131]
      obtain ⟨c2, f2, hc2, hex2, harr2, h122, h142, hfit2, hpres2⟩ :=
        ih L b d sl out (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) (i + 1) (wq + 1) (S - 7) r hsL hnext (by omega)
          e12g e14g e11g e18g e19g e1g e2g esrcg hvfit htake1 hdrop1 fi6 hbL hdL
          h2L hb33 hd33 hdisj (by omega) (by omega)
      refine ⟨7 + c2, f2, by omega, ?_, harr2, h122, h142, hfit2, ?_⟩
      · have hS7 : S - 6 - 1 = S - 7 := by omega
        have hS2 : S - 7 - c2 = S - (7 + c2) := by omega
        rw [hS7, hex2, hS2]
      · have q1 : Pres (MReg d L) f (up f 20 (b + i)) :=
          pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
        have q2 : Pres (MReg d L) (up f 20 (b + i)) (up (up f 20 (b + i)) 15 (sl.getD i 0)) :=
          pres_up (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        have q3 : Pres (MReg d L) (up (up f 20 (b + i)) 15 (sl.getD i 0)) (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) :=
          pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
        have q4 : Pres (MReg d L) (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) := pres_up (MReg_dst (by omega) (by omega))
        have q5 : Pres (MReg d L) (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) := pres_up (Or.inl rfl)
        have q6 : Pres (MReg d L) (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) :=
          pres_up (Or.inr (Or.inr (Or.inl rfl)))
        exact pres_trans q1 (pres_trans q2 (pres_trans q3 (pres_trans q4
          (pres_trans q5 (pres_trans q6 hpres2)))))
    · have h131 : ¬ (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 12 < (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 11 := by

        rw [e12g, e11g]
        omega
      have h132 : (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 2 < (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 1 := by rw [e2g, e1g]; omega
      have hrw2 : exec prog ρ S 125 r (memOf w f)
          = exec prog ρ (S - 8) 141 r (memOf w (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1))) := by
        rw [hsteps,
          exec_blt_ge_step (by omega)
            (show prog.getD 131 Instr.reject = Instr.blt 12 11 125 by rfl) fi6 h131,
          exec_blt_lt_step (by omega)
            (show prog.getD 132 Instr.reject = Instr.blt 2 1 141 by rfl) fi6 h132]
        simp only [Nat.sub_sub, Nat.reduceAdd]
      have hfull : arrL (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) d (2 * L) = out := by
        have hq2 : wq + 1 = 2 * L := by omega
        rw [hq2] at htake1
        have hto := takeAll (l := out) (n := 2 * L) (by omega)
        have hla : (arrL (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) d (2 * L)).length = 2 * L := by simp [arrL]
        have hta := takeAll (l := arrL (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) d (2 * L)) (n := 2 * L) (by omega)
        rw [← hta, ← hto, htake1, hq2]
      refine ⟨8, (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)), by omega, hrw2, hfull, by rw [e12g]; omega,
        by rw [e14g]; omega, fi6, ?_⟩
      have q1 : Pres (MReg d L) f (up f 20 (b + i)) :=
        pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      have q2 : Pres (MReg d L) (up f 20 (b + i)) (up (up f 20 (b + i)) 15 (sl.getD i 0)) :=
        pres_up (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      have q3 : Pres (MReg d L) (up (up f 20 (b + i)) 15 (sl.getD i 0)) (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) :=
        pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
      have q4 : Pres (MReg d L) (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) := pres_up (MReg_dst (by omega) (by omega))
      have q5 : Pres (MReg d L) (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) := pres_up (Or.inl rfl)
      exact pres_trans q1 (pres_trans q2 (pres_trans q3 (pres_trans q4
        (pres_trans q5 (pres_up (Or.inr (Or.inr (Or.inl rfl))))))))

/-- Drain-j do-while loop (pc 133 → 141). -/
theorem djLoop_exec {w : Nat} (ρ : Nat → BitVec w) :
    ∀ (N L b d ak : Nat) (sl out : List Nat) (f : Nat → Nat) (j wq S r : Nat),
    sl.length = L →
    j < L → wq = L + j → f 12 = L → f 13 = j → f 14 = wq → f 11 = L →
    f 17 = ak → f 18 = b → f 19 = d → f 1 = 1 → f 2 = 0 →
    (∀ q, q < L → f (b + q) = sl.getD q 0) →
    (∀ v ∈ sl, v + ak < 2 ^ w) →
    (out.take wq = (arrL f d (2 * L)).take wq) →
    out.drop wq = (sl.map (fun z => z + ak)).drop j →
    (∀ q, f q < 2 ^ w) → b + L < 2 ^ w → d + 2 * L < 2 ^ w → 2 * L < 2 ^ w →
    33 ≤ b → 33 ≤ d → (∀ p q, p < 2 * L → q < L → d + p ≠ b + q) →
    L - j ≤ N → 8 * N + 8 ≤ S →
    ∃ c f', c ≤ 8 * N + 8 ∧
      exec prog ρ S 133 r (memOf w f) = exec prog ρ (S - c) 141 r (memOf w f') ∧
      arrL f' d (2 * L) = out ∧ f' 12 = L ∧ f' 13 = L ∧ f' 14 = 2 * L ∧
      (∀ q, f' q < 2 ^ w) ∧ Pres (MReg d L) f f' := by
  intro N
  induction N with
  | zero =>
    intro L b d ak sl out f j wq S r hsL hjL hwj hf12 hf13 hf14 hf11 hf17 hf18
      hf19 h1 h2 hsrc hvfit htake hdrop hfit hbL hdL h2L hb33 hd33 hdisj hN hS
    exact absurd hN (by omega)
  | succ N ih =>
    intro L b d ak sl out f j wq S r hsL hjL hwj hf12 hf13 hf14 hf11 hf17 hf18
      hf19 h1 h2 hsrc hvfit htake hdrop hfit hbL hdL h2L hb33 hd33 hdisj hN hS
    have hvj : sl.getD j 0 + ak < 2 ^ w := hvfit _ (mem_getD (by omega))
    have fi1 : ∀ q, (up f 21 (b + j)) q < 2 ^ w := up_fit hfit (by have := hbL; omega)
    have fi2 : ∀ q, (up (up f 21 (b + j)) 16 (sl.getD j 0)) q < 2 ^ w := up_fit fi1 (by omega)
    have fi3 : ∀ q, (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) q < 2 ^ w := up_fit fi2 hvj
    have fi4 : ∀ q, (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) q < 2 ^ w := up_fit fi3 (by have := hdL; omega)
    have fi5 : ∀ q, (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) q < 2 ^ w := up_fit fi4 (by omega)
    have fi6 : ∀ q, (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) q < 2 ^ w := up_fit fi5 (by omega)
    have fi7 : ∀ q, (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) q < 2 ^ w := up_fit fi6 (by omega)
    have hA4 : arrL (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) d (2 * L) = arrL f d (2 * L) := by
      rw [show arrL (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) d (2 * L) = arrL (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) d (2 * L) from
          arrL_up_out (fun q _ => show (20:Nat) ≠ d + q by omega),
        show arrL (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) d (2 * L) = arrL (up (up f 21 (b + j)) 16 (sl.getD j 0)) d (2 * L) from
          arrL_up_out (fun q _ => show (16:Nat) ≠ d + q by omega),
        show arrL (up (up f 21 (b + j)) 16 (sl.getD j 0)) d (2 * L) = arrL (up f 21 (b + j)) d (2 * L) from
          arrL_up_out (fun q _ => show (16:Nat) ≠ d + q by omega),
        show arrL (up f 21 (b + j)) d (2 * L) = arrL f d (2 * L) from
          arrL_up_out (fun q _ => show (21:Nat) ≠ d + q by omega)]
    have hA7 : arrL (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) d (2 * L) = arrL (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) d (2 * L) := by
      rw [show arrL (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) d (2 * L) = arrL (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) d (2 * L) from
          arrL_up_out (fun q _ => show (14:Nat) ≠ d + q by omega),
        show arrL (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) d (2 * L) = arrL (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) d (2 * L) from
          arrL_up_out (fun q _ => show (13:Nat) ≠ d + q by omega)]
    have hMlen : (sl.map (fun z => z + ak)).length = L := by
      simp [List.length_map, hsL]
    have hleno : out.length = 2 * L := by
      have h1l := List.length_drop (l := out) (i := wq)
      rw [hdrop] at h1l
      rw [List.length_drop (l := sl.map (fun z => z + ak)) (i := j)] at h1l
      have : (sl.map (fun z => z + ak)).length = L := hMlen
      omega
    have hjM : j < (sl.map (fun z => z + ak)).length := by omega
    have hjl : j < sl.length := by omega
    have hjm : j < (sl.map (fun z => z + ak)).length := by
      simp [List.length_map, hsL]
      omega
    have hdrop1 : out.drop (wq + 1) = (sl.map (fun z => z + ak)).drop (j + 1) := by
      rw [dropSucc, hdrop, dropCons hjM, getD_map_add sl ak j hjl]
      simp
    have hwqo : wq < out.length := by omega
    have hwq2L : wq < 2 * L := by omega
    have htake1 : out.take (wq + 1) = (arrL (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) d (2 * L)).take (wq + 1) := by
      rw [hA7, arrL_take_up hwq2L, hA4, ← htake, takeSucc hwqo]
      congr 1
      rw [← getDDrop, hdrop, dropCons hjM, getD_map_add sl ak j hjl]
      rfl
    -- register facts on T7
    have e13g : (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 13 = j + 1 := by
      rw [up_ne (show (13:Nat) ≠ 14 by omega), up_eq]
    have e14g : (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 14 = wq + 1 := up_eq _ _ _
    have e11g : (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 11 = L := by rw [up_ne (show (11:Nat) ≠ 14 by omega), up_ne (show (11:Nat) ≠ 13 by omega), up_ne (show (11:Nat) ≠ d + wq by omega), up_ne (show (11:Nat) ≠ 20 by omega), up_ne (show (11:Nat) ≠ 16 by omega), up_ne (show (11:Nat) ≠ 16 by omega), up_ne (show (11:Nat) ≠ 21 by omega), hf11]
    have e12g : (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 12 = L := by
      rw [up_ne (show (12:Nat) ≠ 14 by omega), up_ne (show (12:Nat) ≠ 13 by omega), up_ne (show (12:Nat) ≠ d + wq by omega), up_ne (show (12:Nat) ≠ 20 by omega), up_ne (show (12:Nat) ≠ 16 by omega), up_ne (show (12:Nat) ≠ 16 by omega), up_ne (show (12:Nat) ≠ 21 by omega), hf12]
    have e17g : (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 17 = ak := by
      rw [up_ne (show (17:Nat) ≠ 14 by omega), up_ne (show (17:Nat) ≠ 13 by omega), up_ne (show (17:Nat) ≠ d + wq by omega), up_ne (show (17:Nat) ≠ 20 by omega), up_ne (show (17:Nat) ≠ 16 by omega), up_ne (show (17:Nat) ≠ 16 by omega), up_ne (show (17:Nat) ≠ 21 by omega), hf17]
    have e18g : (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 18 = b := by rw [up_ne (show (18:Nat) ≠ 14 by omega), up_ne (show (18:Nat) ≠ 13 by omega), up_ne (show (18:Nat) ≠ d + wq by omega), up_ne (show (18:Nat) ≠ 20 by omega), up_ne (show (18:Nat) ≠ 16 by omega), up_ne (show (18:Nat) ≠ 16 by omega), up_ne (show (18:Nat) ≠ 21 by omega), hf18]
    have e19g : (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 19 = d := by rw [up_ne (show (19:Nat) ≠ 14 by omega), up_ne (show (19:Nat) ≠ 13 by omega), up_ne (show (19:Nat) ≠ d + wq by omega), up_ne (show (19:Nat) ≠ 20 by omega), up_ne (show (19:Nat) ≠ 16 by omega), up_ne (show (19:Nat) ≠ 16 by omega), up_ne (show (19:Nat) ≠ 21 by omega), hf19]
    have e1g : (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 1 = 1 := by rw [up_ne (show (1:Nat) ≠ 14 by omega), up_ne (show (1:Nat) ≠ 13 by omega), up_ne (show (1:Nat) ≠ d + wq by omega), up_ne (show (1:Nat) ≠ 20 by omega), up_ne (show (1:Nat) ≠ 16 by omega), up_ne (show (1:Nat) ≠ 16 by omega), up_ne (show (1:Nat) ≠ 21 by omega), h1]
    have e2g : (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 2 = 0 := by rw [up_ne (show (2:Nat) ≠ 14 by omega), up_ne (show (2:Nat) ≠ 13 by omega), up_ne (show (2:Nat) ≠ d + wq by omega), up_ne (show (2:Nat) ≠ 20 by omega), up_ne (show (2:Nat) ≠ 16 by omega), up_ne (show (2:Nat) ≠ 16 by omega), up_ne (show (2:Nat) ≠ 21 by omega), h2]
    have hdisj2 : ∀ q, q < L → b + q ≠ d + wq := by
      intro q hq
      exact Ne.symm (hdisj wq q (by omega) hq)
    have esrcg : ∀ q, q < L → (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) (b + q) = sl.getD q 0 := by
      intro q hq
      rw [up_ne (show b + q ≠ 14 by omega), up_ne (show b + q ≠ 13 by omega),
        up_ne (hdisj2 q hq), up_ne (show b + q ≠ 20 by omega),
        up_ne (show b + q ≠ 16 by omega), up_ne (show b + q ≠ 16 by omega),
        up_ne (show b + q ≠ 21 by omega)]
      exact hsrc q hq
    -- the seven body steps with inline normalization
    have hsteps : exec prog ρ S 133 r (memOf w f)
        = exec prog ρ (S - 6) 139 r (memOf w (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1))) := by
      rw [exec_add_step (by omega)
          (show prog.getD 133 Instr.reject = Instr.add 21 18 13 by rfl),
          show f 18 + f 13 = b + j from by rw [hf18, hf13],
        exec_load_step (by omega)
          (show prog.getD 134 Instr.reject = Instr.load 16 21 by rfl) fi1,
          up_eq, up_ne (show b + j ≠ 21 by omega), hsrc j hjL,
        exec_add_step (by omega)
          (show prog.getD 135 Instr.reject = Instr.add 16 16 17 by rfl),
          show (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 + (up (up f 21 (b + j)) 16 (sl.getD j 0)) 17 = sl.getD j 0 + ak from by
            rw [up_eq, up_ne (show (17:Nat) ≠ 16 by omega),
              up_ne (show (17:Nat) ≠ 21 by omega), hf17],
        exec_add_step (by omega)
          (show prog.getD 136 Instr.reject = Instr.add 20 19 14 by rfl),
          show (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 19 + (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 14 = d + wq from by
            rw [up_ne (show (19:Nat) ≠ 16 by omega),
              up_ne (show (19:Nat) ≠ 16 by omega),
              up_ne (show (19:Nat) ≠ 21 by omega), hf19,
              up_ne (show (14:Nat) ≠ 16 by omega),
              up_ne (show (14:Nat) ≠ 16 by omega),
              up_ne (show (14:Nat) ≠ 21 by omega), hf14],
        exec_store_step (by omega)
          (show prog.getD 137 Instr.reject = Instr.store 20 16 by rfl) fi4,
          up_eq,
          show (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) 16 = sl.getD j 0 + ak from by
            rw [up_ne (show (16:Nat) ≠ 20 by omega), up_eq],
        exec_add_step (by omega)
          (show prog.getD 138 Instr.reject = Instr.add 13 13 1 by rfl),
          show (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 + (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 1 = j + 1 from by
            rw [up_ne (show (13:Nat) ≠ d + wq by omega),
              up_ne (show (13:Nat) ≠ 20 by omega),
              up_ne (show (13:Nat) ≠ 16 by omega),
              up_ne (show (13:Nat) ≠ 16 by omega),
              up_ne (show (13:Nat) ≠ 21 by omega), hf13,
              up_ne (show (1:Nat) ≠ d + wq by omega),
              up_ne (show (1:Nat) ≠ 20 by omega),
              up_ne (show (1:Nat) ≠ 16 by omega),
              up_ne (show (1:Nat) ≠ 16 by omega),
              up_ne (show (1:Nat) ≠ 21 by omega), h1]]
      simp only [Nat.sub_sub, Nat.reduceAdd]
    by_cases hnext : j + 1 < L
    · have h140 : (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 13 < (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 11 := by rw [e13g, e11g]; exact hnext
      have hS8 : S - 6 - 1 - 1 = S - 8 := by omega
      rw [hsteps, exec_add_step (by omega)
          (show prog.getD 139 Instr.reject = Instr.add 14 14 1 by rfl),
          show (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 + (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 1 = wq + 1 from by
            rw [up_ne (show (14:Nat) ≠ 13 by omega),
              up_ne (show (14:Nat) ≠ d + wq by omega),
              up_ne (show (14:Nat) ≠ 20 by omega),
              up_ne (show (14:Nat) ≠ 16 by omega),
              up_ne (show (14:Nat) ≠ 16 by omega),
              up_ne (show (14:Nat) ≠ 21 by omega), hf14,
              up_ne (show (1:Nat) ≠ 13 by omega),
              up_ne (show (1:Nat) ≠ d + wq by omega),
              up_ne (show (1:Nat) ≠ 20 by omega),
              up_ne (show (1:Nat) ≠ 16 by omega),
              up_ne (show (1:Nat) ≠ 16 by omega),
              up_ne (show (1:Nat) ≠ 21 by omega), h1],
          exec_blt_lt_step (by omega)
          (show prog.getD 140 Instr.reject = Instr.blt 13 11 133 by rfl) fi7
          h140, hS8]
      have hwj2 : wq + 1 = L + (j + 1) := by omega
      have hN2 : L - (j + 1) ≤ N := by omega
      have hS2 : 8 * N + 8 ≤ S - 8 := by omega
      obtain ⟨c2, f2, hc2, hex2, harr2, h122, h132, h142, hfit2, hpres2⟩ :=
        ih L b d ak sl out (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) (j + 1) (wq + 1) (S - 8) r hsL hnext hwj2
          e12g e13g e14g e11g e17g e18g e19g e1g e2g esrcg hvfit htake1 hdrop1
          fi7 hbL hdL h2L hb33 hd33 hdisj hN2 hS2
      refine ⟨8 + c2, f2, by omega, ?_, harr2, h122, h132, h142, hfit2, ?_⟩
      · rw [hex2]
        have hS9 : S - 8 - c2 = S - (8 + c2) := by omega
        rw [hS9]
      have q1 : Pres (MReg d L) f (up f 21 (b + j)) := pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
      have q2 : Pres (MReg d L) (up f 21 (b + j)) (up (up f 21 (b + j)) 16 (sl.getD j 0)) := pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      have q3 : Pres (MReg d L) (up (up f 21 (b + j)) 16 (sl.getD j 0)) (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) := pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      have q4 : Pres (MReg d L) (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) := pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      have q5 : Pres (MReg d L) (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) := pres_up (MReg_dst (by omega) (by omega))
      have q6 : Pres (MReg d L) (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) := pres_up (Or.inr (Or.inl rfl))
      have q7 : Pres (MReg d L) (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) := pres_up (Or.inr (Or.inr (Or.inl rfl)))
      exact pres_trans q1 (pres_trans q2 (pres_trans q3 (pres_trans q4
        (pres_trans q5 (pres_trans q6 (pres_trans q7 hpres2))))))
    · have h140 : ¬ (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 13 < (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 11 := by rw [e13g, e11g]; omega
      have hrw2 : exec prog ρ S 133 r (memOf w f)
          = exec prog ρ (S - 8) 141 r (memOf w (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1))) := by
        rw [hsteps,
          exec_add_step (by omega)
            (show prog.getD 139 Instr.reject = Instr.add 14 14 1 by rfl),
          show (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 + (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 1 = wq + 1 from by
            rw [up_ne (show (14:Nat) ≠ 13 by omega),
              up_ne (show (14:Nat) ≠ d + wq by omega),
              up_ne (show (14:Nat) ≠ 20 by omega),
              up_ne (show (14:Nat) ≠ 16 by omega),
              up_ne (show (14:Nat) ≠ 16 by omega),
              up_ne (show (14:Nat) ≠ 21 by omega), hf14,
              up_ne (show (1:Nat) ≠ 13 by omega),
              up_ne (show (1:Nat) ≠ d + wq by omega),
              up_ne (show (1:Nat) ≠ 20 by omega),
              up_ne (show (1:Nat) ≠ 16 by omega),
              up_ne (show (1:Nat) ≠ 16 by omega),
              up_ne (show (1:Nat) ≠ 21 by omega), h1],
          exec_blt_ge_step (by omega)
            (show prog.getD 140 Instr.reject = Instr.blt 13 11 133 by rfl) fi7 h140]
        simp only [Nat.sub_sub, Nat.reduceAdd]
      have hfull : arrL (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) d (2 * L) = out := by
        have hq2 : wq + 1 = 2 * L := by omega
        rw [hq2] at htake1
        have hto := takeAll (l := out) (n := 2 * L) (by omega)
        have hla : (arrL (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) d (2 * L)).length = 2 * L := by simp [arrL]
        have hta := takeAll (l := arrL (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) d (2 * L)) (n := 2 * L) (by omega)
        rw [← hta, ← hto, htake1, hq2]
      refine ⟨8, (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)), by omega, hrw2, hfull, e12g, by rw [e13g]; omega,
        by rw [e14g]; omega, fi7, ?_⟩
      have q1 : Pres (MReg d L) f (up f 21 (b + j)) := pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
      have q2 : Pres (MReg d L) (up f 21 (b + j)) (up (up f 21 (b + j)) 16 (sl.getD j 0)) := pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      have q3 : Pres (MReg d L) (up (up f 21 (b + j)) 16 (sl.getD j 0)) (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) := pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      have q4 : Pres (MReg d L) (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) := pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      have q5 : Pres (MReg d L) (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) := pres_up (MReg_dst (by omega) (by omega))
      have q6 : Pres (MReg d L) (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) := pres_up (Or.inr (Or.inl rfl))
      have q7 : Pres (MReg d L) (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) := pres_up (Or.inr (Or.inr (Or.inl rfl)))
      exact pres_trans q1 (pres_trans q2 (pres_trans q3 (pres_trans q4
        (pres_trans q5 (pres_trans q6 (pres_up (Or.inr (Or.inr (Or.inl rfl)))))))))

/-- Length of a merge, by total-length induction (the `b < a` branch
recurses with `a :: l'` unchanged, so structure-on-`l` induction fails). -/
theorem mmerge_length_aux : ∀ (N : Nat) (l r : List Nat),
    l.length + r.length ≤ N → (mmerge l r).length = l.length + r.length := by
  intro N
  induction N with
  | zero =>
    intro l r hlen
    cases l with
    | nil => simp [mmerge]
    | cons a l' => exact absurd hlen (by simp only [List.length_cons]; omega)
  | succ N ih =>
    intro l r hlen
    cases l with
    | nil => simp [mmerge]
    | cons a l' =>
      cases r with
      | nil => simp [mmerge]
      | cons b r' =>
        rw [mmerge]
        by_cases h : b < a
        · rw [if_pos h]
          have ih2 := ih (a :: l') r' (by simp only [List.length_cons] at hlen ⊢; omega)
          rw [List.length_cons, ih2]
          simp only [List.length_cons]
          omega
        · rw [if_neg h]
          have ih2 := ih l' (b :: r') (by simp only [List.length_cons] at hlen ⊢; omega)
          rw [List.length_cons, ih2]
          simp only [List.length_cons]
          omega

theorem mmerge_length (l r : List Nat) : (mmerge l r).length = l.length + r.length :=
  mmerge_length_aux (l.length + r.length) l r (Nat.le_refl _)

/-- `drop` past the end is empty. -/
theorem dropNil {l : List Nat} {n : Nat} (h : l.length ≤ n) : l.drop n = [] := by
  cases hll : l.drop n with
  | nil => rfl
  | cons x r =>
      have hlen := List.length_drop (l := l) (i := n)
      rw [hll] at hlen
      have h0 : (x :: r).length = r.length + 1 := rfl
      omega

theorem mmerge_nil_l (l : List Nat) : mmerge [] l = l := by
  cases l <;> simp [mmerge]
--
/-! ## §5. The merge loop (pc 103 → 141). -/
/-- Merge loop: both-sides iterations until one side exhausts, then the
matching drain finishes the array.  `wq = i + j` throughout; each
both-sides step is 14 instructions, consuming `mmerge_stepL/J` for the
take/drop invariants. -/
theorem merge_exec {w : Nat} (ρ : Nat → BitVec w) :
    ∀ (N L b d ak : Nat) (sl out : List Nat) (f : Nat → Nat) (i j wq S r : Nat),
    sl.length = L →
    i ≤ L → j ≤ L → wq = i + j → f 12 = i → f 13 = j → f 14 = wq → f 11 = L →
    f 17 = ak → f 18 = b → f 19 = d → f 1 = 1 → f 2 = 0 →
    (∀ q, q < L → f (b + q) = sl.getD q 0) →
    (∀ v ∈ sl, v + ak < 2 ^ w) →
    (out.take wq = (arrL f d (2 * L)).take wq) →
    (out.drop wq = mmerge (sl.drop i) ((sl.map (fun z => z + ak)).drop j)) →
    out = mmerge sl (sl.map (fun z => z + ak)) →
    (∀ q, f q < 2 ^ w) → b + L < 2 ^ w → d + 2 * L < 2 ^ w → 2 * L < 2 ^ w →
    33 ≤ b → 33 ≤ d → (∀ p q, p < 2 * L → q < L → d + p ≠ b + q) →
    (L - i) + (L - j) ≤ N → 22 * N + 12 ≤ S →
    ∃ c f', c ≤ 22 * N + 12 ∧
      exec prog ρ S 103 r (memOf w f) = exec prog ρ (S - c) 141 r (memOf w f') ∧
      arrL f' d (2 * L) = out ∧ f' 12 = L ∧ f' 14 = 2 * L ∧
      (∀ q, f' q < 2 ^ w) ∧ Pres (MReg d L) f f' := by
  intro N
  induction N with
  | zero =>
    intro L b d ak sl out f i j wq S r hsL hiLe hjLe hwq hf12 hf13 hf14 hf11 hf17 hf18 hf19 h1 h2 hsrc hvfit htake hdrop hout hfit hbL hdL h2L hb33 hd33 hdisj hfuel hhor
    have hiL : i = L := by omega
    have hjL : j = L := by omega
    have hw2 : wq = 2 * L := by omega
    have hlen : out.length = 2 * L := by
      rw [hout, mmerge_length, List.length_map, hsL]
      omega
    have hfull : arrL f d (2 * L) = out := by
      rw [hw2] at htake
      have hto := takeAll (l := out) (n := 2 * L) (by omega)
      have hla : (arrL f d (2 * L)).length = 2 * L := by simp [arrL]
      have hta := takeAll (l := arrL f d (2 * L)) (n := 2 * L) (by omega)
      rw [← hta, ← hto, htake]
    refine ⟨4, f, by omega, ?_, hfull, by omega, by omega, hfit, ?_⟩
    · rw [exec_blt_ge_step (by omega)
          (show prog.getD 103 Instr.reject = Instr.blt 13 11 105 by rfl) hfit
          (by rw [hf13, hf11]; omega),
        exec_blt_lt_step (by omega)
          (show prog.getD 104 Instr.reject = Instr.blt 2 1 123 by rfl) hfit
          (by rw [h2, h1]; omega),
        exec_blt_ge_step (by omega)
          (show prog.getD 123 Instr.reject = Instr.blt 12 11 125 by rfl) hfit
          (by rw [hf12, hf11]; omega),
        exec_blt_lt_step (by omega)
          (show prog.getD 124 Instr.reject = Instr.blt 2 1 141 by rfl) hfit
          (by rw [h2, h1]; omega)]
      simp only [Nat.sub_sub, Nat.reduceAdd]
    · intro x hx
      rfl
  | succ N ih =>
    intro L b d ak sl out f i j wq S r hsL hiLe hjLe hwq hf12 hf13 hf14 hf11 hf17 hf18 hf19 h1 h2 hsrc hvfit htake hdrop hout hfit hbL hdL h2L hb33 hd33 hdisj hfuel hhor
    have hMlen : (sl.map (fun z => z + ak)).length = L := by simp [List.length_map, hsL]
    by_cases hj : j < L
    · by_cases hi : i < L
      ·         -- both-sides merge iteration
        have hjl : j < sl.length := by omega
        have fi1 : ∀ q, (up f 20 (b + i)) q < 2 ^ w := up_fit hfit (by have := hbL; omega)
        have fi2 : ∀ q, (up (up f 20 (b + i)) 15 (sl.getD i 0)) q < 2 ^ w := up_fit fi1 (by have := hvfit _ (mem_getD (i := i) (by omega)); omega)
        have fi3 : ∀ q, (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) q < 2 ^ w := up_fit fi2 (by have := hbL; omega)
        have fi4 : ∀ q, (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) q < 2 ^ w := up_fit fi3 (by have := hvfit _ (mem_getD (i := j) (by omega)); omega)
        have hvj : sl.getD j 0 + ak < 2 ^ w := hvfit _ (mem_getD (i := j) (by omega))
        have fi5 : ∀ q, (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) q < 2 ^ w := up_fit fi4 hvj
        have fi6 : ∀ q, (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) q < 2 ^ w := up_fit fi5 (by have := hdL; omega)
        have fi7 : ∀ q, (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) q < 2 ^ w := up_fit fi6 hvj
        have fi8 : ∀ q, (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) q < 2 ^ w := up_fit fi7 (by have := h2L; omega)
        have fi9 : ∀ q, (up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) q < 2 ^ w := up_fit fi8 (by have := h2L; omega)
        have hvi : sl.getD i 0 < 2 ^ w := by have := hvfit _ (mem_getD (i := i) (by omega)); omega
        have fi7U : ∀ q, (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) q < 2 ^ w := up_fit fi6 hvi
        have fi8U : ∀ q, (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) q < 2 ^ w := up_fit fi7U (by have := h2L; omega)
        have fi9U : ∀ q, (up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) q < 2 ^ w := up_fit fi8U (by have := h2L; omega)
        have e15_5 : up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak) 15 = sl.getD i 0 := by
          rw [up_ne (show (15:Nat) ≠ (16 : Nat) by omega), up_ne (show (15:Nat) ≠ (16 : Nat) by omega), up_ne (show (15:Nat) ≠ (21 : Nat) by omega), up_eq]
        have e16_5 : up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak) 16 = sl.getD j 0 + ak := up_eq _ _ _
        have hlen : out.length = 2 * L := by
          rw [hout, mmerge_length, List.length_map, hsL]
          omega
        have hwqo : wq < out.length := by rw [hlen]; omega
        have hwq2L : wq < 2 * L := by omega
        have hB : (mmerge sl (sl.map (fun z => z + ak))).drop (i + j)
            = mmerge (sl.drop i) ((sl.map (fun z => z + ak)).drop j) := by
          rw [← hwq, ← hout]
          exact hdrop
        by_cases hcmp : sl.getD j 0 + ak < sl.getD i 0
        · -- LTAKEJ
          have hcmpJ : (sl.map (fun z => z + ak)).getD j 0 < sl.getD i 0 := by
            rw [getD_map_add sl ak j hjl]
            exact hcmp
          have hstep := mmerge_stepJ sl (sl.map (fun z => z + ak)) i j
              (by omega) (by omega) hcmpJ hB
          have houtwq : out.getD wq 0 = sl.getD j 0 + ak := by
            rw [hout, hwq, hstep.1, getD_map_add sl ak j hjl]
          have hdrop1 : out.drop (wq + 1)
              = mmerge (sl.drop i) ((sl.map (fun z => z + ak)).drop (j + 1)) := by
            rw [hout, show wq + 1 = i + j + 1 from by omega, hstep.2]
          have hA9 : arrL (up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) d (2 * L) = arrL (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) d (2 * L) := by
            rw [show arrL (up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) d (2 * L) = arrL (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) d (2 * L) from arrL_up_out (fun q _ => show (14:Nat) ≠ d + q by omega), show arrL (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) d (2 * L) = arrL (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) d (2 * L) from arrL_up_out (fun q _ => show (13:Nat) ≠ d + q by omega)]
          have hA6 : arrL (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) d (2 * L) = arrL f d (2 * L) := by
            rw [show arrL (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) d (2 * L) = arrL (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) d (2 * L) from arrL_up_out (fun q _ => show (20:Nat) ≠ d + q by omega), show arrL (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) d (2 * L) = arrL (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) d (2 * L) from arrL_up_out (fun q _ => show (16:Nat) ≠ d + q by omega), show arrL (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) d (2 * L) = arrL (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) d (2 * L) from arrL_up_out (fun q _ => show (16:Nat) ≠ d + q by omega), show arrL (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) d (2 * L) = arrL (up (up f 20 (b + i)) 15 (sl.getD i 0)) d (2 * L) from arrL_up_out (fun q _ => show (21:Nat) ≠ d + q by omega), show arrL (up (up f 20 (b + i)) 15 (sl.getD i 0)) d (2 * L) = arrL (up f 20 (b + i)) d (2 * L) from arrL_up_out (fun q _ => show (15:Nat) ≠ d + q by omega), show arrL (up f 20 (b + i)) d (2 * L) = arrL (f) d (2 * L) from arrL_up_out (fun q _ => show (20:Nat) ≠ d + q by omega)]
          have htake1 : out.take (wq + 1) = (arrL (up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) d (2 * L)).take (wq + 1) := by
            rw [hA9, arrL_take_up hwq2L, hA6, ← htake, takeSucc hwqo, houtwq]
          have e1_8 : up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1) 1 = 1 := by
            rw [up_ne (show (1:Nat) ≠ (13 : Nat) by omega), up_ne (show (1:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (21 : Nat) by omega), up_ne (show (1:Nat) ≠ (15 : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), h1]
          have e2_8 : up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1) 2 = 0 := by
            rw [up_ne (show (2:Nat) ≠ (13 : Nat) by omega), up_ne (show (2:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (2:Nat) ≠ (20 : Nat) by omega), up_ne (show (2:Nat) ≠ (16 : Nat) by omega), up_ne (show (2:Nat) ≠ (16 : Nat) by omega), up_ne (show (2:Nat) ≠ (21 : Nat) by omega), up_ne (show (2:Nat) ≠ (15 : Nat) by omega), up_ne (show (2:Nat) ≠ (20 : Nat) by omega), h2]
          have e12_9 : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1) 12 = i := by
            rw [up_ne (show (12:Nat) ≠ (14 : Nat) by omega), up_ne (show (12:Nat) ≠ (13 : Nat) by omega), up_ne (show (12:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (12:Nat) ≠ (20 : Nat) by omega), up_ne (show (12:Nat) ≠ (16 : Nat) by omega), up_ne (show (12:Nat) ≠ (16 : Nat) by omega), up_ne (show (12:Nat) ≠ (21 : Nat) by omega), up_ne (show (12:Nat) ≠ (15 : Nat) by omega), up_ne (show (12:Nat) ≠ (20 : Nat) by omega), hf12]
          have e13_9 : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1) 13 = j + 1 := by
            rw [up_ne (show (13:Nat) ≠ (14 : Nat) by omega), up_eq]
          have e14_9 : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1) 14 = wq + 1 := by
            rw [up_eq]
          have e11_9 : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1) 11 = L := by
            rw [up_ne (show (11:Nat) ≠ (14 : Nat) by omega), up_ne (show (11:Nat) ≠ (13 : Nat) by omega), up_ne (show (11:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (11:Nat) ≠ (20 : Nat) by omega), up_ne (show (11:Nat) ≠ (16 : Nat) by omega), up_ne (show (11:Nat) ≠ (16 : Nat) by omega), up_ne (show (11:Nat) ≠ (21 : Nat) by omega), up_ne (show (11:Nat) ≠ (15 : Nat) by omega), up_ne (show (11:Nat) ≠ (20 : Nat) by omega), hf11]
          have e17_9 : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1) 17 = ak := by
            rw [up_ne (show (17:Nat) ≠ (14 : Nat) by omega), up_ne (show (17:Nat) ≠ (13 : Nat) by omega), up_ne (show (17:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (17:Nat) ≠ (20 : Nat) by omega), up_ne (show (17:Nat) ≠ (16 : Nat) by omega), up_ne (show (17:Nat) ≠ (16 : Nat) by omega), up_ne (show (17:Nat) ≠ (21 : Nat) by omega), up_ne (show (17:Nat) ≠ (15 : Nat) by omega), up_ne (show (17:Nat) ≠ (20 : Nat) by omega), hf17]
          have e18_9 : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1) 18 = b := by
            rw [up_ne (show (18:Nat) ≠ (14 : Nat) by omega), up_ne (show (18:Nat) ≠ (13 : Nat) by omega), up_ne (show (18:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (18:Nat) ≠ (20 : Nat) by omega), up_ne (show (18:Nat) ≠ (16 : Nat) by omega), up_ne (show (18:Nat) ≠ (16 : Nat) by omega), up_ne (show (18:Nat) ≠ (21 : Nat) by omega), up_ne (show (18:Nat) ≠ (15 : Nat) by omega), up_ne (show (18:Nat) ≠ (20 : Nat) by omega), hf18]
          have e19_9 : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1) 19 = d := by
            rw [up_ne (show (19:Nat) ≠ (14 : Nat) by omega), up_ne (show (19:Nat) ≠ (13 : Nat) by omega), up_ne (show (19:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (19:Nat) ≠ (20 : Nat) by omega), up_ne (show (19:Nat) ≠ (16 : Nat) by omega), up_ne (show (19:Nat) ≠ (16 : Nat) by omega), up_ne (show (19:Nat) ≠ (21 : Nat) by omega), up_ne (show (19:Nat) ≠ (15 : Nat) by omega), up_ne (show (19:Nat) ≠ (20 : Nat) by omega), hf19]
          have e1_9 : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1) 1 = 1 := by
            rw [up_ne (show (1:Nat) ≠ (14 : Nat) by omega), up_ne (show (1:Nat) ≠ (13 : Nat) by omega), up_ne (show (1:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (21 : Nat) by omega), up_ne (show (1:Nat) ≠ (15 : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), h1]
          have e2_9 : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1) 2 = 0 := by
            rw [up_ne (show (2:Nat) ≠ (14 : Nat) by omega), up_ne (show (2:Nat) ≠ (13 : Nat) by omega), up_ne (show (2:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (2:Nat) ≠ (20 : Nat) by omega), up_ne (show (2:Nat) ≠ (16 : Nat) by omega), up_ne (show (2:Nat) ≠ (16 : Nat) by omega), up_ne (show (2:Nat) ≠ (21 : Nat) by omega), up_ne (show (2:Nat) ≠ (15 : Nat) by omega), up_ne (show (2:Nat) ≠ (20 : Nat) by omega), h2]
          have esrc_9 : ∀ q, q < L → up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1) (b + q) = sl.getD q 0 := by
            intro q hq
            rw [up_ne (show b + q ≠ (14 : Nat) by omega), up_ne (show b + q ≠ (13 : Nat) by omega), up_ne (Ne.symm (hdisj wq q (by omega) hq)), up_ne (show b + q ≠ (20 : Nat) by omega), up_ne (show b + q ≠ (16 : Nat) by omega), up_ne (show b + q ≠ (16 : Nat) by omega), up_ne (show b + q ≠ (21 : Nat) by omega), up_ne (show b + q ≠ (15 : Nat) by omega), up_ne (show b + q ≠ (20 : Nat) by omega)]
            exact hsrc q hq
          have hwalk : exec prog ρ S 103 r (memOf w f)
              = exec prog ρ (S - 14) 103 r (memOf w (up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1))) := by
            rw [exec_blt_lt_step (by omega) (show prog.getD 103 Instr.reject = Instr.blt 13 11 105 by rfl) hfit (by rw [hf13, hf11]; exact hj),
              exec_blt_lt_step (by omega) (show prog.getD 105 Instr.reject = Instr.blt 12 11 107 by rfl) hfit (by rw [hf12, hf11]; exact hi),
              exec_add_step (by omega) (show prog.getD 107 Instr.reject = Instr.add 20 18 12 by rfl), show f 18 + f 12 = b + i from by rw [hf18, hf12],
              exec_load_step (by omega) (show prog.getD 108 Instr.reject = Instr.load 15 20 by rfl) fi1, up_eq, up_ne (show b + i ≠ 20 by omega), hsrc i hi,
              exec_add_step (by omega) (show prog.getD 109 Instr.reject = Instr.add 21 18 13 by rfl), show up (up f 20 (b + i)) 15 (sl.getD i 0) 18 + up (up f 20 (b + i)) 15 (sl.getD i 0) 13 = b + j from by rw [up_ne (show (18:Nat) ≠ (15 : Nat) by omega), up_ne (show (18:Nat) ≠ (20 : Nat) by omega), hf18, up_ne (show (13:Nat) ≠ (15 : Nat) by omega), up_ne (show (13:Nat) ≠ (20 : Nat) by omega), hf13],
              exec_load_step (by omega) (show prog.getD 110 Instr.reject = Instr.load 16 21 by rfl) fi3, up_eq, up_ne (show b + j ≠ 21 by omega), up_ne (show b + j ≠ (15 : Nat) by omega), up_ne (show b + j ≠ (20 : Nat) by omega), hsrc j hj,
              exec_add_step (by omega) (show prog.getD 111 Instr.reject = Instr.add 16 16 17 by rfl), show up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0) 16 + up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0) 17 = sl.getD j 0 + ak from by rw [up_eq, up_ne (show (17:Nat) ≠ (16 : Nat) by omega), up_ne (show (17:Nat) ≠ (21 : Nat) by omega), up_ne (show (17:Nat) ≠ (15 : Nat) by omega), up_ne (show (17:Nat) ≠ (20 : Nat) by omega), hf17],
              exec_blt_lt_step (by omega) (show prog.getD 112 Instr.reject = Instr.blt 16 15 114 by rfl) fi5 (by rw [e16_5, e15_5]; exact hcmp),
              exec_add_step (by omega) (show prog.getD 114 Instr.reject = Instr.add 20 19 14 by rfl), show up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak) 19 + up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak) 14 = d + wq from by rw [up_ne (show (19:Nat) ≠ (16 : Nat) by omega), up_ne (show (19:Nat) ≠ (16 : Nat) by omega), up_ne (show (19:Nat) ≠ (21 : Nat) by omega), up_ne (show (19:Nat) ≠ (15 : Nat) by omega), up_ne (show (19:Nat) ≠ (20 : Nat) by omega), hf19, up_ne (show (14:Nat) ≠ (16 : Nat) by omega), up_ne (show (14:Nat) ≠ (16 : Nat) by omega), up_ne (show (14:Nat) ≠ (21 : Nat) by omega), up_ne (show (14:Nat) ≠ (15 : Nat) by omega), up_ne (show (14:Nat) ≠ (20 : Nat) by omega), hf14],
              exec_store_step (by omega) (show prog.getD 115 Instr.reject = Instr.store 20 16 by rfl) fi6, up_eq, up_ne (show (16:Nat) ≠ 20 by omega), up_eq,
              exec_add_step (by omega) (show prog.getD 116 Instr.reject = Instr.add 13 13 1 by rfl), show up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak) 13 + up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak) 1 = j + 1 from by rw [up_ne (show (13:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (13:Nat) ≠ (20 : Nat) by omega), up_ne (show (13:Nat) ≠ (16 : Nat) by omega), up_ne (show (13:Nat) ≠ (16 : Nat) by omega), up_ne (show (13:Nat) ≠ (21 : Nat) by omega), up_ne (show (13:Nat) ≠ (15 : Nat) by omega), up_ne (show (13:Nat) ≠ (20 : Nat) by omega), hf13, up_ne (show (1:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (21 : Nat) by omega), up_ne (show (1:Nat) ≠ (15 : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), h1],
              exec_blt_lt_step (by omega) (show prog.getD 117 Instr.reject = Instr.blt 2 1 121 by rfl) fi8 (by rw [e2_8, e1_8]; omega),
              exec_add_step (by omega) (show prog.getD 121 Instr.reject = Instr.add 14 14 1 by rfl), show up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1) 14 + up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1) 1 = wq + 1 from by rw [up_ne (show (14:Nat) ≠ (13 : Nat) by omega), up_ne (show (14:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (14:Nat) ≠ (20 : Nat) by omega), up_ne (show (14:Nat) ≠ (16 : Nat) by omega), up_ne (show (14:Nat) ≠ (16 : Nat) by omega), up_ne (show (14:Nat) ≠ (21 : Nat) by omega), up_ne (show (14:Nat) ≠ (15 : Nat) by omega), up_ne (show (14:Nat) ≠ (20 : Nat) by omega), hf14, up_ne (show (1:Nat) ≠ (13 : Nat) by omega), up_ne (show (1:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (21 : Nat) by omega), up_ne (show (1:Nat) ≠ (15 : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), h1],
              exec_blt_lt_step (by omega) (show prog.getD 122 Instr.reject = Instr.blt 2 1 103 by rfl) fi9 (by rw [e2_9, e1_9]; omega)]
            simp only [Nat.sub_sub, Nat.reduceAdd]
          obtain ⟨c2, f2, hc2, hex2, harr2, h122, h142, hfit2, hpres2⟩ :=
            ih L b d ak sl out (up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) i (j + 1) (wq + 1) (S - 14) r hsL
              (by omega) (by omega) (by omega)
              e12_9 e13_9 e14_9 e11_9 e17_9 e18_9 e19_9 e1_9 e2_9 esrc_9
              hvfit htake1 hdrop1 hout fi9 hbL hdL h2L hb33 hd33 hdisj
              (by omega) (by omega)
          refine ⟨14 + c2, f2, by omega, ?_, harr2, h122, h142, hfit2, ?_⟩
          · rw [hwalk, hex2]
            have hS14 : S - 14 - c2 = S - (14 + c2) := by omega
            rw [hS14]
          · exact pres_trans (pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) (pres_trans (pres_up (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (pres_trans (pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))) (pres_trans (pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (pres_trans (pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (pres_trans (pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) (pres_trans (pres_up (MReg_dst (by omega) (by omega))) (pres_trans (pres_up (Or.inr (Or.inl rfl))) (pres_trans (pres_up (Or.inr (Or.inr (Or.inl rfl)))) (hpres2)))))))))
        · -- LTAKEL
          have hcmpL : ¬ (sl.map (fun z => z + ak)).getD j 0 < sl.getD i 0 := by
            rw [getD_map_add sl ak j hjl]
            exact hcmp
          have hstep := mmerge_stepL sl (sl.map (fun z => z + ak)) i j
              (by omega) (by omega) hcmpL hB
          have houtwq : out.getD wq 0 = sl.getD i 0 := by
            rw [hout, hwq, hstep.1]
          have hdrop1 : out.drop (wq + 1)
              = mmerge (sl.drop (i + 1)) ((sl.map (fun z => z + ak)).drop j) := by
            rw [hout, show wq + 1 = i + j + 1 from by omega, hstep.2]
          have hA9 : arrL (up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) d (2 * L) = arrL (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) d (2 * L) := by
            rw [show arrL (up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) d (2 * L) = arrL (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) d (2 * L) from arrL_up_out (fun q _ => show (14:Nat) ≠ d + q by omega), show arrL (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) d (2 * L) = arrL (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) d (2 * L) from arrL_up_out (fun q _ => show (12:Nat) ≠ d + q by omega)]
          have hA6 : arrL (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) d (2 * L) = arrL f d (2 * L) := by
            rw [show arrL (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) d (2 * L) = arrL (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) d (2 * L) from arrL_up_out (fun q _ => show (20:Nat) ≠ d + q by omega), show arrL (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) d (2 * L) = arrL (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) d (2 * L) from arrL_up_out (fun q _ => show (16:Nat) ≠ d + q by omega), show arrL (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) d (2 * L) = arrL (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) d (2 * L) from arrL_up_out (fun q _ => show (16:Nat) ≠ d + q by omega), show arrL (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) d (2 * L) = arrL (up (up f 20 (b + i)) 15 (sl.getD i 0)) d (2 * L) from arrL_up_out (fun q _ => show (21:Nat) ≠ d + q by omega), show arrL (up (up f 20 (b + i)) 15 (sl.getD i 0)) d (2 * L) = arrL (up f 20 (b + i)) d (2 * L) from arrL_up_out (fun q _ => show (15:Nat) ≠ d + q by omega), show arrL (up f 20 (b + i)) d (2 * L) = arrL (f) d (2 * L) from arrL_up_out (fun q _ => show (20:Nat) ≠ d + q by omega)]
          have htake1 : out.take (wq + 1) = (arrL (up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) d (2 * L)).take (wq + 1) := by
            rw [hA9, arrL_take_up hwq2L, hA6, ← htake, takeSucc hwqo, houtwq]
          have e1_5 : up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak) 1 = 1 := by
            rw [up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (21 : Nat) by omega), up_ne (show (1:Nat) ≠ (15 : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), h1]
          have e2_5 : up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak) 2 = 0 := by
            rw [up_ne (show (2:Nat) ≠ (16 : Nat) by omega), up_ne (show (2:Nat) ≠ (16 : Nat) by omega), up_ne (show (2:Nat) ≠ (21 : Nat) by omega), up_ne (show (2:Nat) ≠ (15 : Nat) by omega), up_ne (show (2:Nat) ≠ (20 : Nat) by omega), h2]
          have e12_9U : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1) 12 = i + 1 := by
            rw [up_ne (show (12:Nat) ≠ (14 : Nat) by omega), up_eq]
          have e13_9U : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1) 13 = j := by
            rw [up_ne (show (13:Nat) ≠ (14 : Nat) by omega), up_ne (show (13:Nat) ≠ (12 : Nat) by omega), up_ne (show (13:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (13:Nat) ≠ (20 : Nat) by omega), up_ne (show (13:Nat) ≠ (16 : Nat) by omega), up_ne (show (13:Nat) ≠ (16 : Nat) by omega), up_ne (show (13:Nat) ≠ (21 : Nat) by omega), up_ne (show (13:Nat) ≠ (15 : Nat) by omega), up_ne (show (13:Nat) ≠ (20 : Nat) by omega), hf13]
          have e14_9U : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1) 14 = wq + 1 := by
            rw [up_eq]
          have e11_9U : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1) 11 = L := by
            rw [up_ne (show (11:Nat) ≠ (14 : Nat) by omega), up_ne (show (11:Nat) ≠ (12 : Nat) by omega), up_ne (show (11:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (11:Nat) ≠ (20 : Nat) by omega), up_ne (show (11:Nat) ≠ (16 : Nat) by omega), up_ne (show (11:Nat) ≠ (16 : Nat) by omega), up_ne (show (11:Nat) ≠ (21 : Nat) by omega), up_ne (show (11:Nat) ≠ (15 : Nat) by omega), up_ne (show (11:Nat) ≠ (20 : Nat) by omega), hf11]
          have e17_9U : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1) 17 = ak := by
            rw [up_ne (show (17:Nat) ≠ (14 : Nat) by omega), up_ne (show (17:Nat) ≠ (12 : Nat) by omega), up_ne (show (17:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (17:Nat) ≠ (20 : Nat) by omega), up_ne (show (17:Nat) ≠ (16 : Nat) by omega), up_ne (show (17:Nat) ≠ (16 : Nat) by omega), up_ne (show (17:Nat) ≠ (21 : Nat) by omega), up_ne (show (17:Nat) ≠ (15 : Nat) by omega), up_ne (show (17:Nat) ≠ (20 : Nat) by omega), hf17]
          have e18_9U : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1) 18 = b := by
            rw [up_ne (show (18:Nat) ≠ (14 : Nat) by omega), up_ne (show (18:Nat) ≠ (12 : Nat) by omega), up_ne (show (18:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (18:Nat) ≠ (20 : Nat) by omega), up_ne (show (18:Nat) ≠ (16 : Nat) by omega), up_ne (show (18:Nat) ≠ (16 : Nat) by omega), up_ne (show (18:Nat) ≠ (21 : Nat) by omega), up_ne (show (18:Nat) ≠ (15 : Nat) by omega), up_ne (show (18:Nat) ≠ (20 : Nat) by omega), hf18]
          have e19_9U : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1) 19 = d := by
            rw [up_ne (show (19:Nat) ≠ (14 : Nat) by omega), up_ne (show (19:Nat) ≠ (12 : Nat) by omega), up_ne (show (19:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (19:Nat) ≠ (20 : Nat) by omega), up_ne (show (19:Nat) ≠ (16 : Nat) by omega), up_ne (show (19:Nat) ≠ (16 : Nat) by omega), up_ne (show (19:Nat) ≠ (21 : Nat) by omega), up_ne (show (19:Nat) ≠ (15 : Nat) by omega), up_ne (show (19:Nat) ≠ (20 : Nat) by omega), hf19]
          have e1_9U : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1) 1 = 1 := by
            rw [up_ne (show (1:Nat) ≠ (14 : Nat) by omega), up_ne (show (1:Nat) ≠ (12 : Nat) by omega), up_ne (show (1:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (21 : Nat) by omega), up_ne (show (1:Nat) ≠ (15 : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), h1]
          have e2_9U : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1) 2 = 0 := by
            rw [up_ne (show (2:Nat) ≠ (14 : Nat) by omega), up_ne (show (2:Nat) ≠ (12 : Nat) by omega), up_ne (show (2:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (2:Nat) ≠ (20 : Nat) by omega), up_ne (show (2:Nat) ≠ (16 : Nat) by omega), up_ne (show (2:Nat) ≠ (16 : Nat) by omega), up_ne (show (2:Nat) ≠ (21 : Nat) by omega), up_ne (show (2:Nat) ≠ (15 : Nat) by omega), up_ne (show (2:Nat) ≠ (20 : Nat) by omega), h2]
          have esrc_9U : ∀ q, q < L → up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1) (b + q) = sl.getD q 0 := by
            intro q hq
            rw [up_ne (show b + q ≠ (14 : Nat) by omega), up_ne (show b + q ≠ (12 : Nat) by omega), up_ne (Ne.symm (hdisj wq q (by omega) hq)), up_ne (show b + q ≠ (20 : Nat) by omega), up_ne (show b + q ≠ (16 : Nat) by omega), up_ne (show b + q ≠ (16 : Nat) by omega), up_ne (show b + q ≠ (21 : Nat) by omega), up_ne (show b + q ≠ (15 : Nat) by omega), up_ne (show b + q ≠ (20 : Nat) by omega)]
            exact hsrc q hq
          have hwalk : exec prog ρ S 103 r (memOf w f)
              = exec prog ρ (S - 14) 103 r (memOf w (up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1))) := by
            rw [exec_blt_lt_step (by omega) (show prog.getD 103 Instr.reject = Instr.blt 13 11 105 by rfl) hfit (by rw [hf13, hf11]; exact hj),
              exec_blt_lt_step (by omega) (show prog.getD 105 Instr.reject = Instr.blt 12 11 107 by rfl) hfit (by rw [hf12, hf11]; exact hi),
              exec_add_step (by omega) (show prog.getD 107 Instr.reject = Instr.add 20 18 12 by rfl), show f 18 + f 12 = b + i from by rw [hf18, hf12],
              exec_load_step (by omega) (show prog.getD 108 Instr.reject = Instr.load 15 20 by rfl) fi1, up_eq, up_ne (show b + i ≠ 20 by omega), hsrc i hi,
              exec_add_step (by omega) (show prog.getD 109 Instr.reject = Instr.add 21 18 13 by rfl), show up (up f 20 (b + i)) 15 (sl.getD i 0) 18 + up (up f 20 (b + i)) 15 (sl.getD i 0) 13 = b + j from by rw [up_ne (show (18:Nat) ≠ (15 : Nat) by omega), up_ne (show (18:Nat) ≠ (20 : Nat) by omega), hf18, up_ne (show (13:Nat) ≠ (15 : Nat) by omega), up_ne (show (13:Nat) ≠ (20 : Nat) by omega), hf13],
              exec_load_step (by omega) (show prog.getD 110 Instr.reject = Instr.load 16 21 by rfl) fi3, up_eq, up_ne (show b + j ≠ 21 by omega), up_ne (show b + j ≠ (15 : Nat) by omega), up_ne (show b + j ≠ (20 : Nat) by omega), hsrc j hj,
              exec_add_step (by omega) (show prog.getD 111 Instr.reject = Instr.add 16 16 17 by rfl), show up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0) 16 + up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0) 17 = sl.getD j 0 + ak from by rw [up_eq, up_ne (show (17:Nat) ≠ (16 : Nat) by omega), up_ne (show (17:Nat) ≠ (21 : Nat) by omega), up_ne (show (17:Nat) ≠ (15 : Nat) by omega), up_ne (show (17:Nat) ≠ (20 : Nat) by omega), hf17],
              exec_blt_ge_step (by omega) (show prog.getD 112 Instr.reject = Instr.blt 16 15 114 by rfl) fi5 (by rw [e16_5, e15_5]; exact hcmp),
              exec_blt_lt_step (by omega) (show prog.getD 113 Instr.reject = Instr.blt 2 1 118 by rfl) fi5 (by rw [e2_5, e1_5]; omega),
              exec_add_step (by omega) (show prog.getD 118 Instr.reject = Instr.add 20 19 14 by rfl), show up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak) 19 + up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak) 14 = d + wq from by rw [up_ne (show (19:Nat) ≠ (16 : Nat) by omega), up_ne (show (19:Nat) ≠ (16 : Nat) by omega), up_ne (show (19:Nat) ≠ (21 : Nat) by omega), up_ne (show (19:Nat) ≠ (15 : Nat) by omega), up_ne (show (19:Nat) ≠ (20 : Nat) by omega), hf19, up_ne (show (14:Nat) ≠ (16 : Nat) by omega), up_ne (show (14:Nat) ≠ (16 : Nat) by omega), up_ne (show (14:Nat) ≠ (21 : Nat) by omega), up_ne (show (14:Nat) ≠ (15 : Nat) by omega), up_ne (show (14:Nat) ≠ (20 : Nat) by omega), hf14],
              exec_store_step (by omega) (show prog.getD 119 Instr.reject = Instr.store 20 15 by rfl) fi6, up_eq, up_ne (show (15:Nat) ≠ 20 by omega), e15_5,
              exec_add_step (by omega) (show prog.getD 120 Instr.reject = Instr.add 12 12 1 by rfl), show up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0) 12 + up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0) 1 = i + 1 from by rw [up_ne (show (12:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (12:Nat) ≠ (20 : Nat) by omega), up_ne (show (12:Nat) ≠ (16 : Nat) by omega), up_ne (show (12:Nat) ≠ (16 : Nat) by omega), up_ne (show (12:Nat) ≠ (21 : Nat) by omega), up_ne (show (12:Nat) ≠ (15 : Nat) by omega), up_ne (show (12:Nat) ≠ (20 : Nat) by omega), hf12, up_ne (show (1:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (21 : Nat) by omega), up_ne (show (1:Nat) ≠ (15 : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), h1],
              exec_add_step (by omega) (show prog.getD 121 Instr.reject = Instr.add 14 14 1 by rfl), show up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1) 14 + up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1) 1 = wq + 1 from by rw [up_ne (show (14:Nat) ≠ (12 : Nat) by omega), up_ne (show (14:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (14:Nat) ≠ (20 : Nat) by omega), up_ne (show (14:Nat) ≠ (16 : Nat) by omega), up_ne (show (14:Nat) ≠ (16 : Nat) by omega), up_ne (show (14:Nat) ≠ (21 : Nat) by omega), up_ne (show (14:Nat) ≠ (15 : Nat) by omega), up_ne (show (14:Nat) ≠ (20 : Nat) by omega), hf14, up_ne (show (1:Nat) ≠ (12 : Nat) by omega), up_ne (show (1:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (21 : Nat) by omega), up_ne (show (1:Nat) ≠ (15 : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), h1],
              exec_blt_lt_step (by omega) (show prog.getD 122 Instr.reject = Instr.blt 2 1 103 by rfl) fi9U (by rw [e2_9U, e1_9U]; omega)]
            simp only [Nat.sub_sub, Nat.reduceAdd]
          obtain ⟨c2, f2, hc2, hex2, harr2, h122, h142, hfit2, hpres2⟩ :=
            ih L b d ak sl out (up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) (i + 1) j (wq + 1) (S - 14) r hsL
              (by omega) (by omega) (by omega)
              e12_9U e13_9U e14_9U e11_9U e17_9U e18_9U e19_9U e1_9U e2_9U esrc_9U
              hvfit htake1 hdrop1 hout fi9U hbL hdL h2L hb33 hd33 hdisj
              (by omega) (by omega)
          refine ⟨14 + c2, f2, by omega, ?_, harr2, h122, h142, hfit2, ?_⟩
          · rw [hwalk, hex2]
            have hS14 : S - 14 - c2 = S - (14 + c2) := by omega
            rw [hS14]
          · exact pres_trans (pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) (pres_trans (pres_up (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (pres_trans (pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))) (pres_trans (pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (pres_trans (pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (pres_trans (pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) (pres_trans (pres_up (MReg_dst (by omega) (by omega))) (pres_trans (pres_up (Or.inl rfl)) (pres_trans (pres_up (Or.inr (Or.inr (Or.inl rfl)))) (hpres2)))))))))
      · have hiL : i = L := by omega
        have hdropDJ : out.drop wq = (sl.map (fun z => z + ak)).drop j := by
          rw [hdrop, hiL, dropNil (by rw [hsL]; exact Nat.le_refl L), mmerge_nil_l]
        have hwalkB : exec prog ρ S 103 r (memOf w f)
            = exec prog ρ (S - 3) 133 r (memOf w f) := by
          rw [exec_blt_lt_step (by omega)
              (show prog.getD 103 Instr.reject = Instr.blt 13 11 105 by rfl) hfit
              (by rw [hf13, hf11]; exact hj),
            exec_blt_ge_step (by omega)
              (show prog.getD 105 Instr.reject = Instr.blt 12 11 107 by rfl) hfit
              (by rw [hf12, hf11, hiL]; omega),
            exec_blt_lt_step (by omega)
              (show prog.getD 106 Instr.reject = Instr.blt 2 1 133 by rfl) hfit
              (by rw [h2, h1]; omega)]
          simp only [Nat.sub_sub, Nat.reduceAdd]
        obtain ⟨c2, f2, hc2, hex2, harr2, h122, h132, h142, hfit2, hpres2⟩ :=
          djLoop_exec ρ (L - j) L b d ak sl out f j wq (S - 3) r hsL hj
            (by omega) (by rw [hf12, hiL]) hf13 hf14 hf11 hf17 hf18 hf19 h1 h2
            hsrc hvfit htake hdropDJ hfit hbL hdL h2L hb33 hd33 hdisj
            (Nat.le_refl _) (by omega)
        refine ⟨3 + c2, f2, by omega, ?_, harr2, h122, h142, hfit2, hpres2⟩
        · rw [hwalkB, hex2]
          have hS3 : S - 3 - c2 = S - (3 + c2) := by omega
          rw [hS3]
    · have hjL : j = L := by omega
      by_cases hi2 : i < L
      · have hdropDI : out.drop wq = sl.drop i := by
          have hmd : (sl.map (fun z => z + ak)).drop L = [] := dropNil (by omega)
          rw [hdrop, hjL, hmd, mmerge_nil_r]
        have hvfit0 : ∀ v ∈ sl, v < 2 ^ w := fun v hv => by
          have := hvfit v hv
          omega
        have hwalkA1 : exec prog ρ S 103 r (memOf w f)
            = exec prog ρ (S - 3) 125 r (memOf w f) := by
          rw [exec_blt_ge_step (by omega)
              (show prog.getD 103 Instr.reject = Instr.blt 13 11 105 by rfl) hfit
              (by rw [hf13, hf11]; exact hj),
            exec_blt_lt_step (by omega)
              (show prog.getD 104 Instr.reject = Instr.blt 2 1 123 by rfl) hfit
              (by rw [h2, h1]; omega),
            exec_blt_lt_step (by omega)
              (show prog.getD 123 Instr.reject = Instr.blt 12 11 125 by rfl) hfit
              (by rw [hf12, hf11]; exact hi2)]
          simp only [Nat.sub_sub, Nat.reduceAdd]
        obtain ⟨c2, f2, hc2, hex2, harr2, h122, h142, hfit2, hpres2⟩ :=
          diLoop_exec ρ (L - i) L b d sl out f i wq (S - 3) r hsL hi2
            (by omega) hf12 hf14 hf11 hf18 hf19 h1 h2
            hsrc hvfit0 htake hdropDI hfit hbL hdL h2L hb33 hd33 hdisj
            (Nat.le_refl _) (by omega)
        refine ⟨3 + c2, f2, by omega, ?_, harr2, h122, h142, hfit2, hpres2⟩
        · rw [hwalkA1, hex2]
          have hS3 : S - 3 - c2 = S - (3 + c2) := by omega
          rw [hS3]
      · have hw2 : wq = 2 * L := by omega
        have hlen : out.length = 2 * L := by
          rw [hout, mmerge_length, List.length_map, hsL]
          omega
        have hfull : arrL f d (2 * L) = out := by
          rw [hw2] at htake
          have hto := takeAll (l := out) (n := 2 * L) (by omega)
          have hla : (arrL f d (2 * L)).length = 2 * L := by simp [arrL]
          have hta := takeAll (l := arrL f d (2 * L)) (n := 2 * L) (by omega)
          rw [← hta, ← hto, htake]
        refine ⟨4, f, by omega, ?_, hfull, by omega, by omega, hfit, ?_⟩
        · rw [exec_blt_ge_step (by omega)
              (show prog.getD 103 Instr.reject = Instr.blt 13 11 105 by rfl) hfit
              (by rw [hf13, hf11]; omega),
            exec_blt_lt_step (by omega)
              (show prog.getD 104 Instr.reject = Instr.blt 2 1 123 by rfl) hfit
              (by rw [h2, h1]; omega),
            exec_blt_ge_step (by omega)
              (show prog.getD 123 Instr.reject = Instr.blt 12 11 125 by rfl) hfit
              (by rw [hf12, hf11]; omega),
            exec_blt_lt_step (by omega)
              (show prog.getD 124 Instr.reject = Instr.blt 2 1 141 by rfl) hfit
              (by rw [h2, h1]; omega)]
          simp only [Nat.sub_sub, Nat.reduceAdd]
        · intro x hx
          rfl

/-! ## §6. Round driver: LROUND setup, merge, LSWAP tail (pc 98 → 147). -/

/-- Cells strictly below the MReg register range, or in the 17–19/22 gap
(register cells are 12–16, 20, 21), are not `MReg` cells, given the arrays
live at ≥ 33. -/
theorem mreg_ne_small {d L c : Nat} (hd : 33 ≤ d)
    (h : c < 12 ∨ (17 ≤ c ∧ c ≤ 19) ∨ c = 22) : ¬ MReg d L c := by
  intro hmc
  rcases hmc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|harr
  all_goals rcases h with h1 | ⟨h1, h2⟩ | h1 <;> omega

/-- Three `sub r r r` zeroings at `pc`, `pc+1`, `pc+2` (cells 12, 13, 14). -/
theorem subs3_exec {w : Nat} {P : List Instr} {ρ : Nat → BitVec w} {f : Nat → Nat}
    {S r pc : Nat}
    (hfit : ∀ x, f x < 2 ^ w)
    (h1 : P.getD pc Instr.reject = Instr.sub 12 12 12)
    (h2 : P.getD (pc + 1) Instr.reject = Instr.sub 13 13 13)
    (h3 : P.getD (pc + 2) Instr.reject = Instr.sub 14 14 14)
    (hS : 3 ≤ S) :
    exec P ρ S pc r (memOf w f)
      = exec P ρ (S - 3) (pc + 3) r (memOf w (up (up (up f 12 0) 13 0) 14 0)) := by
  have f1 : ∀ x, (up f 12 0) x < 2 ^ w :=
    up_fit hfit (by have h : (1:Nat) ≤ 2 ^ w := Nat.one_le_two_pow; omega)
  have f2 : ∀ x, (up (up f 12 0) 13 0) x < 2 ^ w :=
    up_fit f1 (by have h : (1:Nat) ≤ 2 ^ w := Nat.one_le_two_pow; omega)
  rw [exec_sub_step (by omega) h1 hfit (Nat.le_refl _), Nat.sub_self,
      exec_sub_step (by omega) h2 f1 (Nat.le_refl _), Nat.sub_self,
      exec_sub_step (by omega) h3 f2 (Nat.le_refl _), Nat.sub_self]
  simp only [Nat.sub_sub, Nat.reduceAdd]

/-- The LSWAP tail (pc 141–146): double `L`, swap the array pointers,
bump `k`, load the bound `h+1` into cell 21. -/
theorem lswap_exec {w : Nat} {P : List Instr} {ρ : Nat → BitVec w} {f : Nat → Nat}
    {S r pc L b d k h : Nat}
    (h11 : f 11 = L) (h1 : f 1 = 1) (h2 : f 2 = 0) (h9 : f 9 = h)
    (h10 : f 10 = k) (h18 : f 18 = b) (h19 : f 19 = d)
    (c1 : P.getD pc Instr.reject = Instr.add 11 11 11)
    (c2 : P.getD (pc + 1) Instr.reject = Instr.add 20 18 2)
    (c3 : P.getD (pc + 2) Instr.reject = Instr.add 18 19 2)
    (c4 : P.getD (pc + 3) Instr.reject = Instr.add 19 20 2)
    (c5 : P.getD (pc + 4) Instr.reject = Instr.add 10 10 1)
    (c6 : P.getD (pc + 5) Instr.reject = Instr.add 21 9 1)
    (hS : 6 ≤ S) :
    exec P ρ S pc r (memOf w f)
      = exec P ρ (S - 6) (pc + 6) r
          (memOf w (up (up (up (up (up (up f 11 (2 * L)) 20 b) 18 d) 19 b)
            10 (k + 1)) 21 (h + 1))) := by
  rw [exec_add_step (by omega) c1,
      show f 11 + f 11 = 2 * L from by omega,
      exec_add_step (by omega) c2,
      show (up f 11 (2 * L)) 18 + (up f 11 (2 * L)) 2 = b from by
        rw [up_ne (show (18:Nat) ≠ 11 by omega),
            up_ne (show (2:Nat) ≠ 11 by omega), h18, h2, Nat.add_zero],
      exec_add_step (by omega) c3,
      show (up (up f 11 (2 * L)) 20 b) 19 + (up (up f 11 (2 * L)) 20 b) 2 = d from by
        rw [up_ne (show (19:Nat) ≠ 20 by omega),
            up_ne (show (19:Nat) ≠ 11 by omega),
            up_ne (show (2:Nat) ≠ 20 by omega),
            up_ne (show (2:Nat) ≠ 11 by omega), h19, h2, Nat.add_zero],
      exec_add_step (by omega) c4,
      show (up (up (up f 11 (2 * L)) 20 b) 18 d) 20
          + (up (up (up f 11 (2 * L)) 20 b) 18 d) 2 = b from by
        rw [up_ne (show (20:Nat) ≠ 18 by omega), up_eq,
            up_ne (show (2:Nat) ≠ 18 by omega),
            up_ne (show (2:Nat) ≠ 20 by omega),
            up_ne (show (2:Nat) ≠ 11 by omega), h2, Nat.add_zero],
      exec_add_step (by omega) c5,
      show (up (up (up (up f 11 (2 * L)) 20 b) 18 d) 19 b) 10
          + (up (up (up (up f 11 (2 * L)) 20 b) 18 d) 19 b) 1 = k + 1 from by
        rw [up_ne (show (10:Nat) ≠ 19 by omega),
            up_ne (show (10:Nat) ≠ 18 by omega),
            up_ne (show (10:Nat) ≠ 20 by omega),
            up_ne (show (10:Nat) ≠ 11 by omega), h10,
            up_ne (show (1:Nat) ≠ 19 by omega),
            up_ne (show (1:Nat) ≠ 18 by omega),
            up_ne (show (1:Nat) ≠ 20 by omega),
            up_ne (show (1:Nat) ≠ 11 by omega), h1],
      exec_add_step (by omega) c6,
      show (up (up (up (up (up f 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 9
          + (up (up (up (up (up f 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 1
          = h + 1 from by
        rw [up_ne (show (9:Nat) ≠ 10 by omega),
            up_ne (show (9:Nat) ≠ 19 by omega),
            up_ne (show (9:Nat) ≠ 18 by omega),
            up_ne (show (9:Nat) ≠ 20 by omega),
            up_ne (show (9:Nat) ≠ 11 by omega), h9,
            up_ne (show (1:Nat) ≠ 10 by omega),
            up_ne (show (1:Nat) ≠ 19 by omega),
            up_ne (show (1:Nat) ≠ 18 by omega),
            up_ne (show (1:Nat) ≠ 20 by omega),
            up_ne (show (1:Nat) ≠ 11 by omega), h1]]
  simp only [Nat.sub_sub, Nat.reduceAdd]

/-- One full round `k` (1 ≤ k ≤ h): LROUND setup (98–102), the merge
(103–141, via `merge_exec` from `(0,0,0)`), the LSWAP tail (141–146).
Lands at pc 147 with the guard `blt 10 21 98` pending. -/
theorem round_exec {w n : Nat} (ρ : Nat → BitVec w) {x : Instance n}
    (hn : 3 ≤ n) (hw : wordLength n x.bits ≤ w) :
    ∀ (h k L b d : Nat) (f : Nat → Nat) (S r : Nat),
    h = n / 2 → 1 ≤ k → k ≤ h → L = 2 ^ (k - 1) →
    f 1 = 1 → f 2 = 0 → f 7 = n → f 8 = 2 * n + 23 → f 9 = h →
    f 10 = k → f 11 = L → f 18 = b → f 19 = d →
    arrL f b L = halfSums (instA x) (k - 1) →
    (b = 3 * n + 25 ∧ d = 3 * n + 25 + 2 ^ h + 1 ∨
      d = 3 * n + 25 ∧ b = 3 * n + 25 + 2 ^ h + 1) →
    (∀ i, 1 ≤ i → i ≤ n → f (2 * n + 23 + i) = instA x (i - 1)) →
    (∀ i, i < n → instA x i < 2 ^ w) →
    (∀ q, f q < 2 ^ w) →
    (∀ c, c ≤ 3 * n + 25 + 2 ^ (h + 1) + 1 → c < 2 ^ w) →
    44 * L + 23 ≤ S →
    ∃ c f', c ≤ 44 * L + 23 ∧
      exec prog ρ S 98 r (memOf w f) = exec prog ρ (S - c) 147 r (memOf w f') ∧
      f' 10 = k + 1 ∧ f' 11 = 2 * L ∧ f' 18 = d ∧ f' 19 = b ∧ f' 21 = h + 1 ∧
      arrL f' d (2 * L) = halfSums (instA x) k ∧
      f' 1 = 1 ∧ f' 2 = 0 ∧ f' 7 = n ∧ f' 8 = 2 * n + 23 ∧ f' 9 = h ∧
      (∀ q, f' q < 2 ^ w) ∧ Pres (AReg n) f f' := by
  intro h k L b d f S r hh hk1 hkh hL hf1 hf2 hf7 hf8 hf9 hf10 hf11 hf18 hf19
    harr hbases hrel hin hfit haddr hS
  have h2h1 : (1:Nat) ≤ 2 ^ h := Nat.one_le_two_pow
  have hbd33 : 33 ≤ b ∧ 33 ≤ d := by
    rcases hbases with ⟨hb, hd⟩|⟨hd, hb⟩ <;> omega
  obtain ⟨hb33, hd33⟩ := hbd33
  have hLh : L ≤ 2 ^ h := by
    rw [hL]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have h2k : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← Nat.pow_succ', show (k - 1).succ = k from by omega]
  have h2Lh : 2 * L ≤ 2 ^ h := by
    rw [hL, ← h2k]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have h2p1 : 2 ^ (h + 1) = 2 * 2 ^ h := by rw [Nat.pow_succ, Nat.mul_comm]
  have hak : instA x (k - 1) < 2 ^ w := hin (k - 1) (by omega)
  have hfit1 : ∀ q, (up f 20 (2 * n + 23 + k)) q < 2 ^ w :=
    up_fit hfit (haddr _ (by omega))
  have hfit2 : ∀ q, (up (up f 20 (2 * n + 23 + k)) 17 (instA x (k - 1))) q < 2 ^ w :=
    up_fit hfit1 hak
  have hwalk5 : exec prog ρ S 98 r (memOf w f)
      = exec prog ρ (S - 5) 103 r (memOf w (up (up (up (up (up f 20 (2 * n + 23 + k)) 17 (instA x (k - 1))) 12 0) 13 0) 14 0)) := by
    rw [exec_add_step (by omega) (show prog.getD 98 Instr.reject = Instr.add 20 8 10 by rfl),
        show f 8 + f 10 = 2 * n + 23 + k from by rw [hf8, hf10],
        exec_load_step (by omega) (show prog.getD 99 Instr.reject = Instr.load 17 20 by rfl)
          hfit1,
        up_eq, up_ne (show 2 * n + 23 + k ≠ 20 by omega),
        hrel k (by omega) (by omega),
        subs3_exec hfit2
          (show prog.getD 100 Instr.reject = Instr.sub 12 12 12 by rfl)
          (show prog.getD 101 Instr.reject = Instr.sub 13 13 13 by rfl)
          (show prog.getD 102 Instr.reject = Instr.sub 14 14 14 by rfl)
          (by omega)]
    simp only [Nat.sub_sub, Nat.reduceAdd]
  have g12 : (up (up (up (up (up f 20 (2 * n + 23 + k)) 17 (instA x (k - 1))) 12 0) 13 0) 14 0) 12 = 0 := by
    rw [up_ne (show (12:Nat) ≠ 14 by omega), up_ne (show (12:Nat) ≠ 13 by omega), up_eq]
  have g13 : (up (up (up (up (up f 20 (2 * n + 23 + k)) 17 (instA x (k - 1))) 12 0) 13 0) 14 0) 13 = 0 := by
    rw [up_ne (show (13:Nat) ≠ 14 by omega), up_eq]
  have g14 : (up (up (up (up (up f 20 (2 * n + 23 + k)) 17 (instA x (k - 1))) 12 0) 13 0) 14 0) 14 = 0 := by rw [up_eq]
  have g11 : (up (up (up (up (up f 20 (2 * n + 23 + k)) 17 (instA x (k - 1))) 12 0) 13 0) 14 0) 11 = L := by
    rw [up_ne (show (11:Nat) ≠ 14 by omega), up_ne (show (11:Nat) ≠ 13 by omega),
      up_ne (show (11:Nat) ≠ 12 by omega), up_ne (show (11:Nat) ≠ 17 by omega),
      up_ne (show (11:Nat) ≠ 20 by omega), hf11]
  have g17 : (up (up (up (up (up f 20 (2 * n + 23 + k)) 17 (instA x (k - 1))) 12 0) 13 0) 14 0) 17 = instA x (k - 1) := by
    rw [up_ne (show (17:Nat) ≠ 14 by omega), up_ne (show (17:Nat) ≠ 13 by omega),
      up_ne (show (17:Nat) ≠ 12 by omega), up_eq]
  have g18 : (up (up (up (up (up f 20 (2 * n + 23 + k)) 17 (instA x (k - 1))) 12 0) 13 0) 14 0) 18 = b := by
    rw [up_ne (show (18:Nat) ≠ 14 by omega), up_ne (show (18:Nat) ≠ 13 by omega),
      up_ne (show (18:Nat) ≠ 12 by omega), up_ne (show (18:Nat) ≠ 17 by omega),
      up_ne (show (18:Nat) ≠ 20 by omega), hf18]
  have g19 : (up (up (up (up (up f 20 (2 * n + 23 + k)) 17 (instA x (k - 1))) 12 0) 13 0) 14 0) 19 = d := by
    rw [up_ne (show (19:Nat) ≠ 14 by omega), up_ne (show (19:Nat) ≠ 13 by omega),
      up_ne (show (19:Nat) ≠ 12 by omega), up_ne (show (19:Nat) ≠ 17 by omega),
      up_ne (show (19:Nat) ≠ 20 by omega), hf19]
  have g1 : (up (up (up (up (up f 20 (2 * n + 23 + k)) 17 (instA x (k - 1))) 12 0) 13 0) 14 0) 1 = 1 := by
    rw [up_ne (show (1:Nat) ≠ 14 by omega), up_ne (show (1:Nat) ≠ 13 by omega),
      up_ne (show (1:Nat) ≠ 12 by omega), up_ne (show (1:Nat) ≠ 17 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega), hf1]
  have g2 : (up (up (up (up (up f 20 (2 * n + 23 + k)) 17 (instA x (k - 1))) 12 0) 13 0) 14 0) 2 = 0 := by
    rw [up_ne (show (2:Nat) ≠ 14 by omega), up_ne (show (2:Nat) ≠ 13 by omega),
      up_ne (show (2:Nat) ≠ 12 by omega), up_ne (show (2:Nat) ≠ 17 by omega),
      up_ne (show (2:Nat) ≠ 20 by omega), hf2]
  have g7 : (up (up (up (up (up f 20 (2 * n + 23 + k)) 17 (instA x (k - 1))) 12 0) 13 0) 14 0) 7 = n := by
    rw [up_ne (show (7:Nat) ≠ 14 by omega), up_ne (show (7:Nat) ≠ 13 by omega),
      up_ne (show (7:Nat) ≠ 12 by omega), up_ne (show (7:Nat) ≠ 17 by omega),
      up_ne (show (7:Nat) ≠ 20 by omega), hf7]
  have g8 : (up (up (up (up (up f 20 (2 * n + 23 + k)) 17 (instA x (k - 1))) 12 0) 13 0) 14 0) 8 = 2 * n + 23 := by
    rw [up_ne (show (8:Nat) ≠ 14 by omega), up_ne (show (8:Nat) ≠ 13 by omega),
      up_ne (show (8:Nat) ≠ 12 by omega), up_ne (show (8:Nat) ≠ 17 by omega),
      up_ne (show (8:Nat) ≠ 20 by omega), hf8]
  have g9 : (up (up (up (up (up f 20 (2 * n + 23 + k)) 17 (instA x (k - 1))) 12 0) 13 0) 14 0) 9 = h := by
    rw [up_ne (show (9:Nat) ≠ 14 by omega), up_ne (show (9:Nat) ≠ 13 by omega),
      up_ne (show (9:Nat) ≠ 12 by omega), up_ne (show (9:Nat) ≠ 17 by omega),
      up_ne (show (9:Nat) ≠ 20 by omega), hf9]
  have g10 : (up (up (up (up (up f 20 (2 * n + 23 + k)) 17 (instA x (k - 1))) 12 0) 13 0) 14 0) 10 = k := by
    rw [up_ne (show (10:Nat) ≠ 14 by omega), up_ne (show (10:Nat) ≠ 13 by omega),
      up_ne (show (10:Nat) ≠ 12 by omega), up_ne (show (10:Nat) ≠ 17 by omega),
      up_ne (show (10:Nat) ≠ 20 by omega), hf10]
  have h0lt : (0:Nat) < 2 ^ w := Nat.one_le_two_pow (n := w)
  have gfit : ∀ q, (up (up (up (up (up f 20 (2 * n + 23 + k)) 17 (instA x (k - 1))) 12 0) 13 0) 14 0) q < 2 ^ w :=
    up_fit (up_fit (up_fit hfit2 h0lt) h0lt) h0lt
  have hgsrc : ∀ q, q < L → (up (up (up (up (up f 20 (2 * n + 23 + k)) 17 (instA x (k - 1))) 12 0) 13 0) 14 0) (b + q) = (halfSums (instA x) (k - 1)).getD q 0 := by
    intro q hq
    rw [up_ne (show b + q ≠ 14 by omega), up_ne (show b + q ≠ 13 by omega),
      up_ne (show b + q ≠ 12 by omega), up_ne (show b + q ≠ 17 by omega),
      up_ne (show b + q ≠ 20 by omega), ← harr, getD_arrL hq]
  have hsL' : (halfSums (instA x) (k - 1)).length = L := by
    rw [length_halfSums, hL]
  have hbL : b + L < 2 ^ w := haddr _ (by omega)
  have hdL : d + 2 * L < 2 ^ w := haddr _ (by omega)
  have h2L : 2 * L < 2 ^ w := haddr _ (by omega)
  have hdisj : ∀ p q, p < 2 * L → q < L → d + p ≠ b + q := by
    intro p q hp hq
    rcases hbases with ⟨hb, hd⟩|⟨hd, hb⟩ <;> omega
  have hout : halfSums (instA x) k
      = mmerge (halfSums (instA x) (k - 1))
          ((halfSums (instA x) (k - 1)).map (fun z => z + instA x (k - 1))) := by
    rw [show k = (k - 1) + 1 from by omega, halfSums,
        show k - 1 + 1 - 1 = k - 1 from by omega]
  obtain ⟨c2, fm, hc2, hex2, harrm, h12m, h14m, hfitm, hpm⟩ :=
    merge_exec ρ (2 * L) L b d (instA x (k - 1)) (halfSums (instA x) (k - 1))
      (halfSums (instA x) k) (up (up (up (up (up f 20 (2 * n + 23 + k)) 17 (instA x (k - 1))) 12 0) 13 0) 14 0) 0 0 0 (S - 5) r hsL'
      (by omega) (by omega) (by omega) g12 g13 g14 g11 g17 g18 g19 g1 g2
      hgsrc (fun v hv => halfSumAddFit (by omega) hw (k - 1) (by omega) v hv)
      (by exact rfl) (by exact hout) hout gfit hbL hdL h2L hb33 hd33 hdisj
      (by omega) (by omega)
  have fm11 : fm 11 = L := by
    rw [hpm 11 (mreg_ne_small hd33 (Or.inl (by omega))), g11]
  have fm18 : fm 18 = b := by
    rw [hpm 18 (mreg_ne_small hd33 (Or.inr (Or.inl ⟨by omega, by omega⟩))), g18]
  have fm19 : fm 19 = d := by
    rw [hpm 19 (mreg_ne_small hd33 (Or.inr (Or.inl ⟨by omega, by omega⟩))), g19]
  have fm1 : fm 1 = 1 := by rw [hpm 1 (mreg_ne_small hd33 (Or.inl (by omega))), g1]
  have fm2 : fm 2 = 0 := by rw [hpm 2 (mreg_ne_small hd33 (Or.inl (by omega))), g2]
  have fm7 : fm 7 = n := by rw [hpm 7 (mreg_ne_small hd33 (Or.inl (by omega))), g7]
  have fm8 : fm 8 = 2 * n + 23 := by
    rw [hpm 8 (mreg_ne_small hd33 (Or.inl (by omega))), g8]
  have fm9 : fm 9 = h := by rw [hpm 9 (mreg_ne_small hd33 (Or.inl (by omega))), g9]
  have fm10 : fm 10 = k := by rw [hpm 10 (mreg_ne_small hd33 (Or.inl (by omega))), g10]
  have htail : exec prog ρ (S - 5 - c2) 141 r (memOf w fm)
      = exec prog ρ (S - 5 - c2 - 6) 147 r (memOf w (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 21 (h + 1))) :=
    lswap_exec fm11 fm1 fm2 fm9 fm10 fm18 fm19
      (show prog.getD 141 Instr.reject = Instr.add 11 11 11 by rfl)
      (show prog.getD 142 Instr.reject = Instr.add 20 18 2 by rfl)
      (show prog.getD 143 Instr.reject = Instr.add 18 19 2 by rfl)
      (show prog.getD 144 Instr.reject = Instr.add 19 20 2 by rfl)
      (show prog.getD 145 Instr.reject = Instr.add 10 10 1 by rfl)
      (show prog.getD 146 Instr.reject = Instr.add 21 9 1 by rfl)
      (by omega)
  have f'10 : (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 21 (h + 1)) 10 = k + 1 := by
    rw [up_ne (show (10:Nat) ≠ 21 by omega), up_eq]
  have f'11 : (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 21 (h + 1)) 11 = 2 * L := by
    rw [up_ne (show (11:Nat) ≠ 21 by omega), up_ne (show (11:Nat) ≠ 10 by omega),
      up_ne (show (11:Nat) ≠ 19 by omega), up_ne (show (11:Nat) ≠ 18 by omega),
      up_ne (show (11:Nat) ≠ 20 by omega), up_eq]
  have f'18 : (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 21 (h + 1)) 18 = d := by
    rw [up_ne (show (18:Nat) ≠ 21 by omega), up_ne (show (18:Nat) ≠ 10 by omega),
      up_ne (show (18:Nat) ≠ 19 by omega), up_eq]
  have f'19 : (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 21 (h + 1)) 19 = b := by
    rw [up_ne (show (19:Nat) ≠ 21 by omega), up_ne (show (19:Nat) ≠ 10 by omega),
      up_eq]
  have f'21 : (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 21 (h + 1)) 21 = h + 1 := by rw [up_eq]
  have f'arr : arrL (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 21 (h + 1)) d (2 * L) = halfSums (instA x) k := by
    rw [arrL_up_out (fun q _ => show (21:Nat) ≠ d + q by omega),
        arrL_up_out (fun q _ => show (10:Nat) ≠ d + q by omega),
        arrL_up_out (fun q _ => show (19:Nat) ≠ d + q by omega),
        arrL_up_out (fun q _ => show (18:Nat) ≠ d + q by omega),
        arrL_up_out (fun q _ => show (20:Nat) ≠ d + q by omega),
        arrL_up_out (fun q _ => show (11:Nat) ≠ d + q by omega),
        harrm]
  have f'1 : (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 21 (h + 1)) 1 = 1 := by
    rw [up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (1:Nat) ≠ 10 by omega),
      up_ne (show (1:Nat) ≠ 19 by omega), up_ne (show (1:Nat) ≠ 18 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega), up_ne (show (1:Nat) ≠ 11 by omega), fm1]
  have f'2 : (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 21 (h + 1)) 2 = 0 := by
    rw [up_ne (show (2:Nat) ≠ 21 by omega), up_ne (show (2:Nat) ≠ 10 by omega),
      up_ne (show (2:Nat) ≠ 19 by omega), up_ne (show (2:Nat) ≠ 18 by omega),
      up_ne (show (2:Nat) ≠ 20 by omega), up_ne (show (2:Nat) ≠ 11 by omega), fm2]
  have f'7 : (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 21 (h + 1)) 7 = n := by
    rw [up_ne (show (7:Nat) ≠ 21 by omega), up_ne (show (7:Nat) ≠ 10 by omega),
      up_ne (show (7:Nat) ≠ 19 by omega), up_ne (show (7:Nat) ≠ 18 by omega),
      up_ne (show (7:Nat) ≠ 20 by omega), up_ne (show (7:Nat) ≠ 11 by omega), fm7]
  have f'8 : (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 21 (h + 1)) 8 = 2 * n + 23 := by
    rw [up_ne (show (8:Nat) ≠ 21 by omega), up_ne (show (8:Nat) ≠ 10 by omega),
      up_ne (show (8:Nat) ≠ 19 by omega), up_ne (show (8:Nat) ≠ 18 by omega),
      up_ne (show (8:Nat) ≠ 20 by omega), up_ne (show (8:Nat) ≠ 11 by omega), fm8]
  have f'9 : (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 21 (h + 1)) 9 = h := by
    rw [up_ne (show (9:Nat) ≠ 21 by omega), up_ne (show (9:Nat) ≠ 10 by omega),
      up_ne (show (9:Nat) ≠ 19 by omega), up_ne (show (9:Nat) ≠ 18 by omega),
      up_ne (show (9:Nat) ≠ 20 by omega), up_ne (show (9:Nat) ≠ 11 by omega), fm9]
  have f'fit : ∀ q, (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 21 (h + 1)) q < 2 ^ w :=
    up_fit (up_fit (up_fit (up_fit (up_fit (up_fit hfitm h2L) (haddr _ (by omega)))
      (haddr _ (by omega))) (haddr _ (by omega))) (haddr _ (by omega)))
      (haddr _ (by omega))
  have hAReq : 2 ^ (n / 2 + 1) = 2 ^ (h + 1) := by rw [← hh]
  have hsub : ∀ c, MReg d L c → AReg n c := by
    intro c hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|harr
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · rcases hbases with ⟨hb, hd⟩|⟨hd, hb⟩
      · exact Or.inr ⟨by omega, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
  have hpres5 : Pres (AReg n) f
      (up (up (up (up (up f 20 (2 * n + 23 + k)) 17 (instA x (k - 1))) 12 0) 13 0) 14 0) := by
    refine pres_trans (pres_up (c := 20) (v := 2 * n + 23 + k) (Or.inl (by omega))) ?_
    refine pres_trans (pres_up (c := 17) (v := instA x (k - 1)) (Or.inl (by omega))) ?_
    refine pres_trans (pres_up (c := 12) (v := 0) (Or.inl (by omega))) ?_
    refine pres_trans (pres_up (c := 13) (v := 0) (Or.inl (by omega))) ?_
    exact pres_up (c := 14) (v := 0) (Or.inl (by omega))
  have hpresf : Pres (AReg n) f fm := pres_trans hpres5 (pres_mono hsub hpm)
  have hPA : Pres (AReg n) f (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 21 (h + 1)) := by
    refine pres_trans hpresf ?_
    refine pres_trans (pres_up (c := 11) (v := 2 * L) (Or.inl (by omega))) ?_
    refine pres_trans (pres_up (c := 20) (v := b) (Or.inl (by omega))) ?_
    refine pres_trans (pres_up (c := 18) (v := d) (Or.inl (by omega))) ?_
    refine pres_trans (pres_up (c := 19) (v := b) (Or.inl (by omega))) ?_
    refine pres_trans (pres_up (c := 10) (v := k + 1) (Or.inl (by omega))) ?_
    exact pres_up (c := 21) (v := h + 1) (Or.inl (by omega))
  refine ⟨5 + c2 + 6, up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 21 (h + 1), by omega, ?_, f'10, f'11, f'18, f'19, f'21, f'arr,
    f'1, f'2, f'7, f'8, f'9, f'fit, hPA⟩
  rw [hwalk5, hex2, htail]
  simp only [Nat.sub_sub]

/-! ## §7. The round loop (pc 98 → 148) and the phase driver (86 → 148). -/

/-- All rounds `k..h` from pc 98: each round merges, doubles `L`, swaps
the pointers; after round `h` the guard at 147 falls through to Phase B
(pc 148) with `halfSums (instA x) h` at `[rSRC]`. -/
theorem lround_exec {w n : Nat} (ρ : Nat → BitVec w) {x : Instance n}
    (hn : 3 ≤ n) (hw : wordLength n x.bits ≤ w) :
    ∀ F (h k L b d : Nat) (f : Nat → Nat) (S r : Nat),
    h = n / 2 → 1 ≤ k → k ≤ h → L = 2 ^ (k - 1) →
    f 1 = 1 → f 2 = 0 → f 7 = n → f 8 = 2 * n + 23 → f 9 = h →
    f 10 = k → f 11 = L → f 18 = b → f 19 = d →
    arrL f b L = halfSums (instA x) (k - 1) →
    (b = 3 * n + 25 ∧ d = 3 * n + 25 + 2 ^ h + 1 ∨
      d = 3 * n + 25 ∧ b = 3 * n + 25 + 2 ^ h + 1) →
    (∀ i, 1 ≤ i → i ≤ n → f (2 * n + 23 + i) = instA x (i - 1)) →
    (∀ i, i < n → instA x i < 2 ^ w) →
    (∀ q, f q < 2 ^ w) →
    (∀ c, c ≤ 3 * n + 25 + 2 ^ (h + 1) + 1 → c < 2 ^ w) →
    h + 1 - k ≤ F →
    44 * (2 ^ h - 2 ^ (k - 1)) + 24 * (h - k + 1) ≤ S →
    ∃ c f' bd, c ≤ 44 * (2 ^ h - 2 ^ (k - 1)) + 24 * (h - k + 1) ∧
      exec prog ρ S 98 r (memOf w f) = exec prog ρ (S - c) 148 r (memOf w f') ∧
      f' 10 = h + 1 ∧ f' 11 = 2 ^ h ∧ f' 18 = bd ∧
      (bd = 3 * n + 25 ∨ bd = 3 * n + 25 + 2 ^ h + 1) ∧
      arrL f' bd (2 ^ h) = halfSums (instA x) h ∧
      f' 1 = 1 ∧ f' 2 = 0 ∧ f' 7 = n ∧ f' 8 = 2 * n + 23 ∧ f' 9 = h ∧
      (∀ q, f' q < 2 ^ w) ∧ Pres (AReg n) f f' := by
  intro F
  induction F with
  | zero =>
    intro h k L b d f S r hh hk1 hkh hL hf1 hf2 hf7 hf8 hf9 hf10 hf11 hf18 hf19
      harr hbases hrel hin hfit haddr hfuel hS
    omega
  | succ F ih =>
    intro h k L b d f S r hh hk1 hkh hL hf1 hf2 hf7 hf8 hf9 hf10 hf11 hf18 hf19
      harr hbases hrel hin hfit haddr hfuel hS
    have hLh : L ≤ 2 ^ h := by
      rw [hL]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    have h2k : 2 ^ k = 2 * 2 ^ (k - 1) := by
      rw [← Nat.pow_succ', show (k - 1).succ = k from by omega]
    have hk2h : 2 ^ k ≤ 2 ^ h := Nat.pow_le_pow_right (by omega) (by omega)
    obtain ⟨c1, fr, hc1, hex1, hfr10, hfr11, hfr18, hfr19, hfr21, hfrarr,
      hfr1, hfr2, hfr7, hfr8, hfr9, hfrfit, hfrpres⟩ :=
      round_exec ρ hn hw h k L b d f S r hh hk1 hkh hL hf1 hf2 hf7 hf8 hf9 hf10
        hf11 hf18 hf19 harr hbases hrel hin hfit haddr
        (by omega)
    by_cases hkl : k < h
    · -- guard taken: round k+1 from pc 98
      have hwalk : exec prog ρ S 98 r (memOf w f)
          = exec prog ρ (S - (c1 + 1)) 98 r (memOf w fr) := by
        rw [hex1,
          exec_blt_lt_step (by omega)
            (show prog.getD 147 Instr.reject = Instr.blt 10 21 98 by rfl) hfrfit
            (by rw [hfr10, hfr21]; omega)]
        simp only [Nat.sub_sub]
      have hL' : 2 * L = 2 ^ (k + 1 - 1) := by
        rw [show k + 1 - 1 = k from by omega, h2k, ← hL]
      have hbases' : (d = 3 * n + 25 ∧ b = 3 * n + 25 + 2 ^ h + 1 ∨
          b = 3 * n + 25 ∧ d = 3 * n + 25 + 2 ^ h + 1) := by
        rcases hbases with ⟨hb, hd⟩|⟨hd, hb⟩
        · exact Or.inr ⟨hb, hd⟩
        · exact Or.inl ⟨hd, hb⟩
      have hrel' : ∀ i, 1 ≤ i → i ≤ n → fr (2 * n + 23 + i) = instA x (i - 1) := by
        intro i hi1 hin'
        have hnA : ¬ AReg n (2 * n + 23 + i) := by
          intro hA
          rcases hA with hA|hA <;> omega
        rw [hfrpres _ hnA]
        exact hrel i hi1 hin'
      obtain ⟨c2, f2', bd, hc2, hex2, hf210, hf211, hf218, hf2bd, hf2arr,
        hf21, hf22, hf27, hf28, hf29, hf2fit, hf2pres⟩ :=
        ih h (k + 1) (2 * L) d b fr (S - (c1 + 1)) r hh (by omega) (by omega)
          hL' hfr1 hfr2 hfr7 hfr8 hfr9 hfr10 hfr11 hfr18 hfr19
          (by rw [show k + 1 - 1 = k from by omega]; exact hfrarr)
          hbases' hrel' hin hfrfit haddr (by omega)
          (by rw [show (k + 1) - 1 = k from by omega]; omega)
      refine ⟨c1 + 1 + c2, f2', bd, by omega, ?_, hf210, hf211, hf218, hf2bd,
        hf2arr, hf21, hf22, hf27, hf28, hf29, hf2fit,
        pres_trans hfrpres hf2pres⟩
      rw [hwalk, hex2]
      rw [show S - (c1 + 1) - c2 = S - (c1 + 1 + c2) from by omega]
    · -- k = h: the guard falls through to Phase B
      have hkh2 : k = h := by omega
      have h2h : 2 * L = 2 ^ h := by
        rw [hL, ← h2k, hkh2]
      have hwalkE : exec prog ρ S 98 r (memOf w f)
          = exec prog ρ (S - (c1 + 1)) 148 r (memOf w fr) := by
        rw [hex1,
          exec_blt_ge_step (by omega)
            (show prog.getD 147 Instr.reject = Instr.blt 10 21 98 by rfl) hfrfit
            (by rw [hfr10, hfr21]; omega)]
        simp only [Nat.sub_sub]
      refine ⟨c1 + 1, fr, d, by omega, hwalkE, by rw [hfr10, hkh2], by rw [hfr11, h2h],
        hfr18, ?_, by rw [← h2h, ← hkh2, hfrarr], hfr1, hfr2, hfr7, hfr8, hfr9,
        hfrfit, hfrpres⟩
      rcases hbases with ⟨hb, hd⟩|⟨hd, hb⟩
      · exact Or.inr hd
      · exact Or.inl hd

/-- The whole phase: prologue-style entry bundle at pc 86, then all `h`
rounds; lands at the Phase B entry (pc 148) with `halfSums (instA x) h`
at `[rSRC]`, `L = 2^h`, `k = h+1`. -/
theorem phaseA_exec {w n : Nat} (ρ : Nat → BitVec w) {x : Instance n}
    (hn : 4 ≤ n) (hw : wordLength n x.bits ≤ w)
    (f0 : Nat → Nat) (r S : Nat)
    (hfit : ∀ q, f0 q < 2 ^ w)
    (h1 : f0 1 = 1) (h2 : f0 2 = 0) (h7 : f0 7 = n) (h8 : f0 8 = 2 * n + 23)
    (haddr : ∀ c, c ≤ 3 * n + 26 + 2 * 2 ^ (n / 2) → c < 2 ^ w)
    (hrel : ∀ i, 1 ≤ i → i ≤ n → f0 (2 * n + 23 + i) = instA x (i - 1))
    (hin : ∀ i, i < n → instA x i < 2 ^ w)
    (hS : 12 + 44 * (2 ^ (n / 2) - 1) + 24 * (n / 2) ≤ S) :
    ∃ c f' bd, c ≤ 12 + 44 * (2 ^ (n / 2) - 1) + 24 * (n / 2) ∧
      exec prog ρ S 86 r (memOf w f0) = exec prog ρ (S - c) 148 r (memOf w f') ∧
      f' 10 = n / 2 + 1 ∧ f' 11 = 2 ^ (n / 2) ∧ f' 18 = bd ∧
      (bd = 3 * n + 25 ∨ bd = 3 * n + 25 + 2 ^ (n / 2) + 1) ∧
      arrL f' bd (2 ^ (n / 2)) = halfSums (instA x) (n / 2) ∧
      f' 1 = 1 ∧ f' 2 = 0 ∧ f' 7 = n ∧ f' 8 = 2 * n + 23 ∧ f' 9 = n / 2 ∧
      (∀ q, f' q < 2 ^ w) ∧ Pres (AReg n) f0 f' := by
  obtain ⟨f1, hinit, hfit1, h1_9, h1_18, h1_19, h1_10, h1_11, h1_c1, h1_c2,
    h1_c7, h1_c8, h1_arr, h1_pres⟩ :=
    init_exec ρ f0 r S hfit h1 h2 h7 h8 haddr (by omega)
  have h2p1 : 2 ^ (n / 2 + 1) = 2 * 2 ^ (n / 2) := by
    rw [Nat.pow_succ, Nat.mul_comm]
  have haddr1 : ∀ c, c ≤ 3 * n + 25 + 2 ^ (n / 2 + 1) + 1 → c < 2 ^ w :=
    fun c hc => haddr c (by omega)
  have hrel1 : ∀ i, 1 ≤ i → i ≤ n → f1 (2 * n + 23 + i) = instA x (i - 1) := by
    intro i hi1 hin'
    have hnA : ¬ AReg n (2 * n + 23 + i) := by
      intro hA
      rcases hA with hA|hA <;> omega
    rw [h1_pres _ hnA]
    exact hrel i hi1 hin'
  obtain ⟨c2, f2', bd, hc2, hex2, hf210, hf211, hf218, hf2bd, hf2arr,
    hf21, hf22, hf27, hf28, hf29, hf2fit, hf2pres⟩ :=
    lround_exec ρ (by omega) hw (n / 2) (n / 2) (1:Nat) (1:Nat) (3 * n + 25)
      (3 * n + 25 + 2 ^ (n / 2) + 1) f1 (S - 12) r rfl (by omega) (by omega)
      (by rw [show (1:Nat) - 1 = 0 from rfl, Nat.pow_zero])
      h1_c1 h1_c2 h1_c7 h1_c8 h1_9 h1_10 h1_11 h1_18 h1_19
      (by rw [h1_arr]; rfl)
      (Or.inl ⟨rfl, rfl⟩) hrel1 hin hfit1 haddr1 (by omega)
      (by rw [show (1:Nat) - 1 = 0 from rfl, Nat.pow_zero]; omega)
  refine ⟨12 + c2, f2', bd, by omega, ?_, hf210, hf211, hf218, hf2bd, hf2arr,
    hf21, hf22, hf27, hf28, hf29, hf2fit, pres_trans h1_pres hf2pres⟩
  rw [hinit, hex2]
  rw [show S - 12 - c2 = S - (12 + c2) from by omega]

end SubsetSum.MITM
