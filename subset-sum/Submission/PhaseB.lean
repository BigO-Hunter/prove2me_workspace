import Submission.Prologue
import Submission.PhaseA
import Submission.Sort
import Submission.Words
set_option autoImplicit true

/-!
# Phase B: binary search + the correctness bridge (R2125607414)

Three layers:

§0 the list-level binary search `bsFind`, mirroring the RAM loop at
`LBSRCH` (pc 175): probe `mid = (lo + hi) / 2`, recurse left on
`arr[mid] < x`, right on `x < arr[mid]`, hit on equality.  Soundness
(every probe stays inside the caller's interval) needs no sortedness;
completeness (a witness in `[lo, hi]` is found) needs `Pairwise (· ≤ ·)`.

§1 the spec bridge: searching `t - s` in `halfSums a h` succeeds iff
`isSum a h (t - s)`, which by `isSum_split` makes the MITM instance
solvable.  Also the wrapped-complement unmatchability fact (a `t < s`
complement exceeds every `total`-bounded half-sum, so the RAM's wrapped
search target never hits).

§2 the exec translation: the RAM's search loop at pcs 175–189 over the
array at `[rSRC]` implements `bsFind` — a miss walks to `LNEXT` (pc 189)
with `lo = hi + 1`, a hit accepts.  Register-file facts, canonical
memory, `decide`-free pc facts via `rfl` (Prologue's step lemmas).
-/

namespace SubsetSum.MITM

open BigOSpeedrun.SubsetSum SubsetSum.MITM.Spec

/-! ## §0. The list-level binary search -/

/-- Binary search mirroring the RAM loop: while `lo ≤ hi`, probe
`mid = (lo + hi) / 2`; `lo := mid + 1` when the probe is small,
`hi := mid - 1` when large, `true` on equality.  Fuel-driven. -/
def bsFind (arr : List Nat) (x : Nat) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fl + 1, lo, hi =>
    if lo ≤ hi then
      if arr.getD ((lo + hi) / 2) 0 < x then bsFind arr x fl ((lo + hi) / 2 + 1) hi
      else if x < arr.getD ((lo + hi) / 2) 0 then bsFind arr x fl lo ((lo + hi) / 2 - 1)
      else true
    else false

/-- `mid = (lo + hi) / 2` sits inside `[lo, hi]` (via `div_add_mod`). -/
theorem div2_bounds {lo hi : Nat} (h : lo ≤ hi) :
    lo ≤ (lo + hi) / 2 ∧ (lo + hi) / 2 ≤ hi := by
  have hd := Nat.div_add_mod (lo + hi) 2
  have hm := Nat.mod_lt (lo + hi) (show 0 < 2 by decide)
  omega

/-- Both division bounds on `a / 2` without a side condition: the halves
of a search window shrink by (at least) a factor of two per probe. -/
theorem div2_mul_bounds (a : Nat) : 2 * (a / 2) ≤ a ∧ a ≤ 2 * (a / 2) + 1 := by
  have hd := Nat.div_add_mod a 2
  have hm := Nat.mod_lt a (show 0 < 2 by decide)
  omega

/-- Every probe the search accepts lies inside the caller's interval. -/
theorem bsFind_sound_idx (arr : List Nat) (x : Nat) :
    ∀ (fl lo hi : Nat), bsFind arr x fl lo hi = true →
      ∃ m, lo ≤ m ∧ m ≤ hi ∧ arr.getD m 0 = x := by
  intro fl
  induction fl with
  | zero => intro lo hi h; simp [bsFind] at h
  | succ fl ih =>
    intro lo hi h
    simp only [bsFind] at h
    split at h
    · next hle =>
      split at h
      · next hlt =>
        obtain ⟨m, hm1, hm2, hm3⟩ := ih _ _ h
        have hb := div2_bounds hle
        exact ⟨m, by omega, hm2, hm3⟩
      · next hlt =>
        split at h
        · next hgt =>
          obtain ⟨m, hm1, hm2, hm3⟩ := ih _ _ h
          have hb := div2_bounds hle
          exact ⟨m, hm1, by omega, hm3⟩
        · have hb := div2_bounds hle
          refine ⟨(lo + hi) / 2, hb.1, hb.2, ?_⟩
          omega
    · exact absurd h (by simp)

theorem getD_mem_of_lt {l : List Nat} {j : Nat} (h : j < l.length) : l.getD j 0 ∈ l := by
  induction l generalizing j with
  | nil => exact absurd h (by simp)
  | cons a t ih =>
    cases j with
    | zero => exact List.mem_cons_self
    | succ j =>
      show t.getD j 0 ∈ a :: t
      exact List.mem_cons_of_mem _ (ih (by simpa using h))

/-- An accepted search that stays under the array length found a member. -/
theorem bsFind_sound (arr : List Nat) (x fl lo hi : Nat) (hlen : hi < arr.length)
    (h : bsFind arr x fl lo hi = true) : x ∈ arr := by
  obtain ⟨m, _, hm2, hm3⟩ := bsFind_sound_idx arr x fl lo hi h
  have hmem : arr.getD m 0 ∈ arr := getD_mem_of_lt (by omega)
  rw [hm3] at hmem
  exact hmem

/-! ### Sortedness monotonicity -/

/-- In a `Pairwise (· ≤ ·)` list, earlier indices hold smaller values. -/
theorem getD_le_getD_of_pairwise {l : List Nat} (h : List.Pairwise (· ≤ ·) l) :
    ∀ i j : Nat, i ≤ j → j < l.length → l.getD i 0 ≤ l.getD j 0 := by
  induction l with
  | nil => intro i j _ hj; exact absurd hj (by simp)
  | cons a t ih =>
    intro i j hij hjj
    match i, j with
    | 0, 0 => exact Nat.le_refl _
    | 0, j + 1 =>
      have hmem : t.getD j 0 ∈ t := getD_mem_of_lt (by simpa using hjj)
      exact (List.pairwise_cons.mp h).1 _ hmem
    | i + 1, j + 1 =>
      exact ih (List.pairwise_cons.mp h).2 i j (Nat.le_of_succ_le_succ hij)
        (Nat.lt_of_succ_lt_succ hjj)
    | i + 1, 0 => exact absurd hij (by omega)

/-- A witness in `[lo, hi]` (with `hi` in range) is always found. -/
theorem bsFind_complete (arr : List Nat) (hsort : List.Pairwise (· ≤ ·) arr) (x : Nat) :
    ∀ (fl lo hi : Nat), hi < arr.length →
      (∃ m, lo ≤ m ∧ m ≤ hi ∧ arr.getD m 0 = x) → hi < lo + fl →
      bsFind arr x fl lo hi = true := by
  intro fl
  induction fl with
  | zero => intro lo hi _ _ hf; omega
  | succ fl ih =>
    intro lo hi hlen hw hf
    obtain ⟨m, hm1, hm2, hmeq⟩ := hw
    simp only [bsFind]
    have hle : lo ≤ hi := by omega
    rw [if_pos hle]
    have hb := div2_bounds hle
    rcases Nat.lt_trichotomy (arr.getD ((lo + hi) / 2) 0) x with hcmp | hcmp | hcmp
    · -- probe < x: go right-end up (LLESS)
      rw [if_pos hcmp]
      have hmg1 : (lo + hi) / 2 < m := by
        by_cases hme : m = (lo + hi) / 2
        · rw [hme] at hmeq; omega
        · by_cases hml : m ≤ (lo + hi) / 2
          · have h1 := getD_le_getD_of_pairwise hsort m ((lo + hi) / 2) hml (by omega)
            omega
          · omega
      refine ih _ _ hlen ⟨m, by omega, hm2, hmeq⟩ (by omega)
    · -- probe = x: hit
      rw [if_neg (by omega), if_neg (by omega)]
    · -- x < probe: go left-end down (LGTR)
      rw [if_neg (by omega), if_pos hcmp]
      have hmml : m < (lo + hi) / 2 := by
        by_cases hme : m = (lo + hi) / 2
        · rw [hme] at hmeq; omega
        · by_cases hml : m ≤ (lo + hi) / 2
          · omega
          · have h1 := getD_le_getD_of_pairwise hsort ((lo + hi) / 2) m (by omega) (by omega)
            omega
      refine ih _ _ (by omega) ⟨m, hm1, by omega, hmeq⟩ (by omega)

/-! ## §1. The spec bridge -/

theorem mem_getD_index {l : List Nat} {x : Nat} (h : x ∈ l) :
    ∃ i, i < l.length ∧ l.getD i 0 = x := by
  induction l with
  | nil => cases h
  | cons a t ih =>
    rcases List.mem_cons.mp h with h | h
    · exact ⟨0, by simp, by rw [h]; rfl⟩
    · obtain ⟨i, hi, hx⟩ := ih h
      exact ⟨i + 1, by simpa using hi, by simpa using hx⟩

/-- The smallest subset sum is 0: the doubling merge never loses the head. -/
theorem halfSums_cons_zero (a : Nat → Nat) (k : Nat) :
    ∃ t, halfSums a k = 0 :: t := by
  induction k with
  | zero => exact ⟨[], rfl⟩
  | succ k ih =>
    obtain ⟨t, ht⟩ := ih
    rw [halfSums, ht, List.map_cons, mmerge,
      if_neg (show ¬ (0 + a k < 0) by omega)]
    exact ⟨_, rfl⟩

theorem halfSums_head_zero (a : Nat → Nat) (k : Nat) : (halfSums a k).getD 0 0 = 0 := by
  obtain ⟨t, ht⟩ := halfSums_cons_zero a k
  rw [ht]; rfl

/-- THE search fact at spec level: the binary search over the first-half
array hits exactly when `t - s` is a first-half subset sum. -/
theorem bsearch_halfSums_iff (a : Nat → Nat) (h t s : Nat) :
    bsFind (halfSums a h) (t - s) (2 ^ h) 0 (2 ^ h - 1) = true ↔
      isSum a h (t - s) := by
  have hlen : (halfSums a h).length = 2 ^ h := length_halfSums a h
  have hone : 1 ≤ 2 ^ h := Nat.one_le_two_pow
  constructor
  · intro hb
    have hmem : (t - s) ∈ halfSums a h :=
      bsFind_sound (halfSums a h) (t - s) (2 ^ h) 0 (2 ^ h - 1) (by rw [hlen]; omega) hb
    exact (mem_halfSums a h _).mp hmem
  · intro hsum
    obtain ⟨m, hml, hmeq⟩ := mem_getD_index ((mem_halfSums a h (t - s)).mpr hsum)
    rw [hlen] at hml
    exact bsFind_complete (halfSums a h) (halfSums_sorted a h) (t - s) (2 ^ h) 0 (2 ^ h - 1)
      (by omega) ⟨m, Nat.zero_le _, by omega, hmeq⟩ (by omega)

/-- A hit on the second-half sum `s ≤ t` makes the instance solvable. -/
theorem phaseb_solvable_of_hit (a : Nat → Nat) (h n t s : Nat) (hst : s ≤ t)
    (h2 : isSum (fun i => a (i + h)) n s)
    (hb : bsFind (halfSums a h) (t - s) (2 ^ h) 0 (2 ^ h - 1) = true) :
    isSum a (h + n) t := by
  have h1 : isSum a h (t - s) := (bsearch_halfSums_iff a h t s).mp hb
  exact (isSum_split a h n t).mpr ⟨t - s, by omega, h1, by
    rw [show t - (t - s) = s from by omega]; exact h2⟩

/-- A solvable instance yields a second-half sum `s ≤ t` whose complement
search hits. -/
theorem phaseb_hit_of_solvable (a : Nat → Nat) (h n t : Nat)
    (hs : isSum a (h + n) t) :
    ∃ s, s ≤ t ∧ isSum (fun i => a (i + h)) n s ∧
      bsFind (halfSums a h) (t - s) (2 ^ h) 0 (2 ^ h - 1) = true := by
  obtain ⟨s', hs'le, h1, h2⟩ := (isSum_split a h n t).mp hs
  have hty : t - (t - s') = s' := by omega
  refine ⟨t - s', by omega, ?_, ?_⟩
  · exact h2
  · exact (bsearch_halfSums_iff a h t (t - s')).mpr (by rw [hty]; exact h1)

/-- A wrapped complement (`t < s`) is strictly above every value bounded
by `total` — it can never equal a half-sum cell.  (Nat-level form of
`Words.wrapped_gt`.) -/
theorem wrapped_ne_of_le {w total s t v : Nat} (htot : 2 * total < 2 ^ w)
    (hst : t < s) (hs : s ≤ total) (hv : v ≤ total) :
    v ≠ 2 ^ w - (s - t) := by omega

/-! ## §2. The exec translation: the RAM search implements `bsFind`

Resolved pcs (from `resolve (prologue ++ phaseA ++ phaseB ++ smallN)`):
`175` LBSRCH · `178` LSMID · `185` LGTR · `187` LLESS · `189` LNEXT. -/

/-- Fit is preserved by a cell update (PhaseA owns the name `up_fit`;
this is PhaseB's non-clashing twin). -/
theorem fit_up {f : Nat → Nat} {c v w : Nat} (hfit : ∀ q, f q < 2 ^ w)
    (hv : v < 2 ^ w) : ∀ q, (up f c v) q < 2 ^ w := by
  intro q
  by_cases h : q = c <;> simp [h, up, hfit, hv]

/-- The first six instructions of the search loop (175–181): from the
loop head with `lo ≤ hi` to the probe comparison at pc 182, with the
probe value `f (b + mid)` in cell 15 and `mid` in cell 20. -/
theorem bsrch_pre {w : Nat} (ρ : Nat → BitVec w) (L b lo hi cc : Nat)
    (f : Nat → Nat) (S r : Nat)
    (hf12 : f 12 = lo) (hf13 : f 13 = hi) (hf16 : f 16 = cc) (hf18 : f 18 = b)
    (hf1 : f 1 = 1) (hf2 : f 2 = 0)
    (hb23 : 23 ≤ b) (hle : lo ≤ hi) (hhi : hi + 1 ≤ L)
    (hfit : ∀ q, f q < 2 ^ w) (hbL : b + L < 2 ^ w) (h2L : 2 * L < 2 ^ w)
    (hS : 6 ≤ S) :
    ∃ g, exec prog ρ S 175 r (memOf w f)
        = exec prog ρ (S - 6) 182 r (memOf w g) ∧
      lo ≤ (lo + hi) / 2 ∧ (lo + hi) / 2 ≤ hi ∧
      g 12 = lo ∧ g 13 = hi ∧ g 16 = cc ∧ g 18 = b ∧ g 1 = 1 ∧ g 2 = 0 ∧
      g 15 = f (b + (lo + hi) / 2) ∧ g 20 = (lo + hi) / 2 ∧
      g b = f b ∧ (∀ q, g q < 2 ^ w) ∧
      (∀ q, q ≠ 15 → q ≠ 20 → q ≠ 21 → g q = f q) := by
  have hLw : L < 2 ^ w := by omega
  have fA1 : ∀ q, (up f 20 (hi + 1)) q < 2 ^ w := fit_up hfit (by omega)
  have fA2 : ∀ q, (up (up f 20 (hi + 1)) 20 (lo + hi)) q < 2 ^ w :=
    fit_up fA1 (by omega)
  have fA3 : ∀ q,
      (up (up (up f 20 (hi + 1)) 20 (lo + hi)) 20 ((lo + hi) / 2)) q < 2 ^ w :=
    fit_up fA2 (by have := div2_bounds hle; omega)
  have fA4 : ∀ q,
      (up (up (up (up f 20 (hi + 1)) 20 (lo + hi)) 20 ((lo + hi) / 2))
        21 (b + (lo + hi) / 2)) q < 2 ^ w :=
    fit_up fA3 (by omega)
  have e175 : f 13 + f 1 = hi + 1 := by rw [hf13, hf1]
  have e178 : (up f 20 (hi + 1)) 12 + (up f 20 (hi + 1)) 13 = lo + hi := by
    rw [up_ne (show (12:Nat) ≠ 20 by omega), up_ne (show (13:Nat) ≠ 20 by omega),
      hf12, hf13]
  have e179 : (up (up f 20 (hi + 1)) 20 (lo + hi)) 20
      / 2 ^ (up (up f 20 (hi + 1)) 20 (lo + hi)) 1 = (lo + hi) / 2 := by
    rw [up_eq, up_ne (show (1:Nat) ≠ 20 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega), hf1, Nat.pow_one]
  have e180 : (up (up (up f 20 (hi + 1)) 20 (lo + hi)) 20 ((lo + hi) / 2)) 18
      + (up (up (up f 20 (hi + 1)) 20 (lo + hi)) 20 ((lo + hi) / 2)) 20
      = b + (lo + hi) / 2 := by
    rw [up_ne (show (18:Nat) ≠ 20 by omega),
      up_ne (show (18:Nat) ≠ 20 by omega), up_ne (show (18:Nat) ≠ 20 by omega),
      hf18, up_eq]
  have e181 : (up (up (up (up f 20 (hi + 1)) 20 (lo + hi)) 20 ((lo + hi) / 2))
        21 (b + (lo + hi) / 2))
      ((up (up (up (up f 20 (hi + 1)) 20 (lo + hi)) 20 ((lo + hi) / 2))
        21 (b + (lo + hi) / 2)) 21)
      = f (b + (lo + hi) / 2) := by
    rw [up_eq, up_ne (show b + (lo + hi) / 2 ≠ 21 by omega),
      up_ne (show b + (lo + hi) / 2 ≠ 20 by omega),
      up_ne (show b + (lo + hi) / 2 ≠ 20 by omega),
      up_ne (show b + (lo + hi) / 2 ≠ 20 by omega)]
  refine ⟨up (up (up (up (up f 20 (hi + 1)) 20 (lo + hi)) 20 ((lo + hi) / 2))
    21 (b + (lo + hi) / 2)) 15 (f (b + (lo + hi) / 2)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [exec_add_step (by omega)
        (show prog.getD 175 Instr.reject = Instr.add 20 13 1 by rfl), e175,
      exec_blt_lt_step (by omega)
        (show prog.getD 176 Instr.reject = Instr.blt 12 20 178 by rfl) fA1
        (by rw [up_ne (show (12:Nat) ≠ 20 by omega), up_eq, hf12]; omega),
      exec_add_step (by omega)
        (show prog.getD 178 Instr.reject = Instr.add 20 12 13 by rfl), e178,
      exec_shr_step (by omega)
        (show prog.getD 179 Instr.reject = Instr.shr 20 20 1 by rfl) fA2, e179,
      exec_add_step (by omega)
        (show prog.getD 180 Instr.reject = Instr.add 21 18 20 by rfl), e180,
      exec_load_step (by omega)
        (show prog.getD 181 Instr.reject = Instr.load 15 21 by rfl) fA4, e181]
    simp only [Nat.sub_sub, Nat.reduceAdd]
  · exact (div2_bounds hle).1
  · exact (div2_bounds hle).2
  · rw [up_ne (show (12:Nat) ≠ 15 by omega), up_ne (show (12:Nat) ≠ 21 by omega),
      up_ne (show (12:Nat) ≠ 20 by omega), up_ne (show (12:Nat) ≠ 20 by omega),
      up_ne (show (12:Nat) ≠ 20 by omega), hf12]
  · rw [up_ne (show (13:Nat) ≠ 15 by omega), up_ne (show (13:Nat) ≠ 21 by omega),
      up_ne (show (13:Nat) ≠ 20 by omega), up_ne (show (13:Nat) ≠ 20 by omega),
      up_ne (show (13:Nat) ≠ 20 by omega), hf13]
  · rw [up_ne (show (16:Nat) ≠ 15 by omega), up_ne (show (16:Nat) ≠ 21 by omega),
      up_ne (show (16:Nat) ≠ 20 by omega), up_ne (show (16:Nat) ≠ 20 by omega),
      up_ne (show (16:Nat) ≠ 20 by omega), hf16]
  · rw [up_ne (show (18:Nat) ≠ 15 by omega), up_ne (show (18:Nat) ≠ 21 by omega),
      up_ne (show (18:Nat) ≠ 20 by omega), up_ne (show (18:Nat) ≠ 20 by omega),
      up_ne (show (18:Nat) ≠ 20 by omega), hf18]
  · rw [up_ne (show (1:Nat) ≠ 15 by omega), up_ne (show (1:Nat) ≠ 21 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega), up_ne (show (1:Nat) ≠ 20 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega), hf1]
  · rw [up_ne (show (2:Nat) ≠ 15 by omega), up_ne (show (2:Nat) ≠ 21 by omega),
      up_ne (show (2:Nat) ≠ 20 by omega), up_ne (show (2:Nat) ≠ 20 by omega),
      up_ne (show (2:Nat) ≠ 20 by omega), hf2]
  · exact up_eq _ _ _
  · rw [up_ne (show (20:Nat) ≠ 15 by omega), up_ne (show (20:Nat) ≠ 21 by omega),
      up_eq]
  · rw [up_ne (show b ≠ 15 by omega), up_ne (show b ≠ 21 by omega),
      up_ne (show b ≠ 20 by omega), up_ne (show b ≠ 20 by omega),
      up_ne (show b ≠ 20 by omega)]
  · exact fit_up fA4 (hfit _)
  · intro q h15 h20 h21
    rw [up_ne (show q ≠ 15 by omega), up_ne (show q ≠ 21 by omega),
      up_ne (show q ≠ 20 by omega), up_ne (show q ≠ 20 by omega),
      up_ne (show q ≠ 20 by omega)]

/-- The exhausted guard: with `lo = hi + 1`, three steps reach `LNEXT`
(pc 189), writing only cell 20. -/
theorem bsrch_exit {w : Nat} (ρ : Nat → BitVec w) (L b lo hi cc : Nat)
    (f : Nat → Nat) (S r : Nat)
    (hf12 : f 12 = lo) (hf13 : f 13 = hi) (hf16 : f 16 = cc) (hf18 : f 18 = b)
    (hf1 : f 1 = 1) (hf2 : f 2 = 0)
    (hxx : hi + 1 ≤ lo) (hfit : ∀ q, f q < 2 ^ w) (hS : 3 ≤ S) :
    exec prog ρ S 175 r (memOf w f)
      = exec prog ρ (S - 3) 189 r (memOf w (up f 20 (hi + 1))) := by
  have hLw : hi + 1 < 2 ^ w := by
    have := hfit 12; rw [hf12] at this; omega
  have fA1 : ∀ q, (up f 20 (hi + 1)) q < 2 ^ w := fit_up hfit hLw
  have e175 : f 13 + f 1 = hi + 1 := by rw [hf13, hf1]
  rw [exec_add_step (by omega)
      (show prog.getD 175 Instr.reject = Instr.add 20 13 1 by rfl), e175,
    exec_blt_ge_step (by omega)
      (show prog.getD 176 Instr.reject = Instr.blt 12 20 178 by rfl) fA1
      (by rw [up_ne (show (12:Nat) ≠ 20 by omega), up_eq, hf12]; omega),
    exec_blt_lt_step (by omega)
      (show prog.getD 177 Instr.reject = Instr.blt 2 1 189 by rfl) fA1
      (by rw [up_ne (show (2:Nat) ≠ 20 by omega),
        up_ne (show (1:Nat) ≠ 20 by omega), hf1, hf2]; omega)]
  simp only [Nat.sub_sub, Nat.reduceAdd]

/-- THE miss theorem: if no cell of `[rSRC]` in `[lo, hi]` holds `cc`,
the RAM search walks to `LNEXT` (pc 189) with `lo = hi + 1`, preserving
everything outside the register cells 12/13/15/20/21. -/
theorem bsrch_miss_exec {w : Nat} (ρ : Nat → BitVec w) :
    ∀ (N L b lo hi cc : Nat) (f : Nat → Nat) (S r : Nat),
    f 12 = lo → f 13 = hi → f 16 = cc → f 18 = b → f 1 = 1 → f 2 = 0 →
    f b = 0 → 23 ≤ b → lo ≤ hi + 1 → hi + 1 ≤ L →
    (∀ m, lo ≤ m → m ≤ hi → f (b + m) ≠ cc) →
    (∀ q, f q < 2 ^ w) → b + L < 2 ^ w → 2 * L < 2 ^ w →
    hi + 1 - lo ≤ 2 ^ N → 10 * N + 13 ≤ S →
    ∃ c f', c ≤ 10 * N + 13 ∧
      exec prog ρ S 175 r (memOf w f) = exec prog ρ (S - c) 189 r (memOf w f') ∧
      f' 12 = f' 13 + 1 ∧ f' 13 ≤ hi ∧ f' 16 = cc ∧ f' 18 = b ∧ f' 1 = 1 ∧
      f' 2 = 0 ∧ f' b = f b ∧ (∀ q, f' q < 2 ^ w) ∧
      (∀ q, q ≠ 12 → q ≠ 13 → q ≠ 15 → q ≠ 20 → q ≠ 21 → f' q = f q) := by
  intro N
  induction N with
  | zero =>
    intro L b lo hi cc f S r hf12 hf13 hf16 hf18 hf1 hf2 hz hb23 hle hhi hmiss
      hfit hbL h2L hN hS
    by_cases hle2 : lo ≤ hi
    · -- window 1: lo = hi, one probe round, then the exit
      have hlohi : lo = hi := by
        have h1 : (2:Nat) ^ 0 = 1 := by decide
        omega
      obtain ⟨g, hexec, hmlo, hmhi, hg12, hg13, hg16, hg18, hg1, hg2, hg15,
        hg20, hgb, hgfit, hpres⟩ :=
        bsrch_pre ρ L b lo hi cc f S r hf12 hf13 hf16 hf18 hf1 hf2 hb23 hle2
          hhi hfit hbL h2L (by omega)
      have hmid : (lo + hi) / 2 = lo := by
        have hb := div2_bounds hle2
        omega
      have hne : g 15 ≠ g 16 := by
        rw [hg15, hg16, hmid]
        exact hmiss lo (by omega) (by omega)
      by_cases hc1 : g 15 < g 16
      · -- probe < target: LLESS — lo := mid + 1 = hi + 1, exit
        have e187 : g 20 + g 1 = (lo + hi) / 2 + 1 := by rw [hg20, hg1]
        have s6fit : ∀ q, (up g 12 ((lo + hi) / 2 + 1)) q < 2 ^ w :=
          fit_up hgfit (by have := div2_bounds hle2; omega)
        rw [hexec,
          exec_blt_lt_step (by omega)
            (show prog.getD 182 Instr.reject = Instr.blt 15 16 187 by rfl) hgfit hc1,
          exec_add_step (by omega)
            (show prog.getD 187 Instr.reject = Instr.add 12 20 1 by rfl), e187,
          exec_blt_lt_step (by omega)
            (show prog.getD 188 Instr.reject = Instr.blt 2 1 175 by rfl) s6fit
            (by rw [up_ne (show (2:Nat) ≠ 12 by omega),
              up_ne (show (1:Nat) ≠ 12 by omega), hg2, hg1]; omega)]
        simp only [Nat.sub_sub, Nat.reduceAdd]
        have hxe := bsrch_exit ρ L b ((lo + hi) / 2 + 1) hi cc
          (up g 12 ((lo + hi) / 2 + 1)) (S - 9) r
          (up_eq _ _ _) (by rw [up_ne (show (13:Nat) ≠ 12 by omega), hg13])
          (by rw [up_ne (show (16:Nat) ≠ 12 by omega), hg16])
          (by rw [up_ne (show (18:Nat) ≠ 12 by omega), hg18])
          (by rw [up_ne (show (1:Nat) ≠ 12 by omega), hg1])
          (by rw [up_ne (show (2:Nat) ≠ 12 by omega), hg2])
          (by omega) s6fit (by omega)
        refine ⟨12, up (up g 12 ((lo + hi) / 2 + 1)) 20 (hi + 1), by omega, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hxe, show S - 9 - 3 = S - 12 from by omega]
        · rw [up_ne (show (12:Nat) ≠ 20 by omega), up_eq,
            up_ne (show (13:Nat) ≠ 20 by omega),
            up_ne (show (13:Nat) ≠ 12 by omega), hg13]
          omega
        · rw [up_ne (show (13:Nat) ≠ 20 by omega),
            up_ne (show (13:Nat) ≠ 12 by omega), hg13]
          omega
        · rw [up_ne (show (16:Nat) ≠ 20 by omega),
            up_ne (show (16:Nat) ≠ 12 by omega), hg16]
        · rw [up_ne (show (18:Nat) ≠ 20 by omega),
            up_ne (show (18:Nat) ≠ 12 by omega), hg18]
        · rw [up_ne (show (1:Nat) ≠ 20 by omega),
            up_ne (show (1:Nat) ≠ 12 by omega), hg1]
        · rw [up_ne (show (2:Nat) ≠ 20 by omega),
            up_ne (show (2:Nat) ≠ 12 by omega), hg2]
        · rw [up_ne (show b ≠ 20 by omega), up_ne (show b ≠ 12 by omega)]
          exact hgb
        · exact fit_up s6fit (by have := hfit 13; rw [hf13] at this; omega)
        · intro q h12 h13 h15 h20 h21
          rw [up_ne (show (q:Nat) ≠ 20 by omega), up_ne (show q ≠ 12 by omega)]
          exact hpres q (by omega) (by omega) (by omega)
      · by_cases hc2 : g 16 < g 15
        · -- target < probe: LGTR — hi := mid - 1 = lo - 1, exit
          have hmid1 : 1 ≤ (lo + hi) / 2 := by
            by_cases hme : (lo + hi) / 2 = 0
            · rw [hme, Nat.add_zero] at hg15
              rw [hg16, hg15, hz] at hc2
              omega
            · omega
          have e185 : g 20 - g 1 = (lo + hi) / 2 - 1 := by rw [hg20, hg1]
          have s6fit : ∀ q, (up g 13 ((lo + hi) / 2 - 1)) q < 2 ^ w :=
            fit_up hgfit (by omega)
          rw [hexec,
            exec_blt_ge_step (by omega)
              (show prog.getD 182 Instr.reject = Instr.blt 15 16 187 by rfl)
              hgfit hc1,
            exec_blt_lt_step (by omega)
              (show prog.getD 183 Instr.reject = Instr.blt 16 15 185 by rfl)
              hgfit hc2,
            exec_sub_step (by omega)
              (show prog.getD 185 Instr.reject = Instr.sub 13 20 1 by rfl)
              hgfit (by rw [hg20, hg1]; omega), e185,
            exec_blt_lt_step (by omega)
              (show prog.getD 186 Instr.reject = Instr.blt 2 1 175 by rfl) s6fit
              (by rw [up_ne (show (2:Nat) ≠ 13 by omega),
                up_ne (show (1:Nat) ≠ 13 by omega), hg2, hg1]; omega)]
          simp only [Nat.sub_sub, Nat.reduceAdd]
          have hxe := bsrch_exit ρ L b lo ((lo + hi) / 2 - 1) cc
            (up g 13 ((lo + hi) / 2 - 1)) (S - 10) r
            (by rw [up_ne (show (12:Nat) ≠ 13 by omega), hg12])
            (up_eq _ _ _)
            (by rw [up_ne (show (16:Nat) ≠ 13 by omega), hg16])
            (by rw [up_ne (show (18:Nat) ≠ 13 by omega), hg18])
            (by rw [up_ne (show (1:Nat) ≠ 13 by omega), hg1])
            (by rw [up_ne (show (2:Nat) ≠ 13 by omega), hg2])
            (by omega) s6fit (by omega)
          refine ⟨13, up (up g 13 ((lo + hi) / 2 - 1)) 20 ((lo + hi) / 2 - 1 + 1),
            by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hxe, show S - 10 - 3 = S - 13 from by omega]
          · rw [up_ne (show (12:Nat) ≠ 20 by omega),
              up_ne (show (12:Nat) ≠ 13 by omega), hg12, up_ne (show (13:Nat) ≠ 20 by omega),
              up_eq]
            omega
          · rw [up_ne (show (13:Nat) ≠ 20 by omega), up_eq]
            omega
          · rw [up_ne (show (16:Nat) ≠ 20 by omega),
              up_ne (show (16:Nat) ≠ 13 by omega), hg16]
          · rw [up_ne (show (18:Nat) ≠ 20 by omega),
              up_ne (show (18:Nat) ≠ 13 by omega), hg18]
          · rw [up_ne (show (1:Nat) ≠ 20 by omega),
              up_ne (show (1:Nat) ≠ 13 by omega), hg1]
          · rw [up_ne (show (2:Nat) ≠ 20 by omega),
              up_ne (show (2:Nat) ≠ 13 by omega), hg2]
          · rw [up_ne (show b ≠ 20 by omega), up_ne (show b ≠ 13 by omega)]
            exact hgb
          · exact fit_up s6fit (by have := hfit 13; rw [hf13] at this; omega)
          · intro q h12 h13 h15 h20 h21
            rw [up_ne (show (q:Nat) ≠ 20 by omega), up_ne (show q ≠ 13 by omega)]
            exact hpres q (by omega) (by omega) (by omega)
        · -- equal: contradicts the miss hypothesis at mid
          have hva : g 15 = g 16 := by omega
          rw [hg15, hg16] at hva
          exact absurd hva (hmiss _ hmlo hmhi)
    · -- exhausted entry: three steps out
      refine ⟨3, up f 20 (hi + 1), by omega, bsrch_exit ρ L b lo hi cc f S r hf12
        hf13 hf16 hf18 hf1 hf2 (by omega) hfit (by omega), ?_, by
        rw [up_ne (show (13:Nat) ≠ 20 by omega), hf13]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [up_ne (show (12:Nat) ≠ 20 by omega), hf12,
          up_ne (show (13:Nat) ≠ 20 by omega), hf13]
        omega
      · rw [up_ne (show (16:Nat) ≠ 20 by omega), hf16]
      · rw [up_ne (show (18:Nat) ≠ 20 by omega), hf18]
      · rw [up_ne (show (1:Nat) ≠ 20 by omega), hf1]
      · rw [up_ne (show (2:Nat) ≠ 20 by omega), hf2]
      · rw [up_ne (show b ≠ 20 by omega)]
      · exact fit_up hfit (by have := hfit 13; rw [hf13] at this; omega)
      · intro q _ _ _ h20 _; exact up_ne h20
  | succ N ih =>
    intro L b lo hi cc f S r hf12 hf13 hf16 hf18 hf1 hf2 hz hb23 hle hhi hmiss
      hfit hbL h2L hN hS
    by_cases hle2 : lo ≤ hi
    · obtain ⟨g, hexec, hmlo, hmhi, hg12, hg13, hg16, hg18, hg1, hg2, hg15,
        hg20, hgb, hgfit, hpres⟩ :=
      bsrch_pre ρ L b lo hi cc f S r hf12 hf13 hf16 hf18 hf1 hf2 hb23 hle2 hhi
        hfit hbL h2L (by omega)
      by_cases hc1 : g 15 < g 16
      · -- probe < target: LLESS — lo := mid + 1 (9 steps), recurse
        have e187 : g 20 + g 1 = (lo + hi) / 2 + 1 := by rw [hg20, hg1]
        have s6fit : ∀ q, (up g 12 ((lo + hi) / 2 + 1)) q < 2 ^ w :=
          fit_up hgfit (by have := div2_bounds hle2; omega)
        rw [hexec,
          exec_blt_lt_step (by omega)
            (show prog.getD 182 Instr.reject = Instr.blt 15 16 187 by rfl) hgfit hc1,
          exec_add_step (by omega)
            (show prog.getD 187 Instr.reject = Instr.add 12 20 1 by rfl), e187,
          exec_blt_lt_step (by omega)
            (show prog.getD 188 Instr.reject = Instr.blt 2 1 175 by rfl) s6fit
            (by rw [up_ne (show (2:Nat) ≠ 12 by omega),
              up_ne (show (1:Nat) ≠ 12 by omega), hg2, hg1]; omega)]
        simp only [Nat.sub_sub, Nat.reduceAdd]
        obtain ⟨c, f2, hc, hex, hf2a, hf2b, hf2c, hf2d, hf2e, hf2f, hf2g, hf2h,
            hf2i⟩ :=
          ih L b ((lo + hi) / 2 + 1) hi cc
            (up g 12 ((lo + hi) / 2 + 1)) (S - 9) r
            (up_eq _ _ _) (by rw [up_ne (show (13:Nat) ≠ 12 by omega), hg13])
            (by rw [up_ne (show (16:Nat) ≠ 12 by omega), hg16])
            (by rw [up_ne (show (18:Nat) ≠ 12 by omega), hg18])
            (by rw [up_ne (show (1:Nat) ≠ 12 by omega), hg1])
            (by rw [up_ne (show (2:Nat) ≠ 12 by omega), hg2])
            (by rw [up_ne (show b ≠ 12 by omega), hgb, hz])
            hb23 (by omega) (by omega)
            (by intro m hm1 hm2
                rw [up_ne (show b + m ≠ 12 by omega),
                  hpres (b + m) (by omega) (by omega) (by omega)]
                exact hmiss m (by omega) hm2)
            s6fit hbL h2L
            (by have hd := div2_mul_bounds (lo + hi)
                have hp := Nat.pow_succ 2 N
                omega) (by omega)
        refine ⟨9 + c, f2, by omega, ?_, hf2a, by omega, hf2c, hf2d, hf2e, hf2f,
          ?_, hf2h, ?_⟩
        · rw [hex, show S - 9 - c = S - (9 + c) from by omega]
        · rw [hf2g, up_ne (show b ≠ 12 by omega), hgb]
        · intro q h12 h13 h15 h20 h21
          rw [hf2i q h12 h13 h15 h20 h21, up_ne (show q ≠ 12 by omega),
            hpres q (by omega) (by omega) (by omega)]
      · by_cases hc2 : g 16 < g 15
        · -- target < probe: LGTR — hi := mid - 1 (10 steps), recurse
          have hm1 : 1 ≤ (lo + hi) / 2 := by
            by_cases hme : (lo + hi) / 2 = 0
            · rw [hme, Nat.add_zero] at hg15
              rw [hg16, hg15, hz] at hc2
              omega
            · omega
          have e185 : g 20 - g 1 = (lo + hi) / 2 - 1 := by rw [hg20, hg1]
          have s6fit : ∀ q, (up g 13 ((lo + hi) / 2 - 1)) q < 2 ^ w :=
            fit_up hgfit (by omega)
          rw [hexec,
            exec_blt_ge_step (by omega)
              (show prog.getD 182 Instr.reject = Instr.blt 15 16 187 by rfl) hgfit hc1,
            exec_blt_lt_step (by omega)
              (show prog.getD 183 Instr.reject = Instr.blt 16 15 185 by rfl) hgfit hc2,
            exec_sub_step (by omega)
              (show prog.getD 185 Instr.reject = Instr.sub 13 20 1 by rfl) hgfit
              (by rw [hg20, hg1]; omega), e185,
            exec_blt_lt_step (by omega)
              (show prog.getD 186 Instr.reject = Instr.blt 2 1 175 by rfl) s6fit
              (by rw [up_ne (show (2:Nat) ≠ 13 by omega),
                up_ne (show (1:Nat) ≠ 13 by omega), hg2, hg1]; omega)]
          simp only [Nat.sub_sub, Nat.reduceAdd]
          obtain ⟨c, f2, hc, hex, hf2a, hf2b, hf2c, hf2d, hf2e, hf2f, hf2g, hf2h,
              hf2i⟩ :=
            ih L b lo ((lo + hi) / 2 - 1) cc (up g 13 ((lo + hi) / 2 - 1))
              (S - 10) r
              (by rw [up_ne (show (12:Nat) ≠ 13 by omega), hg12])
              (up_eq _ _ _)
              (by rw [up_ne (show (16:Nat) ≠ 13 by omega), hg16])
              (by rw [up_ne (show (18:Nat) ≠ 13 by omega), hg18])
              (by rw [up_ne (show (1:Nat) ≠ 13 by omega), hg1])
              (by rw [up_ne (show (2:Nat) ≠ 13 by omega), hg2])
              (by rw [up_ne (show b ≠ 13 by omega), hgb, hz])
              hb23 (by omega) (by omega)
              (by intro m hm1 hm2
                  rw [up_ne (show b + m ≠ 13 by omega),
                    hpres (b + m) (by omega) (by omega) (by omega)]
                  exact hmiss m hm1 (by omega))
              s6fit hbL h2L
              (by have hd := div2_mul_bounds (lo + hi)
                  have hp := Nat.pow_succ 2 N
                  omega) (by omega)
          refine ⟨10 + c, f2, by omega, ?_, hf2a, by omega, hf2c, hf2d, hf2e,
            hf2f, ?_, hf2h, ?_⟩
          · rw [hex, show S - 10 - c = S - (10 + c) from by omega]
          · rw [hf2g, up_ne (show b ≠ 13 by omega), hgb]
          · intro q h12 h13 h15 h20 h21
            rw [hf2i q h12 h13 h15 h20 h21, up_ne (show q ≠ 13 by omega),
              hpres q (by omega) (by omega) (by omega)]
        · -- equal: contradicts the miss hypothesis at mid
          have hva : g 15 = g 16 := by omega
          rw [hg15, hg16] at hva
          exact absurd hva (hmiss _ hmlo hmhi)
    · -- exhausted entry: three steps out
      refine ⟨3, up f 20 (hi + 1), by omega, bsrch_exit ρ L b lo hi cc f S r hf12
        hf13 hf16 hf18 hf1 hf2 (by omega) hfit (by omega), ?_, by
        rw [up_ne (show (13:Nat) ≠ 20 by omega), hf13]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [up_ne (show (12:Nat) ≠ 20 by omega), hf12,
          up_ne (show (13:Nat) ≠ 20 by omega), hf13]
        omega
      · rw [up_ne (show (16:Nat) ≠ 20 by omega), hf16]
      · rw [up_ne (show (18:Nat) ≠ 20 by omega), hf18]
      · rw [up_ne (show (1:Nat) ≠ 20 by omega), hf1]
      · rw [up_ne (show (2:Nat) ≠ 20 by omega), hf2]
      · rw [up_ne (show b ≠ 20 by omega)]
      · exact fit_up hfit (by have := hfit 13; rw [hf13] at this; omega)
      · intro q _ _ _ h20 _; exact up_ne h20

/-- THE hit theorem: if some cell of `[rSRC]` in `[lo, hi]` holds `cc`
and the array at `[rSRC]` is sorted, the RAM search accepts. -/
theorem bsrch_hit_exec {w : Nat} (ρ : Nat → BitVec w) :
    ∀ (N L b lo hi cc : Nat) (arr : List Nat) (f : Nat → Nat) (S r : Nat),
    List.Pairwise (· ≤ ·) arr → arr.length = L →
    f 12 = lo → f 13 = hi → f 16 = cc → f 18 = b → f 1 = 1 → f 2 = 0 →
    f b = 0 → 23 ≤ b → lo ≤ hi → hi + 1 ≤ L →
    (∀ q, q < L → f (b + q) = arr.getD q 0) →
    (∃ m, lo ≤ m ∧ m ≤ hi ∧ f (b + m) = cc) →
    (∀ q, f q < 2 ^ w) → b + L < 2 ^ w → 2 * L < 2 ^ w →
    hi + 1 - lo ≤ 2 ^ N → 10 * N + 19 ≤ S →
    ∃ c, c ≤ 10 * N + 19 ∧ exec prog ρ S 175 r (memOf w f) = some true := by
  intro N
  induction N with
  | zero =>
    intro L b lo hi cc arr f S r hsort hlen hf12 hf13 hf16 hf18 hf1 hf2 hz hb23
      hle hhi hbind hwit hfit hbL h2L hN hS
    obtain ⟨m, hm1, hm2, hwm⟩ := hwit
    have hlohi : lo = hi := by
      have h1 : (2:Nat) ^ 0 = 1 := by decide
      omega
    have hmlo : lo ≤ (lo + hi) / 2 := (div2_bounds hle).1
    have hmhi : (lo + hi) / 2 ≤ hi := (div2_bounds hle).2
    have hmid : (lo + hi) / 2 = lo := by omega
    have hmeq : m = lo := by omega
    obtain ⟨g, hexec, hmlo', hmhi', hg12, hg13, hg16, hg18, hg1, hg2, hg15,
      hg20, hgb, hgfit, hpres⟩ :=
      bsrch_pre ρ L b lo hi cc f S r hf12 hf13 hf16 hf18 hf1 hf2 hb23 hle hhi
        hfit hbL h2L (by omega)
    have hev : g 15 = g 16 := by
      rw [hg15, hg16, hmid, ← hmeq]
      exact hwm
    rw [hexec,
      exec_blt_ge_step (by omega)
        (show prog.getD 182 Instr.reject = Instr.blt 15 16 187 by rfl) hgfit
        (by rw [hev]; omega),
      exec_blt_ge_step (by omega)
        (show prog.getD 183 Instr.reject = Instr.blt 16 15 185 by rfl) hgfit
        (by rw [hev]; omega),
      exec_accept_step (by omega)
        (show prog.getD 184 Instr.reject = Instr.accept by rfl)]
    exact ⟨9, by omega, rfl⟩
  | succ N ih =>
    intro L b lo hi cc arr f S r hsort hlen hf12 hf13 hf16 hf18 hf1 hf2 hz hb23
      hle hhi hbind hwit hfit hbL h2L hN hS
    obtain ⟨m, hm1, hm2, hwm⟩ := hwit
    have hmono : ∀ i j, i ≤ j → j < L → f (b + i) ≤ f (b + j) := by
      intro i j hij hjj
      rw [hbind i (by omega), hbind j hjj]
      exact getD_le_getD_of_pairwise hsort i j hij (by rw [hlen]; omega)
    obtain ⟨g, hexec, hmlo, hmhi, hg12, hg13, hg16, hg18, hg1, hg2, hg15,
      hg20, hgb, hgfit, hpres⟩ :=
      bsrch_pre ρ L b lo hi cc f S r hf12 hf13 hf16 hf18 hf1 hf2 hb23 hle hhi
        hfit hbL h2L (by omega)
    rcases Nat.lt_trichotomy (g 15) (g 16) with hc1 | hc1 | hc1
    · -- probe < target: LLESS — witness m ≥ mid + 1 (9 steps), recurse
      have hmg1 : (lo + hi) / 2 < m := by
        by_cases hme : m = (lo + hi) / 2
        · rw [hme] at hwm
          rw [hg15, hwm] at hc1
          omega
        · by_cases hml : m ≤ (lo + hi) / 2
          · have h1 := hmono m ((lo + hi) / 2) hml (by have := div2_bounds hle; omega)
            rw [hg15] at hc1
            omega
          · omega
      have e187 : g 20 + g 1 = (lo + hi) / 2 + 1 := by rw [hg20, hg1]
      have s6fit : ∀ q, (up g 12 ((lo + hi) / 2 + 1)) q < 2 ^ w :=
        fit_up hgfit (by have := div2_bounds hle; omega)
      have s6bind : ∀ q, q < L →
          (up g 12 ((lo + hi) / 2 + 1)) (b + q) = arr.getD q 0 := by
        intro q hq
        rw [up_ne (show b + q ≠ 12 by omega),
          hpres (b + q) (by omega) (by omega) (by omega)]
        exact hbind q hq
      rw [hexec,
        exec_blt_lt_step (by omega)
          (show prog.getD 182 Instr.reject = Instr.blt 15 16 187 by rfl) hgfit hc1,
        exec_add_step (by omega)
          (show prog.getD 187 Instr.reject = Instr.add 12 20 1 by rfl), e187,
        exec_blt_lt_step (by omega)
          (show prog.getD 188 Instr.reject = Instr.blt 2 1 175 by rfl) s6fit
          (by rw [up_ne (show (2:Nat) ≠ 12 by omega),
            up_ne (show (1:Nat) ≠ 12 by omega), hg2, hg1]; omega)]
      simp only [Nat.sub_sub, Nat.reduceAdd]
      obtain ⟨c, hc, hex⟩ :=
        ih L b ((lo + hi) / 2 + 1) hi cc arr (up g 12 ((lo + hi) / 2 + 1))
          (S - 9) r hsort hlen
          (up_eq _ _ _) (by rw [up_ne (show (13:Nat) ≠ 12 by omega), hg13])
          (by rw [up_ne (show (16:Nat) ≠ 12 by omega), hg16])
          (by rw [up_ne (show (18:Nat) ≠ 12 by omega), hg18])
          (by rw [up_ne (show (1:Nat) ≠ 12 by omega), hg1])
          (by rw [up_ne (show (2:Nat) ≠ 12 by omega), hg2])
          (by rw [up_ne (show b ≠ 12 by omega), hgb, hz])
          hb23 (by omega) (by omega) s6bind
          ⟨m, by omega, hm2, by
            rw [up_ne (show b + m ≠ 12 by omega),
              hpres (b + m) (by omega) (by omega) (by omega)]
            exact hwm⟩
          s6fit hbL h2L
          (by have hd := div2_mul_bounds (lo + hi)
              have hp := Nat.pow_succ 2 N
              omega) (by omega)
      exact ⟨9 + c, by omega, hex⟩
    · -- equal: accept (9 steps)
      rw [hexec,
        exec_blt_ge_step (by omega)
          (show prog.getD 182 Instr.reject = Instr.blt 15 16 187 by rfl) hgfit
          (by omega),
        exec_blt_ge_step (by omega)
          (show prog.getD 183 Instr.reject = Instr.blt 16 15 185 by rfl) hgfit
          (by omega),
        exec_accept_step (by omega)
          (show prog.getD 184 Instr.reject = Instr.accept by rfl)]
      exact ⟨9, by omega, rfl⟩
    · -- target < probe: LGTR — mid ≥ 1, witness m ≤ mid - 1 (10 steps)
      have hmid1 : 1 ≤ (lo + hi) / 2 := by
        by_cases hme : (lo + hi) / 2 = 0
        · rw [hme, Nat.add_zero] at hg15
          rw [hg16, hg15, hz] at hc1
          omega
        · omega
      have hmml : m < (lo + hi) / 2 := by
        by_cases hme : m = (lo + hi) / 2
        · rw [hme] at hwm
          rw [hg15, hwm] at hc1
          omega
        · by_cases hml : m ≤ (lo + hi) / 2
          · omega
          · have h1 := hmono ((lo + hi) / 2) m (by omega)
              (by have := div2_bounds hle; omega)
            rw [hg15] at hc1
            omega
      have e185 : g 20 - g 1 = (lo + hi) / 2 - 1 := by rw [hg20, hg1]
      have s6fit : ∀ q, (up g 13 ((lo + hi) / 2 - 1)) q < 2 ^ w :=
        fit_up hgfit (by omega)
      have s6bind : ∀ q, q < L →
          (up g 13 ((lo + hi) / 2 - 1)) (b + q) = arr.getD q 0 := by
        intro q hq
        rw [up_ne (show b + q ≠ 13 by omega),
          hpres (b + q) (by omega) (by omega) (by omega)]
        exact hbind q hq
      rw [hexec,
        exec_blt_ge_step (by omega)
          (show prog.getD 182 Instr.reject = Instr.blt 15 16 187 by rfl) hgfit
          (by omega),
        exec_blt_lt_step (by omega)
          (show prog.getD 183 Instr.reject = Instr.blt 16 15 185 by rfl) hgfit hc1,
        exec_sub_step (by omega)
          (show prog.getD 185 Instr.reject = Instr.sub 13 20 1 by rfl) hgfit
          (by rw [hg20, hg1]; omega), e185,
        exec_blt_lt_step (by omega)
          (show prog.getD 186 Instr.reject = Instr.blt 2 1 175 by rfl) s6fit
          (by rw [up_ne (show (2:Nat) ≠ 13 by omega),
            up_ne (show (1:Nat) ≠ 13 by omega), hg2, hg1]; omega)]
      simp only [Nat.sub_sub, Nat.reduceAdd]
      obtain ⟨c, hc, hex⟩ :=
        ih L b lo ((lo + hi) / 2 - 1) cc arr (up g 13 ((lo + hi) / 2 - 1))
          (S - 10) r hsort hlen
          (by rw [up_ne (show (12:Nat) ≠ 13 by omega), hg12])
          (up_eq _ _ _)
          (by rw [up_ne (show (16:Nat) ≠ 13 by omega), hg16])
          (by rw [up_ne (show (18:Nat) ≠ 13 by omega), hg18])
          (by rw [up_ne (show (1:Nat) ≠ 13 by omega), hg1])
          (by rw [up_ne (show (2:Nat) ≠ 13 by omega), hg2])
          (by rw [up_ne (show b ≠ 13 by omega), hgb, hz])
          hb23 (by omega) (by omega) s6bind
          ⟨m, hm1, by omega, by
            rw [up_ne (show b + m ≠ 13 by omega),
              hpres (b + m) (by omega) (by omega) (by omega)]
            exact hwm⟩
          s6fit hbL h2L
          (by have hd := div2_mul_bounds (lo + hi)
              have hp := Nat.pow_succ 2 N
              omega) (by omega)
      exact ⟨10 + c, by omega, hex⟩

/-! ### The `LNEXT` tails -/

/-- `LNEXT` with `idx + 1 = CNT2`: increment, guard fails, reject. -/
theorem lnext_reject_exec {w : Nat} (ρ : Nat → BitVec w) (f : Nat → Nat)
    (S r : Nat)
    (hf10 : f 10 + 1 = f 22) (hf1 : f 1 = 1) (hf2 : f 2 = 0)
    (hfit : ∀ q, f q < 2 ^ w) (hS : 3 ≤ S) :
    exec prog ρ S 189 r (memOf w f) = some false := by
  have fA1 : ∀ q, (up f 10 (f 10 + 1)) q < 2 ^ w :=
    fit_up hfit (by rw [hf10]; exact hfit 22)
  have e189 : f 10 + f 1 = f 10 + 1 := by rw [hf1]
  rw [exec_add_step (by omega)
      (show prog.getD 189 Instr.reject = Instr.add 10 10 1 by rfl), e189,
    exec_blt_ge_step (by omega)
      (show prog.getD 190 Instr.reject = Instr.blt 10 22 154 by rfl) fA1
      (by rw [up_eq, up_ne (show (22:Nat) ≠ 10 by omega)]; omega),
    exec_reject_step (by omega)
      (show prog.getD 191 Instr.reject = Instr.reject by rfl)]

/-- `LNEXT` with `idx + 1 < CNT2`: loop back to `LBIDX` (pc 154). -/
theorem lnext_loop_exec {w : Nat} (ρ : Nat → BitVec w) (f : Nat → Nat)
    (S r : Nat)
    (hlt : f 10 + 1 < f 22) (hf1 : f 1 = 1)
    (hfit : ∀ q, f q < 2 ^ w) (hS : 2 ≤ S) :
    exec prog ρ S 189 r (memOf w f)
      = exec prog ρ (S - 2) 154 r (memOf w (up f 10 (f 10 + 1))) := by
  have fA1 : ∀ q, (up f 10 (f 10 + 1)) q < 2 ^ w :=
    fit_up hfit (by have := hfit 22; omega)
  have e189 : f 10 + f 1 = f 10 + 1 := by rw [hf1]
  rw [exec_add_step (by omega)
      (show prog.getD 189 Instr.reject = Instr.add 10 10 1 by rfl), e189,
    exec_blt_lt_step (by omega)
      (show prog.getD 190 Instr.reject = Instr.blt 10 22 154 by rfl) fA1
      (by rw [up_eq, up_ne (show (22:Nat) ≠ 10 by omega)]; omega)]
  simp only [Nat.sub_sub, Nat.reduceAdd]

/-! ## §3. Candidate sums: second-half choice sums as bit-reads of an index

The candidate loop (pc 154) walks `idx = 0, 1, …` and, for each, sums the
second-half entries selected by `idx`'s bits.  This section is pure
list/Nat arithmetic: peel-first sums, the shifted-total bound, the
`candSum` vocabulary, and the realization of any eventually-false choice
function as the bits of some index below `2 ^ m2`. -/

/-- Peeling the LAST cell of a range map-sum (PhaseA owns the name). -/
theorem sumRangeSuccB (a : Nat → Nat) (k : Nat) :
    ((List.range (k + 1)).map a).sum = ((List.range k).map a).sum + a k := by
  rw [List.range_succ, List.map_append, List.map_singleton, List.sum_append,
    List.sum_singleton]

/-- Pointwise-smaller terms give a smaller range-sum. -/
theorem range_map_sum_le (c A : Nat → Nat) (k : Nat)
    (h : ∀ i, i < k → c i ≤ A i) :
    ((List.range k).map c).sum ≤ ((List.range k).map A).sum := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sumRangeSuccB c k, sumRangeSuccB A k]
    have h1 : c k ≤ A k := h k (by omega)
    have h2 := ih (fun i hi => h i (by omega))
    omega

/-- Peeling the FIRST cell of a range map-sum. -/
theorem sum_peel_first (F : Nat → Nat) (k : Nat) :
    ((List.range (k + 1)).map F).sum
      = F 0 + ((List.range k).map (fun i => F (i + 1))).sum := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sumRangeSuccB F (k + 1), ih, sumRangeSuccB (fun i => F (i + 1)) k]
    omega

/-- A range sum splits at `h`: the first `h` cells plus the shifted rest. -/
theorem sum_split_shift (a : Nat → Nat) (k h : Nat) :
    ((List.range (h + k)).map a).sum
      = ((List.range h).map a).sum
        + ((List.range k).map (fun i => a (h + i))).sum := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show h + (k + 1) = (h + k) + 1 from by omega,
      sumRangeSuccB a (h + k), ih, sumRangeSuccB (fun i => a (h + i)) k]
    omega

/-- Range sums are monotone in the range. -/
theorem range_sum_mono (a : Nat → Nat) (k n : Nat) (h : k ≤ n) :
    ((List.range k).map a).sum ≤ ((List.range n).map a).sum := by
  obtain ⟨m, rfl⟩ : ∃ m, n = k + m := ⟨n - k, by omega⟩
  rw [sum_split_shift a m k]
  omega

/-- Every half-sum of the first `k` values sits under their total
(PhaseB-local twin of PhaseA's `halfSumsLe`). -/
theorem halfSums_le (a : Nat → Nat) : ∀ (k v : Nat), v ∈ halfSums a k →
    v ≤ ((List.range k).map a).sum := by
  intro k
  induction k with
  | zero =>
    intro v hv
    rw [halfSums] at hv
    simp at hv
    subst hv
    simp
  | succ k ih =>
    intro v hv
    rw [halfSums, mem_mmerge] at hv
    rcases hv with h | h
    · have h1 := ih v h
      rw [sumRangeSuccB a k]
      omega
    · rw [List.mem_map] at h
      obtain ⟨y, hy, hyv⟩ := h
      have h1 := ih y hy
      rw [sumRangeSuccB a k]
      omega

/-- Every half-sum of the first `k` values sits under the full-range total
whenever `k ≤ n`. -/
theorem halfSums_le_total {a : Nat → Nat} {k n : Nat} (hkn : k ≤ n) (v : Nat)
    (hv : v ∈ halfSums a k) : v ≤ ((List.range n).map a).sum :=
  Nat.le_trans (halfSums_le a k v hv) (range_sum_mono a k n hkn)

/-- The second-half family's full sum sits under the total. -/
theorem shifted_le_total (a : Nat → Nat) {h m2 n : Nat} (hnm : h + m2 = n) :
    ((List.range m2).map (fun i => a (h + i))).sum ≤ ((List.range n).map a).sum := by
  rw [← hnm, sum_split_shift a m2 h]
  omega

/-- The candidate value for index `idx` over the second half: the choice
sum selected by `idx`'s bits, from round `j` up to `m2`. -/
def candSum (A : Nat → Nat) (idx j m2 : Nat) : Nat :=
  ((List.range (m2 - j)).map
    (fun i => if (idx / 2 ^ (i + j)) % 2 = 1 then A (i + j) else 0)).sum

theorem candSum_of_le {A : Nat → Nat} {idx j m2 : Nat} (h : m2 ≤ j) :
    candSum A idx j m2 = 0 := by
  have hj : m2 - j = 0 := by omega
  unfold candSum
  rw [hj]
  simp

theorem candSum_succ {A : Nat → Nat} {idx j m2 : Nat} (h : j < m2) :
    candSum A idx j m2
      = (if (idx / 2 ^ j) % 2 = 1 then A j else 0) + candSum A idx (j + 1) m2 := by
  have hj : m2 - j = (m2 - (j + 1)) + 1 := by omega
  unfold candSum
  rw [hj, sum_peel_first]
  have hmap : ((List.range (m2 - (j + 1))).map
      (fun i => if (idx / 2 ^ (i + 1 + j)) % 2 = 1 then A (i + 1 + j) else 0))
      = ((List.range (m2 - (j + 1))).map
        (fun i => if (idx / 2 ^ (i + (j + 1))) % 2 = 1 then A (i + (j + 1)) else 0)) :=
    List.map_congr_left fun i _ => by
      have hconv : i + 1 + j = i + (j + 1) := by omega
      rw [hconv]
  rw [hmap]
  have h0 : (if (idx / 2 ^ (0 + j)) % 2 = 1 then A (0 + j) else 0)
      = (if (idx / 2 ^ j) % 2 = 1 then A j else 0) := by
    rw [Nat.zero_add]
  rw [h0]

theorem candSum_le (A : Nat → Nat) (idx m2 : Nat) :
    candSum A idx 0 m2 ≤ ((List.range m2).map A).sum := by
  unfold candSum
  rw [Nat.sub_zero]
  refine range_map_sum_le _ _ _ ?_
  intro i _
  by_cases hb : (idx / 2 ^ i) % 2 = 1 <;> simp [hb]

theorem candSum_eq_choiceSum {A : Nat → Nat} {idx m2 : Nat} {S : Nat → Bool}
    (hS : ∀ i, i < m2 → (idx / 2 ^ i) % 2 = (if S i then 1 else 0)) :
    candSum A idx 0 m2 = choiceSum A S m2 := by
  unfold candSum choiceSum
  rw [Nat.sub_zero]
  refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
  simp only [Nat.add_zero]
  rw [hS i (List.mem_range.mp hi)]
  by_cases hb : S i <;> simp [hb]

/-- `candSum` IS a second-half subset sum, for every index. -/
theorem candSum_isSum (A : Nat → Nat) (idx m2 : Nat) :
    isSum A m2 (candSum A idx 0 m2) := by
  refine ⟨fun i => if i < m2 then decide ((idx / 2 ^ i) % 2 = 1) else false, ?_, ?_⟩
  · intro i hi
    simp only [if_neg (show ¬ i < m2 by omega)]
  · refine (candSum_eq_choiceSum (fun i hi => ?_)).symm
    have hmod := Nat.mod_two_eq_zero_or_one (idx / 2 ^ i)
    by_cases hb : (idx / 2 ^ i) % 2 = 1
    · simp [hi, hb]
    · simp [hi, hb]
      omega

/-- Adding a higher power of two splits cleanly under `/ 2 ^ j` (`j ≤ m`). -/
theorem add_pow_div {a j m : Nat} (hj : j ≤ m) :
    (a + 2 ^ m) / 2 ^ j = a / 2 ^ j + 2 ^ (m - j) := by
  have hp : j + (m - j) = m := by omega
  have hpow : 2 ^ j * 2 ^ (m - j) = 2 ^ m := by rw [← Nat.pow_add 2 j (m - j), hp]
  rw [← hpow]
  exact Nat.add_mul_div_left a (2 ^ (m - j)) (Nat.two_pow_pos j)

/-- Adding an even number preserves the low bit. -/
theorem add_even_mod_two (a e : Nat) : (a + 2 * e) % 2 = a % 2 :=
  Nat.add_mul_mod_self_left a 2 e

/-- Every eventually-false choice function is the bit-read of some index
below `2 ^ m`. -/
private def sMod (S : Nat → Bool) (m i : Nat) : Bool :=
  if i = m then false else S i

theorem realize_idx : ∀ (m : Nat) (S : Nat → Bool), (∀ i, m ≤ i → S i = false) →
    ∃ idx, idx < 2 ^ m ∧ ∀ j, j < m → (idx / 2 ^ j) % 2 = (if S j then 1 else 0) := by
  intro m
  induction m with
  | zero =>
    intro _ _
    refine ⟨0, by simp, ?_⟩
    intro j hj
    exact absurd hj (by omega)
  | succ m ih =>
    intro S hS
    have hS' : ∀ i, m ≤ i → sMod S m i = false := by
      intro i hi
      by_cases him : i = m
      · simp [sMod, him]
      · simp [sMod, him]
        exact hS i (by omega)
    obtain ⟨idx₀, hlt, hbits⟩ := ih (sMod S m) hS'
    have hbits' : ∀ j, j < m → (idx₀ / 2 ^ j) % 2 = (if S j then 1 else 0) := by
      intro j hj
      have hb := hbits j hj
      have hmodj : sMod S m j = S j := by
        by_cases h : j = m
        · exact absurd h (by omega)
        · simp [sMod, h]
      rw [hmodj] at hb
      exact hb
    by_cases hm : S m
    · refine ⟨idx₀ + 2 ^ m, by rw [Nat.pow_succ]; omega, ?_⟩
      intro j hj
      by_cases hjm : j < m
      · rw [add_pow_div (by omega : j ≤ m)]
        have hconv : 2 ^ (m - j) = 2 * 2 ^ (m - j - 1) := by
          have h1 : 2 ^ (m - j) = 2 ^ ((m - j - 1) + 1) := by
            congr 1
            omega
          rw [h1, Nat.pow_succ, Nat.mul_comm]
        rw [hconv, add_even_mod_two]
        exact hbits' j hjm
      · have hjm2 : m = j := by omega
        subst hjm2
        rw [add_pow_div (Nat.le_refl m), Nat.sub_self, Nat.pow_zero]
        have hz : idx₀ / 2 ^ m = 0 := Nat.div_eq_of_lt hlt
        rw [hz]
        simp [hm]
    · refine ⟨idx₀, by rw [Nat.pow_succ]; omega, ?_⟩
      intro j hj
      by_cases hjm : j < m
      · exact hbits' j hjm
      · have hjm2 : m = j := by omega
        subst hjm2
        have hz : idx₀ / 2 ^ m = 0 := Nat.div_eq_of_lt hlt
        rw [hz]
        simp [hm]

/-! ## §4. The wrapped-subtraction exec step

Pc 172 computes `c := t − s` in words; when `s ≤ t` the existing
`exec_sub_step` applies, but the candidate loop also visits sums `s > t`,
whose word is the wrapped complement `2^w − (s − t)` (never equal to a
half-sum by `wrapped_ne_of_le`). -/

/-- The word of a wrapped difference (`t < s`): `2^w − (s − t)`. -/
theorem bv_sub_w {w s t : Nat} (hs : s < 2 ^ w) (h : t < s) :
    BitVec.ofNat w t - BitVec.ofNat w s = BitVec.ofNat w (2 ^ w - (s - t)) := by
  have ht : t < 2 ^ w := by omega
  have hbound : 2 ^ w - (s - t) < 2 ^ w := by omega
  have houter : 2 ^ w - s + t < 2 ^ w := by omega
  rw [BitVec.toNat_eq, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt hs,
    Nat.mod_eq_of_lt houter, Nat.mod_eq_of_lt hbound]
  omega

/-- Wrapped `sub` step (`f j < f k`): cell `i` gets `2^w − (f k − f j)`. -/
theorem exec_sub_wrap_step {w : Nat} {P : List Instr} {ρ : Nat → BitVec w}
    {f : Nat → Nat} {S pc r : Nat} (hS : 0 < S)
    (h : P.getD pc Instr.reject = Instr.sub i j k)
    (hfit : ∀ x, f x < 2 ^ w) (hgt : f j < f k) :
    exec P ρ S pc r (memOf w f)
      = exec P ρ (S - 1) (pc + 1) r (memOf w (up f i (2 ^ w - (f k - f j)))) := by
  obtain ⟨t, rfl⟩ : ∃ t, S = t + 1 := ⟨S - 1, by omega⟩
  simp only [Nat.add_sub_cancel_right, exec, h]
  congr 1
  funext x
  by_cases hxi : x = i <;>
    simp [memOf, up, hxi, bv_sub_w (hfit k) hgt]

/-! ## §5. The Phase B driver (pc 148 → verdict)

The entry bridge (148–153) derives the loop constants; the candidate loop
(154–168) builds `s = candSum` of the current index over the second half;
the tail (169–174) loads `t`, forms the search target `cc := t − s`
(wrapped when `t < s` — never a spurious hit by `wrapped_ne_of_le`), and
the existing search lemmas (§2) drive to ACCEPT / the LNEXT fork.  The
driver below closes the loop: `exec = some (decide (isSum (instA x) n x.t))`
— the run's VALUE is the membership decision. -/

/-- The entry bridge (pcs 148–153, 6 steps): `L := 2^h` (cell 11),
`m2 := n − h` (cell 19), `CNT2 := 2^m2` (cell 22), `idx := 0` (cell 10);
everything at `q ≥ 23` — relocated input, `t`, both half-sum strips —
is untouched. -/
theorem pb_pre {w n : Nat} (ρ : Nat → BitVec w) {x : Instance n}
    (f : Nat → Nat) (S r : Nat)
    (hfit : ∀ q, f q < 2 ^ w)
    (h1 : f 1 = 1) (h2 : f 2 = 0) (h7 : f 7 = n) (h9 : f 9 = n / 2)
    (haddr : ∀ c, c ≤ 3 * n + 26 + 2 * 2 ^ (n / 2) → c < 2 ^ w)
    (hS : 6 ≤ S) :
    ∃ g, exec prog ρ S 148 r (memOf w f) = exec prog ρ (S - 6) 154 r (memOf w g) ∧
      g 1 = 1 ∧ g 2 = 0 ∧ g 7 = n ∧ g 8 = f 8 ∧ g 9 = n / 2 ∧
      g 10 = 0 ∧ g 11 = 2 ^ (n / 2) ∧ g 19 = n - n / 2 ∧
      g 22 = 2 ^ (n - n / 2) ∧
      g 18 = f 18 ∧ (∀ q, g q < 2 ^ w) ∧ (∀ q, 23 ≤ q → g q = f q) := by
  have hone : (1:Nat) ≤ 2 ^ (n / 2) := Nat.one_le_two_pow
  have h2h : 2 ^ (n / 2) < 2 ^ w := haddr _ (by omega)
  have hnm2 : n - n / 2 ≤ n / 2 + 1 := by omega
  have h2m2 : 2 ^ (n - n / 2) < 2 ^ w := by
    have hle := Nat.pow_le_pow_right (n := 2) (by omega) hnm2
    rw [Nat.pow_succ, Nat.mul_comm] at hle
    exact haddr _ (by omega)
  have e148 : f 1 + f 2 = 1 := by rw [h1, h2]
  have e149 : (up f 11 1) 11 * 2 ^ (up f 11 1) 9 = 2 ^ (n / 2) := by
    rw [up_eq, up_ne (show (9:Nat) ≠ 11 by omega), h9, Nat.one_mul]
  have hle150 : (up (up f 11 1) 11 (2 ^ (n / 2))) 9
      ≤ (up (up f 11 1) 11 (2 ^ (n / 2))) 7 := by
    rw [up_ne (show (9:Nat) ≠ 11 by omega), up_ne (show (7:Nat) ≠ 11 by omega),
      up_ne (show (9:Nat) ≠ 11 by omega), up_ne (show (7:Nat) ≠ 11 by omega),
      h9, h7]
    exact Nat.div_le_self n 2
  have e150 : (up (up f 11 1) 11 (2 ^ (n / 2))) 7
      - (up (up f 11 1) 11 (2 ^ (n / 2))) 9 = n - n / 2 := by
    rw [up_ne (show (7:Nat) ≠ 11 by omega), up_ne (show (9:Nat) ≠ 11 by omega),
      up_ne (show (7:Nat) ≠ 11 by omega), up_ne (show (9:Nat) ≠ 11 by omega),
      h7, h9]
  have e151 : (up (up (up f 11 1) 11 (2 ^ (n / 2))) 19 (n - n / 2)) 1
      + (up (up (up f 11 1) 11 (2 ^ (n / 2))) 19 (n - n / 2)) 2 = 1 := by
    rw [up_ne (show (1:Nat) ≠ 19 by omega), up_ne (show (2:Nat) ≠ 19 by omega),
      up_ne (show (1:Nat) ≠ 11 by omega), up_ne (show (2:Nat) ≠ 11 by omega),
      up_ne (show (1:Nat) ≠ 11 by omega), up_ne (show (2:Nat) ≠ 11 by omega), h1, h2]
  have e152 : (up (up (up (up f 11 1) 11 (2 ^ (n / 2))) 19 (n - n / 2)) 22 1) 22
      * 2 ^ (up (up (up (up f 11 1) 11 (2 ^ (n / 2))) 19 (n - n / 2)) 22 1) 19
      = 2 ^ (n - n / 2) := by
    rw [up_eq, up_ne (show (19:Nat) ≠ 22 by omega),
      up_eq, Nat.one_mul]
  have fS0 : ∀ q, (up f 11 1) q < 2 ^ w := fit_up hfit (by omega)
  have fS1 : ∀ q, (up (up f 11 1) 11 (2 ^ (n / 2))) q < 2 ^ w := fit_up fS0 h2h
  have fS2 : ∀ q, (up (up (up f 11 1) 11 (2 ^ (n / 2))) 19 (n - n / 2)) q < 2 ^ w :=
    fit_up fS1 (haddr _ (by omega))
  have fS3 : ∀ q,
      (up (up (up (up f 11 1) 11 (2 ^ (n / 2))) 19 (n - n / 2)) 22 1) q < 2 ^ w :=
    fit_up fS2 (by omega)
  have fS4 : ∀ q,
      (up (up (up (up (up f 11 1) 11 (2 ^ (n / 2))) 19 (n - n / 2)) 22 1) 22
        (2 ^ (n - n / 2))) q < 2 ^ w := fit_up fS3 h2m2
  have key : ∀ q, q ≠ 10 → q ≠ 11 → q ≠ 19 → q ≠ 22 →
      (up (up (up (up (up (up f 11 1) 11 (2 ^ (n / 2))) 19 (n - n / 2)) 22 1) 22
        (2 ^ (n - n / 2))) 10 0) q = f q := by
    intro q h10 h11 h19 h22
    rw [up_ne h10, up_ne h22, up_ne h22, up_ne h19, up_ne h11, up_ne h11]
  refine ⟨up (up (up (up (up (up f 11 1) 11 (2 ^ (n / 2))) 19 (n - n / 2)) 22 1) 22
      (2 ^ (n - n / 2))) 10 0,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [exec_add_step (by omega)
        (show prog.getD 148 Instr.reject = Instr.add 11 1 2 by rfl), e148,
      exec_shl_step (by omega)
        (show prog.getD 149 Instr.reject = Instr.shl 11 11 9 by rfl) fS0
        (by rw [e149]; exact h2h), e149,
      exec_sub_step (by omega)
        (show prog.getD 150 Instr.reject = Instr.sub 19 7 9 by rfl) fS1 hle150, e150,
      exec_add_step (by omega)
        (show prog.getD 151 Instr.reject = Instr.add 22 1 2 by rfl), e151,
      exec_shl_step (by omega)
        (show prog.getD 152 Instr.reject = Instr.shl 22 22 19 by rfl) fS3
        (by rw [e152]; exact h2m2), e152,
      exec_sub_step (by omega)
        (show prog.getD 153 Instr.reject = Instr.sub 10 10 10 by rfl) fS4
        (Nat.le_refl _)]
    simp only [Nat.sub_sub, Nat.reduceAdd, Nat.sub_self]
  · exact (key 1 (by omega) (by omega) (by omega) (by omega)).trans h1
  · exact (key 2 (by omega) (by omega) (by omega) (by omega)).trans h2
  · exact (key 7 (by omega) (by omega) (by omega) (by omega)).trans h7
  · exact key 8 (by omega) (by omega) (by omega) (by omega)
  · exact (key 9 (by omega) (by omega) (by omega) (by omega)).trans h9
  · exact up_eq _ _ _
  · rw [up_ne (show (11:Nat) ≠ 10 by omega), up_ne (show (11:Nat) ≠ 22 by omega),
      up_ne (show (11:Nat) ≠ 22 by omega), up_ne (show (11:Nat) ≠ 19 by omega),
      up_eq]
  · rw [up_ne (show (19:Nat) ≠ 10 by omega), up_ne (show (19:Nat) ≠ 22 by omega),
      up_ne (show (19:Nat) ≠ 22 by omega), up_eq]
  · rw [up_ne (show (22:Nat) ≠ 10 by omega), up_eq]
  · exact key 18 (by omega) (by omega) (by omega) (by omega)
  · exact fit_up fS4 (by omega)
  · intro q hq
    exact key q (by omega) (by omega) (by omega) (by omega)

/-- THE candidate loop (pcs 156–168): from the inner guard with
`j = f 13` and partial sum `s = f 14`, walk to pc 169 with
`f' 14 = s + candSum (fun i => instA x (n / 2 + i)) idx j m2` — the
second-half choice sum selected by `idx`'s bits from round `j` on.
Each round costs 11 steps; the exhausted exit costs 2.  The partial
sum stays under the second-half total (`hv`, `hT`) — that is what keeps
cell 14 fitting after the `add` at 166. -/
theorem cand_exec {w n : Nat} (ρ : Nat → BitVec w) {x : Instance n} :
    ∀ (F j m2 idx s : Nat) (f : Nat → Nat) (S r : Nat),
    f 1 = 1 → f 2 = 0 → f 8 = 2 * n + 23 → f 9 = n / 2 → f 10 = idx →
    f 13 = j → f 14 = s → f 19 = m2 →
    j ≤ m2 → n / 2 + m2 = n →
    (∀ i, 1 ≤ i → i ≤ n → f (2 * n + 23 + i) = instA x (i - 1)) →
    (∀ q, f q < 2 ^ w) →
    (∀ c, c ≤ 3 * n + 26 + 2 * 2 ^ (n / 2) → c < 2 ^ w) →
    s ≤ ((List.range j).map (fun i => instA x (n / 2 + i))).sum →
    ((List.range m2).map (fun i => instA x (n / 2 + i))).sum < 2 ^ w →
    m2 - j ≤ F → 11 * (m2 - j) + 2 ≤ S →
    ∃ c f', c ≤ 11 * (m2 - j) + 2 ∧
      exec prog ρ S 156 r (memOf w f) = exec prog ρ (S - c) 169 r (memOf w f') ∧
      f' 14 = s + candSum (fun i => instA x (n / 2 + i)) idx j m2 ∧
      f' 1 = 1 ∧ f' 2 = 0 ∧ f' 10 = idx ∧
      (∀ q, f' q < 2 ^ w) ∧
      (∀ q, q ≠ 13 → q ≠ 14 → q ≠ 17 → q ≠ 20 → q ≠ 21 → f' q = f q) := by
  intro F
  induction F with
  | zero =>
    intro j m2 idx s f S r hf1 hf2 hf8 hf9 hf10 hf13 hf14 hf19 hjm hmn hrel hfit
      haddr hv hT hfuel hS
    refine ⟨2, f, by omega, ?_, by rw [← hf14, candSum_of_le (show m2 ≤ j by omega),
      Nat.add_zero], hf1, hf2, hf10, hfit, fun q _ _ _ _ _ => rfl⟩
    rw [exec_blt_ge_step (by omega)
        (show prog.getD 156 Instr.reject = Instr.blt 13 19 158 by rfl) hfit
        (by rw [hf13, hf19]; omega),
      exec_blt_lt_step (by omega)
        (show prog.getD 157 Instr.reject = Instr.blt 2 1 169 by rfl) hfit
        (by rw [hf2, hf1]; omega)]
    simp only [Nat.sub_sub, Nat.reduceAdd]
  | succ F ih =>
    intro j m2 idx s f S r hf1 hf2 hf8 hf9 hf10 hf13 hf14 hf19 hjm hmn hrel hfit
      haddr hv hT hfuel hS
    by_cases hjm2 : j < m2
    · -- the common 7-step prefix 156 → 164
      -- the loaded value fits (it is a memory cell)
      have hVfit : instA x (n / 2 + j) < 2 ^ w := by
        have h1 := hrel (n / 2 + 1 + j) (by omega) (by omega)
        have h2 := hfit (2 * n + 23 + (n / 2 + 1 + j))
        rw [h1, show n / 2 + 1 + j - 1 = n / 2 + j from by omega] at h2
        exact h2
      have e158 : f 8 + f 9 = 2 * n + 23 + n / 2 := by rw [hf8, hf9]
      have e159 : (up f 20 (2 * n + 23 + n / 2)) 20
          + (up f 20 (2 * n + 23 + n / 2)) 1 = 2 * n + 23 + n / 2 + 1 := by
        rw [up_eq, up_ne (show (1:Nat) ≠ 20 by omega), hf1]
      have e160 : (up (up f 20 (2 * n + 23 + n / 2)) 20 (2 * n + 23 + n / 2 + 1)) 20
          + (up (up f 20 (2 * n + 23 + n / 2)) 20 (2 * n + 23 + n / 2 + 1)) 13
          = 2 * n + 23 + n / 2 + 1 + j := by
        rw [up_eq, up_ne (show (13:Nat) ≠ 20 by omega),
          up_ne (show (13:Nat) ≠ 20 by omega), hf13]
      have hB3 : 2 * n + 23 + n / 2 + 1 + j ≠ 20 := by omega
      have e161 : (up (up (up f 20 (2 * n + 23 + n / 2)) 20 (2 * n + 23 + n / 2 + 1))
            20 (2 * n + 23 + n / 2 + 1 + j))
          ((up (up (up f 20 (2 * n + 23 + n / 2)) 20 (2 * n + 23 + n / 2 + 1))
            20 (2 * n + 23 + n / 2 + 1 + j)) 20)
          = instA x (n / 2 + j) := by
        rw [up_eq, up_ne hB3, up_ne hB3, up_ne hB3]
        have hAeq : 2 * n + 23 + n / 2 + 1 + j = 2 * n + 23 + (n / 2 + 1 + j) := by
          omega
        rw [hAeq, hrel (n / 2 + 1 + j) (by omega) (by omega)]
        congr 1
        omega
      have e162 : (up (up (up (up f 20 (2 * n + 23 + n / 2)) 20 (2 * n + 23 + n / 2
                + 1)) 20 (2 * n + 23 + n / 2 + 1 + j)) 17 (instA x (n / 2 + j))) 10
          / 2 ^ (up (up (up (up f 20 (2 * n + 23 + n / 2)) 20 (2 * n + 23 + n / 2
                + 1)) 20 (2 * n + 23 + n / 2 + 1 + j)) 17 (instA x (n / 2 + j))) 13
          = idx / 2 ^ j := by
        rw [up_ne (show (10:Nat) ≠ 17 by omega), up_ne (show (13:Nat) ≠ 17 by omega),
          up_ne (show (10:Nat) ≠ 20 by omega), up_ne (show (13:Nat) ≠ 20 by omega),
          up_ne (show (10:Nat) ≠ 20 by omega), up_ne (show (13:Nat) ≠ 20 by omega),
          up_ne (show (10:Nat) ≠ 20 by omega), up_ne (show (13:Nat) ≠ 20 by omega),
          hf10, hf13]
      have fA1 : ∀ q, (up f 20 (2 * n + 23 + n / 2)) q < 2 ^ w :=
        fit_up hfit (haddr _ (by omega))
      have fA2 : ∀ q, (up (up f 20 (2 * n + 23 + n / 2)) 20 (2 * n + 23 + n / 2 + 1))
          q < 2 ^ w := fit_up fA1 (haddr _ (by omega))
      have fA3 : ∀ q, (up (up (up f 20 (2 * n + 23 + n / 2)) 20 (2 * n + 23 + n / 2
          + 1)) 20 (2 * n + 23 + n / 2 + 1 + j)) q < 2 ^ w :=
        fit_up fA2 (haddr _ (by omega))
      have fA4 : ∀ q, (up (up (up (up f 20 (2 * n + 23 + n / 2)) 20 (2 * n + 23
          + n / 2 + 1)) 20 (2 * n + 23 + n / 2 + 1 + j)) 17 (instA x (n / 2 + j))) q
          < 2 ^ w := fit_up fA3 hVfit
      have h10lt := hfit 10
      rw [hf10] at h10lt
      have hdiv := Nat.div_le_self idx (2 ^ j)
      have h1lt := hfit 1
      rw [hf1] at h1lt
      have hmod := Nat.mod_lt (idx / 2 ^ j) (show 0 < 2 by decide)
      have fA5 : ∀ q, (up (up (up (up (up f 20 (2 * n + 23 + n / 2)) 20 (2 * n + 23
          + n / 2 + 1)) 20 (2 * n + 23 + n / 2 + 1 + j)) 17 (instA x (n / 2 + j)))
          21 (idx / 2 ^ j)) q < 2 ^ w :=
        fit_up fA4 (by omega)
      have fG : ∀ q, (up (up (up (up (up (up f 20 (2 * n + 23 + n / 2)) 20 (2 * n
          + 23 + n / 2 + 1)) 20 (2 * n + 23 + n / 2 + 1 + j)) 17 (instA x (n / 2
          + j))) 21 (idx / 2 ^ j)) 21 ((idx / 2 ^ j) % 2)) q < 2 ^ w :=
        fit_up fA5 (by omega)
      have hw1 : 1 ≤ w := by
        have h1lt : f 1 < 2 ^ w := hfit 1
        rw [hf1] at h1lt
        cases w with
        | zero => simp at h1lt
        | succ w' => omega
      have hpref : exec prog ρ S 156 r (memOf w f)
          = exec prog ρ (S - 7) 164 r (memOf w
              (up (up (up (up (up (up f 20 (2 * n + 23 + n / 2)) 20 (2 * n + 23 + n
                / 2 + 1)) 20 (2 * n + 23 + n / 2 + 1 + j)) 17 (instA x (n / 2 + j)))
                21 (idx / 2 ^ j)) 21 ((idx / 2 ^ j) % 2))) := by
        rw [exec_blt_lt_step (by omega)
            (show prog.getD 156 Instr.reject = Instr.blt 13 19 158 by rfl) hfit
            (by rw [hf13, hf19]; omega),
          exec_add_step (by omega)
            (show prog.getD 158 Instr.reject = Instr.add 20 8 9 by rfl), e158,
          exec_add_step (by omega)
            (show prog.getD 159 Instr.reject = Instr.add 20 20 1 by rfl), e159,
          exec_add_step (by omega)
            (show prog.getD 160 Instr.reject = Instr.add 20 20 13 by rfl), e160,
          exec_load_step (by omega)
            (show prog.getD 161 Instr.reject = Instr.load 17 20 by rfl) fA3, e161,
          exec_shr_step (by omega)
            (show prog.getD 162 Instr.reject = Instr.shr 21 10 13 by rfl) fA4, e162,
          exec_and1_step (by omega) hw1
            (show prog.getD 163 Instr.reject = Instr.and 21 21 1 by rfl)
            (by rw [up_ne (show (1:Nat) ≠ 21 by omega),
              up_ne (show (1:Nat) ≠ 17 by omega),
              up_ne (show (1:Nat) ≠ 20 by omega), up_ne (show (1:Nat) ≠ 20 by omega),
              up_ne (show (1:Nat) ≠ 20 by omega), hf1]) fA5]
        rw [up_eq (up (up (up (up f 20 (2 * n + 23 + n / 2)) 20 (2 * n + 23 + n / 2
          + 1)) 20 (2 * n + 23 + n / 2 + 1 + j)) 17 (instA x (n / 2 + j))) 21
          (idx / 2 ^ j)]
        simp only [Nat.sub_sub, Nat.reduceAdd]
      -- the second-half total and its peels
      have hRS : ((List.range (j + 1)).map (fun i => instA x (n / 2 + i))).sum
          = ((List.range j).map (fun i => instA x (n / 2 + i))).sum
            + instA x (n / 2 + j) := sumRangeSuccB _ j
      have hRM := range_sum_mono (fun i => instA x (n / 2 + i)) (j + 1) m2 (by omega)
      have hRM0 := range_sum_mono (fun i => instA x (n / 2 + i)) j (j + 1) (by omega)
      -- the fit of the post-add state (bit = 1)
      have hSV : s + instA x (n / 2 + j) < 2 ^ w := by omega
      have hnw : n < 2 ^ w := by have h8lt := hfit 8; rw [hf8] at h8lt; omega
      -- the common recursion tail
      have hsplit : 11 * (m2 - j) = 11 * (m2 - (j + 1)) + 11 := by
        have hj : m2 - j = (m2 - (j + 1)) + 1 := by omega
        rw [hj, Nat.mul_add, Nat.mul_one]
      have hrest : ∀ (u : Nat → Nat),
          u 1 = 1 → u 2 = 0 → u 8 = 2 * n + 23 → u 9 = n / 2 → u 10 = idx →
          u 13 = j + 1 → u 19 = m2 → (∀ q, u q < 2 ^ w) →
          (u 14 ≤ ((List.range (j + 1)).map (fun i => instA x (n / 2 + i))).sum) →
          (u 14 + candSum (fun i => instA x (n / 2 + i)) idx (j + 1) m2
            = s + candSum (fun i => instA x (n / 2 + i)) idx j m2) →
          (∀ q, q ≠ 13 → q ≠ 14 → q ≠ 17 → q ≠ 20 → q ≠ 21 → u q = f q) →
          (exec prog ρ S 156 r (memOf w f)
            = exec prog ρ (S - 11) 156 r (memOf w u)) →
          ∃ c f', c ≤ 11 * (m2 - j) + 2 ∧
            exec prog ρ S 156 r (memOf w f)
              = exec prog ρ (S - c) 169 r (memOf w f') ∧
            f' 14 = s + candSum (fun i => instA x (n / 2 + i)) idx j m2 ∧
            f' 1 = 1 ∧ f' 2 = 0 ∧ f' 10 = idx ∧
            (∀ q, f' q < 2 ^ w) ∧
            (∀ q, q ≠ 13 → q ≠ 14 → q ≠ 17 → q ≠ 20 → q ≠ 21 → f' q = f q) := by
        intro u hu1 hu2 hu8 hu9 hu10 hu13 hu19 hufit hvb hval hupres hexec
        have hrel' : ∀ i, 1 ≤ i → i ≤ n → u (2 * n + 23 + i) = instA x (i - 1) := by
          intro i hi1 hin
          rw [hupres (2 * n + 23 + i) (by omega) (by omega) (by omega) (by omega)
            (by omega)]
          exact hrel i hi1 hin
        obtain ⟨c', f', hc', hex', hf'14, hf'1, hf'2, hf'10, hf'fit, hf'pres⟩ :=
          ih (j + 1) m2 idx (u 14) u (S - 11) r hu1 hu2 hu8 hu9 hu10
            hu13 rfl hu19 (by omega) hmn hrel' hufit haddr hvb hT
            (by omega) (by omega)
        refine ⟨11 + c', f', ?_, ?_, ?_, hf'1, hf'2, hf'10, hf'fit, ?_⟩
        · omega
        · rw [hexec, hex', show S - 11 - c' = S - (11 + c') from by omega]
        · exact hf'14.trans hval
        · intro q h13 h14 h17 h20 h21
          exact (hf'pres q h13 h14 h17 h20 h21).trans (hupres q h13 h14 h17 h20 h21)
      -- the two bit branches
      rcases Nat.mod_two_eq_zero_or_one (idx / 2 ^ j) with hb | hb
      · -- bit = 0: 164 falls through, 165 → 167 (no add), loop
        refine hrest (up (up (up (up (up (up (up f 20 (2 * n + 23 + n / 2)) 20
              (2 * n + 23 + n / 2 + 1)) 20 (2 * n + 23 + n / 2 + 1 + j))
              17 (instA x (n / 2 + j))) 21 (idx / 2 ^ j)) 21 ((idx / 2 ^ j) % 2))
            13 (j + 1)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · rw [up_ne (show (1:Nat) ≠ 13 by omega), up_ne (show (1:Nat) ≠ 21 by omega),
            up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (1:Nat) ≠ 17 by omega),
            up_ne (show (1:Nat) ≠ 20 by omega), up_ne (show (1:Nat) ≠ 20 by omega),
            up_ne (show (1:Nat) ≠ 20 by omega)]
          exact hf1
        · rw [up_ne (show (2:Nat) ≠ 13 by omega), up_ne (show (2:Nat) ≠ 21 by omega),
            up_ne (show (2:Nat) ≠ 21 by omega), up_ne (show (2:Nat) ≠ 17 by omega),
            up_ne (show (2:Nat) ≠ 20 by omega), up_ne (show (2:Nat) ≠ 20 by omega),
            up_ne (show (2:Nat) ≠ 20 by omega)]
          exact hf2
        · rw [up_ne (show (8:Nat) ≠ 13 by omega), up_ne (show (8:Nat) ≠ 21 by omega),
            up_ne (show (8:Nat) ≠ 21 by omega), up_ne (show (8:Nat) ≠ 17 by omega),
            up_ne (show (8:Nat) ≠ 20 by omega), up_ne (show (8:Nat) ≠ 20 by omega),
            up_ne (show (8:Nat) ≠ 20 by omega)]
          exact hf8
        · rw [up_ne (show (9:Nat) ≠ 13 by omega), up_ne (show (9:Nat) ≠ 21 by omega),
            up_ne (show (9:Nat) ≠ 21 by omega), up_ne (show (9:Nat) ≠ 17 by omega),
            up_ne (show (9:Nat) ≠ 20 by omega), up_ne (show (9:Nat) ≠ 20 by omega),
            up_ne (show (9:Nat) ≠ 20 by omega)]
          exact hf9
        · rw [up_ne (show (10:Nat) ≠ 13 by omega), up_ne (show (10:Nat) ≠ 21 by omega),
            up_ne (show (10:Nat) ≠ 21 by omega), up_ne (show (10:Nat) ≠ 17 by omega),
            up_ne (show (10:Nat) ≠ 20 by omega), up_ne (show (10:Nat) ≠ 20 by omega),
            up_ne (show (10:Nat) ≠ 20 by omega)]
          exact hf10
        · exact up_eq _ _ _
        · rw [up_ne (show (19:Nat) ≠ 13 by omega), up_ne (show (19:Nat) ≠ 21 by omega),
            up_ne (show (19:Nat) ≠ 21 by omega), up_ne (show (19:Nat) ≠ 17 by omega),
            up_ne (show (19:Nat) ≠ 20 by omega), up_ne (show (19:Nat) ≠ 20 by omega),
            up_ne (show (19:Nat) ≠ 20 by omega)]
          exact hf19
        · exact fit_up fG (by omega)
        · rw [up_ne (show (14:Nat) ≠ 13 by omega), up_ne (show (14:Nat) ≠ 21 by omega),
            up_ne (show (14:Nat) ≠ 21 by omega), up_ne (show (14:Nat) ≠ 17 by omega),
            up_ne (show (14:Nat) ≠ 20 by omega), up_ne (show (14:Nat) ≠ 20 by omega),
            up_ne (show (14:Nat) ≠ 20 by omega), hf14]
          omega
        · rw [up_ne (show (14:Nat) ≠ 13 by omega), up_ne (show (14:Nat) ≠ 21 by omega),
            up_ne (show (14:Nat) ≠ 21 by omega), up_ne (show (14:Nat) ≠ 17 by omega),
            up_ne (show (14:Nat) ≠ 20 by omega), up_ne (show (14:Nat) ≠ 20 by omega),
            up_ne (show (14:Nat) ≠ 20 by omega), hf14, candSum_succ hjm2,
            if_neg (show ¬ (idx / 2 ^ j) % 2 = 1 by omega)]
          omega
        · intro q h13 h14 h17 h20 h21
          rw [up_ne (show q ≠ 13 by omega), up_ne (show q ≠ 21 by omega),
            up_ne (show q ≠ 21 by omega), up_ne (show q ≠ 17 by omega),
            up_ne (show q ≠ 20 by omega), up_ne (show q ≠ 20 by omega),
            up_ne (show q ≠ 20 by omega)]
        · rw [hpref, exec_blt_ge_step (by omega)
            (show prog.getD 164 Instr.reject = Instr.blt 2 21 166 by rfl) fG
            (by rw [up_ne (show (2:Nat) ≠ 21 by omega),
              up_ne (show (2:Nat) ≠ 21 by omega), up_ne (show (2:Nat) ≠ 17 by omega),
              up_ne (show (2:Nat) ≠ 20 by omega), up_ne (show (2:Nat) ≠ 20 by omega),
              up_ne (show (2:Nat) ≠ 20 by omega), hf2, up_eq, hb]; omega),
          exec_blt_lt_step (by omega)
            (show prog.getD 165 Instr.reject = Instr.blt 2 1 167 by rfl) fG
            (by rw [up_ne (show (2:Nat) ≠ 21 by omega),
              up_ne (show (2:Nat) ≠ 21 by omega), up_ne (show (2:Nat) ≠ 17 by omega),
              up_ne (show (2:Nat) ≠ 20 by omega), up_ne (show (2:Nat) ≠ 20 by omega),
              up_ne (show (2:Nat) ≠ 20 by omega),
              up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (1:Nat) ≠ 21 by omega),
              up_ne (show (1:Nat) ≠ 17 by omega), up_ne (show (1:Nat) ≠ 20 by omega),
              up_ne (show (1:Nat) ≠ 20 by omega), up_ne (show (1:Nat) ≠ 20 by omega),
              hf2, hf1]; omega),
          exec_add_step (by omega)
            (show prog.getD 167 Instr.reject = Instr.add 13 13 1 by rfl)]
          rw [show (up (up (up (up (up (up f 20 (2 * n + 23 + n / 2)) 20 (2 * n + 23
                + n / 2 + 1)) 20 (2 * n + 23 + n / 2 + 1 + j)) 17 (instA x (n / 2
                + j))) 21 (idx / 2 ^ j)) 21 ((idx / 2 ^ j) % 2)) 13
              + (up (up (up (up (up (up f 20 (2 * n + 23 + n / 2)) 20 (2 * n + 23
                + n / 2 + 1)) 20 (2 * n + 23 + n / 2 + 1 + j)) 17 (instA x (n / 2
                + j))) 21 (idx / 2 ^ j)) 21 ((idx / 2 ^ j) % 2)) 1
              = j + 1 from by
            rw [up_ne (show (13:Nat) ≠ 21 by omega),
              up_ne (show (13:Nat) ≠ 21 by omega), up_ne (show (13:Nat) ≠ 17 by omega),
              up_ne (show (13:Nat) ≠ 20 by omega), up_ne (show (13:Nat) ≠ 20 by omega),
              up_ne (show (13:Nat) ≠ 20 by omega), hf13,
              up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (1:Nat) ≠ 21 by omega),
              up_ne (show (1:Nat) ≠ 17 by omega), up_ne (show (1:Nat) ≠ 20 by omega),
              up_ne (show (1:Nat) ≠ 20 by omega), up_ne (show (1:Nat) ≠ 20 by omega),
              hf1]]
          rw [exec_blt_lt_step (by omega)
            (show prog.getD 168 Instr.reject = Instr.blt 2 1 156 by rfl)
            (fit_up fG (by omega))
            (by rw [up_ne (show (2:Nat) ≠ 13 by omega),
              up_ne (show (2:Nat) ≠ 21 by omega), up_ne (show (2:Nat) ≠ 21 by omega),
              up_ne (show (2:Nat) ≠ 17 by omega), up_ne (show (2:Nat) ≠ 20 by omega),
              up_ne (show (2:Nat) ≠ 20 by omega), up_ne (show (2:Nat) ≠ 20 by omega),
              up_ne (show (1:Nat) ≠ 13 by omega), up_ne (show (1:Nat) ≠ 21 by omega),
              up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (1:Nat) ≠ 17 by omega),
              up_ne (show (1:Nat) ≠ 20 by omega), up_ne (show (1:Nat) ≠ 20 by omega),
              up_ne (show (1:Nat) ≠ 20 by omega), hf2, hf1]; omega)]
          simp only [Nat.sub_sub, Nat.reduceAdd]
      · -- bit = 1: 164 → 166 (s += v), 167 (j++), loop
        refine hrest (up (up (up (up (up (up (up (up f 20 (2 * n + 23 + n / 2)) 20
              (2 * n + 23 + n / 2 + 1)) 20 (2 * n + 23 + n / 2 + 1 + j))
              17 (instA x (n / 2 + j))) 21 (idx / 2 ^ j)) 21 ((idx / 2 ^ j) % 2))
              14 (s + instA x (n / 2 + j))) 13 (j + 1)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          ?_ ?_ ?_
        · rw [up_ne (show (1:Nat) ≠ 13 by omega), up_ne (show (1:Nat) ≠ 14 by omega),
            up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (1:Nat) ≠ 21 by omega),
            up_ne (show (1:Nat) ≠ 17 by omega), up_ne (show (1:Nat) ≠ 20 by omega),
            up_ne (show (1:Nat) ≠ 20 by omega), up_ne (show (1:Nat) ≠ 20 by omega)]
          exact hf1
        · rw [up_ne (show (2:Nat) ≠ 13 by omega), up_ne (show (2:Nat) ≠ 14 by omega),
            up_ne (show (2:Nat) ≠ 21 by omega), up_ne (show (2:Nat) ≠ 21 by omega),
            up_ne (show (2:Nat) ≠ 17 by omega), up_ne (show (2:Nat) ≠ 20 by omega),
            up_ne (show (2:Nat) ≠ 20 by omega), up_ne (show (2:Nat) ≠ 20 by omega)]
          exact hf2
        · rw [up_ne (show (8:Nat) ≠ 13 by omega), up_ne (show (8:Nat) ≠ 14 by omega),
            up_ne (show (8:Nat) ≠ 21 by omega), up_ne (show (8:Nat) ≠ 21 by omega),
            up_ne (show (8:Nat) ≠ 17 by omega), up_ne (show (8:Nat) ≠ 20 by omega),
            up_ne (show (8:Nat) ≠ 20 by omega), up_ne (show (8:Nat) ≠ 20 by omega)]
          exact hf8
        · rw [up_ne (show (9:Nat) ≠ 13 by omega), up_ne (show (9:Nat) ≠ 14 by omega),
            up_ne (show (9:Nat) ≠ 21 by omega), up_ne (show (9:Nat) ≠ 21 by omega),
            up_ne (show (9:Nat) ≠ 17 by omega), up_ne (show (9:Nat) ≠ 20 by omega),
            up_ne (show (9:Nat) ≠ 20 by omega), up_ne (show (9:Nat) ≠ 20 by omega)]
          exact hf9
        · rw [up_ne (show (10:Nat) ≠ 13 by omega), up_ne (show (10:Nat) ≠ 14 by omega),
            up_ne (show (10:Nat) ≠ 21 by omega), up_ne (show (10:Nat) ≠ 21 by omega),
            up_ne (show (10:Nat) ≠ 17 by omega), up_ne (show (10:Nat) ≠ 20 by omega),
            up_ne (show (10:Nat) ≠ 20 by omega), up_ne (show (10:Nat) ≠ 20 by omega)]
          exact hf10
        · exact up_eq _ _ _
        · rw [up_ne (show (19:Nat) ≠ 13 by omega), up_ne (show (19:Nat) ≠ 14 by omega),
            up_ne (show (19:Nat) ≠ 21 by omega), up_ne (show (19:Nat) ≠ 21 by omega),
            up_ne (show (19:Nat) ≠ 17 by omega), up_ne (show (19:Nat) ≠ 20 by omega),
            up_ne (show (19:Nat) ≠ 20 by omega), up_ne (show (19:Nat) ≠ 20 by omega)]
          exact hf19
        · exact fit_up (fit_up fG hSV) (by omega)
        · rw [up_ne (show (14:Nat) ≠ 13 by omega), up_eq]
          omega
        · rw [up_ne (show (14:Nat) ≠ 13 by omega), up_eq, candSum_succ hjm2,
            if_pos hb]
          omega
        · intro q h13 h14 h17 h20 h21
          rw [up_ne (show q ≠ 13 by omega), up_ne (show q ≠ 14 by omega),
            up_ne (show q ≠ 21 by omega), up_ne (show q ≠ 21 by omega),
            up_ne (show q ≠ 17 by omega), up_ne (show q ≠ 20 by omega),
            up_ne (show q ≠ 20 by omega), up_ne (show q ≠ 20 by omega)]
        · rw [hpref, exec_blt_lt_step (by omega)
            (show prog.getD 164 Instr.reject = Instr.blt 2 21 166 by rfl) fG
            (by rw [up_ne (show (2:Nat) ≠ 21 by omega),
              up_ne (show (2:Nat) ≠ 21 by omega), up_ne (show (2:Nat) ≠ 17 by omega),
              up_ne (show (2:Nat) ≠ 20 by omega), up_ne (show (2:Nat) ≠ 20 by omega),
              up_ne (show (2:Nat) ≠ 20 by omega), hf2, up_eq, hb]; omega),
          exec_add_step (by omega)
            (show prog.getD 166 Instr.reject = Instr.add 14 14 17 by rfl)]
          rw [show (up (up (up (up (up (up f 20 (2 * n + 23 + n / 2)) 20 (2 * n + 23
                + n / 2 + 1)) 20 (2 * n + 23 + n / 2 + 1 + j)) 17 (instA x (n / 2
                + j))) 21 (idx / 2 ^ j)) 21 ((idx / 2 ^ j) % 2)) 14
              + (up (up (up (up (up (up f 20 (2 * n + 23 + n / 2)) 20 (2 * n + 23
                + n / 2 + 1)) 20 (2 * n + 23 + n / 2 + 1 + j)) 17 (instA x (n / 2
                + j))) 21 (idx / 2 ^ j)) 21 ((idx / 2 ^ j) % 2)) 17
              = s + instA x (n / 2 + j) from by
            rw [up_ne (show (14:Nat) ≠ 21 by omega),
              up_ne (show (14:Nat) ≠ 21 by omega), up_ne (show (14:Nat) ≠ 17 by omega),
              up_ne (show (14:Nat) ≠ 20 by omega), up_ne (show (14:Nat) ≠ 20 by omega),
              up_ne (show (14:Nat) ≠ 20 by omega), hf14,
              up_ne (show (17:Nat) ≠ 21 by omega), up_ne (show (17:Nat) ≠ 21 by omega),
              up_eq]]
          rw [exec_add_step (by omega)
            (show prog.getD 167 Instr.reject = Instr.add 13 13 1 by rfl)]
          rw [show (up (up (up (up (up (up (up f 20 (2 * n + 23 + n / 2)) 20 (2 * n
                + 23 + n / 2 + 1)) 20 (2 * n + 23 + n / 2 + 1 + j)) 17 (instA x
                (n / 2 + j))) 21 (idx / 2 ^ j)) 21 ((idx / 2 ^ j) % 2)) 14
                (s + instA x (n / 2 + j))) 13
              + (up (up (up (up (up (up (up f 20 (2 * n + 23 + n / 2)) 20 (2 * n
                + 23 + n / 2 + 1)) 20 (2 * n + 23 + n / 2 + 1 + j)) 17 (instA x
                (n / 2 + j))) 21 (idx / 2 ^ j)) 21 ((idx / 2 ^ j) % 2)) 14
                (s + instA x (n / 2 + j))) 1
              = j + 1 from by
            rw [up_ne (show (13:Nat) ≠ 14 by omega),
              up_ne (show (13:Nat) ≠ 21 by omega), up_ne (show (13:Nat) ≠ 21 by omega),
              up_ne (show (13:Nat) ≠ 17 by omega), up_ne (show (13:Nat) ≠ 20 by omega),
              up_ne (show (13:Nat) ≠ 20 by omega), up_ne (show (13:Nat) ≠ 20 by omega),
              hf13,
              up_ne (show (1:Nat) ≠ 14 by omega), up_ne (show (1:Nat) ≠ 21 by omega),
              up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (1:Nat) ≠ 17 by omega),
              up_ne (show (1:Nat) ≠ 20 by omega), up_ne (show (1:Nat) ≠ 20 by omega),
              up_ne (show (1:Nat) ≠ 20 by omega), hf1]]
          rw [exec_blt_lt_step (by omega)
            (show prog.getD 168 Instr.reject = Instr.blt 2 1 156 by rfl)
            (fit_up (fit_up fG hSV) (by omega))
            (by rw [up_ne (show (2:Nat) ≠ 13 by omega),
              up_ne (show (2:Nat) ≠ 14 by omega), up_ne (show (2:Nat) ≠ 21 by omega),
              up_ne (show (2:Nat) ≠ 21 by omega), up_ne (show (2:Nat) ≠ 17 by omega),
              up_ne (show (2:Nat) ≠ 20 by omega), up_ne (show (2:Nat) ≠ 20 by omega),
              up_ne (show (2:Nat) ≠ 20 by omega),
              up_ne (show (1:Nat) ≠ 13 by omega), up_ne (show (1:Nat) ≠ 14 by omega),
              up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (1:Nat) ≠ 21 by omega),
              up_ne (show (1:Nat) ≠ 17 by omega), up_ne (show (1:Nat) ≠ 20 by omega),
              up_ne (show (1:Nat) ≠ 20 by omega), up_ne (show (1:Nat) ≠ 20 by omega),
              hf2, hf1]; omega)]
          simp only [Nat.sub_sub, Nat.reduceAdd]
    · -- exhausted entry: two steps out
      refine ⟨2, f, by omega, ?_, by rw [← hf14, candSum_of_le (by omega),
        Nat.add_zero], hf1, hf2, hf10, hfit, fun q _ _ _ _ _ => rfl⟩
      rw [exec_blt_ge_step (by omega)
          (show prog.getD 156 Instr.reject = Instr.blt 13 19 158 by rfl) hfit
          (by rw [hf13, hf19]; omega),
        exec_blt_lt_step (by omega)
          (show prog.getD 157 Instr.reject = Instr.blt 2 1 169 by rfl) hfit
          (by rw [hf2, hf1]; omega)]
      simp only [Nat.sub_sub, Nat.reduceAdd]

open scoped Classical in
set_option maxHeartbeats 2000000 in
/-- THE outer driver (pc 154 → verdict): for each candidate `idx`, build
`s = candSum` (inner loop), form the target `t − s` (wrapped when
`s > t`), binary-search the sorted first-half sums (§2): a hit accepts,
a miss advances `idx`.  After all `2^m2` candidates miss, REJECT.  The
run's value is exactly `decide (isSum (instA x) n x.t)` — ρ-independent.
Per-candidate budget: `11·m2 + 10·2^h + 19` steps. -/
theorem pb_loop {w n : Nat} (ρ : Nat → BitVec w) {x : Instance n} (hn : 4 ≤ n) :
    ∀ (F bd idx : Nat) (f : Nat → Nat) (S r : Nat),
    f 1 = 1 → f 2 = 0 → f 7 = n → f 8 = 2 * n + 23 → f 9 = n / 2 →
    f 10 = idx → f 11 = 2 ^ (n / 2) → f 19 = n - n / 2 →
    f 22 = 2 ^ (n - n / 2) → f 18 = bd →
    (bd = 3 * n + 25 ∨ bd = 3 * n + 25 + 2 ^ (n / 2) + 1) →
    arrL f bd (2 ^ (n / 2)) = halfSums (instA x) (n / 2) →
    (∀ i, 1 ≤ i → i ≤ n → f (2 * n + 23 + i) = instA x (i - 1)) →
    f (2 * n + 23 + (n + 1)) = x.t →
    (∀ q, f q < 2 ^ w) →
    (∀ c, c ≤ 3 * n + 26 + 2 * 2 ^ (n / 2) → c < 2 ^ w) →
    2 * ((List.range n).map (instA x)).sum < 2 ^ w →
    idx < 2 ^ (n - n / 2) →
    (∀ i, i < idx →
      ¬ (candSum (fun i => instA x (n / 2 + i)) i 0 (n - n / 2) ≤ x.t ∧
        ∃ q, q < 2 ^ (n / 2) ∧
          (halfSums (instA x) (n / 2)).getD q 0
            = x.t - candSum (fun i => instA x (n / 2 + i)) i 0 (n - n / 2))) →
    2 ^ (n - n / 2) - idx ≤ F →
    (11 * (n - n / 2) + 10 * (n / 2) + 29) * (2 ^ (n - n / 2) - idx) ≤ S →
    ∃ c, c ≤ (11 * (n - n / 2) + 10 * (n / 2) + 29)
        * (2 ^ (n - n / 2) - idx) ∧
      exec prog ρ S 154 r (memOf w f)
        = some (decide (isSum (instA x) n x.t)) := by
  intro F
  induction F with
  | zero =>
    intro bd idx f S r hf1 hf2 hf7 hf8 hf9 hf10 hf11 hf19 hf22 hf18 hbd harr
      hrel htgt hfit haddr htot hidx hpast hfuel hS
    exact absurd hfuel (by omega)
  | succ F ih =>
    intro bd idx f S r hf1 hf2 hf7 hf8 hf9 hf10 hf11 hf19 hf22 hf18 hbd harr
      hrel htgt hfit haddr htot hidx hpast hfuel hS
    have hone : (1:Nat) ≤ 2 ^ (n / 2) := Nat.one_le_two_pow
    have hmn : n / 2 + (n - n / 2) = n := by omega
    have hbd23 : 23 ≤ bd := by rcases hbd with h | h <;> omega
    have h2h : 2 ^ (n / 2) < 2 ^ w := haddr _ (by omega)
    have hbdL : bd + 2 ^ (n / 2) < 2 ^ w := by
      apply haddr
      rcases hbd with h | h <;> rw [h] <;> omega
    have h2L : 2 * 2 ^ (n / 2) < 2 ^ w := haddr _ (by omega)
    have hPR : (11 * (n - n / 2) + 10 * (n / 2) + 29)
        ≤ (11 * (n - n / 2) + 10 * (n / 2) + 29)
          * (2 ^ (n - n / 2) - idx) :=
      Nat.le_mul_of_pos_right _ (by omega)
    have hT' : ((List.range (n - n / 2)).map (fun i => instA x (n / 2 + i))).sum
        < 2 ^ w := by
      have h1 := shifted_le_total (instA x) hmn
      omega
    -- 1. the two reset steps (154, 155)
    have f155fit : ∀ q, (up (up f 14 0) 13 0) q < 2 ^ w :=
      fit_up (fit_up hfit (by omega)) (by omega)
    have hwalk2 : exec prog ρ S 154 r (memOf w f)
        = exec prog ρ (S - 2) 156 r (memOf w (up (up f 14 0) 13 0)) := by
      rw [exec_sub_step (by omega)
          (show prog.getD 154 Instr.reject = Instr.sub 14 14 14 by rfl) hfit
          (Nat.le_refl _),
        exec_sub_step (by omega)
          (show prog.getD 155 Instr.reject = Instr.sub 13 13 13 by rfl)
          (fit_up hfit (by omega)) (Nat.le_refl _)]
      simp only [Nat.sub_sub, Nat.reduceAdd, Nat.sub_self]
    -- 2. the candidate loop
    have grel : ∀ i, 1 ≤ i → i ≤ n → (up (up f 14 0) 13 0) (2 * n + 23 + i)
        = instA x (i - 1) := by
      intro i hi1 hin
      rw [up_ne (show 2 * n + 23 + i ≠ 13 by omega),
        up_ne (show 2 * n + 23 + i ≠ 14 by omega)]
      exact hrel i hi1 hin
    obtain ⟨c1, g, hc1, hex1, hg14, hg1, hg2, hg10, hgfit, hgpre⟩ :=
      cand_exec ρ (n - n / 2) 0 (n - n / 2) idx 0 (up (up f 14 0) 13 0)
        (S - 2) r hf1 hf2 hf8 hf9 hf10 (up_eq _ _ _)
        (by rw [up_ne (show (14:Nat) ≠ 13 by omega), up_eq])
        (by rw [up_ne (show (19:Nat) ≠ 13 by omega),
          up_ne (show (19:Nat) ≠ 14 by omega)]; exact hf19)
        (by omega) hmn grel f155fit haddr (by omega) hT' (by omega)
        (by rw [Nat.sub_zero]; have := hPR; omega)
    -- 3. the carried register facts of g
    have hs : g 14 = candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2) := by
      rw [hg14, Nat.zero_add]
    have g1 : g 1 = 1 := hg1
    have g2 : g 2 = 0 := hg2
    have g7 : g 7 = n := by
      rw [hgpre 7 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hf7
    have g8 : g 8 = 2 * n + 23 := by
      rw [hgpre 8 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hf8
    have g9 : g 9 = n / 2 := by
      rw [hgpre 9 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hf9
    have g11 : g 11 = 2 ^ (n / 2) := by
      rw [hgpre 11 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hf11
    have g18 : g 18 = bd := by
      rw [hgpre 18 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hf18
    have g19 : g 19 = n - n / 2 := by
      rw [hgpre 19 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hf19
    have g22 : g 22 = 2 ^ (n - n / 2) := by
      rw [hgpre 22 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hf22
    have gmem : ∀ q, 23 ≤ q → g q = f q := by
      intro q hq
      rw [hgpre q (by omega) (by omega) (by omega) (by omega) (by omega),
        up_ne (show q ≠ 13 by omega), up_ne (show q ≠ 14 by omega)]
    have gtgt : g (2 * n + 23 + (n + 1)) = x.t := by
      rw [gmem (2 * n + 23 + (n + 1)) (by omega)]
      exact htgt
    have hxt : x.t < 2 ^ w := by
      have h1 := hgfit (2 * n + 23 + (n + 1))
      rw [gtgt] at h1
      exact h1
    -- 4. the common tail 169 → 172
    have e169 : g 8 + g 7 = 2 * n + 23 + n := by rw [g8, g7]
    have e170 : (up g 20 (2 * n + 23 + n)) 20
        + (up g 20 (2 * n + 23 + n)) 1 = 2 * n + 23 + n + 1 := by
      rw [up_eq, up_ne (show (1:Nat) ≠ 20 by omega), g1]
    have hB2 : 2 * n + 23 + n + 1 ≠ 20 := by omega
    have e171 : (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1))
          ((up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1)) 20)
        = x.t := by
      rw [up_eq, up_ne hB2, up_ne hB2,
        show 2 * n + 23 + n + 1 = 2 * n + 23 + (n + 1) from by omega]
      exact gtgt
    have fv1 : ∀ q, (up g 20 (2 * n + 23 + n)) q < 2 ^ w :=
      fit_up hgfit (haddr _ (by omega))
    have fv2 : ∀ q, (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1)) q
        < 2 ^ w := fit_up fv1 (haddr _ (by omega))
    have fv3 : ∀ q, (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1))
        21 x.t) q < 2 ^ w := fit_up fv2 hxt
    have hwalk3 : exec prog ρ (S - 2 - c1) 169 r (memOf w g)
        = exec prog ρ (S - 2 - c1 - 3) 172 r (memOf w
            (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1)) 21 x.t)) := by
      rw [exec_add_step (by omega)
          (show prog.getD 169 Instr.reject = Instr.add 20 8 7 by rfl), e169,
        exec_add_step (by omega)
          (show prog.getD 170 Instr.reject = Instr.add 20 20 1 by rfl), e170,
        exec_load_step (by omega)
          (show prog.getD 171 Instr.reject = Instr.load 21 20 by rfl) fv2, e171]
      simp only [Nat.sub_sub, Nat.reduceAdd]
    -- 5. the dispatch: search + verdict + fork (W3 abstract over the two
    --    subtraction modes at pc 172)
    have hdisp : ∀ (W3 : Nat → Nat),
        W3 12 = 0 → W3 13 = 2 ^ (n / 2) - 1 →
        W3 1 = 1 → W3 2 = 0 → W3 7 = n → W3 8 = 2 * n + 23 → W3 9 = n / 2 →
        W3 10 = idx → W3 11 = 2 ^ (n / 2) → W3 19 = n - n / 2 →
        W3 22 = 2 ^ (n - n / 2) → W3 18 = bd → W3 bd = 0 →
        (∀ q, q < 2 ^ (n / 2) →
          W3 (bd + q) = (halfSums (instA x) (n / 2)).getD q 0) →
        (∀ q, W3 q < 2 ^ w) →
        (∀ q, 23 ≤ q → W3 q = f q) →
        (W3 16 = x.t - candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2) ∧
           candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2) ≤ x.t ∨
         x.t < candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2) ∧
           W3 16 = 2 ^ w
             - (candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2) - x.t)) →
        (exec prog ρ S 154 r (memOf w f)
          = exec prog ρ (S - 2 - c1 - 6) 175 r (memOf w W3)) →
        ∃ c, c ≤ (11 * (n - n / 2) + 10 * (n / 2) + 29)
            * (2 ^ (n - n / 2) - idx) ∧
          exec prog ρ S 154 r (memOf w f)
            = some (decide (isSum (instA x) n x.t)) := by
      intro W3 w12 w13 w1 w2 w7 w8 w9 w10 w11 w19 w22 w18 wbd0 wbind wfit wmem
        hcc hexec
      have hlen := length_halfSums (instA x) (n / 2)
      have hstot : candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2)
          ≤ ((List.range n).map (instA x)).sum := by
        have h1 := candSum_le (fun i => instA x (n / 2 + i)) idx (n - n / 2)
        have h2 := shifted_le_total (instA x) hmn
        omega
      by_cases hwit : ∃ m, m ≤ 2 ^ (n / 2) - 1 ∧ W3 (bd + m) = W3 16
      · -- a RAM hit: accept
        obtain ⟨m0, hm0, hval⟩ := hwit
        obtain ⟨c2, hc2, hexH⟩ :=
          bsrch_hit_exec ρ (n / 2) (2 ^ (n / 2)) bd 0 (2 ^ (n / 2) - 1)
            (W3 16) (halfSums (instA x) (n / 2)) W3 (S - 2 - c1 - 6) r
            (halfSums_sorted _ _) hlen w12 w13 rfl w18 w1 w2 wbd0 hbd23
            (by have := hone; omega) (by have := hone; omega) wbind
            ⟨m0, Nat.zero_le _, hm0, hval⟩
            wfit hbdL h2L (by have := hone; omega) (by have := hPR; omega)
        rcases hcc with ⟨hccv, hsle⟩ | ⟨hgtC, hccw⟩
        · -- honest complement: the instance is solvable
          have hP : isSum (instA x) n x.t := by
            have hgetD : (halfSums (instA x) (n / 2)).getD m0 0
                = x.t - candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2) := by
              rw [← wbind m0 (by omega), hval, hccv]
            have hmem := getD_mem_of_lt
              (show m0 < (halfSums (instA x) (n / 2)).length by rw [hlen]; omega)
            rw [hgetD] at hmem
            have hfirst := (mem_halfSums (instA x) (n / 2) _).mp hmem
            have hsecond : isSum (fun i => instA x (i + n / 2)) (n - n / 2)
                (x.t - (x.t - candSum (fun i => instA x (n / 2 + i)) idx 0
                  (n - n / 2))) := by
              rw [show x.t - (x.t - candSum (fun i => instA x (n / 2 + i)) idx 0
                    (n - n / 2))
                  = candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2)
                  from by omega]
              rw [funext (fun i : Nat =>
                show (fun i => instA x (i + n / 2)) i
                  = (fun i => instA x (n / 2 + i)) i from by
                  show instA x (i + n / 2) = instA x (n / 2 + i)
                  congr 1
                  omega)]
              exact candSum_isSum _ _ _
            have hsplit := (isSum_split (instA x) (n / 2) (n - n / 2) x.t).mpr
              ⟨x.t - candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2),
                by omega, hfirst, hsecond⟩
            rw [hmn] at hsplit
            exact hsplit
          refine ⟨8 + c1 + (10 * (n / 2) + 19), by omega, ?_⟩
          rw [hexec, hexH, decide_eq_true hP]
        · -- wrapped complement: exceeds every half-sum — impossible
          have hvle : (halfSums (instA x) (n / 2)).getD m0 0
              ≤ ((List.range n).map (instA x)).sum := by
            apply halfSums_le_total (k := n / 2) (by omega)
            exact getD_mem_of_lt (show m0 < (halfSums (instA x) (n / 2)).length by
              rw [hlen]; omega)
          rw [← wbind m0 (by omega), hval, hccw] at hvle
          exact absurd hvle
            (by have := wrapped_gt htot hstot (Nat.le_refl _) hgtC; omega)
      · -- no RAM hit: walk to LNEXT
        have hmissRAM : ∀ m, 0 ≤ m → m ≤ 2 ^ (n / 2) - 1 → W3 (bd + m) ≠ W3 16 := by
          intro m _ hm hval
          exact hwit ⟨m, hm, hval⟩
        obtain ⟨c2, fm, hc2, hexM, hfm12, hfm13, hfm16, hfm18, hfm1, hfm2, hfmb,
            hfmfit, hfmpre⟩ :=
          bsrch_miss_exec ρ (n / 2) (2 ^ (n / 2)) bd 0 (2 ^ (n / 2) - 1)
            (W3 16) W3 (S - 2 - c1 - 6) r w12 w13 rfl w18 w1 w2 wbd0 hbd23
            (by have := hone; omega) (by have := hone; omega) hmissRAM wfit hbdL
            h2L (by have := hone; omega) (by have := hPR; omega)
        have hfm10 : fm 10 = idx := by
          rw [hfmpre 10 (by omega) (by omega) (by omega) (by omega) (by omega)]
          exact w10
        have hfm22 : fm 22 = 2 ^ (n - n / 2) := by
          rw [hfmpre 22 (by omega) (by omega) (by omega) (by omega) (by omega)]
          exact w22
        have hfmmem : ∀ q, 23 ≤ q → fm q = f q := by
          intro q hq
          rw [hfmpre q (by omega) (by omega) (by omega) (by omega) (by omega)]
          exact wmem q hq
        -- this candidate missed at math level too
        have hmissIdx : ¬ (candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2)
            ≤ x.t ∧ ∃ q, q < 2 ^ (n / 2) ∧
              (halfSums (instA x) (n / 2)).getD q 0
                = x.t - candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2)) := by
          rintro ⟨hsle, q, hq, hvalq⟩
          rcases hcc with ⟨hccv, _⟩ | ⟨hgtC, _⟩
          · exact hwit ⟨q, by omega, by rw [wbind q (by omega), hvalq, ← hccv]⟩
          · omega
        by_cases hlast : idx + 1 < 2 ^ (n - n / 2)
        · -- loop back to pc 154 with idx + 1
          have hlnext : exec prog ρ (S - 2 - c1 - 6 - c2) 189 r (memOf w fm)
              = exec prog ρ (S - 2 - c1 - 6 - c2 - 2) 154 r
                  (memOf w (up fm 10 (fm 10 + 1))) :=
            lnext_loop_exec ρ fm _ r (by rw [hfm10, hfm22]; omega) hfm1 hfmfit
              (by omega)
          have hfm22lt := hfmfit 22
          rw [hfm22] at hfm22lt
          have hfuel' : 2 ^ (n - n / 2) - (idx + 1) ≤ F := by omega
          have hnx10 : (up fm 10 (fm 10 + 1)) 10 = idx + 1 := by
            rw [up_eq, hfm10]
          have hnxarr : arrL (up fm 10 (fm 10 + 1)) bd (2 ^ (n / 2))
              = halfSums (instA x) (n / 2) := by
            refine (arrL_congr (f := up fm 10 (fm 10 + 1)) (g := f) ?_).trans harr
            intro i hi
            rw [up_ne (show bd + i ≠ 10 by omega)]
            exact hfmmem (bd + i) (by omega)
          have hnxrel : ∀ i, 1 ≤ i → i ≤ n →
              (up fm 10 (fm 10 + 1)) (2 * n + 23 + i) = instA x (i - 1) := by
            intro i hi1 hin
            rw [up_ne (show 2 * n + 23 + i ≠ 10 by omega),
              hfmmem (2 * n + 23 + i) (by omega)]
            exact hrel i hi1 hin
          have hnxtgt : (up fm 10 (fm 10 + 1)) (2 * n + 23 + (n + 1)) = x.t := by
            rw [up_ne (show 2 * n + 23 + (n + 1) ≠ 10 by omega),
              hfmmem (2 * n + 23 + (n + 1)) (by omega)]
            exact htgt
          have hnxpast : ∀ i, i < idx + 1 →
              ¬ (candSum (fun i => instA x (n / 2 + i)) i 0 (n - n / 2) ≤ x.t ∧
                ∃ q, q < 2 ^ (n / 2) ∧ (halfSums (instA x) (n / 2)).getD q 0
                  = x.t - candSum (fun i => instA x (n / 2 + i)) i 0 (n - n / 2)) := by
            intro i hi
            by_cases hilt : i < idx
            · exact hpast i hilt
            · have hie : i = idx := by omega
              rw [hie]
              exact hmissIdx
          have hdec : 2 ^ (n - n / 2) - idx
              = (2 ^ (n - n / 2) - (idx + 1)) + 1 := by omega
          have hmul : (11 * (n - n / 2) + 10 * (n / 2) + 29)
                * (2 ^ (n - n / 2) - idx)
              = (11 * (n - n / 2) + 10 * (n / 2) + 29)
                  * (2 ^ (n - n / 2) - (idx + 1))
                + (11 * (n - n / 2) + 10 * (n / 2) + 29) := by
            rw [hdec, Nat.mul_add, Nat.mul_one]
          have hS' : (11 * (n - n / 2) + 10 * (n / 2) + 29)
              * (2 ^ (n - n / 2) - (idx + 1)) ≤ S - (10 + c1 + c2) := by omega
          have hnx1 : (up fm 10 (fm 10 + 1)) 1 = 1 := by
            rw [up_ne (show (1:Nat) ≠ 10 by omega)]
            exact hfm1
          have hnx2 : (up fm 10 (fm 10 + 1)) 2 = 0 := by
            rw [up_ne (show (2:Nat) ≠ 10 by omega)]
            exact hfm2
          have hnx7 : (up fm 10 (fm 10 + 1)) 7 = n := by
            rw [up_ne (show (7:Nat) ≠ 10 by omega),
              hfmpre 7 (by omega) (by omega) (by omega) (by omega) (by omega)]
            exact w7
          have hnx8 : (up fm 10 (fm 10 + 1)) 8 = 2 * n + 23 := by
            rw [up_ne (show (8:Nat) ≠ 10 by omega),
              hfmpre 8 (by omega) (by omega) (by omega) (by omega) (by omega)]
            exact w8
          have hnx9 : (up fm 10 (fm 10 + 1)) 9 = n / 2 := by
            rw [up_ne (show (9:Nat) ≠ 10 by omega),
              hfmpre 9 (by omega) (by omega) (by omega) (by omega) (by omega)]
            exact w9
          have hnx11 : (up fm 10 (fm 10 + 1)) 11 = 2 ^ (n / 2) := by
            rw [up_ne (show (11:Nat) ≠ 10 by omega),
              hfmpre 11 (by omega) (by omega) (by omega) (by omega) (by omega)]
            exact w11
          have hnx19 : (up fm 10 (fm 10 + 1)) 19 = n - n / 2 := by
            rw [up_ne (show (19:Nat) ≠ 10 by omega),
              hfmpre 19 (by omega) (by omega) (by omega) (by omega) (by omega)]
            exact w19
          have hnx22 : (up fm 10 (fm 10 + 1)) 22 = 2 ^ (n - n / 2) := by
            rw [up_ne (show (22:Nat) ≠ 10 by omega),
              hfmpre 22 (by omega) (by omega) (by omega) (by omega) (by omega)]
            exact w22
          have hnx18 : (up fm 10 (fm 10 + 1)) 18 = bd := by
            rw [up_ne (show (18:Nat) ≠ 10 by omega)]
            exact hfm18
          have hnxfit : ∀ q, (up fm 10 (fm 10 + 1)) q < 2 ^ w :=
            fit_up hfmfit (by rw [hfm10]; omega)
          have hres := ih bd (idx + 1) (up fm 10 (fm 10 + 1)) (S - (10 + c1 + c2)) r
            hnx1 hnx2 hnx7 hnx8 hnx9 hnx10 hnx11 hnx19 hnx22 hnx18
            hbd hnxarr hnxrel hnxtgt hnxfit haddr htot hlast hnxpast hfuel' hS'
          obtain ⟨c3, hc3, hex3⟩ := hres
          refine ⟨10 + c1 + c2 + c3, ?_, ?_⟩
          · have hkey : 10 + c1 + c2 + c3
              ≤ (11 * (n - n / 2) + 10 * (n / 2) + 29)
                + (11 * (n - n / 2) + 10 * (n / 2) + 29)
                  * (2 ^ (n - n / 2) - (idx + 1)) :=
              Nat.add_le_add (by omega) hc3
            omega
          · rw [hexec, hexM, hlnext,
              show S - 2 - c1 - 6 - c2 - 2 = S - (10 + c1 + c2) from by omega, hex3]
        · -- the last candidate missed: reject
          have hrej : exec prog ρ (S - 2 - c1 - 6 - c2) 189 r (memOf w fm)
              = some false :=
            lnext_reject_exec ρ fm _ r (by rw [hfm10, hfm22]; omega) hfm1 hfm2
              hfmfit (by omega)
          have hnotP : ¬ isSum (instA x) n x.t := by
            intro hP
            have hP' : isSum (instA x) (n / 2 + (n - n / 2)) x.t := by
              rw [hmn]; exact hP
            obtain ⟨s', hs'le, hfirst, hsecond⟩ :=
              (isSum_split (instA x) (n / 2) (n - n / 2) x.t).mp hP'
            obtain ⟨S₂, hS₂f, hS₂sum⟩ := hsecond
            have hAx : (fun i => instA x (i + n / 2))
                = (fun i => instA x (n / 2 + i)) :=
              funext fun i => by congr 1; omega
            rw [hAx] at hS₂sum
            obtain ⟨idxs, hidxslt, hbits⟩ := realize_idx (n - n / 2) S₂ hS₂f
            have hcand : candSum (fun i => instA x (n / 2 + i)) idxs 0 (n - n / 2)
                = x.t - s' :=
              (candSum_eq_choiceSum (fun _ hi => hbits _ hi)).trans hS₂sum
            obtain ⟨q, hq, hvalq⟩ :=
              mem_getD_index ((mem_halfSums (instA x) (n / 2) s').mpr hfirst)
            rw [hlen] at hq
            have hall : ∀ i, i < 2 ^ (n - n / 2) →
                ¬ (candSum (fun i => instA x (n / 2 + i)) i 0 (n - n / 2) ≤ x.t ∧
                  ∃ q, q < 2 ^ (n / 2) ∧ (halfSums (instA x) (n / 2)).getD q 0
                    = x.t - candSum (fun i => instA x (n / 2 + i)) i 0
                      (n - n / 2)) := by
              intro i hi
              by_cases hilt : i < idx
              · exact hpast i hilt
              · have hie : i = idx := by omega
                rw [hie]
                exact hmissIdx
            exact hall idxs hidxslt ⟨by omega, q, hq, by
              rw [hcand, show x.t - (x.t - s') = s' from by omega]; exact hvalq⟩
          refine ⟨10 + c1 + c2 + 1, by have := hPR; omega, ?_⟩
          rw [hexec, hexM, hrej,
            show decide (isSum (instA x) n x.t) = false from by simp [hnotP]]
    -- 6. the two subtraction modes at pc 172
    by_cases hle : g 14 ≤ x.t
    · -- honest complement: cc := t − s
      have hle172 : (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1)) 21
          x.t) 14
          ≤ (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1)) 21 x.t) 21 := by
        rw [up_eq, up_ne (show (14:Nat) ≠ 21 by omega),
          up_ne (show (14:Nat) ≠ 20 by omega), up_ne (show (14:Nat) ≠ 20 by omega)]
        exact hle
      have e172 : (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1)) 21
          x.t) 21
          - (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1)) 21 x.t) 14
          = x.t - candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2) := by
        rw [up_eq, up_ne (show (14:Nat) ≠ 21 by omega),
          up_ne (show (14:Nat) ≠ 20 by omega), up_ne (show (14:Nat) ≠ 20 by omega),
          hs]
      have hCCfit : ∀ q, (up (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n
              + 1)) 21 x.t) 16 (x.t - candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2))) q < 2 ^ w :=
        fit_up fv3 (by omega)
      have hle174 : (up (up (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n
              + 1)) 21 x.t) 16 (x.t - candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2))) 12 0) 1
          ≤ (up (up (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1)) 21
              x.t) 16 (x.t - candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2))) 12 0) 11 := by
        rw [up_ne (show (1:Nat) ≠ 12 by omega), up_ne (show (1:Nat) ≠ 16 by omega),
          up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (1:Nat) ≠ 20 by omega),
          up_ne (show (1:Nat) ≠ 20 by omega),
          up_ne (show (11:Nat) ≠ 12 by omega), up_ne (show (11:Nat) ≠ 16 by omega),
          up_ne (show (11:Nat) ≠ 21 by omega), up_ne (show (11:Nat) ≠ 20 by omega),
          up_ne (show (11:Nat) ≠ 20 by omega), g1, g11]
        exact hone
      have e174 : (up (up (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1))
              21 x.t) 16 (x.t - candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2))) 12 0) 11
          - (up (up (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1)) 21
              x.t) 16 (x.t - candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2))) 12 0) 1
          = 2 ^ (n / 2) - 1 := by
        rw [up_ne (show (11:Nat) ≠ 12 by omega), up_ne (show (11:Nat) ≠ 16 by omega),
          up_ne (show (11:Nat) ≠ 21 by omega), up_ne (show (11:Nat) ≠ 20 by omega),
          up_ne (show (11:Nat) ≠ 20 by omega),
          up_ne (show (1:Nat) ≠ 12 by omega), up_ne (show (1:Nat) ≠ 16 by omega),
          up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (1:Nat) ≠ 20 by omega),
          up_ne (show (1:Nat) ≠ 20 by omega), g1, g11]
      have hwalk4 : exec prog ρ (S - 2 - c1 - 3) 172 r (memOf w
            (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1)) 21 x.t))
          = exec prog ρ (S - 2 - c1 - 6) 175 r (memOf w
              (up (up (up (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1)) 21 x.t) 16 (x.t - candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2))) 12 0) 13 (2 ^ (n / 2) - 1))) := by
        rw [exec_sub_step (by omega)
            (show prog.getD 172 Instr.reject = Instr.sub 16 21 14 by rfl)
            fv3 hle172, e172,
          exec_sub_step (by omega)
            (show prog.getD 173 Instr.reject = Instr.sub 12 12 12 by rfl) hCCfit
            (Nat.le_refl _), Nat.sub_self,
          exec_sub_step (by omega)
            (show prog.getD 174 Instr.reject = Instr.sub 13 11 1 by rfl)
            (fit_up hCCfit (by omega)) hle174, e174]
        simp only [Nat.sub_sub, Nat.reduceAdd, Nat.sub_self]
      -- the array facts of the 175-state
      have warr : arrL (up (up (up (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1)) 21 x.t) 16 (x.t - candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2))) 12 0) 13 (2 ^ (n / 2) - 1)) bd (2 ^ (n / 2))
          = halfSums (instA x) (n / 2) := by
        refine (arrL_congr (f := (up (up (up (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1)) 21 x.t) 16 (x.t - candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2))) 12 0) 13 (2 ^ (n / 2) - 1))) (g := f) ?_).trans harr
        intro i hi
        rw [up_ne (show (bd + i:Nat) ≠ 13 by omega), up_ne (show (bd + i:Nat) ≠ 12 by omega), up_ne (show (bd + i:Nat) ≠ 16 by omega), up_ne (show (bd + i:Nat) ≠ 21 by omega), up_ne (show (bd + i:Nat) ≠ 20 by omega), up_ne (show (bd + i:Nat) ≠ 20 by omega), gmem (bd + i) (by omega)]
      have wbd0 : (up (up (up (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1)) 21 x.t) 16 (x.t - candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2))) 12 0) 13 (2 ^ (n / 2) - 1)) bd = 0 := by
        have h1 := getD_arrL (f := (up (up (up (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1)) 21 x.t) 16 (x.t - candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2))) 12 0) 13 (2 ^ (n / 2) - 1))) (b := bd) (L := 2 ^ (n / 2)) (q := 0)
          (by omega)
        rw [warr, halfSums_head_zero] at h1
        exact h1.symm
      have wbind : ∀ q, q < 2 ^ (n / 2) → (up (up (up (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1)) 21 x.t) 16 (x.t - candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2))) 12 0) 13 (2 ^ (n / 2) - 1)) (bd + q)
          = (halfSums (instA x) (n / 2)).getD q 0 := by
        intro q hq
        have h1 := getD_arrL (f := (up (up (up (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1)) 21 x.t) 16 (x.t - candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2))) 12 0) 13 (2 ^ (n / 2) - 1))) (b := bd) hq
        rw [warr] at h1
        exact h1.symm
      have wfit : ∀ q, (up (up (up (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1)) 21 x.t) 16 (x.t - candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2))) 12 0) 13 (2 ^ (n / 2) - 1)) q < 2 ^ w :=
        fit_up (fit_up (fit_up fv3 (by omega)) (by omega)) (by omega)
      refine hdisp (up (up (up (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1)) 21 x.t) 16 (x.t - candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2))) 12 0) 13 (2 ^ (n / 2) - 1)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · rw [up_ne (show (12:Nat) ≠ 13 by omega), up_eq]
      · exact up_eq _ _ _
      · rw [up_ne (show (1:Nat) ≠ 13 by omega), up_ne (show (1:Nat) ≠ 12 by omega), up_ne (show (1:Nat) ≠ 16 by omega), up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (1:Nat) ≠ 20 by omega), up_ne (show (1:Nat) ≠ 20 by omega), g1]
      · rw [up_ne (show (2:Nat) ≠ 13 by omega), up_ne (show (2:Nat) ≠ 12 by omega), up_ne (show (2:Nat) ≠ 16 by omega), up_ne (show (2:Nat) ≠ 21 by omega), up_ne (show (2:Nat) ≠ 20 by omega), up_ne (show (2:Nat) ≠ 20 by omega), g2]
      · rw [up_ne (show (7:Nat) ≠ 13 by omega), up_ne (show (7:Nat) ≠ 12 by omega), up_ne (show (7:Nat) ≠ 16 by omega), up_ne (show (7:Nat) ≠ 21 by omega), up_ne (show (7:Nat) ≠ 20 by omega), up_ne (show (7:Nat) ≠ 20 by omega), g7]
      · rw [up_ne (show (8:Nat) ≠ 13 by omega), up_ne (show (8:Nat) ≠ 12 by omega), up_ne (show (8:Nat) ≠ 16 by omega), up_ne (show (8:Nat) ≠ 21 by omega), up_ne (show (8:Nat) ≠ 20 by omega), up_ne (show (8:Nat) ≠ 20 by omega), g8]
      · rw [up_ne (show (9:Nat) ≠ 13 by omega), up_ne (show (9:Nat) ≠ 12 by omega), up_ne (show (9:Nat) ≠ 16 by omega), up_ne (show (9:Nat) ≠ 21 by omega), up_ne (show (9:Nat) ≠ 20 by omega), up_ne (show (9:Nat) ≠ 20 by omega), g9]
      · rw [up_ne (show (10:Nat) ≠ 13 by omega), up_ne (show (10:Nat) ≠ 12 by omega), up_ne (show (10:Nat) ≠ 16 by omega), up_ne (show (10:Nat) ≠ 21 by omega), up_ne (show (10:Nat) ≠ 20 by omega), up_ne (show (10:Nat) ≠ 20 by omega), hg10]
      · rw [up_ne (show (11:Nat) ≠ 13 by omega), up_ne (show (11:Nat) ≠ 12 by omega), up_ne (show (11:Nat) ≠ 16 by omega), up_ne (show (11:Nat) ≠ 21 by omega), up_ne (show (11:Nat) ≠ 20 by omega), up_ne (show (11:Nat) ≠ 20 by omega), g11]
      · rw [up_ne (show (19:Nat) ≠ 13 by omega), up_ne (show (19:Nat) ≠ 12 by omega), up_ne (show (19:Nat) ≠ 16 by omega), up_ne (show (19:Nat) ≠ 21 by omega), up_ne (show (19:Nat) ≠ 20 by omega), up_ne (show (19:Nat) ≠ 20 by omega), g19]
      · rw [up_ne (show (22:Nat) ≠ 13 by omega), up_ne (show (22:Nat) ≠ 12 by omega), up_ne (show (22:Nat) ≠ 16 by omega), up_ne (show (22:Nat) ≠ 21 by omega), up_ne (show (22:Nat) ≠ 20 by omega), up_ne (show (22:Nat) ≠ 20 by omega), g22]
      · rw [up_ne (show (18:Nat) ≠ 13 by omega), up_ne (show (18:Nat) ≠ 12 by omega), up_ne (show (18:Nat) ≠ 16 by omega), up_ne (show (18:Nat) ≠ 21 by omega), up_ne (show (18:Nat) ≠ 20 by omega), up_ne (show (18:Nat) ≠ 20 by omega), g18]
      · exact wbd0
      · exact wbind
      · exact wfit
      · intro q hq
        rw [up_ne (show (q:Nat) ≠ 13 by omega), up_ne (show (q:Nat) ≠ 12 by omega), up_ne (show (q:Nat) ≠ 16 by omega), up_ne (show (q:Nat) ≠ 21 by omega), up_ne (show (q:Nat) ≠ 20 by omega), up_ne (show (q:Nat) ≠ 20 by omega), gmem q hq]
      · exact Or.inl ⟨by
          rw [up_ne (show (16:Nat) ≠ 13 by omega),
            up_ne (show (16:Nat) ≠ 12 by omega), up_eq], by rw [← hs]; exact hle⟩
      · rw [hwalk2, hex1, hwalk3, hwalk4]
    · -- wrapped complement: cc := 2^w − (s − t)
      have hgt172 : (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1)) 21
          x.t) 21
          < (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1)) 21 x.t) 14 := by
        rw [up_eq, up_ne (show (14:Nat) ≠ 21 by omega),
          up_ne (show (14:Nat) ≠ 20 by omega), up_ne (show (14:Nat) ≠ 20 by omega)]
        omega
      have e172 : (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1)) 21
          x.t) 14
          - (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1)) 21 x.t) 21
          = candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2) - x.t := by
        rw [up_eq, up_ne (show (14:Nat) ≠ 21 by omega),
          up_ne (show (14:Nat) ≠ 20 by omega), up_ne (show (14:Nat) ≠ 20 by omega),
          hs]
      have hCCfit : ∀ q, (up (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n
              + 1)) 21 x.t) 16 (2 ^ w - (candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2) - x.t))) q < 2 ^ w :=
        fit_up fv3 (by omega)
      have hle174 : (up (up (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n
              + 1)) 21 x.t) 16 (2 ^ w - (candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2) - x.t))) 12 0) 1
          ≤ (up (up (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1)) 21
              x.t) 16 (2 ^ w - (candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2) - x.t))) 12 0) 11 := by
        rw [up_ne (show (1:Nat) ≠ 12 by omega), up_ne (show (1:Nat) ≠ 16 by omega),
          up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (1:Nat) ≠ 20 by omega),
          up_ne (show (1:Nat) ≠ 20 by omega),
          up_ne (show (11:Nat) ≠ 12 by omega), up_ne (show (11:Nat) ≠ 16 by omega),
          up_ne (show (11:Nat) ≠ 21 by omega), up_ne (show (11:Nat) ≠ 20 by omega),
          up_ne (show (11:Nat) ≠ 20 by omega), g1, g11]
        exact hone
      have e174 : (up (up (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1))
              21 x.t) 16 (2 ^ w - (candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2) - x.t))) 12 0) 11
          - (up (up (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1)) 21
              x.t) 16 (2 ^ w - (candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2) - x.t))) 12 0) 1
          = 2 ^ (n / 2) - 1 := by
        rw [up_ne (show (11:Nat) ≠ 12 by omega), up_ne (show (11:Nat) ≠ 16 by omega),
          up_ne (show (11:Nat) ≠ 21 by omega), up_ne (show (11:Nat) ≠ 20 by omega),
          up_ne (show (11:Nat) ≠ 20 by omega),
          up_ne (show (1:Nat) ≠ 12 by omega), up_ne (show (1:Nat) ≠ 16 by omega),
          up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (1:Nat) ≠ 20 by omega),
          up_ne (show (1:Nat) ≠ 20 by omega), g1, g11]
      have hwalk4 : exec prog ρ (S - 2 - c1 - 3) 172 r (memOf w
            (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1)) 21 x.t))
          = exec prog ρ (S - 2 - c1 - 6) 175 r (memOf w
              (up (up (up (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1)) 21 x.t) 16 (2 ^ w - (candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2) - x.t))) 12 0) 13 (2 ^ (n / 2) - 1))) := by
        rw [exec_sub_wrap_step (by omega)
            (show prog.getD 172 Instr.reject = Instr.sub 16 21 14 by rfl)
            fv3 hgt172, e172,
          exec_sub_step (by omega)
            (show prog.getD 173 Instr.reject = Instr.sub 12 12 12 by rfl) hCCfit
            (Nat.le_refl _), Nat.sub_self,
          exec_sub_step (by omega)
            (show prog.getD 174 Instr.reject = Instr.sub 13 11 1 by rfl)
            (fit_up hCCfit (by omega)) hle174, e174]
        simp only [Nat.sub_sub, Nat.reduceAdd, Nat.sub_self]
      -- the array facts of the 175-state
      have warr : arrL (up (up (up (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1)) 21 x.t) 16 (2 ^ w - (candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2) - x.t))) 12 0) 13 (2 ^ (n / 2) - 1)) bd (2 ^ (n / 2))
          = halfSums (instA x) (n / 2) := by
        refine (arrL_congr (f := (up (up (up (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1)) 21 x.t) 16 (2 ^ w - (candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2) - x.t))) 12 0) 13 (2 ^ (n / 2) - 1))) (g := f) ?_).trans harr
        intro i hi
        rw [up_ne (show (bd + i:Nat) ≠ 13 by omega), up_ne (show (bd + i:Nat) ≠ 12 by omega), up_ne (show (bd + i:Nat) ≠ 16 by omega), up_ne (show (bd + i:Nat) ≠ 21 by omega), up_ne (show (bd + i:Nat) ≠ 20 by omega), up_ne (show (bd + i:Nat) ≠ 20 by omega), gmem (bd + i) (by omega)]
      have wbd0 : (up (up (up (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1)) 21 x.t) 16 (2 ^ w - (candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2) - x.t))) 12 0) 13 (2 ^ (n / 2) - 1)) bd = 0 := by
        have h1 := getD_arrL (f := (up (up (up (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1)) 21 x.t) 16 (2 ^ w - (candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2) - x.t))) 12 0) 13 (2 ^ (n / 2) - 1))) (b := bd) (L := 2 ^ (n / 2)) (q := 0)
          (by omega)
        rw [warr, halfSums_head_zero] at h1
        exact h1.symm
      have wbind : ∀ q, q < 2 ^ (n / 2) → (up (up (up (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1)) 21 x.t) 16 (2 ^ w - (candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2) - x.t))) 12 0) 13 (2 ^ (n / 2) - 1)) (bd + q)
          = (halfSums (instA x) (n / 2)).getD q 0 := by
        intro q hq
        have h1 := getD_arrL (f := (up (up (up (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1)) 21 x.t) 16 (2 ^ w - (candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2) - x.t))) 12 0) 13 (2 ^ (n / 2) - 1))) (b := bd) hq
        rw [warr] at h1
        exact h1.symm
      have wfit : ∀ q, (up (up (up (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1)) 21 x.t) 16 (2 ^ w - (candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2) - x.t))) 12 0) 13 (2 ^ (n / 2) - 1)) q < 2 ^ w :=
        fit_up (fit_up (fit_up fv3 (by omega)) (by omega)) (by omega)
      refine hdisp (up (up (up (up (up (up g 20 (2 * n + 23 + n)) 20 (2 * n + 23 + n + 1)) 21 x.t) 16 (2 ^ w - (candSum (fun i => instA x (n / 2 + i)) idx 0 (n - n / 2) - x.t))) 12 0) 13 (2 ^ (n / 2) - 1)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · rw [up_ne (show (12:Nat) ≠ 13 by omega), up_eq]
      · exact up_eq _ _ _
      · rw [up_ne (show (1:Nat) ≠ 13 by omega), up_ne (show (1:Nat) ≠ 12 by omega), up_ne (show (1:Nat) ≠ 16 by omega), up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (1:Nat) ≠ 20 by omega), up_ne (show (1:Nat) ≠ 20 by omega), g1]
      · rw [up_ne (show (2:Nat) ≠ 13 by omega), up_ne (show (2:Nat) ≠ 12 by omega), up_ne (show (2:Nat) ≠ 16 by omega), up_ne (show (2:Nat) ≠ 21 by omega), up_ne (show (2:Nat) ≠ 20 by omega), up_ne (show (2:Nat) ≠ 20 by omega), g2]
      · rw [up_ne (show (7:Nat) ≠ 13 by omega), up_ne (show (7:Nat) ≠ 12 by omega), up_ne (show (7:Nat) ≠ 16 by omega), up_ne (show (7:Nat) ≠ 21 by omega), up_ne (show (7:Nat) ≠ 20 by omega), up_ne (show (7:Nat) ≠ 20 by omega), g7]
      · rw [up_ne (show (8:Nat) ≠ 13 by omega), up_ne (show (8:Nat) ≠ 12 by omega), up_ne (show (8:Nat) ≠ 16 by omega), up_ne (show (8:Nat) ≠ 21 by omega), up_ne (show (8:Nat) ≠ 20 by omega), up_ne (show (8:Nat) ≠ 20 by omega), g8]
      · rw [up_ne (show (9:Nat) ≠ 13 by omega), up_ne (show (9:Nat) ≠ 12 by omega), up_ne (show (9:Nat) ≠ 16 by omega), up_ne (show (9:Nat) ≠ 21 by omega), up_ne (show (9:Nat) ≠ 20 by omega), up_ne (show (9:Nat) ≠ 20 by omega), g9]
      · rw [up_ne (show (10:Nat) ≠ 13 by omega), up_ne (show (10:Nat) ≠ 12 by omega), up_ne (show (10:Nat) ≠ 16 by omega), up_ne (show (10:Nat) ≠ 21 by omega), up_ne (show (10:Nat) ≠ 20 by omega), up_ne (show (10:Nat) ≠ 20 by omega), hg10]
      · rw [up_ne (show (11:Nat) ≠ 13 by omega), up_ne (show (11:Nat) ≠ 12 by omega), up_ne (show (11:Nat) ≠ 16 by omega), up_ne (show (11:Nat) ≠ 21 by omega), up_ne (show (11:Nat) ≠ 20 by omega), up_ne (show (11:Nat) ≠ 20 by omega), g11]
      · rw [up_ne (show (19:Nat) ≠ 13 by omega), up_ne (show (19:Nat) ≠ 12 by omega), up_ne (show (19:Nat) ≠ 16 by omega), up_ne (show (19:Nat) ≠ 21 by omega), up_ne (show (19:Nat) ≠ 20 by omega), up_ne (show (19:Nat) ≠ 20 by omega), g19]
      · rw [up_ne (show (22:Nat) ≠ 13 by omega), up_ne (show (22:Nat) ≠ 12 by omega), up_ne (show (22:Nat) ≠ 16 by omega), up_ne (show (22:Nat) ≠ 21 by omega), up_ne (show (22:Nat) ≠ 20 by omega), up_ne (show (22:Nat) ≠ 20 by omega), g22]
      · rw [up_ne (show (18:Nat) ≠ 13 by omega), up_ne (show (18:Nat) ≠ 12 by omega), up_ne (show (18:Nat) ≠ 16 by omega), up_ne (show (18:Nat) ≠ 21 by omega), up_ne (show (18:Nat) ≠ 20 by omega), up_ne (show (18:Nat) ≠ 20 by omega), g18]
      · exact wbd0
      · exact wbind
      · exact wfit
      · intro q hq
        rw [up_ne (show (q:Nat) ≠ 13 by omega), up_ne (show (q:Nat) ≠ 12 by omega), up_ne (show (q:Nat) ≠ 16 by omega), up_ne (show (q:Nat) ≠ 21 by omega), up_ne (show (q:Nat) ≠ 20 by omega), up_ne (show (q:Nat) ≠ 20 by omega), gmem q hq]
      · exact Or.inr ⟨by rw [← hs]; omega, by
          rw [up_ne (show (16:Nat) ≠ 13 by omega),
            up_ne (show (16:Nat) ≠ 12 by omega), up_eq]⟩
      · rw [hwalk2, hex1, hwalk3, hwalk4]

open scoped Classical in
set_option maxHeartbeats 2000000 in
/-- THE Phase B driver (pc 148 → verdict): from the Phase A output state
(the entry contract of `pb_loop`), the whole candidate × search cascade
runs to a verdict — and the run's VALUE is the membership decision
`decide (isSum (instA x) n x.t)`, independent of `ρ`. -/
theorem phaseB_exec {w n : Nat} (ρ : Nat → BitVec w) {x : Instance n}
    (hn : 4 ≤ n) (hw : wordLength n x.bits ≤ w)
    (bd : Nat) (f : Nat → Nat) (r S : Nat)
    (hfit : ∀ q, f q < 2 ^ w)
    (h1 : f 1 = 1) (h2 : f 2 = 0) (h7 : f 7 = n) (h8 : f 8 = 2 * n + 23)
    (h9 : f 9 = n / 2) (h18 : f 18 = bd)
    (hbd : bd = 3 * n + 25 ∨ bd = 3 * n + 25 + 2 ^ (n / 2) + 1)
    (harr : arrL f bd (2 ^ (n / 2)) = halfSums (instA x) (n / 2))
    (hrel : ∀ i, 1 ≤ i → i ≤ n → f (2 * n + 23 + i) = instA x (i - 1))
    (htgt : f (2 * n + 23 + (n + 1)) = x.t)
    (haddr : ∀ c, c ≤ 3 * n + 26 + 2 * 2 ^ (n / 2) → c < 2 ^ w)
    (hS : 6 + (11 * (n - n / 2) + 10 * (n / 2) + 29) * 2 ^ (n - n / 2) ≤ S) :
    ∃ c, c ≤ 6 + (11 * (n - n / 2) + 10 * (n / 2) + 29) * 2 ^ (n - n / 2) ∧
      exec prog ρ S 148 r (memOf w f)
        = some (decide (isSum (instA x) n x.t)) := by
  have htot : 2 * ((List.range n).map (instA x)).sum < 2 ^ w := by
    have h1' := two_sum_lt_pow_wordLength x (by omega)
    have h2' := Nat.pow_le_pow_right (n := 2) (by omega : (1:Nat) ≤ 2) hw
    omega
  obtain ⟨g, hex, g1, g2, g7, g8f, g9, g10, g11, g19, g22, g18f, gfit, gmem⟩ :=
    pb_pre (x := x) ρ f S r hfit h1 h2 h7 h9 haddr (by omega)
  have g8 := g8f.trans h8
  have g18 := g18f.trans h18
  have hrel' : ∀ i, 1 ≤ i → i ≤ n → g (2 * n + 23 + i) = instA x (i - 1) :=
    fun i hi1 hin => (gmem (2 * n + 23 + i) (by omega)).trans (hrel i hi1 hin)
  have htgt' : g (2 * n + 23 + (n + 1)) = x.t :=
    (gmem (2 * n + 23 + (n + 1)) (by omega)).trans htgt
  have harr' : arrL g bd (2 ^ (n / 2)) = halfSums (instA x) (n / 2) := by
    refine (arrL_congr (f := g) (g := f) ?_).trans harr
    intro i hi
    exact gmem (bd + i) (by omega)
  have hidx0 : (0:Nat) < 2 ^ (n - n / 2) := by
    have := Nat.one_le_two_pow (n := n - n / 2)
    omega
  have hpast0 : ∀ i, i < 0 →
      ¬ (candSum (fun i => instA x (n / 2 + i)) i 0 (n - n / 2) ≤ x.t ∧
        ∃ q, q < 2 ^ (n / 2) ∧ (halfSums (instA x) (n / 2)).getD q 0
          = x.t - candSum (fun i => instA x (n / 2 + i)) i 0 (n - n / 2)) :=
    fun i hi => absurd hi (by omega)
  have hfuel0 : 2 ^ (n - n / 2) - 0 ≤ 2 ^ (n - n / 2) := by omega
  have hS0 : (11 * (n - n / 2) + 10 * (n / 2) + 29) * (2 ^ (n - n / 2) - 0)
      ≤ S - 6 := by
    rw [Nat.sub_zero]
    omega
  have hres := pb_loop ρ hn (2 ^ (n - n / 2)) bd 0 g (S - 6) r g1 g2 g7 g8 g9 g10
    g11 g19 g22 g18 hbd harr' hrel' htgt' gfit haddr htot hidx0 hpast0 hfuel0 hS0
  obtain ⟨c, hc, hexec⟩ := hres
  refine ⟨6 + c, by rw [Nat.sub_zero] at hc; omega, ?_⟩
  rw [hex, hexec]
end SubsetSum.MITM
