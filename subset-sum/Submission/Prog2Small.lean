import Submission.Race
import Submission.Prog2
set_option autoImplicit true
set_option maxHeartbeats 2000000

/-!
# The small-n lane re-proven over `prog2` (R2125607749 Lanes 2+3)

For `n ∈ {2,3}` the prologue dispatches at pc 12 (`blt 0 3 ·`) to LSMALL,
which resolves to 244 in prog2 (192 in prog); smallN occupies pcs 244–300
(a uniform +52 shift of prog's 192–248 — the segment's internal jump
targets shift identically since `resolve` produces absolute positions).
This module ports SmallN.lean + Race.lean's `pro_segA23`/`pro_dispatch23`
and the small-n verdict theorems into `namespace SubsetSum.MITM.P2Small`
with that shift and `prog` → `prog2`.  Budgets 34/48 are UNCHANGED (the
small-n path executes identical instructions).
-/

namespace SubsetSum.MITM.P2Small

open BigOSpeedrun.SubsetSum SubsetSum.MITM.Spec

theorem run_eq_exec2 {n : Nat} (x : Instance n) (ρ : Nat → BitVec (wordLength n x.bits))
    (T : Nat) :
    run prog2 x ρ T
      = exec prog2 ρ T 0 0 (memOf (wordLength n x.bits) (inF x)) := rfl


/-! ## §0. The equality-test triple -/

/-- `blt ci cj L; blt cj ci L; accept` at consecutive pcs: equal
fitting values accept in 3 steps. -/
theorem eq_triple_eq {w : Nat} (ρ : Nat → BitVec w) (p L ci cj x y : Nat)
    (u : Nat → Nat) (S r : Nat)
    (hui : u ci = x) (huj : u cj = y) (hfit : ∀ q, u q < 2 ^ w)
    (heq : x = y) (hS : 3 ≤ S)
    (h1 : prog2.getD p Instr.reject = Instr.blt ci cj L)
    (h2 : prog2.getD (p + 1) Instr.reject = Instr.blt cj ci L)
    (h3 : prog2.getD (p + 2) Instr.reject = Instr.accept) :
    exec prog2 ρ S p r (memOf w u) = some true := by
  rw [exec_blt_ge_step (by omega) h1 hfit (by rw [hui, huj, heq]; omega),
    exec_blt_ge_step (by omega) h2 hfit (by rw [hui, huj, heq]; omega),
    exec_accept_step (by omega) h3]

/-- The same triple with unequal values: continue at `L` in at most 2
steps, memory unchanged. -/
theorem eq_triple_ne {w : Nat} (ρ : Nat → BitVec w) (p L ci cj x y : Nat)
    (u : Nat → Nat) (S r : Nat)
    (hui : u ci = x) (huj : u cj = y) (hfit : ∀ q, u q < 2 ^ w)
    (hne : x ≠ y) (hS : 2 ≤ S)
    (h1 : prog2.getD p Instr.reject = Instr.blt ci cj L)
    (h2 : prog2.getD (p + 1) Instr.reject = Instr.blt cj ci L) :
    ∃ c, c ≤ 2 ∧
      exec prog2 ρ S p r (memOf w u) = exec prog2 ρ (S - c) L r (memOf w u) := by
  by_cases hlt : x < y
  · refine ⟨1, by omega, ?_⟩
    rw [exec_blt_lt_step (by omega) h1 hfit (by rw [hui, huj]; omega)]
  · refine ⟨2, by omega, ?_⟩
    rw [exec_blt_ge_step (by omega) h1 hfit (by rw [hui, huj]; omega),
      exec_blt_lt_step (by omega) h2 hfit (by rw [hui, huj]; omega)]
    simp only [Nat.sub_sub, Nat.reduceAdd]

/-! ## §1. Spec level: the small-n subset-sum sets -/

theorem isSum_one_iff (a : Nat → Nat) (t : Nat) :
    isSum a 1 t ↔ t = 0 ∨ t = a 0 := by
  rw [isSum_succ]
  simp only [isSum_zero]
  constructor
  · rintro (h | ⟨t', rfl, ht⟩)
    · exact Or.inl h
    · exact Or.inr (by omega)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨0, rfl, by omega⟩

theorem isSum_two_iff (a : Nat → Nat) (t : Nat) :
    isSum a 2 t ↔ t ∈ [0, a 0, a 1, a 0 + a 1] := by
  rw [show (2:Nat) = 1 + 1 from rfl, isSum_succ]
  simp only [isSum_one_iff, List.mem_cons, List.not_mem_nil, or_false, false_or]
  constructor
  · rintro ((h | h) | ⟨t', (rfl | rfl), ht⟩)
    · omega
    · omega
    · omega
    · omega
  · rintro (h | h | h | h)
    · left; omega
    · left; omega
    · right; exact ⟨0, by omega, by omega⟩
    · right; exact ⟨a 0, by omega, by omega⟩

theorem isSum_three_iff (a : Nat → Nat) (t : Nat) :
    isSum a 3 t ↔ t ∈ [0, a 0, a 1, a 0 + a 1, a 2, a 2 + a 0, a 2 + a 1,
      a 2 + a 0 + a 1] := by
  rw [show (3:Nat) = 2 + 1 from rfl, isSum_succ]
  simp only [isSum_two_iff, List.mem_cons, List.not_mem_nil, or_false, false_or]
  constructor
  · rintro (h | ⟨t', (rfl | rfl | rfl | rfl), ht⟩)
    · omega
    · omega
    · omega
    · omega
    · omega
  · rintro (h | h | h | h | h | h | h | h)
    · left; omega
    · left; omega
    · left; omega
    · left; omega
    · right; exact ⟨0, by omega, by omega⟩
    · right; exact ⟨a 0, by omega, by omega⟩
    · right; exact ⟨a 1, by omega, by omega⟩
    · right; exact ⟨a 0 + a 1, by omega, by omega⟩

/-! ## §2. The shared load prefix (pcs 244–253) -/

/-- The first ten instructions: `T1 := 2n` and load cells `15/16/17`
from `mem[2n], mem[2n+1], mem[2n+2]`, then `T2 := 7` and stop AT the
split guard pc 253.  Works for both `n = 2` (`cur = 6`) and `n = 3`
(`cur = 8`). -/
theorem smalln_loads {w : Nat} (ρ : Nat → BitVec w) (cur v4 v5 v6 : Nat)
    (f : Nat → Nat) (S r : Nat)
    (hf0 : f 0 = cur) (hf1 : f 1 = 1) (hf2 : f 2 = 0) (hf3 : f 3 = 9)
    (hfA : f (cur - 2) = v4) (hfB : f (cur - 1) = v5) (hfC : f cur = v6)
    (hcur : 3 ≤ cur) (hcur8 : cur ≤ 8)
    (hfit : ∀ q, f q < 2 ^ w) (hS : 10 ≤ S) :
    ∃ g, exec prog2 ρ S 244 r (memOf w f)
        = exec prog2 ρ (S - 9) 253 r (memOf w g) ∧
      g 15 = v4 ∧ g 16 = v5 ∧ g 17 = v6 ∧ g 21 = 7 ∧ g 0 = cur ∧
      g 1 = 1 ∧ g 2 = 0 ∧ g 3 = 9 ∧ (∀ q, g q < 2 ^ w) ∧
      (∀ q, q ≠ 15 → q ≠ 16 → q ≠ 17 → q ≠ 20 → q ≠ 21 → g q = f q) := by
  have h9 : 9 < 2 ^ w := by have := hfit 3; rw [hf3] at this; omega
  have hcurW : cur < 2 ^ w := by have := hfit 0; rw [hf0] at this; omega
  have hv4W : v4 < 2 ^ w := by have := hfit (cur - 2); rw [hfA] at this; omega
  have hv5W : v5 < 2 ^ w := by have := hfit (cur - 1); rw [hfB] at this; omega
  have hv6W : v6 < 2 ^ w := by have := hfit cur; rw [hfC] at this; omega
  have e193 : (up f 20 (cur - 1)) 20 - (up f 20 (cur - 1)) 1 = cur - 2 := by
    rw [up_eq, up_ne (show (1:Nat) ≠ 20 by omega), hf1]
    omega
  have fA1 : ∀ q, (up f 20 (cur - 1)) q < 2 ^ w := fit_up hfit (by omega)
  have fA2 : ∀ q, (up (up f 20 (cur - 1)) 20 (cur - 2)) q < 2 ^ w :=
    fit_up fA1 (by omega)
  have e194 : (up (up f 20 (cur - 1)) 20 (cur - 2))
      ((up (up f 20 (cur - 1)) 20 (cur - 2)) 20) = v4 := by
    rw [up_eq, up_ne (show cur - 2 ≠ 20 by omega),
      up_ne (show cur - 2 ≠ 20 by omega), hfA]
  have fA3 : ∀ q, (up (up (up f 20 (cur - 1)) 20 (cur - 2)) 15 v4) q < 2 ^ w :=
    fit_up fA2 hv4W
  have e195 : (up (up (up f 20 (cur - 1)) 20 (cur - 2)) 15 v4) 20
      + (up (up (up f 20 (cur - 1)) 20 (cur - 2)) 15 v4) 1 = cur - 1 := by
    rw [up_ne (show (20:Nat) ≠ 15 by omega), up_ne (show (1:Nat) ≠ 15 by omega),
      up_eq, up_ne (show (1:Nat) ≠ 20 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega), hf1]
    omega
  have fA4 : ∀ q,
      (up (up (up (up f 20 (cur - 1)) 20 (cur - 2)) 15 v4) 20 (cur - 1)) q
        < 2 ^ w := fit_up fA3 (by omega)
  have e196 : (up (up (up (up f 20 (cur - 1)) 20 (cur - 2)) 15 v4) 20 (cur - 1))
      ((up (up (up (up f 20 (cur - 1)) 20 (cur - 2)) 15 v4) 20 (cur - 1)) 20)
      = v5 := by
    rw [up_eq, up_ne (show cur - 1 ≠ 20 by omega),
      up_ne (show cur - 1 ≠ 15 by omega), up_ne (show cur - 1 ≠ 20 by omega),
      up_ne (show cur - 1 ≠ 20 by omega), hfB]
  have fA5 : ∀ q,
      (up (up (up (up (up f 20 (cur - 1)) 20 (cur - 2)) 15 v4) 20 (cur - 1))
        16 v5) q < 2 ^ w := fit_up fA4 (by omega)
  have e197 : (up (up (up (up (up f 20 (cur - 1)) 20 (cur - 2)) 15 v4)
        20 (cur - 1)) 16 v5) 20
      + (up (up (up (up (up f 20 (cur - 1)) 20 (cur - 2)) 15 v4)
        20 (cur - 1)) 16 v5) 1 = cur := by
    rw [up_ne (show (20:Nat) ≠ 16 by omega), up_ne (show (1:Nat) ≠ 16 by omega),
      up_eq, up_ne (show (1:Nat) ≠ 20 by omega),
      up_ne (show (1:Nat) ≠ 15 by omega), up_ne (show (1:Nat) ≠ 20 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega), hf1]
    omega
  have fA6 : ∀ q,
      (up (up (up (up (up (up f 20 (cur - 1)) 20 (cur - 2)) 15 v4)
        20 (cur - 1)) 16 v5) 20 cur) q < 2 ^ w := fit_up fA5 (by omega)
  have e198 : (up (up (up (up (up (up f 20 (cur - 1)) 20 (cur - 2)) 15 v4)
        20 (cur - 1)) 16 v5) 20 cur)
      ((up (up (up (up (up (up f 20 (cur - 1)) 20 (cur - 2)) 15 v4)
        20 (cur - 1)) 16 v5) 20 cur) 20) = v6 := by
    rw [up_eq, up_ne (show cur ≠ 20 by omega), up_ne (show cur ≠ 16 by omega),
      up_ne (show cur ≠ 20 by omega), up_ne (show cur ≠ 15 by omega),
      up_ne (show cur ≠ 20 by omega), up_ne (show cur ≠ 20 by omega), hfC]
  have fA7 : ∀ q,
      (up (up (up (up (up (up (up f 20 (cur - 1)) 20 (cur - 2)) 15 v4)
        20 (cur - 1)) 16 v5) 20 cur) 17 v6) q < 2 ^ w :=
    fit_up fA6 (by omega)
  have e199 : (up (up (up (up (up (up (up f 20 (cur - 1)) 20 (cur - 2)) 15 v4)
        20 (cur - 1)) 16 v5) 20 cur) 17 v6) 3
      - (up (up (up (up (up (up (up f 20 (cur - 1)) 20 (cur - 2)) 15 v4)
        20 (cur - 1)) 16 v5) 20 cur) 17 v6) 1 = 8 := by
    rw [up_ne (show (3:Nat) ≠ 17 by omega), up_ne (show (1:Nat) ≠ 17 by omega),
      up_ne (show (3:Nat) ≠ 20 by omega), up_ne (show (1:Nat) ≠ 20 by omega),
      up_ne (show (3:Nat) ≠ 16 by omega), up_ne (show (1:Nat) ≠ 16 by omega),
      up_ne (show (3:Nat) ≠ 20 by omega), up_ne (show (1:Nat) ≠ 20 by omega),
      up_ne (show (3:Nat) ≠ 15 by omega), up_ne (show (1:Nat) ≠ 15 by omega),
      up_ne (show (3:Nat) ≠ 20 by omega), up_ne (show (1:Nat) ≠ 20 by omega),
      up_ne (show (3:Nat) ≠ 20 by omega), up_ne (show (1:Nat) ≠ 20 by omega),
      hf3, hf1]
  have fA8 : ∀ q,
      (up (up (up (up (up (up (up (up f 20 (cur - 1)) 20 (cur - 2)) 15 v4)
        20 (cur - 1)) 16 v5) 20 cur) 17 v6) 21 8) q < 2 ^ w :=
    fit_up fA7 (by omega)
  have e200 : (up (up (up (up (up (up (up (up f 20 (cur - 1)) 20 (cur - 2))
        15 v4) 20 (cur - 1)) 16 v5) 20 cur) 17 v6) 21 8) 21
      - (up (up (up (up (up (up (up (up f 20 (cur - 1)) 20 (cur - 2)) 15 v4)
        20 (cur - 1)) 16 v5) 20 cur) 17 v6) 21 8) 1 = 7 := by
    rw [up_eq, up_ne (show (1:Nat) ≠ 21 by omega),
      up_ne (show (1:Nat) ≠ 17 by omega), up_ne (show (1:Nat) ≠ 20 by omega),
      up_ne (show (1:Nat) ≠ 16 by omega), up_ne (show (1:Nat) ≠ 20 by omega),
      up_ne (show (1:Nat) ≠ 15 by omega), up_ne (show (1:Nat) ≠ 20 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega), hf1]
  refine ⟨up (up (up (up (up (up (up (up (up f 20 (cur - 1)) 20 (cur - 2))
    15 v4) 20 (cur - 1)) 16 v5) 20 cur) 17 v6) 21 8) 21 7, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [exec_sub_step (by omega)
        (show prog2.getD 244 Instr.reject = Instr.sub 20 0 1 by rfl) hfit
        (by omega), hf0, hf1,
      exec_sub_step (by omega)
        (show prog2.getD 245 Instr.reject = Instr.sub 20 20 1 by rfl) fA1
        (by rw [up_ne (show (1:Nat) ≠ 20 by omega), up_eq]; omega), e193,
      exec_load_step (by omega)
        (show prog2.getD 246 Instr.reject = Instr.load 15 20 by rfl) fA2, e194,
      exec_add_step (by omega)
        (show prog2.getD 247 Instr.reject = Instr.add 20 20 1 by rfl), e195,
      exec_load_step (by omega)
        (show prog2.getD 248 Instr.reject = Instr.load 16 20 by rfl) fA4, e196,
      exec_add_step (by omega)
        (show prog2.getD 249 Instr.reject = Instr.add 20 20 1 by rfl), e197,
      exec_load_step (by omega)
        (show prog2.getD 250 Instr.reject = Instr.load 17 20 by rfl) fA6, e198,
      exec_sub_step (by omega)
        (show prog2.getD 251 Instr.reject = Instr.sub 21 3 1 by rfl) fA7
        (by rw [up_ne (show (1:Nat) ≠ 17 by omega),
            up_ne (show (3:Nat) ≠ 17 by omega),
            up_ne (show (1:Nat) ≠ 20 by omega),
            up_ne (show (3:Nat) ≠ 20 by omega),
            up_ne (show (1:Nat) ≠ 16 by omega),
            up_ne (show (3:Nat) ≠ 16 by omega),
            up_ne (show (1:Nat) ≠ 20 by omega),
            up_ne (show (3:Nat) ≠ 20 by omega),
            up_ne (show (1:Nat) ≠ 15 by omega),
            up_ne (show (3:Nat) ≠ 15 by omega),
            up_ne (show (1:Nat) ≠ 20 by omega),
            up_ne (show (3:Nat) ≠ 20 by omega),
            up_ne (show (1:Nat) ≠ 20 by omega),
            up_ne (show (3:Nat) ≠ 20 by omega),
            hf1, hf3]; omega), e199,
      exec_sub_step (by omega)
        (show prog2.getD 252 Instr.reject = Instr.sub 21 21 1 by rfl) fA8
        (by rw [up_eq, up_ne (show (1:Nat) ≠ 21 by omega),
            up_ne (show (1:Nat) ≠ 17 by omega),
            up_ne (show (1:Nat) ≠ 20 by omega),
            up_ne (show (1:Nat) ≠ 16 by omega),
            up_ne (show (1:Nat) ≠ 20 by omega),
            up_ne (show (1:Nat) ≠ 15 by omega),
            up_ne (show (1:Nat) ≠ 20 by omega),
            up_ne (show (1:Nat) ≠ 20 by omega), hf1]; omega), e200]
    simp only [Nat.sub_sub, Nat.reduceAdd]
  · rw [up_ne (show (15:Nat) ≠ 21 by omega), up_ne (show (15:Nat) ≠ 21 by omega),
      up_ne (show (15:Nat) ≠ 17 by omega), up_ne (show (15:Nat) ≠ 20 by omega),
      up_ne (show (15:Nat) ≠ 16 by omega), up_ne (show (15:Nat) ≠ 20 by omega),
      up_eq]
  · rw [up_ne (show (16:Nat) ≠ 21 by omega), up_ne (show (16:Nat) ≠ 21 by omega),
      up_ne (show (16:Nat) ≠ 17 by omega), up_ne (show (16:Nat) ≠ 20 by omega),
      up_eq]
  · rw [up_ne (show (17:Nat) ≠ 21 by omega), up_ne (show (17:Nat) ≠ 21 by omega),
      up_eq]
  · rw [up_eq]
  · rw [up_ne (show (0:Nat) ≠ 21 by omega), up_ne (show (0:Nat) ≠ 21 by omega),
      up_ne (show (0:Nat) ≠ 17 by omega), up_ne (show (0:Nat) ≠ 20 by omega),
      up_ne (show (0:Nat) ≠ 16 by omega), up_ne (show (0:Nat) ≠ 20 by omega),
      up_ne (show (0:Nat) ≠ 15 by omega), up_ne (show (0:Nat) ≠ 20 by omega),
      up_ne (show (0:Nat) ≠ 20 by omega), hf0]
  · rw [up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (1:Nat) ≠ 21 by omega),
      up_ne (show (1:Nat) ≠ 17 by omega), up_ne (show (1:Nat) ≠ 20 by omega),
      up_ne (show (1:Nat) ≠ 16 by omega), up_ne (show (1:Nat) ≠ 20 by omega),
      up_ne (show (1:Nat) ≠ 15 by omega), up_ne (show (1:Nat) ≠ 20 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega), hf1]
  · rw [up_ne (show (2:Nat) ≠ 21 by omega), up_ne (show (2:Nat) ≠ 21 by omega),
      up_ne (show (2:Nat) ≠ 17 by omega), up_ne (show (2:Nat) ≠ 20 by omega),
      up_ne (show (2:Nat) ≠ 16 by omega), up_ne (show (2:Nat) ≠ 20 by omega),
      up_ne (show (2:Nat) ≠ 15 by omega), up_ne (show (2:Nat) ≠ 20 by omega),
      up_ne (show (2:Nat) ≠ 20 by omega), hf2]
  · rw [up_ne (show (3:Nat) ≠ 21 by omega), up_ne (show (3:Nat) ≠ 21 by omega),
      up_ne (show (3:Nat) ≠ 17 by omega), up_ne (show (3:Nat) ≠ 20 by omega),
      up_ne (show (3:Nat) ≠ 16 by omega), up_ne (show (3:Nat) ≠ 20 by omega),
      up_ne (show (3:Nat) ≠ 15 by omega), up_ne (show (3:Nat) ≠ 20 by omega),
      up_ne (show (3:Nat) ≠ 20 by omega), hf3]
  · exact fit_up fA8 (by omega)
  · intro q h15 h16 h17 h20 h21
    rw [up_ne (show q ≠ 21 by omega), up_ne (show q ≠ 21 by omega),
      up_ne (show q ≠ 17 by omega), up_ne (show q ≠ 20 by omega),
      up_ne (show q ≠ 16 by omega), up_ne (show q ≠ 20 by omega),
      up_ne (show q ≠ 15 by omega), up_ne (show q ≠ 20 by omega),
      up_ne (show q ≠ 20 by omega)]

/-! ## §3. The n = 2 verdict -/

/-- `n = 2` (cursor 6, saved `a₁ @4, a₂ @5, t @6`): the unrolled code
decides `t ∈ {0, a₁, a₂, a₁+a₂}` in at most 21 steps. -/
theorem smalln2_exec {w : Nat} (ρ : Nat → BitVec w) (a1 a2 t : Nat)
    (f : Nat → Nat) (S r : Nat)
    (hf0 : f 0 = 6) (hf1 : f 1 = 1) (hf2 : f 2 = 0) (hf3 : f 3 = 9)
    (hf4 : f 4 = a1) (hf5 : f 5 = a2) (hf6 : f 6 = t)
    (hv12 : a1 + a2 < 2 ^ w)
    (hfit : ∀ q, f q < 2 ^ w)
    (hS : 21 ≤ S) :
    exec prog2 ρ S 244 r (memOf w f)
      = some (decide (t ∈ [0, a1, a2, a1 + a2])) := by
  obtain ⟨g, hex, hg15, hg16, hg17, hg21, hg0, hg1, hg2, _, hgfit, _⟩ :=
    smalln_loads ρ 6 a1 a2 t f S r hf0 hf1 hf2 hf3
      (by simpa using hf4) (by simpa using hf5) hf6 (by omega) (by omega) hfit
      (by omega)
  have e207 : g 17 + g 2 = t := by rw [hg17, hg2]; omega
  have fW : ∀ q, (up g 14 t) q < 2 ^ w := by
    have h17 := hgfit 17
    rw [hg17] at h17
    exact fit_up hgfit (by omega)
  have u14 : (up g 14 t) 14 = t := up_eq _ _ _
  have u15 : (up g 14 t) 15 = a1 := by
    rw [up_ne (show (15:Nat) ≠ 14 by omega), hg15]
  have u16 : (up g 14 t) 16 = a2 := by
    rw [up_ne (show (16:Nat) ≠ 14 by omega), hg16]
  have u1 : (up g 14 t) 1 = 1 := by
    rw [up_ne (show (1:Nat) ≠ 14 by omega), hg1]
  have u2 : (up g 14 t) 2 = 0 := by
    rw [up_ne (show (2:Nat) ≠ 14 by omega), hg2]
  have u21 : (up g 14 t) 21 = 7 := by
    rw [up_ne (show (21:Nat) ≠ 14 by omega), hg21]
  -- 253 taken (6 < 7) → 259: W := t; 260: t < 1 ?
  rw [hex,
    exec_blt_lt_step (by omega)
      (show prog2.getD 253 Instr.reject = Instr.blt 0 21 259 by rfl) hgfit
      (by rw [hg0, hg21]; omega),
    exec_add_step (by omega)
      (show prog2.getD 259 Instr.reject = Instr.add 14 17 2 by rfl), e207]
  rcases Nat.eq_zero_or_pos t with ht0 | ht0
  · rw [exec_blt_lt_step (by omega)
      (show prog2.getD 260 Instr.reject = Instr.blt 14 1 272 by rfl) fW
      (by rw [u14, u1]; omega),
    exec_accept_step (by omega)
      (show prog2.getD 272 Instr.reject = Instr.accept by rfl)]
    have hmem : t ∈ [0, a1, a2, a1 + a2] := by
      simp [List.mem_cons, List.mem_singleton, ht0]
    rw [decide_eq_true_iff.mpr hmem]
  · -- t ≥ 1: 261: T2 := a1 + a2, then the ladder at 262
    have e209 : (up g 14 t) 15 + (up g 14 t) 16 = a1 + a2 := by rw [u15, u16]
    have fT2 : ∀ q, (up (up g 14 t) 21 (a1 + a2)) q < 2 ^ w := fit_up fW hv12
    rw [exec_blt_ge_step (by omega)
      (show prog2.getD 260 Instr.reject = Instr.blt 14 1 272 by rfl) fW
      (by rw [u14, u1]; omega),
    exec_add_step (by omega)
      (show prog2.getD 261 Instr.reject = Instr.add 21 15 16 by rfl), e209]
    simp only [Nat.sub_sub, Nat.reduceAdd]
    have v15 : (up (up g 14 t) 21 (a1 + a2)) 15 = a1 := by
      rw [up_ne (show (15:Nat) ≠ 21 by omega), u15]
    have v14 : (up (up g 14 t) 21 (a1 + a2)) 14 = t := by
      rw [up_ne (show (14:Nat) ≠ 21 by omega), u14]
    have v16 : (up (up g 14 t) 21 (a1 + a2)) 16 = a2 := by
      rw [up_ne (show (16:Nat) ≠ 21 by omega), u16]
    have v21 : (up (up g 14 t) 21 (a1 + a2)) 21 = a1 + a2 := up_eq _ _ _
    by_cases hta : t = a1
    · rw [eq_triple_eq ρ 262 265 15 14 a1 t _ (S - 13) r v15 v14 fT2
        (by rw [hta]) (by omega)
        (show prog2.getD 262 Instr.reject = Instr.blt 15 14 265 by rfl)
        (show prog2.getD 263 Instr.reject = Instr.blt 14 15 265 by rfl)
        (show prog2.getD 264 Instr.reject = Instr.accept by rfl)]
      have hmem : t ∈ [0, a1, a2, a1 + a2] := by
        simp [List.mem_cons, List.mem_singleton, hta]
      rw [decide_eq_true_iff.mpr hmem]
    · obtain ⟨c1, hc1, hch1⟩ := eq_triple_ne ρ 262 265 15 14 a1 t _ (S - 13) r
        v15 v14 fT2 (Ne.symm hta) (by omega)
        (show prog2.getD 262 Instr.reject = Instr.blt 15 14 265 by rfl)
        (show prog2.getD 263 Instr.reject = Instr.blt 14 15 265 by rfl)
      rw [hch1]
      by_cases htb : t = a2
      · rw [eq_triple_eq ρ 265 268 16 14 a2 t _ ((S - 13) - c1) r v16 v14 fT2
          (by rw [htb]) (by omega)
          (show prog2.getD 265 Instr.reject = Instr.blt 16 14 268 by rfl)
          (show prog2.getD 266 Instr.reject = Instr.blt 14 16 268 by rfl)
          (show prog2.getD 267 Instr.reject = Instr.accept by rfl)]
        have hmem : t ∈ [0, a1, a2, a1 + a2] := by
          simp [List.mem_cons, List.mem_singleton, htb]
        rw [decide_eq_true_iff.mpr hmem]
      · obtain ⟨c2, hc2, hch2⟩ := eq_triple_ne ρ 265 268 16 14 a2 t _
          ((S - 13) - c1) r v16 v14 fT2 (Ne.symm htb) (by omega)
          (show prog2.getD 265 Instr.reject = Instr.blt 16 14 268 by rfl)
          (show prog2.getD 266 Instr.reject = Instr.blt 14 16 268 by rfl)
        rw [hch2]
        by_cases htc : t = a1 + a2
        · rw [eq_triple_eq ρ 268 271 21 14 (a1 + a2) t _ ((S - 13) - c1 - c2) r
            v21 v14 fT2 (by rw [htc]) (by omega)
            (show prog2.getD 268 Instr.reject = Instr.blt 21 14 271 by rfl)
            (show prog2.getD 269 Instr.reject = Instr.blt 14 21 271 by rfl)
            (show prog2.getD 270 Instr.reject = Instr.accept by rfl)]
          have hmem : t ∈ [0, a1, a2, a1 + a2] := by
            simp [List.mem_cons, List.mem_singleton, htc]
          rw [decide_eq_true_iff.mpr hmem]
        · obtain ⟨c3, hc3, hch3⟩ := eq_triple_ne ρ 268 271 21 14 (a1 + a2) t _
            ((S - 13) - c1 - c2) r v21 v14 fT2 (Ne.symm htc) (by omega)
            (show prog2.getD 268 Instr.reject = Instr.blt 21 14 271 by rfl)
            (show prog2.getD 269 Instr.reject = Instr.blt 14 21 271 by rfl)
          rw [hch3,
            exec_reject_step (by omega)
              (show prog2.getD 271 Instr.reject = Instr.reject by rfl)]
          have hmem : ¬ t ∈ [0, a1, a2, a1 + a2] := by
            simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
              or_false]
            omega
          simp [hmem]

/-! ## §4. The n = 3 verdict -/

/-- `n = 3` (cursor 8, saved `a₁ @6, a₂ @7, a₃ @8`, `t` pristine at
cell 4): the unrolled code decides `t` against the full 8-element
subset-sum set in at most 35 steps. -/
theorem smalln3_exec {w : Nat} (ρ : Nat → BitVec w) (a1 a2 a3 t : Nat)
    (f : Nat → Nat) (S r : Nat)
    (hf0 : f 0 = 8) (hf1 : f 1 = 1) (hf2 : f 2 = 0) (hf3 : f 3 = 9)
    (hf4 : f 4 = t) (hf6 : f 6 = a1) (hf7 : f 7 = a2) (hf8 : f 8 = a3)
    (hv12 : a1 + a2 < 2 ^ w) (hv31 : a3 + a1 < 2 ^ w)
    (hv32 : a3 + a2 < 2 ^ w) (hv312 : a3 + a1 + a2 < 2 ^ w)
    (hfit : ∀ q, f q < 2 ^ w)
    (hS : 35 ≤ S) :
    exec prog2 ρ S 244 r (memOf w f)
      = some (decide (t ∈ [0, a1, a2, a1 + a2, a3, a3 + a1, a3 + a2,
          a3 + a1 + a2])) := by
  obtain ⟨g, hex, hg15, hg16, hg17, hg21, hg0, hg1, hg2, hg3, hgfit, hgpres⟩ :=
    smalln_loads ρ 8 a1 a2 a3 f S r hf0 hf1 hf2 hf3
      (by simpa using hf6) (by simpa using hf7) hf8 (by omega) (by omega)
      hfit (by omega)
  have hpow : 4 < 2 ^ w := by
    have h9 := hfit 3
    rw [hf3] at h9
    omega
  -- 253 NOT taken (8 < 7 false); 254–256: T2 := 2, 3, 4; 257: W := t
  have e202 : g 1 + g 1 = 2 := by rw [hg1]
  have fB1 : ∀ q, (up g 21 2) q < 2 ^ w := fit_up hgfit (by omega)
  have e203 : (up g 21 2) 21 + (up g 21 2) 1 = 3 := by
    rw [up_eq, up_ne (show (1:Nat) ≠ 21 by omega), hg1]
  have fB2 : ∀ q, (up (up g 21 2) 21 3) q < 2 ^ w := fit_up fB1 (by omega)
  have e204 : (up (up g 21 2) 21 3) 21 + (up (up g 21 2) 21 3) 1 = 4 := by
    rw [up_eq, up_ne (show (1:Nat) ≠ 21 by omega),
      up_ne (show (1:Nat) ≠ 21 by omega), hg1]
  have fB3 : ∀ q, (up (up (up g 21 2) 21 3) 21 4) q < 2 ^ w :=
    fit_up fB2 (by omega)
  have e205 : (up (up (up g 21 2) 21 3) 21 4)
      ((up (up (up g 21 2) 21 3) 21 4) 21) = t := by
    rw [up_eq, up_ne (show (4:Nat) ≠ 21 by omega),
      up_ne (show (4:Nat) ≠ 21 by omega), up_ne (show (4:Nat) ≠ 21 by omega),
      hgpres 4 (by omega) (by omega) (by omega) (by omega) (by omega), hf4]
  have htW : t < 2 ^ w := by
    have h4 := hfit 4
    rw [hf4] at h4
    exact h4
  have fB4 : ∀ q,
      (up (up (up (up g 21 2) 21 3) 21 4) 14 t) q < 2 ^ w :=
    fit_up fB3 htW
  -- state facts at pc 273
  have k14 : (up (up (up (up g 21 2) 21 3) 21 4) 14 t) 14 = t := up_eq _ _ _
  have k15 : (up (up (up (up g 21 2) 21 3) 21 4) 14 t) 15 = a1 := by
    rw [up_ne (show (15:Nat) ≠ 14 by omega),
      up_ne (show (15:Nat) ≠ 21 by omega),
      up_ne (show (15:Nat) ≠ 21 by omega),
      up_ne (show (15:Nat) ≠ 21 by omega), hg15]
  have k16 : (up (up (up (up g 21 2) 21 3) 21 4) 14 t) 16 = a2 := by
    rw [up_ne (show (16:Nat) ≠ 14 by omega),
      up_ne (show (16:Nat) ≠ 21 by omega),
      up_ne (show (16:Nat) ≠ 21 by omega),
      up_ne (show (16:Nat) ≠ 21 by omega), hg16]
  have k17 : (up (up (up (up g 21 2) 21 3) 21 4) 14 t) 17 = a3 := by
    rw [up_ne (show (17:Nat) ≠ 14 by omega),
      up_ne (show (17:Nat) ≠ 21 by omega),
      up_ne (show (17:Nat) ≠ 21 by omega),
      up_ne (show (17:Nat) ≠ 21 by omega), hg17]
  have k1 : (up (up (up (up g 21 2) 21 3) 21 4) 14 t) 1 = 1 := by
    rw [up_ne (show (1:Nat) ≠ 14 by omega), up_ne (show (1:Nat) ≠ 21 by omega),
      up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (1:Nat) ≠ 21 by omega),
      hg1]
  rw [hex,
    exec_blt_ge_step (by omega)
      (show prog2.getD 253 Instr.reject = Instr.blt 0 21 259 by rfl) hgfit
      (by rw [hg0, hg21]; omega),
    exec_add_step (by omega)
      (show prog2.getD 254 Instr.reject = Instr.add 21 1 1 by rfl), e202,
    exec_add_step (by omega)
      (show prog2.getD 255 Instr.reject = Instr.add 21 21 1 by rfl), e203,
    exec_add_step (by omega)
      (show prog2.getD 256 Instr.reject = Instr.add 21 21 1 by rfl), e204,
    exec_load_step (by omega)
      (show prog2.getD 257 Instr.reject = Instr.load 14 21 by rfl) fB3, e205,
    exec_blt_lt_step (by omega)
      (show prog2.getD 258 Instr.reject = Instr.blt 2 1 273 by rfl) fB4
      (by rw [up_ne (show (2:Nat) ≠ 14 by omega),
        up_ne (show (1:Nat) ≠ 14 by omega), up_ne (show (2:Nat) ≠ 21 by omega),
        up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (2:Nat) ≠ 21 by omega),
        up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (2:Nat) ≠ 21 by omega),
        up_ne (show (1:Nat) ≠ 21 by omega), hg2, hg1]; omega)]
  -- pc 273, horizon S - 16, state b4
  rcases Nat.eq_zero_or_pos t with ht0 | ht0
  · rw [exec_blt_lt_step (by omega)
      (show prog2.getD 273 Instr.reject = Instr.blt 14 1 300 by rfl) fB4
      (by rw [k14, k1]; omega),
    exec_accept_step (by omega)
      (show prog2.getD 300 Instr.reject = Instr.accept by rfl)]
    have hmem : t ∈ [0, a1, a2, a1 + a2, a3, a3 + a1, a3 + a2, a3 + a1 + a2] :=
      by simp [List.mem_cons, List.mem_singleton, ht0]
    rw [decide_eq_true_iff.mpr hmem]
  · -- 274: T2 := a1 + a2, then the ladder at 275
    have e222 : (up (up (up (up g 21 2) 21 3) 21 4) 14 t) 15
        + (up (up (up (up g 21 2) 21 3) 21 4) 14 t) 16 = a1 + a2 := by
      rw [k15, k16]
    have fW1 : ∀ q,
        (up (up (up (up (up g 21 2) 21 3) 21 4) 14 t) 21 (a1 + a2)) q < 2 ^ w :=
      fit_up fB4 hv12
    rw [exec_blt_ge_step (by omega)
      (show prog2.getD 273 Instr.reject = Instr.blt 14 1 300 by rfl) fB4
      (by rw [k14, k1]; omega),
    exec_add_step (by omega)
      (show prog2.getD 274 Instr.reject = Instr.add 21 15 16 by rfl), e222]
    simp only [Nat.sub_sub, Nat.reduceAdd]
    -- state w1, pc 275, horizon S - 17
    have v15 : (up (up (up (up (up g 21 2) 21 3) 21 4) 14 t) 21 (a1 + a2)) 15
        = a1 := by rw [up_ne (show (15:Nat) ≠ 21 by omega), k15]
    have v16 : (up (up (up (up (up g 21 2) 21 3) 21 4) 14 t) 21 (a1 + a2)) 16
        = a2 := by rw [up_ne (show (16:Nat) ≠ 21 by omega), k16]
    have v17 : (up (up (up (up (up g 21 2) 21 3) 21 4) 14 t) 21 (a1 + a2)) 17
        = a3 := by rw [up_ne (show (17:Nat) ≠ 21 by omega), k17]
    have v14 : (up (up (up (up (up g 21 2) 21 3) 21 4) 14 t) 21 (a1 + a2)) 14
        = t := by rw [up_ne (show (14:Nat) ≠ 21 by omega), k14]
    have v21 : (up (up (up (up (up g 21 2) 21 3) 21 4) 14 t) 21 (a1 + a2)) 21
        = a1 + a2 := up_eq _ _ _
    by_cases hta : t = a1
    · rw [eq_triple_eq ρ 275 278 15 14 a1 t _ (S - 17) r v15 v14 fW1
        (by rw [hta]) (by omega)
        (show prog2.getD 275 Instr.reject = Instr.blt 15 14 278 by rfl)
        (show prog2.getD 276 Instr.reject = Instr.blt 14 15 278 by rfl)
        (show prog2.getD 277 Instr.reject = Instr.accept by rfl)]
      have hmem : t ∈ [0, a1, a2, a1 + a2, a3, a3 + a1, a3 + a2,
          a3 + a1 + a2] := by simp [List.mem_cons, List.mem_singleton, hta]
      rw [decide_eq_true_iff.mpr hmem]
    · obtain ⟨c1, hc1, hch1⟩ := eq_triple_ne ρ 275 278 15 14 a1 t _ (S - 17) r
        v15 v14 fW1 (Ne.symm hta) (by omega)
        (show prog2.getD 275 Instr.reject = Instr.blt 15 14 278 by rfl)
        (show prog2.getD 276 Instr.reject = Instr.blt 14 15 278 by rfl)
      rw [hch1]
      by_cases htb : t = a2
      · rw [eq_triple_eq ρ 278 281 16 14 a2 t _ ((S - 17) - c1) r v16 v14 fW1
          (by rw [htb]) (by omega)
          (show prog2.getD 278 Instr.reject = Instr.blt 16 14 281 by rfl)
          (show prog2.getD 279 Instr.reject = Instr.blt 14 16 281 by rfl)
          (show prog2.getD 280 Instr.reject = Instr.accept by rfl)]
        have hmem : t ∈ [0, a1, a2, a1 + a2, a3, a3 + a1, a3 + a2,
            a3 + a1 + a2] := by simp [List.mem_cons, List.mem_singleton, htb]
        rw [decide_eq_true_iff.mpr hmem]
      · obtain ⟨c2, hc2, hch2⟩ := eq_triple_ne ρ 278 281 16 14 a2 t _
          ((S - 17) - c1) r v16 v14 fW1 (Ne.symm htb) (by omega)
          (show prog2.getD 278 Instr.reject = Instr.blt 16 14 281 by rfl)
          (show prog2.getD 279 Instr.reject = Instr.blt 14 16 281 by rfl)
        rw [hch2]
        by_cases htc : t = a1 + a2
        · rw [eq_triple_eq ρ 281 284 21 14 (a1 + a2) t _
              ((S - 17) - c1 - c2) r v21 v14 fW1 (by rw [htc]) (by omega)
            (show prog2.getD 281 Instr.reject = Instr.blt 21 14 284 by rfl)
            (show prog2.getD 282 Instr.reject = Instr.blt 14 21 284 by rfl)
            (show prog2.getD 283 Instr.reject = Instr.accept by rfl)]
          have hmem : t ∈ [0, a1, a2, a1 + a2, a3, a3 + a1, a3 + a2,
              a3 + a1 + a2] := by simp [List.mem_cons, List.mem_singleton, htc]
          rw [decide_eq_true_iff.mpr hmem]
        · obtain ⟨c3, hc3, hch3⟩ := eq_triple_ne ρ 281 284 21 14 (a1 + a2) t _
            ((S - 17) - c1 - c2) r v21 v14 fW1 (Ne.symm htc) (by omega)
            (show prog2.getD 281 Instr.reject = Instr.blt 21 14 284 by rfl)
            (show prog2.getD 282 Instr.reject = Instr.blt 14 21 284 by rfl)
          rw [hch3]
          by_cases htd : t = a3
          · rw [eq_triple_eq ρ 284 287 17 14 a3 t _ ((S - 17) - c1 - c2 - c3) r
              v17 v14 fW1 (by rw [htd]) (by omega)
              (show prog2.getD 284 Instr.reject = Instr.blt 17 14 287 by rfl)
              (show prog2.getD 285 Instr.reject = Instr.blt 14 17 287 by rfl)
              (show prog2.getD 286 Instr.reject = Instr.accept by rfl)]
            have hmem : t ∈ [0, a1, a2, a1 + a2, a3, a3 + a1, a3 + a2,
                a3 + a1 + a2] := by simp [List.mem_cons, List.mem_singleton, htd]
            rw [decide_eq_true_iff.mpr hmem]
          · obtain ⟨c4, hc4, hch4⟩ := eq_triple_ne ρ 284 287 17 14 a3 t _
              ((S - 17) - c1 - c2 - c3) r v17 v14 fW1 (Ne.symm htd) (by omega)
              (show prog2.getD 284 Instr.reject = Instr.blt 17 14 287 by rfl)
              (show prog2.getD 285 Instr.reject = Instr.blt 14 17 287 by rfl)
            rw [hch4]
            -- 287: T1 := a3 + a1, ladder 288
            have e235 : (up (up (up (up (up g 21 2) 21 3) 21 4) 14 t)
                21 (a1 + a2)) 17
                + (up (up (up (up (up g 21 2) 21 3) 21 4) 14 t) 21 (a1 + a2))
                  15 = a3 + a1 := by rw [v17, v15]
            have fW2 : ∀ q,
                (up (up (up (up (up (up g 21 2) 21 3) 21 4) 14 t)
                  21 (a1 + a2)) 20 (a3 + a1)) q < 2 ^ w := fit_up fW1 hv31
            rw [exec_add_step (by omega)
              (show prog2.getD 287 Instr.reject = Instr.add 20 17 15 by rfl),
              e235]
            have u20 : (up (up (up (up (up (up g 21 2) 21 3) 21 4) 14 t)
                21 (a1 + a2)) 20 (a3 + a1)) 20 = a3 + a1 := up_eq _ _ _
            have u14 : (up (up (up (up (up (up g 21 2) 21 3) 21 4) 14 t)
                21 (a1 + a2)) 20 (a3 + a1)) 14 = t := by
              rw [up_ne (show (14:Nat) ≠ 20 by omega), v14]
            have u17 : (up (up (up (up (up (up g 21 2) 21 3) 21 4) 14 t)
                21 (a1 + a2)) 20 (a3 + a1)) 17 = a3 := by
              rw [up_ne (show (17:Nat) ≠ 20 by omega), v17]
            have u21 : (up (up (up (up (up (up g 21 2) 21 3) 21 4) 14 t)
                21 (a1 + a2)) 20 (a3 + a1)) 21 = a1 + a2 := by
              rw [up_ne (show (21:Nat) ≠ 20 by omega), v21]
            have u16 : (up (up (up (up (up (up g 21 2) 21 3) 21 4) 14 t)
                21 (a1 + a2)) 20 (a3 + a1)) 16 = a2 := by
              rw [up_ne (show (16:Nat) ≠ 20 by omega), v16]
            by_cases hte : t = a3 + a1
            · rw [eq_triple_eq ρ 288 291 20 14 (a3 + a1) t _ _ r u20 u14 fW2
                (by rw [hte]) (by omega)
                (show prog2.getD 288 Instr.reject = Instr.blt 20 14 291 by rfl)
                (show prog2.getD 289 Instr.reject = Instr.blt 14 20 291 by rfl)
                (show prog2.getD 290 Instr.reject = Instr.accept by rfl)]
              have hmem : t ∈ [0, a1, a2, a1 + a2, a3, a3 + a1, a3 + a2,
                  a3 + a1 + a2] := by
                simp [List.mem_cons, List.mem_singleton, hte]
              rw [decide_eq_true_iff.mpr hmem]
            · obtain ⟨c5, hc5, hch5⟩ := eq_triple_ne ρ 288 291 20 14
                (a3 + a1) t _
                ((S - 17) - c1 - c2 - c3 - c4 - 1) r u20 u14 fW2
                (Ne.symm hte) (by omega)
                (show prog2.getD 288 Instr.reject = Instr.blt 20 14 291 by rfl)
                (show prog2.getD 289 Instr.reject = Instr.blt 14 20 291 by rfl)
              rw [hch5]
              -- 291: T1 := a3 + a2, ladder 292
              have e239 : (up (up (up (up (up (up g 21 2) 21 3) 21 4) 14 t)
                    21 (a1 + a2)) 20 (a3 + a1)) 17
                  + (up (up (up (up (up (up g 21 2) 21 3) 21 4) 14 t)
                    21 (a1 + a2)) 20 (a3 + a1)) 16 = a3 + a2 := by
                rw [u17, u16]
              have fW3 : ∀ q,
                  (up (up (up (up (up (up (up g 21 2) 21 3) 21 4) 14 t)
                    21 (a1 + a2)) 20 (a3 + a1)) 20 (a3 + a2)) q < 2 ^ w :=
                fit_up fW2 hv32
              rw [exec_add_step (by omega)
                (show prog2.getD 291 Instr.reject = Instr.add 20 17 16 by rfl),
                e239]
              have x20 : (up (up (up (up (up (up (up g 21 2) 21 3) 21 4) 14 t)
                    21 (a1 + a2)) 20 (a3 + a1)) 20 (a3 + a2)) 20 = a3 + a2 :=
                up_eq _ _ _
              have x14 : (up (up (up (up (up (up (up g 21 2) 21 3) 21 4) 14 t)
                    21 (a1 + a2)) 20 (a3 + a1)) 20 (a3 + a2)) 14 = t := by
                rw [up_ne (show (14:Nat) ≠ 20 by omega), u14]
              have x17 : (up (up (up (up (up (up (up g 21 2) 21 3) 21 4) 14 t)
                    21 (a1 + a2)) 20 (a3 + a1)) 20 (a3 + a2)) 17 = a3 := by
                rw [up_ne (show (17:Nat) ≠ 20 by omega), u17]
              have x21 : (up (up (up (up (up (up (up g 21 2) 21 3) 21 4) 14 t)
                    21 (a1 + a2)) 20 (a3 + a1)) 20 (a3 + a2)) 21 = a1 + a2 := by
                rw [up_ne (show (21:Nat) ≠ 20 by omega), u21]
              by_cases htf : t = a3 + a2
              · rw [eq_triple_eq ρ 292 295 20 14 (a3 + a2) t _ _ r x20 x14 fW3
                  (by rw [htf]) (by omega)
                  (show prog2.getD 292 Instr.reject = Instr.blt 20 14 295 by rfl)
                  (show prog2.getD 293 Instr.reject = Instr.blt 14 20 295 by rfl)
                  (show prog2.getD 294 Instr.reject = Instr.accept by rfl)]
                have hmem : t ∈ [0, a1, a2, a1 + a2, a3, a3 + a1, a3 + a2,
                    a3 + a1 + a2] := by
                  simp [List.mem_cons, List.mem_singleton, htf]
                rw [decide_eq_true_iff.mpr hmem]
              · obtain ⟨c6, hc6, hch6⟩ := eq_triple_ne ρ 292 295 20 14
                  (a3 + a2) t _
                  ((S - 17) - c1 - c2 - c3 - c4 - 1 - c5 - 1) r x20 x14 fW3
                  (Ne.symm htf) (by omega)
                  (show prog2.getD 292 Instr.reject = Instr.blt 20 14 295 by rfl)
                  (show prog2.getD 293 Instr.reject = Instr.blt 14 20 295 by rfl)
                rw [hch6]
                -- 295: T1 := a3 + (a1 + a2), ladder 296
                have e243 : (up (up (up (up (up (up (up g 21 2) 21 3) 21 4)
                          14 t) 21 (a1 + a2)) 20 (a3 + a1)) 20 (a3 + a2)) 17
                    + (up (up (up (up (up (up (up g 21 2) 21 3) 21 4) 14 t)
                          21 (a1 + a2)) 20 (a3 + a1)) 20 (a3 + a2)) 21
                    = a3 + a1 + a2 := by
                  rw [x17, x21]
                  omega
                have fW4 : ∀ q,
                    (up (up (up (up (up (up (up (up g 21 2) 21 3) 21 4) 14 t)
                      21 (a1 + a2)) 20 (a3 + a1)) 20 (a3 + a2))
                      20 (a3 + a1 + a2)) q < 2 ^ w := fit_up fW3 hv312
                rw [exec_add_step (by omega)
                  (show prog2.getD 295 Instr.reject = Instr.add 20 17 21 by rfl),
                  e243]
                have y20 : (up (up (up (up (up (up (up (up g 21 2) 21 3) 21 4)
                          14 t) 21 (a1 + a2)) 20 (a3 + a1)) 20 (a3 + a2))
                      20 (a3 + a1 + a2)) 20 = a3 + a1 + a2 := up_eq _ _ _
                have y14 : (up (up (up (up (up (up (up (up g 21 2) 21 3) 21 4)
                          14 t) 21 (a1 + a2)) 20 (a3 + a1)) 20 (a3 + a2))
                      20 (a3 + a1 + a2)) 14 = t := by
                  rw [up_ne (show (14:Nat) ≠ 20 by omega), x14]
                by_cases htg : t = a3 + a1 + a2
                · rw [eq_triple_eq ρ 296 299 20 14 (a3 + a1 + a2) t _ _ r y20
                      y14 fW4 (by rw [htg]) (by omega)
                    (show prog2.getD 296 Instr.reject
                        = Instr.blt 20 14 299 by rfl)
                    (show prog2.getD 297 Instr.reject
                        = Instr.blt 14 20 299 by rfl)
                    (show prog2.getD 298 Instr.reject = Instr.accept by rfl)]
                  have hmem : t ∈ [0, a1, a2, a1 + a2, a3, a3 + a1, a3 + a2,
                      a3 + a1 + a2] := by
                    simp [List.mem_cons, List.mem_singleton, htg]
                  rw [decide_eq_true_iff.mpr hmem]
                · obtain ⟨c7, hc7, hch7⟩ := eq_triple_ne ρ 296 299 20 14
                    (a3 + a1 + a2) t _
                    ((S - 17) - c1 - c2 - c3 - c4 - 1 - c5 - 1 - c6 - 1) r
                    y20 y14 fW4 (Ne.symm htg)
                    (by omega)
                    (show prog2.getD 296 Instr.reject
                        = Instr.blt 20 14 299 by rfl)
                    (show prog2.getD 297 Instr.reject
                        = Instr.blt 14 20 299 by rfl)
                  rw [hch7,
                    exec_reject_step (by omega)
                      (show prog2.getD 299 Instr.reject = Instr.reject by rfl)]
                  have hmem : ¬ t ∈ [0, a1, a2, a1 + a2, a3, a3 + a1, a3 + a2,
                      a3 + a1 + a2] := by
                    simp only [List.mem_cons, List.mem_singleton,
                      List.not_mem_nil, or_false, not_or]
                    exact ⟨(by omega : t ≠ 0), hta, htb, htc, htd, hte, htf,
                      htg⟩
                  simp [hmem]


/-! ### The small-n dispatch (pcs 0→12→244, n ∈ {2, 3}) -/

theorem pro_segA23 {w n : Nat} (x : Instance n) (ρ : Nat → BitVec w)
    (hn : 2 ≤ n) (hn3 : n ≤ 3) (hpow : 2 ^ (2 * n) ≤ 2 ^ w)
    (hif : ∀ q, inF x q < 2 ^ w)
    (r S : Nat) (hS : 8 ≤ S) :
    ∃ g, exec prog2 ρ S 0 r (memOf w (inF x))
      = exec prog2 ρ (S - 8) 8 r (memOf w g) ∧
      (∀ q, g q < 2 ^ w) ∧ g 0 = 2 * n + 2 ∧ g 1 = 1 ∧ g 2 = 0 ∧
      (∀ j, j + 1 ≤ 3 → j + 1 ≤ n + 1 → g (2 * n + j) = inF x (j + 1)) ∧
      (∀ q, 4 ≤ q → q ≤ n + 1 → g q = inF x q) := by
  have h416 : (2:Nat) ^ (4:Nat) ≤ 2 ^ (2 * n) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h16 : (16:Nat) ≤ 2 ^ w := Nat.le_trans h416 hpow
  have hv0 : (2 * n + 2 : Nat) < 2 ^ w := Nat.lt_of_lt_of_le (by omega) h16
  have e0 : inF x 0 + inF x 0 = 2 * n := by
    rw [inF_zero]
    omega
  have e1 : (up (inF x) (0) (2 * n)) 0 = 2 * n := up_eq _ _ _
  have e2 : (up (inF x) (0) (2 * n)) 1 = inF x 1 := up_ne (by omega)
  have e3 : (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1)) 0
      + (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1)) 1
      = 2 * n + 1 := by
    rw [up_ne (show (0:Nat) ≠ 1 by omega), up_ne (show (0:Nat) ≠ 2 * n by omega),
      up_eq, up_eq]
  have e4 : (up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1))
      (0) (2 * n + 1)) 0 = 2 * n + 1 := up_eq _ _ _
  have e5 : (up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1))
      (0) (2 * n + 1)) 2 = inF x 2 := by
    rw [up_ne (show (2:Nat) ≠ 0 by omega), up_ne (show (2:Nat) ≠ 1 by omega),
      up_ne (show (2:Nat) ≠ 2 * n by omega), up_ne (show (2:Nat) ≠ 0 by omega)]
  have e6 : (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1))
      (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) 2
      - (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1))
      (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) 2 = 0 := by
    rw [up_ne (show (2:Nat) ≠ 2 * n + 1 by omega), up_ne (show (2:Nat) ≠ 0 by omega),
      up_ne (show (2:Nat) ≠ 1 by omega), up_ne (show (2:Nat) ≠ 2 * n by omega),
      up_ne (show (2:Nat) ≠ 0 by omega)]
    omega
  have e7 : (up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1))
      (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0)) 0
      + (up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1))
      (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0)) 1 = 2 * n + 2 := by
    rw [up_ne (show (0:Nat) ≠ 2 by omega), up_ne (show (0:Nat) ≠ 2 * n + 1 by omega),
      up_eq, up_ne (show (1:Nat) ≠ 2 by omega),
      up_ne (show (1:Nat) ≠ 2 * n + 1 by omega), up_ne (show (1:Nat) ≠ 0 by omega),
      up_eq]
  have e8 : (up (up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1))
      (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0)) (0) (2 * n + 2)) 0
      = 2 * n + 2 := up_eq _ _ _
  have e9 : (up (up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1))
      (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0)) (0) (2 * n + 2)) 3
      = inF x 3 := by
    rw [up_ne (show (3:Nat) ≠ 0 by omega), up_ne (show (3:Nat) ≠ 2 by omega),
      up_ne (show (3:Nat) ≠ 2 * n + 1 by omega), up_ne (show (3:Nat) ≠ 0 by omega),
      up_ne (show (3:Nat) ≠ 1 by omega), up_ne (show (3:Nat) ≠ 2 * n by omega),
      up_ne (show (3:Nat) ≠ 0 by omega)]
  have hv : ∀ v, v ≤ 2 * n + 2 → v < 2 ^ w := by
    intro v hvv
    exact Nat.lt_of_le_of_lt hvv hv0
  have hfit1 : ∀ q, up (inF x) (0) (2 * n) q < 2 ^ w :=
    upFit hif (hv _ (by omega))
  have hfit2 : ∀ q, up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1) q < 2 ^ w :=
    upFit hfit1 (hif 1)
  have hfit3 : ∀ q, up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1)
      q < 2 ^ w := upFit hfit2 (hv _ (by omega))
  have hfit4 : ∀ q, up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1))
      (0) (2 * n + 1) q < 2 ^ w := upFit hfit3 (hv _ (by omega))
  have hfit5 : ∀ q, up (up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1))
      (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2) q < 2 ^ w :=
    upFit hfit4 (hif 2)
  have hfit6 : ∀ q, up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1))
      (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0) q < 2 ^ w :=
    upFit hfit5 (hv _ (by omega))
  have hfit7 : ∀ q, up (up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n)
      (inF x 1)) (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0))
      (0) (2 * n + 2) q < 2 ^ w := upFit hfit6 (hv _ (by omega))
  have hfit8 : ∀ q, up (up (up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n)
      (inF x 1)) (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0))
      (0) (2 * n + 2)) (2 * n + 2) (inF x 3) q < 2 ^ w := upFit hfit7 (hif 3)
  have hf0 : (up (up (up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n)
      (inF x 1)) (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0))
      (0) (2 * n + 2)) (2 * n + 2) (inF x 3)) (0) = 2 * n + 2 := by
    rw [up_ne (show (0:Nat) ≠ 2 * n + 2 by omega), up_eq]
  have hf1 : (up (up (up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n)
      (inF x 1)) (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0))
      (0) (2 * n + 2)) (2 * n + 2) (inF x 3)) (1) = 1 := by
    rw [up_ne (show (1:Nat) ≠ 2 * n + 2 by omega), up_ne (show (1:Nat) ≠ 0 by omega),
      up_ne (show (1:Nat) ≠ 2 by omega), up_ne (show (1:Nat) ≠ 2 * n + 1 by omega),
      up_ne (show (1:Nat) ≠ 0 by omega), up_eq]
  have hf2 : (up (up (up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n)
      (inF x 1)) (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0))
      (0) (2 * n + 2)) (2 * n + 2) (inF x 3)) (2) = 0 := by
    rw [up_ne (show (2:Nat) ≠ 2 * n + 2 by omega), up_ne (show (2:Nat) ≠ 0 by omega),
      up_eq]
  have hscr : ∀ j, j + 1 ≤ 3 → j + 1 ≤ n + 1 →
      (up (up (up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n)
      (inF x 1)) (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0))
      (0) (2 * n + 2)) (2 * n + 2) (inF x 3)) (2 * n + j) = inF x (j + 1) := by
    intro j hj1 hj2
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
    · rw [show (2 * n + 0) = 2 * n from Nat.add_zero (2 * n)]
      rw [up_ne (show 2 * n ≠ 2 * n + 2 by omega), up_ne (show 2 * n ≠ 0 by omega),
        up_ne (show 2 * n ≠ 2 by omega), up_ne (show 2 * n ≠ 2 * n + 1 by omega),
        up_ne (show 2 * n ≠ 0 by omega), up_ne (show 2 * n ≠ 1 by omega), up_eq]
    · rw [up_ne (show 2 * n + 1 ≠ 2 * n + 2 by omega),
        up_ne (show 2 * n + 1 ≠ 0 by omega), up_ne (show 2 * n + 1 ≠ 2 by omega),
        up_eq]
    · rw [up_eq]
  have hp4 : ∀ q, 4 ≤ q → q ≤ n + 1 →
      (up (up (up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n)
      (inF x 1)) (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0))
      (0) (2 * n + 2)) (2 * n + 2) (inF x 3)) q = inF x q := by
    intro q hq1 hq2
    rw [up_ne (show q ≠ 2 * n + 2 by omega), up_ne (show q ≠ 0 by omega),
      up_ne (show q ≠ 2 by omega), up_ne (show q ≠ 2 * n + 1 by omega),
      up_ne (show q ≠ 0 by omega), up_ne (show q ≠ 1 by omega),
      up_ne (show q ≠ 2 * n by omega), up_ne (show q ≠ 0 by omega)]
  refine ⟨up (up (up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n)
    (inF x 1)) (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0))
    (0) (2 * n + 2)) (2 * n + 2) (inF x 3), ?_, hfit8, ?_, ?_, ?_, ?_, ?_⟩
  · rw [exec_add_step (by omega) (show prog2.getD 0 Instr.reject = Instr.add 0 0 0 by rfl),
      e0, exec_store_step (by omega)
        (show prog2.getD 1 Instr.reject = Instr.store 0 1 by rfl) hfit1, e1, e2,
      exec_one_step (by omega)
        (show prog2.getD 2 Instr.reject = Instr.one 1 by rfl),
      exec_add_step (by omega)
        (show prog2.getD 3 Instr.reject = Instr.add 0 0 1 by rfl), e3,
      exec_store_step (by omega)
        (show prog2.getD 4 Instr.reject = Instr.store 0 2 by rfl) hfit4, e4, e5,
      exec_sub_step (by omega)
        (show prog2.getD 5 Instr.reject = Instr.sub 2 2 2 by rfl) hfit5 (Nat.le_refl _),
      e6, exec_add_step (by omega)
        (show prog2.getD 6 Instr.reject = Instr.add 0 0 1 by rfl), e7,
      exec_store_step (by omega)
        (show prog2.getD 7 Instr.reject = Instr.store 0 3 by rfl) hfit7, e8, e9]
    simp only [Nat.sub_sub, Nat.reduceAdd]
  · exact hf0
  · exact hf1
  · exact hf2
  · exact hscr
  · exact hp4

/-- The small-n dispatch: pcs 0→12 with the guard `blt 0 3 244` TAKEN
(n ≤ 3 makes cell0 = 2n+2 < 9 = cell3).  Control lands at 244 in the
state `smalln_loads` consumes (cur := 2n+2, [3] := 9). -/

theorem pro_dispatch23 {w n : Nat} (x : Instance n) (ρ : Nat → BitVec w)
    (hn : 2 ≤ n) (hn3 : n ≤ 3) (hpow : 2 ^ (2 * n) ≤ 2 ^ w)
    (hif : ∀ q, inF x q < 2 ^ w) (r S : Nat) (hS : 13 ≤ S) :
    ∃ g, exec prog2 ρ S 0 r (memOf w (inF x))
      = exec prog2 ρ (S - 13) 244 r (memOf w g) ∧
      (∀ q, g q < 2 ^ w) ∧ g 0 = 2 * n + 2 ∧ g 1 = 1 ∧ g 2 = 0 ∧
      g 3 = 9 ∧
      (∀ j, j + 1 ≤ 3 → j + 1 ≤ n + 1 → g (2 * n + j) = inF x (j + 1)) ∧
      (∀ q, 4 ≤ q → q ≤ n + 1 → g q = inF x q) := by
  have h416 : (2:Nat) ^ (4:Nat) ≤ 2 ^ (2 * n) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h16 : (16:Nat) ≤ 2 ^ w := Nat.le_trans h416 hpow
  have h9 : (9:Nat) < 2 ^ w := by omega
  obtain ⟨f, hex, hfit, hf0, hf1, hf2, hscr, hp4⟩ :=
    pro_segA23 x ρ hn hn3 hpow hif r S (by omega)
  have e1 : f 1 + f 1 = 2 := by rw [hf1]
  have e2 : (up f 3 2) 3 + (up f 3 2) 3 = 4 := by rw [up_eq]
  have e3 : (up (up f 3 2) 3 4) 3 + (up (up f 3 2) 3 4) 3 = 8 := by rw [up_eq]
  have e4 : (up (up (up f 3 2) 3 4) 3 8) 3
      + (up (up (up f 3 2) 3 4) 3 8) 1 = 9 := by
    rw [up_eq, up_ne (show (1:Nat) ≠ 3 by omega),
      up_ne (show (1:Nat) ≠ 3 by omega), up_ne (show (1:Nat) ≠ 3 by omega), hf1]
  have hfit1 : ∀ q, (up f 3 2) q < 2 ^ w := upFit hfit (by omega)
  have hfit2 : ∀ q, (up (up f 3 2) 3 4) q < 2 ^ w := upFit hfit1 (by omega)
  have hfit3 : ∀ q, (up (up (up f 3 2) 3 4) 3 8) q < 2 ^ w := upFit hfit2 (by omega)
  have hfit4 : ∀ q, (up (up (up (up f 3 2) 3 4) 3 8) 3 9) q < 2 ^ w :=
    upFit hfit3 h9
  have g0 : (up (up (up (up f 3 2) 3 4) 3 8) 3 9) 0 = 2 * n + 2 := by
    rw [up_ne (show (0:Nat) ≠ 3 by omega), up_ne (show (0:Nat) ≠ 3 by omega),
      up_ne (show (0:Nat) ≠ 3 by omega), up_ne (show (0:Nat) ≠ 3 by omega), hf0]
  have g1 : (up (up (up (up f 3 2) 3 4) 3 8) 3 9) 1 = 1 := by
    rw [up_ne (show (1:Nat) ≠ 3 by omega), up_ne (show (1:Nat) ≠ 3 by omega),
      up_ne (show (1:Nat) ≠ 3 by omega), up_ne (show (1:Nat) ≠ 3 by omega), hf1]
  have g2 : (up (up (up (up f 3 2) 3 4) 3 8) 3 9) 2 = 0 := by
    rw [up_ne (show (2:Nat) ≠ 3 by omega), up_ne (show (2:Nat) ≠ 3 by omega),
      up_ne (show (2:Nat) ≠ 3 by omega), up_ne (show (2:Nat) ≠ 3 by omega), hf2]
  have g3 : (up (up (up (up f 3 2) 3 4) 3 8) 3 9) 3 = 9 := up_eq _ _ _
  have gscr : ∀ j, j + 1 ≤ 3 → j + 1 ≤ n + 1 →
      (up (up (up (up f 3 2) 3 4) 3 8) 3 9) (2 * n + j) = inF x (j + 1) := by
    intro j hj1 hj2
    rw [up_ne (show 2 * n + j ≠ 3 by omega), up_ne (show 2 * n + j ≠ 3 by omega),
      up_ne (show 2 * n + j ≠ 3 by omega), up_ne (show 2 * n + j ≠ 3 by omega)]
    exact hscr j hj1 hj2
  have gp4 : ∀ q, 4 ≤ q → q ≤ n + 1 →
      (up (up (up (up f 3 2) 3 4) 3 8) 3 9) q = inF x q := by
    intro q hq1 hq2
    rw [up_ne (show q ≠ 3 by omega), up_ne (show q ≠ 3 by omega),
      up_ne (show q ≠ 3 by omega), up_ne (show q ≠ 3 by omega)]
    exact hp4 q hq1 hq2
  have hlt0 : (up (up (up (up f 3 2) 3 4) 3 8) 3 9) 0
      < (up (up (up (up f 3 2) 3 4) 3 8) 3 9) 3 := by
    rw [up_ne (show (0:Nat) ≠ 3 by omega), up_ne (show (0:Nat) ≠ 3 by omega),
      up_ne (show (0:Nat) ≠ 3 by omega), up_ne (show (0:Nat) ≠ 3 by omega), hf0,
      up_eq]
    omega
  have hpfx : exec prog2 ρ (S - 8) 8 r (memOf w f)
      = exec prog2 ρ (S - 8 - 5) 244 r
          (memOf w (up (up (up (up f 3 2) 3 4) 3 8) 3 9)) := by
    rw [exec_add_step (by omega)
        (show prog2.getD 8 Instr.reject = Instr.add 3 1 1 by rfl), e1,
      exec_add_step (by omega)
        (show prog2.getD 9 Instr.reject = Instr.add 3 3 3 by rfl), e2,
      exec_add_step (by omega)
        (show prog2.getD 10 Instr.reject = Instr.add 3 3 3 by rfl), e3,
      exec_add_step (by omega)
        (show prog2.getD 11 Instr.reject = Instr.add 3 3 1 by rfl), e4,
      exec_blt_lt_step (by omega)
        (show prog2.getD 12 Instr.reject = Instr.blt 0 3 244 by rfl) hfit4 hlt0]
    simp only [Nat.sub_sub, Nat.reduceAdd]
  refine ⟨up (up (up (up f 3 2) 3 4) 3 8) 3 9, hex.trans hpfx, hfit4,
    g0, g1, g2, g3, gscr, gp4⟩



/-! ### The n ≥ 4 prologue: pcs 0 → 86 -/

/-! ### The small-n verdicts (complete) -/

/-- The horizon covers the unrolled n = 2 run. -/
theorem budget2 : (34:Nat) ≤ Runtime.stepBound 2 + Runtime.constOverhead := by
  decide

/-- The horizon covers the unrolled n = 3 run. -/
theorem budget3 : (48:Nat) ≤ Runtime.stepBound 3 + Runtime.constOverhead := by
  decide

/-- The n = 2 verdict list is exactly the `x.yes` question. -/
theorem verdict2_iff (x : Instance 2) :
    x.yes ↔ x.t ∈ [0, instA x 0, instA x 1, instA x 0 + instA x 1] :=
  (instance_yes_iff x).trans (isSum_two_iff (instA x) x.t)

/-- The n = 3 verdict list is exactly the `x.yes` question. -/
theorem verdict3_iff (x : Instance 3) :
    x.yes ↔ x.t ∈ [0, instA x 0, instA x 1, instA x 0 + instA x 1,
      instA x 2, instA x 2 + instA x 0, instA x 2 + instA x 1,
      instA x 2 + instA x 0 + instA x 1] :=
  (instance_yes_iff x).trans (isSum_three_iff (instA x) x.t)

theorem smalln2_run (x : Instance 2)
    (ρ : Nat → BitVec (wordLength 2 x.bits)) (T : Nat) (hT : 34 ≤ T) :
    run prog2 x ρ T
      = some (decide (x.t ∈ [0, instA x 0, instA x 1, instA x 0 + instA x 1])) := by
  rw [run_eq_exec2]
  obtain ⟨g, hex, hgfit, hg0, hg1, hg2, hg3, hgscr, hgp4⟩ :=
    pro_dispatch23 x ρ (by omega) (by omega)
      (Nat.pow_le_pow_right (by omega)
        (by show 2 * 2 ≤ 4 * (2 + x.bits) + Nat.log2 ((2 + 2) ^ 4 - 1) + 1; omega))
      (inF_fit x _ (by omega) (fun v hv => input_lt_wordLength x (by omega) v hv))
      0 T (by omega)
  have hf4 : g 4 = inF x 1 := hgscr 0 (by omega) (by omega)
  have hf5 : g 5 = inF x 2 := hgscr 1 (by omega) (by omega)
  have hf6 : g 6 = inF x 3 := hgscr 2 (by omega) (by omega)
  have hv12 : inF x 1 + inF x 2 < 2 ^ (wordLength 2 x.bits) := by
    have h2s := two_sum_lt_pow_wordLength x (by omega)
    have hr : (List.range 2) = [0, 1] := by decide
    rw [hr] at h2s
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h2s
    have ha0 : inF x 1 = instA x 0 := (inF_instA x 1 (by omega) (by omega)).symm
    have ha1 : inF x 2 = instA x 1 := (inF_instA x 2 (by omega) (by omega)).symm
    rw [ha0, ha1]
    omega
  have hfinal := smalln2_exec ρ (inF x 1) (inF x 2) (inF x 3) g (T - 13) 0
    (by rw [hg0]) hg1 hg2 hg3 hf4 hf5 hf6 hv12 hgfit (by omega)
  have ht : inF x 3 = x.t := inF_t x
  have ha0 : inF x 1 = instA x 0 := (inF_instA x 1 (by omega) (by omega)).symm
  have ha1 : inF x 2 = instA x 1 := (inF_instA x 2 (by omega) (by omega)).symm
  rw [ht, ha0, ha1] at hfinal
  exact hex.trans hfinal

theorem smalln3_run (x : Instance 3)
    (ρ : Nat → BitVec (wordLength 3 x.bits)) (T : Nat) (hT : 48 ≤ T) :
    run prog2 x ρ T
      = some (decide (x.t ∈ [0, instA x 0, instA x 1, instA x 0 + instA x 1,
        instA x 2, instA x 2 + instA x 0, instA x 2 + instA x 1,
        instA x 2 + instA x 0 + instA x 1])) := by
  rw [run_eq_exec2]
  obtain ⟨g, hex, hgfit, hg0, hg1, hg2, hg3, hgscr, hgp4⟩ :=
    pro_dispatch23 x ρ (by omega) (by omega)
      (Nat.pow_le_pow_right (by omega)
        (by show 2 * 3 ≤ 4 * (3 + x.bits) + Nat.log2 ((3 + 2) ^ 4 - 1) + 1; omega))
      (inF_fit x _ (by omega) (fun v hv => input_lt_wordLength x (by omega) v hv))
      0 T (by omega)
  have hf4t : g 4 = x.t := by
    rw [hgp4 4 (by omega) (by omega)]
    exact inF_t x
  have hf6 : g 6 = inF x 1 := hgscr 0 (by omega) (by omega)
  have hf7 : g 7 = inF x 2 := hgscr 1 (by omega) (by omega)
  have hf8 : g 8 = inF x 3 := hgscr 2 (by omega) (by omega)
  have h2s := two_sum_lt_pow_wordLength x (by omega)
  have hr : (List.range 3) = [0, 1, 2] := by decide
  rw [hr] at h2s
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.add_assoc] at h2s
  have ha0 : inF x 1 = instA x 0 := (inF_instA x 1 (by omega) (by omega)).symm
  have ha1 : inF x 2 = instA x 1 := (inF_instA x 2 (by omega) (by omega)).symm
  have ha2 : inF x 3 = instA x 2 := (inF_instA x 3 (by omega) (by omega)).symm
  have hv12 : inF x 1 + inF x 2 < 2 ^ (wordLength 3 x.bits) := by
    rw [ha0, ha1]; omega
  have hv31 : inF x 3 + inF x 1 < 2 ^ (wordLength 3 x.bits) := by
    rw [ha2, ha0]; omega
  have hv32 : inF x 3 + inF x 2 < 2 ^ (wordLength 3 x.bits) := by
    rw [ha2, ha1]; omega
  have hv312 : inF x 3 + inF x 1 + inF x 2 < 2 ^ (wordLength 3 x.bits) := by
    rw [ha2, ha0, ha1]; omega
  have hfinal := smalln3_exec ρ (inF x 1) (inF x 2) (inF x 3) x.t g (T - 13) 0
    (by rw [hg0]) hg1 hg2 hg3 hf4t hf6 hf7 hf8
    hv12 hv31 hv32 hv312 hgfit (by omega)
  rw [ha0, ha1, ha2] at hfinal
  exact hex.trans hfinal

theorem smalln_halts :
    ∀ (n : Nat) (x : Instance n), n = 2 ∨ n = 3 →
    ∀ ρ, (run prog2 x ρ (Runtime.stepBound n + Runtime.constOverhead)).isSome := by
  intro n x hn ρ
  rcases hn with rfl | rfl
  · rw [smalln2_run x ρ _ budget2]
    simp
  · rw [smalln3_run x ρ _ budget3]
    simp

/-- The small-n half of the correctness obligation: for n ∈ {2, 3} the run
returns exactly the membership decision, which matches `x.yes`. -/
theorem smalln_verdict :
    ∀ (n : Nat) (x : Instance n), n = 2 ∨ n = 3 →
    ∃ v, (∀ ρ, run prog2 x ρ (Runtime.stepBound n + Runtime.constOverhead)
        = some v) ∧ (x.yes → v = true) ∧ (¬x.yes → v = false) := by
  intro n x hn
  rcases hn with rfl | rfl
  · refine ⟨decide (x.t ∈ [0, instA x 0, instA x 1, instA x 0 + instA x 1]),
      fun ρ => smalln2_run x ρ _ budget2, ?_, ?_⟩
    · intro hyes
      exact decide_eq_true_iff.mpr ((verdict2_iff x).mp hyes)
    · intro hno
      by_cases hmem : x.t ∈ [0, instA x 0, instA x 1, instA x 0 + instA x 1]
      · exact absurd ((verdict2_iff x).mpr hmem) hno
      · simp [hmem]
  · refine ⟨decide (x.t ∈ [0, instA x 0, instA x 1, instA x 0 + instA x 1,
      instA x 2, instA x 2 + instA x 0, instA x 2 + instA x 1,
      instA x 2 + instA x 0 + instA x 1]),
      fun ρ => smalln3_run x ρ _ budget3, ?_, ?_⟩
    · intro hyes
      exact decide_eq_true_iff.mpr ((verdict3_iff x).mp hyes)
    · intro hno
      by_cases hmem : x.t ∈ [0, instA x 0, instA x 1, instA x 0 + instA x 1,
        instA x 2, instA x 2 + instA x 0, instA x 2 + instA x 1,
        instA x 2 + instA x 0 + instA x 1]
      · exact absurd ((verdict3_iff x).mpr hmem) hno
      · simp [hmem]

end SubsetSum.MITM.P2Small
