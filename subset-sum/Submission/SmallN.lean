import Submission.PhaseB
set_option autoImplicit true

/-!
# The small-n unrolled verdicts (R2125607414)

For `n ≤ 3` the prologue jumps to `LSMALL` (pc 192) with the register
file `[0] = 2n+2`, `[1] = 1`, `[2] = 0`, `[3] = 9` and the saved strip
`mem[2n] = a₁`, `mem[2n+1] = a₂`, `mem[2n+2] = (t for n = 2, a₃ for
n = 3)`; `t` itself sits pristine at cell `n+1`.  The unrolled
straight-line code decides membership in the full subset-sum set by
pairwise equality tests:

- `n = 2`: accept iff `t ∈ {0, a₁, a₂, a₁+a₂}` (pcs 207–220)
- `n = 3`: accept iff `t ∈ {0, a₁, a₂, a₁+a₂, a₃, a₃+a₁, a₃+a₂, a₃+a₁+a₂}`
  (pcs 221–248)

Each test is the `blt x y L; blt y x L; accept` triple — equal fitting
words fail both strict comparisons.  Spec-level iff lemmas
(`isSum_two_iff`, `isSum_three_iff`) connect the verdicts to `isSum`.
-/

namespace SubsetSum.MITM

open BigOSpeedrun.SubsetSum SubsetSum.MITM.Spec

/-! ## §0. The equality-test triple -/

/-- `blt ci cj L; blt cj ci L; accept` at consecutive pcs: equal
fitting values accept in 3 steps. -/
theorem eq_triple_eq {w : Nat} (ρ : Nat → BitVec w) (p L ci cj x y : Nat)
    (u : Nat → Nat) (S r : Nat)
    (hui : u ci = x) (huj : u cj = y) (hfit : ∀ q, u q < 2 ^ w)
    (heq : x = y) (hS : 3 ≤ S)
    (h1 : prog.getD p Instr.reject = Instr.blt ci cj L)
    (h2 : prog.getD (p + 1) Instr.reject = Instr.blt cj ci L)
    (h3 : prog.getD (p + 2) Instr.reject = Instr.accept) :
    exec prog ρ S p r (memOf w u) = some true := by
  rw [exec_blt_ge_step (by omega) h1 hfit (by rw [hui, huj, heq]; omega),
    exec_blt_ge_step (by omega) h2 hfit (by rw [hui, huj, heq]; omega),
    exec_accept_step (by omega) h3]

/-- The same triple with unequal values: continue at `L` in at most 2
steps, memory unchanged. -/
theorem eq_triple_ne {w : Nat} (ρ : Nat → BitVec w) (p L ci cj x y : Nat)
    (u : Nat → Nat) (S r : Nat)
    (hui : u ci = x) (huj : u cj = y) (hfit : ∀ q, u q < 2 ^ w)
    (hne : x ≠ y) (hS : 2 ≤ S)
    (h1 : prog.getD p Instr.reject = Instr.blt ci cj L)
    (h2 : prog.getD (p + 1) Instr.reject = Instr.blt cj ci L) :
    ∃ c, c ≤ 2 ∧
      exec prog ρ S p r (memOf w u) = exec prog ρ (S - c) L r (memOf w u) := by
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

/-! ## §2. The shared load prefix (pcs 192–201) -/

/-- The first ten instructions: `T1 := 2n` and load cells `15/16/17`
from `mem[2n], mem[2n+1], mem[2n+2]`, then `T2 := 7` and stop AT the
split guard pc 201.  Works for both `n = 2` (`cur = 6`) and `n = 3`
(`cur = 8`). -/
theorem smalln_loads {w : Nat} (ρ : Nat → BitVec w) (cur v4 v5 v6 : Nat)
    (f : Nat → Nat) (S r : Nat)
    (hf0 : f 0 = cur) (hf1 : f 1 = 1) (hf2 : f 2 = 0) (hf3 : f 3 = 9)
    (hfA : f (cur - 2) = v4) (hfB : f (cur - 1) = v5) (hfC : f cur = v6)
    (hcur : 3 ≤ cur) (hcur8 : cur ≤ 8)
    (hfit : ∀ q, f q < 2 ^ w) (hS : 10 ≤ S) :
    ∃ g, exec prog ρ S 192 r (memOf w f)
        = exec prog ρ (S - 9) 201 r (memOf w g) ∧
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
        (show prog.getD 192 Instr.reject = Instr.sub 20 0 1 by rfl) hfit
        (by omega), hf0, hf1,
      exec_sub_step (by omega)
        (show prog.getD 193 Instr.reject = Instr.sub 20 20 1 by rfl) fA1
        (by rw [up_ne (show (1:Nat) ≠ 20 by omega), up_eq]; omega), e193,
      exec_load_step (by omega)
        (show prog.getD 194 Instr.reject = Instr.load 15 20 by rfl) fA2, e194,
      exec_add_step (by omega)
        (show prog.getD 195 Instr.reject = Instr.add 20 20 1 by rfl), e195,
      exec_load_step (by omega)
        (show prog.getD 196 Instr.reject = Instr.load 16 20 by rfl) fA4, e196,
      exec_add_step (by omega)
        (show prog.getD 197 Instr.reject = Instr.add 20 20 1 by rfl), e197,
      exec_load_step (by omega)
        (show prog.getD 198 Instr.reject = Instr.load 17 20 by rfl) fA6, e198,
      exec_sub_step (by omega)
        (show prog.getD 199 Instr.reject = Instr.sub 21 3 1 by rfl) fA7
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
        (show prog.getD 200 Instr.reject = Instr.sub 21 21 1 by rfl) fA8
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
    exec prog ρ S 192 r (memOf w f)
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
  -- 201 taken (6 < 7) → 207: W := t; 208: t < 1 ?
  rw [hex,
    exec_blt_lt_step (by omega)
      (show prog.getD 201 Instr.reject = Instr.blt 0 21 207 by rfl) hgfit
      (by rw [hg0, hg21]; omega),
    exec_add_step (by omega)
      (show prog.getD 207 Instr.reject = Instr.add 14 17 2 by rfl), e207]
  rcases Nat.eq_zero_or_pos t with ht0 | ht0
  · rw [exec_blt_lt_step (by omega)
      (show prog.getD 208 Instr.reject = Instr.blt 14 1 220 by rfl) fW
      (by rw [u14, u1]; omega),
    exec_accept_step (by omega)
      (show prog.getD 220 Instr.reject = Instr.accept by rfl)]
    have hmem : t ∈ [0, a1, a2, a1 + a2] := by
      simp [List.mem_cons, List.mem_singleton, ht0]
    rw [decide_eq_true_iff.mpr hmem]
  · -- t ≥ 1: 209: T2 := a1 + a2, then the ladder at 210
    have e209 : (up g 14 t) 15 + (up g 14 t) 16 = a1 + a2 := by rw [u15, u16]
    have fT2 : ∀ q, (up (up g 14 t) 21 (a1 + a2)) q < 2 ^ w := fit_up fW hv12
    rw [exec_blt_ge_step (by omega)
      (show prog.getD 208 Instr.reject = Instr.blt 14 1 220 by rfl) fW
      (by rw [u14, u1]; omega),
    exec_add_step (by omega)
      (show prog.getD 209 Instr.reject = Instr.add 21 15 16 by rfl), e209]
    simp only [Nat.sub_sub, Nat.reduceAdd]
    have v15 : (up (up g 14 t) 21 (a1 + a2)) 15 = a1 := by
      rw [up_ne (show (15:Nat) ≠ 21 by omega), u15]
    have v14 : (up (up g 14 t) 21 (a1 + a2)) 14 = t := by
      rw [up_ne (show (14:Nat) ≠ 21 by omega), u14]
    have v16 : (up (up g 14 t) 21 (a1 + a2)) 16 = a2 := by
      rw [up_ne (show (16:Nat) ≠ 21 by omega), u16]
    have v21 : (up (up g 14 t) 21 (a1 + a2)) 21 = a1 + a2 := up_eq _ _ _
    by_cases hta : t = a1
    · rw [eq_triple_eq ρ 210 213 15 14 a1 t _ (S - 13) r v15 v14 fT2
        (by rw [hta]) (by omega)
        (show prog.getD 210 Instr.reject = Instr.blt 15 14 213 by rfl)
        (show prog.getD 211 Instr.reject = Instr.blt 14 15 213 by rfl)
        (show prog.getD 212 Instr.reject = Instr.accept by rfl)]
      have hmem : t ∈ [0, a1, a2, a1 + a2] := by
        simp [List.mem_cons, List.mem_singleton, hta]
      rw [decide_eq_true_iff.mpr hmem]
    · obtain ⟨c1, hc1, hch1⟩ := eq_triple_ne ρ 210 213 15 14 a1 t _ (S - 13) r
        v15 v14 fT2 (Ne.symm hta) (by omega)
        (show prog.getD 210 Instr.reject = Instr.blt 15 14 213 by rfl)
        (show prog.getD 211 Instr.reject = Instr.blt 14 15 213 by rfl)
      rw [hch1]
      by_cases htb : t = a2
      · rw [eq_triple_eq ρ 213 216 16 14 a2 t _ ((S - 13) - c1) r v16 v14 fT2
          (by rw [htb]) (by omega)
          (show prog.getD 213 Instr.reject = Instr.blt 16 14 216 by rfl)
          (show prog.getD 214 Instr.reject = Instr.blt 14 16 216 by rfl)
          (show prog.getD 215 Instr.reject = Instr.accept by rfl)]
        have hmem : t ∈ [0, a1, a2, a1 + a2] := by
          simp [List.mem_cons, List.mem_singleton, htb]
        rw [decide_eq_true_iff.mpr hmem]
      · obtain ⟨c2, hc2, hch2⟩ := eq_triple_ne ρ 213 216 16 14 a2 t _
          ((S - 13) - c1) r v16 v14 fT2 (Ne.symm htb) (by omega)
          (show prog.getD 213 Instr.reject = Instr.blt 16 14 216 by rfl)
          (show prog.getD 214 Instr.reject = Instr.blt 14 16 216 by rfl)
        rw [hch2]
        by_cases htc : t = a1 + a2
        · rw [eq_triple_eq ρ 216 219 21 14 (a1 + a2) t _ ((S - 13) - c1 - c2) r
            v21 v14 fT2 (by rw [htc]) (by omega)
            (show prog.getD 216 Instr.reject = Instr.blt 21 14 219 by rfl)
            (show prog.getD 217 Instr.reject = Instr.blt 14 21 219 by rfl)
            (show prog.getD 218 Instr.reject = Instr.accept by rfl)]
          have hmem : t ∈ [0, a1, a2, a1 + a2] := by
            simp [List.mem_cons, List.mem_singleton, htc]
          rw [decide_eq_true_iff.mpr hmem]
        · obtain ⟨c3, hc3, hch3⟩ := eq_triple_ne ρ 216 219 21 14 (a1 + a2) t _
            ((S - 13) - c1 - c2) r v21 v14 fT2 (Ne.symm htc) (by omega)
            (show prog.getD 216 Instr.reject = Instr.blt 21 14 219 by rfl)
            (show prog.getD 217 Instr.reject = Instr.blt 14 21 219 by rfl)
          rw [hch3,
            exec_reject_step (by omega)
              (show prog.getD 219 Instr.reject = Instr.reject by rfl)]
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
    exec prog ρ S 192 r (memOf w f)
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
  -- 201 NOT taken (8 < 7 false); 202–204: T2 := 2, 3, 4; 205: W := t
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
  -- state facts at pc 221
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
      (show prog.getD 201 Instr.reject = Instr.blt 0 21 207 by rfl) hgfit
      (by rw [hg0, hg21]; omega),
    exec_add_step (by omega)
      (show prog.getD 202 Instr.reject = Instr.add 21 1 1 by rfl), e202,
    exec_add_step (by omega)
      (show prog.getD 203 Instr.reject = Instr.add 21 21 1 by rfl), e203,
    exec_add_step (by omega)
      (show prog.getD 204 Instr.reject = Instr.add 21 21 1 by rfl), e204,
    exec_load_step (by omega)
      (show prog.getD 205 Instr.reject = Instr.load 14 21 by rfl) fB3, e205,
    exec_blt_lt_step (by omega)
      (show prog.getD 206 Instr.reject = Instr.blt 2 1 221 by rfl) fB4
      (by rw [up_ne (show (2:Nat) ≠ 14 by omega),
        up_ne (show (1:Nat) ≠ 14 by omega), up_ne (show (2:Nat) ≠ 21 by omega),
        up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (2:Nat) ≠ 21 by omega),
        up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (2:Nat) ≠ 21 by omega),
        up_ne (show (1:Nat) ≠ 21 by omega), hg2, hg1]; omega)]
  -- pc 221, horizon S - 16, state b4
  rcases Nat.eq_zero_or_pos t with ht0 | ht0
  · rw [exec_blt_lt_step (by omega)
      (show prog.getD 221 Instr.reject = Instr.blt 14 1 248 by rfl) fB4
      (by rw [k14, k1]; omega),
    exec_accept_step (by omega)
      (show prog.getD 248 Instr.reject = Instr.accept by rfl)]
    have hmem : t ∈ [0, a1, a2, a1 + a2, a3, a3 + a1, a3 + a2, a3 + a1 + a2] :=
      by simp [List.mem_cons, List.mem_singleton, ht0]
    rw [decide_eq_true_iff.mpr hmem]
  · -- 222: T2 := a1 + a2, then the ladder at 223
    have e222 : (up (up (up (up g 21 2) 21 3) 21 4) 14 t) 15
        + (up (up (up (up g 21 2) 21 3) 21 4) 14 t) 16 = a1 + a2 := by
      rw [k15, k16]
    have fW1 : ∀ q,
        (up (up (up (up (up g 21 2) 21 3) 21 4) 14 t) 21 (a1 + a2)) q < 2 ^ w :=
      fit_up fB4 hv12
    rw [exec_blt_ge_step (by omega)
      (show prog.getD 221 Instr.reject = Instr.blt 14 1 248 by rfl) fB4
      (by rw [k14, k1]; omega),
    exec_add_step (by omega)
      (show prog.getD 222 Instr.reject = Instr.add 21 15 16 by rfl), e222]
    simp only [Nat.sub_sub, Nat.reduceAdd]
    -- state w1, pc 223, horizon S - 17
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
    · rw [eq_triple_eq ρ 223 226 15 14 a1 t _ (S - 17) r v15 v14 fW1
        (by rw [hta]) (by omega)
        (show prog.getD 223 Instr.reject = Instr.blt 15 14 226 by rfl)
        (show prog.getD 224 Instr.reject = Instr.blt 14 15 226 by rfl)
        (show prog.getD 225 Instr.reject = Instr.accept by rfl)]
      have hmem : t ∈ [0, a1, a2, a1 + a2, a3, a3 + a1, a3 + a2,
          a3 + a1 + a2] := by simp [List.mem_cons, List.mem_singleton, hta]
      rw [decide_eq_true_iff.mpr hmem]
    · obtain ⟨c1, hc1, hch1⟩ := eq_triple_ne ρ 223 226 15 14 a1 t _ (S - 17) r
        v15 v14 fW1 (Ne.symm hta) (by omega)
        (show prog.getD 223 Instr.reject = Instr.blt 15 14 226 by rfl)
        (show prog.getD 224 Instr.reject = Instr.blt 14 15 226 by rfl)
      rw [hch1]
      by_cases htb : t = a2
      · rw [eq_triple_eq ρ 226 229 16 14 a2 t _ ((S - 17) - c1) r v16 v14 fW1
          (by rw [htb]) (by omega)
          (show prog.getD 226 Instr.reject = Instr.blt 16 14 229 by rfl)
          (show prog.getD 227 Instr.reject = Instr.blt 14 16 229 by rfl)
          (show prog.getD 228 Instr.reject = Instr.accept by rfl)]
        have hmem : t ∈ [0, a1, a2, a1 + a2, a3, a3 + a1, a3 + a2,
            a3 + a1 + a2] := by simp [List.mem_cons, List.mem_singleton, htb]
        rw [decide_eq_true_iff.mpr hmem]
      · obtain ⟨c2, hc2, hch2⟩ := eq_triple_ne ρ 226 229 16 14 a2 t _
          ((S - 17) - c1) r v16 v14 fW1 (Ne.symm htb) (by omega)
          (show prog.getD 226 Instr.reject = Instr.blt 16 14 229 by rfl)
          (show prog.getD 227 Instr.reject = Instr.blt 14 16 229 by rfl)
        rw [hch2]
        by_cases htc : t = a1 + a2
        · rw [eq_triple_eq ρ 229 232 21 14 (a1 + a2) t _
              ((S - 17) - c1 - c2) r v21 v14 fW1 (by rw [htc]) (by omega)
            (show prog.getD 229 Instr.reject = Instr.blt 21 14 232 by rfl)
            (show prog.getD 230 Instr.reject = Instr.blt 14 21 232 by rfl)
            (show prog.getD 231 Instr.reject = Instr.accept by rfl)]
          have hmem : t ∈ [0, a1, a2, a1 + a2, a3, a3 + a1, a3 + a2,
              a3 + a1 + a2] := by simp [List.mem_cons, List.mem_singleton, htc]
          rw [decide_eq_true_iff.mpr hmem]
        · obtain ⟨c3, hc3, hch3⟩ := eq_triple_ne ρ 229 232 21 14 (a1 + a2) t _
            ((S - 17) - c1 - c2) r v21 v14 fW1 (Ne.symm htc) (by omega)
            (show prog.getD 229 Instr.reject = Instr.blt 21 14 232 by rfl)
            (show prog.getD 230 Instr.reject = Instr.blt 14 21 232 by rfl)
          rw [hch3]
          by_cases htd : t = a3
          · rw [eq_triple_eq ρ 232 235 17 14 a3 t _ ((S - 17) - c1 - c2 - c3) r
              v17 v14 fW1 (by rw [htd]) (by omega)
              (show prog.getD 232 Instr.reject = Instr.blt 17 14 235 by rfl)
              (show prog.getD 233 Instr.reject = Instr.blt 14 17 235 by rfl)
              (show prog.getD 234 Instr.reject = Instr.accept by rfl)]
            have hmem : t ∈ [0, a1, a2, a1 + a2, a3, a3 + a1, a3 + a2,
                a3 + a1 + a2] := by simp [List.mem_cons, List.mem_singleton, htd]
            rw [decide_eq_true_iff.mpr hmem]
          · obtain ⟨c4, hc4, hch4⟩ := eq_triple_ne ρ 232 235 17 14 a3 t _
              ((S - 17) - c1 - c2 - c3) r v17 v14 fW1 (Ne.symm htd) (by omega)
              (show prog.getD 232 Instr.reject = Instr.blt 17 14 235 by rfl)
              (show prog.getD 233 Instr.reject = Instr.blt 14 17 235 by rfl)
            rw [hch4]
            -- 235: T1 := a3 + a1, ladder 236
            have e235 : (up (up (up (up (up g 21 2) 21 3) 21 4) 14 t)
                21 (a1 + a2)) 17
                + (up (up (up (up (up g 21 2) 21 3) 21 4) 14 t) 21 (a1 + a2))
                  15 = a3 + a1 := by rw [v17, v15]
            have fW2 : ∀ q,
                (up (up (up (up (up (up g 21 2) 21 3) 21 4) 14 t)
                  21 (a1 + a2)) 20 (a3 + a1)) q < 2 ^ w := fit_up fW1 hv31
            rw [exec_add_step (by omega)
              (show prog.getD 235 Instr.reject = Instr.add 20 17 15 by rfl),
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
            · rw [eq_triple_eq ρ 236 239 20 14 (a3 + a1) t _ _ r u20 u14 fW2
                (by rw [hte]) (by omega)
                (show prog.getD 236 Instr.reject = Instr.blt 20 14 239 by rfl)
                (show prog.getD 237 Instr.reject = Instr.blt 14 20 239 by rfl)
                (show prog.getD 238 Instr.reject = Instr.accept by rfl)]
              have hmem : t ∈ [0, a1, a2, a1 + a2, a3, a3 + a1, a3 + a2,
                  a3 + a1 + a2] := by
                simp [List.mem_cons, List.mem_singleton, hte]
              rw [decide_eq_true_iff.mpr hmem]
            · obtain ⟨c5, hc5, hch5⟩ := eq_triple_ne ρ 236 239 20 14
                (a3 + a1) t _
                ((S - 17) - c1 - c2 - c3 - c4 - 1) r u20 u14 fW2
                (Ne.symm hte) (by omega)
                (show prog.getD 236 Instr.reject = Instr.blt 20 14 239 by rfl)
                (show prog.getD 237 Instr.reject = Instr.blt 14 20 239 by rfl)
              rw [hch5]
              -- 239: T1 := a3 + a2, ladder 240
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
                (show prog.getD 239 Instr.reject = Instr.add 20 17 16 by rfl),
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
              · rw [eq_triple_eq ρ 240 243 20 14 (a3 + a2) t _ _ r x20 x14 fW3
                  (by rw [htf]) (by omega)
                  (show prog.getD 240 Instr.reject = Instr.blt 20 14 243 by rfl)
                  (show prog.getD 241 Instr.reject = Instr.blt 14 20 243 by rfl)
                  (show prog.getD 242 Instr.reject = Instr.accept by rfl)]
                have hmem : t ∈ [0, a1, a2, a1 + a2, a3, a3 + a1, a3 + a2,
                    a3 + a1 + a2] := by
                  simp [List.mem_cons, List.mem_singleton, htf]
                rw [decide_eq_true_iff.mpr hmem]
              · obtain ⟨c6, hc6, hch6⟩ := eq_triple_ne ρ 240 243 20 14
                  (a3 + a2) t _
                  ((S - 17) - c1 - c2 - c3 - c4 - 1 - c5 - 1) r x20 x14 fW3
                  (Ne.symm htf) (by omega)
                  (show prog.getD 240 Instr.reject = Instr.blt 20 14 243 by rfl)
                  (show prog.getD 241 Instr.reject = Instr.blt 14 20 243 by rfl)
                rw [hch6]
                -- 243: T1 := a3 + (a1 + a2), ladder 244
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
                  (show prog.getD 243 Instr.reject = Instr.add 20 17 21 by rfl),
                  e243]
                have y20 : (up (up (up (up (up (up (up (up g 21 2) 21 3) 21 4)
                          14 t) 21 (a1 + a2)) 20 (a3 + a1)) 20 (a3 + a2))
                      20 (a3 + a1 + a2)) 20 = a3 + a1 + a2 := up_eq _ _ _
                have y14 : (up (up (up (up (up (up (up (up g 21 2) 21 3) 21 4)
                          14 t) 21 (a1 + a2)) 20 (a3 + a1)) 20 (a3 + a2))
                      20 (a3 + a1 + a2)) 14 = t := by
                  rw [up_ne (show (14:Nat) ≠ 20 by omega), x14]
                by_cases htg : t = a3 + a1 + a2
                · rw [eq_triple_eq ρ 244 247 20 14 (a3 + a1 + a2) t _ _ r y20
                      y14 fW4 (by rw [htg]) (by omega)
                    (show prog.getD 244 Instr.reject
                        = Instr.blt 20 14 247 by rfl)
                    (show prog.getD 245 Instr.reject
                        = Instr.blt 14 20 247 by rfl)
                    (show prog.getD 246 Instr.reject = Instr.accept by rfl)]
                  have hmem : t ∈ [0, a1, a2, a1 + a2, a3, a3 + a1, a3 + a2,
                      a3 + a1 + a2] := by
                    simp [List.mem_cons, List.mem_singleton, htg]
                  rw [decide_eq_true_iff.mpr hmem]
                · obtain ⟨c7, hc7, hch7⟩ := eq_triple_ne ρ 244 247 20 14
                    (a3 + a1 + a2) t _
                    ((S - 17) - c1 - c2 - c3 - c4 - 1 - c5 - 1 - c6 - 1) r
                    y20 y14 fW4 (Ne.symm htg)
                    (by omega)
                    (show prog.getD 244 Instr.reject
                        = Instr.blt 20 14 247 by rfl)
                    (show prog.getD 245 Instr.reject
                        = Instr.blt 14 20 247 by rfl)
                  rw [hch7,
                    exec_reject_step (by omega)
                      (show prog.getD 247 Instr.reject = Instr.reject by rfl)]
                  have hmem : ¬ t ∈ [0, a1, a2, a1 + a2, a3, a3 + a1, a3 + a2,
                      a3 + a1 + a2] := by
                    simp only [List.mem_cons, List.mem_singleton,
                      List.not_mem_nil, or_false, not_or]
                    exact ⟨(by omega : t ≠ 0), hta, htb, htc, htd, hte, htf,
                      htg⟩
                  simp [hmem]

end SubsetSum.MITM
