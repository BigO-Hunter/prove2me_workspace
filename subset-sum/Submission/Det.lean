import Submission.Program
set_option autoImplicit true

/-!
# Determinism and the `Correct` collapse (R2125607414)

The program never executes `rand`, so every tape yields the same verdict.
Then `Correct`'s two-thirds probability condition holds at 100%: if every
`s < N` gives verdict `v`, `count` is `N` itself and `2·N ≤ 3·N`.

This module is program-agnostic: it consumes a `no-rand` hypothesis, a
halting horizon, and a verdict-fact, and produces `Correct P x`.
-/

namespace SubsetSum.MITM

open BigOSpeedrun.SubsetSum

/-! ## `getD` and no-rand -/

theorem getD_mem : ∀ (P : List Instr) (pc : Nat) (p : Instr),
    P.getD pc .reject = p → p = .reject ∨ p ∈ P := by
  intro P
  induction P with
  | nil =>
    intro pc p h
    cases pc <;> exact Or.inl h.symm
  | cons q Q ih =>
    intro pc p h
    cases pc with
    | zero => exact Or.inr (by rw [← h]; exact List.mem_cons_self)
    | succ pc =>
      rcases ih pc p h with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (List.mem_cons_of_mem _ h2)

/-- The program contains no `rand` instruction. -/
def NoRand (P : List Instr) : Prop :=
  ∀ p ∈ P, ∀ i, p ≠ Instr.rand i

theorem NoRand.getD {P : List Instr} (hP : NoRand P) (pc i : Nat) :
    P.getD pc .reject ≠ Instr.rand i := by
  intro h
  rcases getD_mem P pc _ h with h1 | h2
  · exact absurd h1 (by simp)
  · exact hP _ h2 i rfl

/-! ## `exec` never consults `ρ` without `rand` -/

theorem exec_no_rand {w : Nat} {P : List Instr} (hP : NoRand P) :
    ∀ (t pc r : Nat) (m : Nat → BitVec w) (ρ1 ρ2 : Nat → BitVec w),
    exec P ρ1 t pc r m = exec P ρ2 t pc r m := by
  intro t
  induction t with
  | zero => intro pc r m ρ1 ρ2; rfl
  | succ t ih =>
    intro pc r m ρ1 ρ2
    simp only [exec]
    split
    · exact ih _ _ _ _ _
    · exact ih _ _ _ _ _
    · exact ih _ _ _ _ _
    · exact ih _ _ _ _ _
    · exact ih _ _ _ _ _
    · exact ih _ _ _ _ _
    · exact ih _ _ _ _ _
    · exact ih _ _ _ _ _
    · exact ih _ _ _ _ _
    · exact ih _ _ _ _ _
    · exact ih _ _ _ _ _
    · exact ih _ _ _ _ _
    · exact ih _ _ _ _ _
    · rename_i i hi
      exact absurd hi (hP.getD pc i)
    · exact ih _ _ _ _ _
    · rfl
    · rfl

theorem run_no_rand {w : Nat} {P : List Instr} (hP : NoRand P)
    (ρ1 ρ2 : Nat → BitVec w) (m : Nat → BitVec w) (t : Nat) :
    exec P ρ1 t 0 0 m = exec P ρ2 t 0 0 m :=
  exec_no_rand hP t 0 0 m ρ1 ρ2

/-! ## `count` of an always-true predicate -/

theorem count_all (p : Nat → Prop) [DecidablePred p] (N : Nat)
    (h : ∀ s, s < N → p s) : count p N = N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have hN : p N := h N (Nat.lt_succ_self N)
    show count p N + (if p N then 1 else 0) = N + 1
    rw [if_pos hN, ih (fun s hs => h s (Nat.lt_succ_of_lt hs))]

/-! ## The collapse -/

/-- Determinism collapses `Correct`'s probability condition: a single
verdict `v` on every tape makes the two-thirds condition hold at 100%. -/
theorem correct_of_det {n : Nat} {P : List Instr} {x : Instance n} (t : Nat)
    (halts : ∀ ρ, (run P x ρ t).isSome)
    (v : Bool) (hv : ∀ ρ, run P x ρ t = some v)
    (hyes : x.yes → v = true) (hno : ¬x.yes → v = false) :
    Correct P x := by
  refine ⟨t, halts, ?_⟩
  by_cases hy : x.yes
  · left
    have hvv : v = true := hyes hy
    refine ⟨hy, ?_⟩
    show 2 * 2 ^ (wordLength n x.bits * t)
        ≤ 3 * count (fun s => run P x (tape _ s) t = some true)
            (2 ^ (wordLength n x.bits * t))
    have hc : count (fun s => run P x (tape _ s) t = some true)
        (2 ^ (wordLength n x.bits * t))
        = 2 ^ (wordLength n x.bits * t) := by
      apply count_all
      intro s _
      show run P x (tape _ s) t = some true
      rw [hv]
      exact congrArg some hvv
    rw [hc]
    omega
  · right
    have hvv : v = false := hno hy
    refine ⟨hy, ?_⟩
    show 2 * 2 ^ (wordLength n x.bits * t)
        ≤ 3 * count (fun s => run P x (tape _ s) t = some false)
            (2 ^ (wordLength n x.bits * t))
    have hc : count (fun s => run P x (tape _ s) t = some false)
        (2 ^ (wordLength n x.bits * t))
        = 2 ^ (wordLength n x.bits * t) := by
      apply count_all
      intro s _
      show run P x (tape _ s) t = some false
      rw [hv]
      exact congrArg some hvv
    rw [hc]
    omega

end SubsetSum.MITM
