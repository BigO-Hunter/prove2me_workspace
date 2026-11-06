import Submission.Bench
import Submission.Det
set_option autoImplicit true

/-!
# The bench mirror IS the statement's `exec` (R2125607414)

`execMem` (Bench.lean) mirrors `exec` case-for-case but threads the final
memory out for diagnostics.  Here we PROVE the boolean parts coincide, so
every bench verdict was a verdict of the real semantics.
-/

namespace SubsetSum.MITM

open BigOSpeedrun.SubsetSum SubsetSum.MITM.Bench

theorem execMem_snd {w : Nat} {P : List Instr} (ρ : Nat → BitVec w) :
    ∀ (t pc r : Nat) (m : Nat → BitVec w),
    (execMem P ρ t pc r m).2 = exec P ρ t pc r m := by
  intro t
  induction t with
  | zero => intro pc r m; rfl
  | succ t ih =>
    intro pc r m
    simp only [execMem, exec]
    cases h : P.getD pc Instr.reject <;>
      first
      | rfl
      | exact ih _ _ _
      | simp only [h] <;> first | rfl | exact ih _ _ _

end SubsetSum.MITM
