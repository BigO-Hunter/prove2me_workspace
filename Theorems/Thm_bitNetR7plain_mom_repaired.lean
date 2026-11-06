import Definitions.Def_IntMul_Kappa_RG_Defs
import Theorems.Thm_mom_eq_repaired
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 200000

/-!
# Repaired round-seven plain moment assembly

The repaired witness is `repairedNet`, definitionally `net ch0R`.  Its raw
one-per-child histogram has exactly the `bitR8` moment, and the compiled Abel
summation theorem dominates that moment by `bitR7plain`.  Runs and edge
admissibility are unconditional.  The only missing input for the full
`BitNetMomStmtG` is the explicitly isolated large-prime `FormalOK` certificate.
-/

namespace IntMul.Kappa.R8

open IntMul.Kappa
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Repaired

/-- The exact remaining repaired-network obligation: formal correctness at all
prime powers whose prime exceeds one finite bound. -/
def RepairedFormalOKLarge : Prop :=
  ∃ q₀ : ℕ, ∀ q, q.Prime → q₀ < q → ∀ f : ℕ, repairedNet.FormalOK (q ^ f)

/-- Everything in the final rung except `FormalOK`, with the repaired
`net ch0R` witness and the full moment-domination chain. -/
theorem bitNetR7plain_mom_repaired_core :
    ∃ (T : ℕ) (C : QHNet (ZMod 2) 104719230 T 529) (q₀ : ℕ),
      C.RunsOK ∧
        (∀ q, q.Prime → q₀ < q → ∀ f, C.EdgesOK (q ^ f)) ∧
          ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
            histMoment C.hist 529 τ ≤ histMoment Jain.bitR7plain 529 τ := by
  refine ⟨3217907, repairedNet, 0, repairedNet_RunsOK, ?_, ?_⟩
  · intro q hq hq₀ f
    exact repairedNet_EdgesOK (q ^ f)
  · intro τ hτ hτ1
    calc
      histMoment repairedNet.hist 529 τ = histMoment Jain.bitR8 529 τ :=
        repairedNet_mom_eq τ
      _ ≤ histMoment Jain.bitR7plain 529 τ :=
        Jain.bitR8_le_bitR7plain_mom τ hτ hτ1

/-- Conditional final assembly.  Supplying exactly `RepairedFormalOKLarge`
closes the complete `BitNetMomStmtG`; no other hypothesis remains. -/
theorem bitNetR7plain_mom_repaired_of_formalOK
    (hFormal : RepairedFormalOKLarge) :
    BitNetMomStmtG 104719230 529 Jain.bitR7plain := by
  obtain ⟨qF, hF⟩ := hFormal
  refine ⟨3217907, repairedNet, qF, repairedNet_RunsOK, ?_, ?_⟩
  · intro q hq hqF f
    exact ⟨repairedNet_EdgesOK (q ^ f), hF q hq hqF f⟩
  · intro τ hτ hτ1
    calc
      histMoment repairedNet.hist 529 τ = histMoment Jain.bitR8 529 τ :=
        repairedNet_mom_eq τ
      _ ≤ histMoment Jain.bitR7plain 529 τ :=
        Jain.bitR8_le_bitR7plain_mom τ hτ hτ1

end IntMul.Kappa.R8
