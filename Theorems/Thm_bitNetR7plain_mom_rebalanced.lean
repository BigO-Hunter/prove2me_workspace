import Theorems.Thm_rebalanced
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 200000

/-!
# Generalized round-seven assembly for the rebalanced witness

This is the witness-generic version of `bitNetR7plain_mom_repaired_of_formalOK`:
it consumes the redesigned `rebalancedNet`, its unconditional run/edge/moment
certificates, and its own all-role `FormalOK` premise.  The original repaired
net's premise is not used.

`Thm_rebalanced` also proves that this particular all-role premise is false:
the stage-one slot-four role is still a one-run width-506 frame.  Thus the file
both generalizes the assembler and records the exact remaining gap; it does not
disguise the failed all-role premise as a completed rung.
-/

namespace IntMul.Kappa.R8

open IntMul.Kappa
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Repaired
open IntMul.Kappa.R8.Bit.Oppbank.Rebalanced

/-- Fully witness-generic assembler.  Any replacement network with the
`bitR8` raw moment and its own run, edge, and all-role formal certificates can
be used; neither the old nor the new concrete program is baked into this
theorem. -/
theorem bitNetR7plain_mom_of_formalOK
    {T q₀ : ℕ} (C : QHNet (ZMod 2) 104719230 T 529)
    (hRuns : C.RunsOK)
    (hEdges : ∀ q, q.Prime → q₀ < q → ∀ f, C.EdgesOK (q ^ f))
    (hFormal : ∀ q, q.Prime → q₀ < q → ∀ f, C.FormalOK (q ^ f))
    (hMom : ∀ τ : ℝ, histMoment C.hist 529 τ = histMoment Jain.bitR8 529 τ) :
    BitNetMomStmtG 104719230 529 Jain.bitR7plain := by
  refine ⟨T, C, q₀, hRuns, ?_, ?_⟩
  · intro q hq hq₀ f
    exact ⟨hEdges q hq hq₀ f, hFormal q hq hq₀ f⟩
  · intro τ hτ hτ1
    calc
      histMoment C.hist 529 τ = histMoment Jain.bitR8 529 τ := hMom τ
      _ ≤ histMoment Jain.bitR7plain 529 τ :=
        Jain.bitR8_le_bitR7plain_mom τ hτ hτ1

/-- Everything in the final rung except all-role `FormalOK`, now instantiated
with the redesigned histogram-neutral witness. -/
theorem bitNetR7plain_mom_rebalanced_core :
    ∃ (T : ℕ) (C : QHNet (ZMod 2) 104719230 T 529) (q₀ : ℕ),
      C.RunsOK ∧
        (∀ q, q.Prime → q₀ < q → ∀ f, C.EdgesOK (q ^ f)) ∧
          ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
            histMoment C.hist 529 τ ≤ histMoment Jain.bitR7plain 529 τ := by
  refine ⟨3217907, rebalancedNet, 0, rebalancedNet_RunsOK, ?_, ?_⟩
  · intro q hq hq₀ f
    exact rebalancedNet_EdgesOK (q ^ f)
  · intro τ hτ hτ1
    calc
      histMoment rebalancedNet.hist 529 τ = histMoment Jain.bitR8 529 τ :=
        rebalancedNet_mom_eq τ
      _ ≤ histMoment Jain.bitR7plain 529 τ :=
        Jain.bitR8_le_bitR7plain_mom τ hτ hτ1

/-- Conditional final assembly against the redesigned witness's own formal
certificate.  No premise about the original `repairedNet` occurs here. -/
theorem bitNetR7plain_mom_rebalanced_of_formalOK
    (hFormal : RebalancedFormalOKLarge) :
    BitNetMomStmtG 104719230 529 Jain.bitR7plain := by
  obtain ⟨qF, hF⟩ := hFormal
  exact bitNetR7plain_mom_of_formalOK (q₀ := qF) rebalancedNet rebalancedNet_RunsOK
    (fun q hq hqF f => rebalancedNet_EdgesOK (q ^ f)) hF rebalancedNet_mom_eq

/-- The remaining gap is not merely hypothetical: the present redesigned net
fails all-role formal correctness at slot four, so its large-prime premise is
uninhabitable. -/
theorem rebalanced_formal_premise_false : ¬ RebalancedFormalOKLarge :=
  not_RebalancedFormalOKLarge

end IntMul.Kappa.R8
