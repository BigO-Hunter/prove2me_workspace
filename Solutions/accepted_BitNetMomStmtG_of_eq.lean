import Definitions.Def_IntMul_Kappa_RG_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa IntMul.Kappa.R6.Bit

theorem solution (Wb mb T q₀ : ℕ) (hb : List (ℕ × ℕ))
    (C : QHNet (ZMod 2) Wb T mb)
    (hRun : C.RunsOK)
    (hOK : ∀ q, q.Prime → q₀ < q → ∀ f, C.EdgesOK (q ^ f) ∧ C.FormalOK (q ^ f))
    (hmom : ∀ τ : ℝ, 0 < τ → τ ≤ 1 → histMoment C.hist mb τ = histMoment hb mb τ) :
    BitNetMomStmtG Wb mb hb :=
  ⟨T, C, q₀, hRun, hOK, fun τ h₁ h₂ => (hmom τ h₁ h₂).le⟩
