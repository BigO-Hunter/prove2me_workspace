-- {"theorem_id": "a8b367da-5f63-4502-8ca7-905d27ab25cf", "theorem_name": "IntMul.Kappa.R6.rG_normalize", "status": "Proved", "preamble": "import Definitions.Def_IntMul_Kappa_R6_Defs1\nimport Definitions.Def_IntMul_KappaJainData\n\nset_option autoImplicit false\nset_option relaxedAutoImplicit false"}
namespace IntMul.Kappa.R6

theorem rG_normalize (mc sc : ℕ) (ab ac ε x C₁ κ : ℝ)
    (hτ : 0 < 1 - ab) (hσ : 0 < 1 - ac) (hab : 0 ≤ ab) (hac : 0 ≤ ac)
    (hasm : CrudeAssembly ab ac (1 / 1000) ε x C₁ κ mc sc) :
    ∃ P : Prm, P.Ok ∧ κ < P.gap ∧ P.τ = 1 - ab ∧ P.σ = 1 - ac ∧
      2 + mc * Real.log sc ≤ P.C1 := by
  sorry

end IntMul.Kappa.R6
