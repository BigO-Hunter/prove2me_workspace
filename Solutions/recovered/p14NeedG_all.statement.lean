-- {"theorem_id": "2f863fbf-8dff-4a45-886d-f2b2f4671772", "theorem_name": "IntMul.Kappa.R6.IL3H.p14NeedG_all", "status": "Proved", "preamble": "import Definitions.Def_IntMul_Kappa_RG_Defs\n\nset_option autoImplicit false\nset_option relaxedAutoImplicit false"}
namespace IntMul.Kappa.R6.IL3H

theorem p14NeedG_all (Wc mc wmax p₀ : ℕ) (hc : List (ℕ × ℕ))
    (hm16 : 16 ≤ mc) (hm' : mc ≤ 1000000) (hW1 : 1 ≤ Wc) (hwm : wmax ≤ mc)
    (hb : ∀ p ∈ hc, 1 ≤ p.1 ∧ p.1 ≤ wmax)
    (hnum : ∀ e, p₀ ≤ e → 2 * ((hc.map Prod.snd).sum * (2 * wmax + 1) ^ e) ≤ (2 * mc) ^ e)
    (hp₀ : (p₀ : ℝ) ≤ 2 + mc * Real.log (histRankSum hc)) (hp1 : 1 ≤ p₀)
    (P : Prm) (hP : P.Ok) : P14NeedG Wc mc hc P := by
  sorry

end IntMul.Kappa.R6.IL3H
