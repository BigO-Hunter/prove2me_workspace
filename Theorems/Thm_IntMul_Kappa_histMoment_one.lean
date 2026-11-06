import Definitions.Def_IntMul_KappaFramework

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa

/-- The tau=1 moment is the rank sum over the width:
`sum n_w * (w/m) = (sum w * n_w) / m`. The bridge every `*_histMoment_one`
instance reduces through. -/
theorem histMoment_one (h : List (ℕ × ℕ)) (m : ℕ) (hm : 0 < m) :
    histMoment h m 1 = (histRankSum h : ℝ) / m := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  have hp : ∀ p : ℕ × ℕ, (p.2 : ℝ) * ((p.1 : ℝ) / m) ^ (1:ℝ) = ((p.1 * p.2 : ℕ) : ℝ) / m := by
    intro p
    rw [Real.rpow_one]
    push_cast
    field_simp [hm']
  simp only [histMoment, hp]
  induction h with
  | nil => simp [histRankSum]
  | cons p h ih =>
    rw [List.map_cons, List.sum_cons, ih]
    simp only [histRankSum, List.map_cons, List.sum_cons, Nat.cast_add]
    rw [← add_div]

end IntMul.Kappa
