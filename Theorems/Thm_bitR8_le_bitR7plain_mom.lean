import Definitions.Def_IntMul_KappaJainData
import Theorems.Thm_moment_dom

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.Jain

open IntMul.Kappa

/-- Equal total weighted width of the two frozen histograms. -/
theorem bitR8_rankSum_eq_bitR7plain : histRankSum bitR8 = histRankSum bitR7plain := by
  native_decide

/-- The cumulative weighted-mass comparison.  Widths above 528 contribute no
additional mass; below that point the frozen data are checked exhaustively. -/
theorem bitR8_cumMass_le_bitR7plain : ∀ x : ℕ,
    ((bitR8.filter (fun p : ℕ × ℕ => p.1 ≤ x)).map (fun p : ℕ × ℕ => p.1 * p.2)).sum ≤
      ((bitR7plain.filter (fun p : ℕ × ℕ => p.1 ≤ x)).map
        (fun p : ℕ × ℕ => p.1 * p.2)).sum := by
  have hfinite : ∀ x ∈ Finset.range 529,
      ((bitR8.filter (fun p : ℕ × ℕ => p.1 ≤ x)).map
        (fun p : ℕ × ℕ => p.1 * p.2)).sum ≤
        ((bitR7plain.filter (fun p : ℕ × ℕ => p.1 ≤ x)).map
          (fun p : ℕ × ℕ => p.1 * p.2)).sum := by
    native_decide
  intro x
  by_cases hx : x < 529
  · exact hfinite x (Finset.mem_range.mpr hx)
  · have hx' : 528 ≤ x := by omega
    have hAmax : ∀ p ∈ bitR8, p.1 ≤ 528 := by native_decide
    have hBmax : ∀ p ∈ bitR7plain, p.1 ≤ 528 := by native_decide
    have hfA : bitR8.filter (fun p : ℕ × ℕ => p.1 ≤ x) = bitR8 := by
      apply List.filter_eq_self.mpr
      intro p hp
      simp [le_trans (hAmax p hp) hx']
    have hfB : bitR7plain.filter (fun p : ℕ × ℕ => p.1 ≤ x) = bitR7plain := by
      apply List.filter_eq_self.mpr
      intro p hp
      simp [le_trans (hBmax p hp) hx']
    rw [hfA, hfB]
    exact le_of_eq bitR8_rankSum_eq_bitR7plain

/-- Round eight's child-width moments are dominated by the round-seven plain
witness, for every exponent between zero and one. -/
theorem bitR8_le_bitR7plain_mom : ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
    histMoment bitR8 529 τ ≤ histMoment bitR7plain 529 τ := by
  exact moment_dom bitR8 bitR7plain 529 (by decide)
    bitR8_cumMass_le_bitR7plain bitR8_rankSum_eq_bitR7plain

end IntMul.Kappa.Jain
