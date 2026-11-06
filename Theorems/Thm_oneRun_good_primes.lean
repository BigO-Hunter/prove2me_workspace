import Theorems.Thm_IntMul_Kappa_R6_Bit_NB_good_edges
import Theorems.Thm_oneRun_transport
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-!
# Large-prime edge admissibility for one-run networks

A finite superset of the network's edges, each with rational `EdgeQ`, gives the
complete large-prime `EdgesOK` certificate through the accepted `good_edges`
theorem.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.OneRun

open IntMul.Kappa IntMul.Kappa.R6.Bit IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Repaired

/-- Finite `EdgeQ` coverage gives large-prime `EdgesOK`. -/
theorem edgesOK_of_finite {ch : Ch} (E : Finset (Edge 529))
    (hQ : ∀ e ∈ E, ∃ q, EdgeQ e q)
    (hcover : ∀ e ∈ (net ch).edges, e ∈ E) :
    ∃ q₀ : ℕ, ∀ q, q.Prime → q₀ < q → ∀ f : ℕ, (net ch).EdgesOK (q ^ f) := by
  obtain ⟨q₀, hq₀⟩ := IntMul.Kappa.R6.Bit.NB.good_edges_sol_aux E hQ
  refine ⟨q₀, fun q hq hlt f e he => ?_⟩
  exact hq₀ q hq hlt f e (hcover e he)

end IntMul.Kappa.R8.Bit.Oppbank.OneRun
