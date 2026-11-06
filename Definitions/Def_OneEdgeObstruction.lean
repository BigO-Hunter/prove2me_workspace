import Definitions.Def_IntMul_Kappa_R6_Defs4

/-!
# One-run edges for the fixed-point/full-swap obstruction

Original definition from the R8 oppbank reconstruction repair (R2125607035).
Only the two interface constructors live here; the proof and its supporting
lemmas are theorem-side, so this definition stays lightweight and census-free.
-/

namespace IntMul.Kappa.R6.Bit.OneEdgeObstruction

open IntMul.Kappa

/-- One contiguous reversed-bank run of width `w` on an `m`-wire chunk. -/
def singleRun (m w : ℕ) : ℕ × ℕ × ℕ := (0, m - w, w)

/-- An edge carrying exactly one reversed-bank run. -/
def singleEdge (m w : ℕ) : Edge m := ⟨1, [singleRun m w], 1⟩

end IntMul.Kappa.R6.Bit.OneEdgeObstruction
