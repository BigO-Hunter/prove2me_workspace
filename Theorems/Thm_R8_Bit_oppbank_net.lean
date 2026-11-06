-- target 1ebc5981-3aec-4a0e-beac-73b5233b6857 R8.Bit.oppbank_net
-- preamble:
--   import Definitions.Def_IntMul_Kappa_RG_Defs
import Definitions.Def_IntMul_KappaJainData
import Definitions.Def_IntMul_Kappa_RG_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit

open IntMul.Kappa IntMul.Kappa.R6.Bit

/-- Geometric content of Jain's opposite-bank recompile on round-seven witness 2:
there exists a QH-network over `ZMod 2` with $W = 104719230$ roles and width $m = 529$
that runs correctly, passes edge/formal checks at large prime powers, and whose
child-width moments agree exactly with `Jain.bitR8` on $(0,1]$.

(The schedule/frames/payload of the plain witness are unchanged; only address geometry
is recompiled. Formalising that transform on an arbitrary `BitNetMomStmtG` witness is
not required here — this leaf is the constructed network.) -/
theorem oppbank_net :
    ∃ (T : ℕ) (C : QHNet (ZMod 2) 104719230 T 529) (q₀ : ℕ),
      C.RunsOK ∧
        (∀ q, q.Prime → q₀ < q → ∀ f, C.EdgesOK (q ^ f) ∧ C.FormalOK (q ^ f)) ∧
          ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
            histMoment C.hist 529 τ = histMoment Jain.bitR8 529 τ := by
  sorry

end IntMul.Kappa.R8.Bit
