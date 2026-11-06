-- target fefc194e-5f71-4f82-bf41-128e02ff35ff R8.bitNetR7plain_mom
-- preamble:
--   import Definitions.Def_IntMul_Kappa_RG_Defs
import Definitions.Def_IntMul_KappaJainData
import Definitions.Def_IntMul_Kappa_RG_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8

open IntMul.Kappa IntMul.Kappa.R6.Bit

/-- Round-seven bit network, witness 2 with the round-six entrance corner (`bitplainHist`):
a QH-network over `ZMod 2` with $W = 104719230$ roles and width $m = 529$ whose
child-width moments are dominated by `Jain.bitR7plain`. This is the `a_old` network
of round eight's stopped bit interchange. -/
theorem bitNetR7plain_mom : BitNetMomStmtG 104719230 529 Jain.bitR7plain := by
  sorry

end IntMul.Kappa.R8
