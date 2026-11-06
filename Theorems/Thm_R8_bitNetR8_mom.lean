-- target 2e2fbbed-4b7d-41fb-805a-f7ccbd667355 R8.bitNetR8_mom
-- preamble:
--   import Definitions.Def_IntMul_Kappa_RG_Defs
import Definitions.Def_IntMul_KappaJainData
import Definitions.Def_IntMul_Kappa_RG_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8

open IntMul.Kappa IntMul.Kappa.R6.Bit

/-- Round-eight bit interchange (opposite bank orders on the round-seven witness 2): a QH-network
over `ZMod 2` with $W = 104719230$ roles and width $m = 529$ whose child-width moments are
dominated by `Jain.bitR8`. -/
theorem bitNetR8_mom : BitNetMomStmtG 104719230 529 Jain.bitR8 := by
  sorry

end IntMul.Kappa.R8
