-- target c9ba878b-4237-4dfe-b46d-64444d96c1a1 R8.Bit.Oppbank.mom_eq
-- preamble:
--   import Definitions.Def_IntMul_Kappa_RG_Defs
import Definitions.Def_IntMul_KappaJainData
import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNet0P
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNetMom
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMomPack
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa
open IntMul.Kappa.Jain
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.Net0P

/-- Child-width moments of densified `net0P` match `Jain.bitR8` on all τ. -/
theorem mom_eq :
    ∀ τ : ℝ, histMoment net0P.hist 529 τ = histMoment bitR8 529 τ := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
