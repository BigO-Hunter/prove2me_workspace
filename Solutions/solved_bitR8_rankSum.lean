import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_KappaJainData

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa IntMul.Kappa.Jain

theorem solution : histRankSum bitR8 = 55395128481 := by
  decide +kernel
