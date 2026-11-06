import Definitions.Def_IntMul_KappaJainData
import Definitions.Def_IntMul_KappaFramework

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.Jain

open IntMul.Kappa

/-- The frozen bitR8 histogram's rank sum = 55,395,128,481.
Independent walk (Python exact, both words) verified this integer first;
this is the kernel's own agreement with the walk. -/
theorem bitR8_rankSum : histRankSum bitR8 = 55395128481 := by
  decide

end IntMul.Kappa.Jain
