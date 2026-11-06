import Definitions.Def_IntMul_KappaJainData
import Definitions.Def_IntMul_KappaFramework

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa
open IntMul.Kappa.Jain

/-- The reordering fact: bitR7plain (witness 2) and bitR8 (its opposite-bank
recompile) carry the SAME rank mass. Walk-verified: both 55,395,128,481. -/
theorem solved_bitR7plain_bitR8_rankSum_eq :
    histRankSum bitR7plain = histRankSum bitR8 := by
  decide
