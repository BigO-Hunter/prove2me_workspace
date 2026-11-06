import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_KappaJainData
import Theorems.Thm_IntMul_Kappa_histMoment_one
import Theorems.Thm_IntMul_Kappa_R8_bitR8_rankSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa IntMul.Kappa.Jain IntMul.Kappa.R8

theorem solution : histMoment bitR8 529 1 = (55395128481 : ℝ) / 529 := by
  have h := histMoment_one bitR8 529 (by norm_num)
  rw [bitR8_rankSum] at h
  exact h

#print solution
