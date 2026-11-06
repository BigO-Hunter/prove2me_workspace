import Theorems.Thm_repaired_formalOK
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 200000

/-!
# Small computational facts for the rebalanced program

These two kernel-computed schedule facts are isolated so checking the main
rebalancing proof does not retain their large native-evaluation artifacts.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.Rebalanced

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Repaired

/-- The first side instruction has width one. -/
theorem sideSchedule1_split : sideSchedule1 = 1 :: sideSchedule1.drop 1 := by
  native_decide

/-- Stage-one slot four is the original width-528 aux instruction. -/
theorem auxWidth_four : auxWidth 4 = 528 := by
  native_decide

end IntMul.Kappa.R8.Bit.Oppbank.Rebalanced
