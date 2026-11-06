-- NetD→Pnd rewire feed for Track A net0_ok assembly.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNet0Pnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankHist
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-!
# Track A rewire: stub NetD/ProjB → densified `Pnd` / `net0Pnd`

Hand to A alongside GoodPrimes / NetMom / NetFB / NetD_Runs:

* `net0` := `Net0Pnd.net0Pnd` (honest `Pnd.ch0P`)
* `codeBound` / `nNodes` densified locks
* `targetHist` := `oppbankHist`
* `ch0Preferred` := `Pnd.ch0P`
-/

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank

namespace IntMul.Kappa.R8.Bit.Oppbank.NetOkFeed

noncomputable def net0 : QHNet (ZMod 2) 104719230 3217907 529 := Net0Pnd.net0Pnd

def codeBound : ℕ := SupG.codeBound
def nNodes : ℕ := SupG.nNodes

theorem codeBound_eq : codeBound = 64251 := rfl
theorem nNodes_eq : nNodes = 62478 := rfl
theorem codeBound_nNodes : codeBound = 1773 + nNodes := (rfl : 64251 = 1773 + 62478)

def targetHist : List (ℕ × ℕ) := oppbankHist

noncomputable def ch0Preferred : Pnd.Ch := Pnd.ch0P

end IntMul.Kappa.R8.Bit.Oppbank.NetOkFeed
