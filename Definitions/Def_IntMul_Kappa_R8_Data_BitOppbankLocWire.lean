import Mathlib.Data.Nat.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R8 / R7-plain BitNB local-wire layout (`NR = 27794`)

Scalar retarget of the R6 `R6Chk.Bit.Loc` wire API (`Defs51`) from `NR = 40077`
to the opp-bank / R7-plain aux block `R = 27794`. Packed R6 `GREC`/`INJ`/`RETS`
cannot be reused (`injS`/`retS` reach ~40k). Geometry matches published
`IntMul_Kappa_R8_Data_BitOppbankConsts` / `BitOppbankWireLayout`.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.Loc

def h : ℕ := 23
def v : ℕ := 1771
def Rslots : ℕ := 27794
def wEnt : ℕ := 3542
def wAuxEnd : ℕ := 31336
def NL : ℕ := 31359

def NR : ℕ := Rslots
theorem NR_eq : NR = 27794 := rfl

def NV : ℕ := v
theorem NV_eq : NV = 1771 := rfl

def wX (t : ℕ) : ℕ := t
def wY (T : ℕ) : ℕ := v + T
def wS (q : ℕ) : ℕ := wEnt + q
def wT (c : ℕ) : ℕ := wAuxEnd + c

theorem wS_base : wEnt = 3542 := rfl
theorem wT_base : wAuxEnd = 31336 := rfl

def IsSlot (w : ℕ) : Prop := wEnt ≤ w ∧ w < wAuxEnd

theorem IsSlot_bounds (w : ℕ) (h : IsSlot w) : 3542 ≤ w ∧ w < 31336 := by
  simpa [IsSlot, wEnt, wAuxEnd] using h

end IntMul.Kappa.R8.Bit.Oppbank.Loc
