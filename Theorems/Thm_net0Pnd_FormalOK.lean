import Theorems.Thm_pnd_formalOK_repair
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

/-!
# The remaining formal-correctness bridge for `net0Pnd`

The RawZero repair changes proof-machinery functions, but does not by itself
rewrite `Pnd.ch0P`.  In particular, at the defective forward move the repaired
matrix is genuinely different from the matrix still used by `Pnd.ch0P`.
Consequently the formal-label/flag-basis argument cannot be discharged merely
by importing the repair.

The exact residual prime-power certificate is packaged as
`Net0PndFormalOKPrimePower`.  The second theorem is the complete large-prime
assembly once that certificate is supplied.  No unproved declaration is used.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.Net0Pnd

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix Module

/-- The repaired forward move is not the original move used by `Pnd.ch0P`. -/
theorem DmRawZero_1773_1774_ne_Dm :
    DmRawZero 1773 1774 ≠ Pnd.Dm 1773 1774 := by
  rw [DmRawZero_1773_1774, Dm_1773_1774]
  intro h
  have hz : Pc 1773 = 0 := sub_eq_self.mp h.symm
  have hr := Pc1773_rank
  rw [hz, Matrix.rank_zero] at hr
  norm_num at hr

/-- The repaired side-rank label is also different at the defective move. -/
theorem rkCRawZero_1773_1774_ne_rkC :
    rkCRawZero 1773 1774 ≠ Pnd.rkC 1773 1774 := by
  rw [rkCRawZero_1773_1774, show Pnd.rkC 1773 1774 = 0 by decide +kernel]
  decide

/-- The exact formal-correctness certificate still needed for the requested
`net0Pnd` witness, above a finite prime bound `q₀`.  The hypothesis name
`net0Pnd_formalOK_of_FB0` in the consumer refers to this packaged conclusion;
it does not assert that the old `Pnd.FB0` is a RawZero flag basis. -/
def Net0PndFormalOKPrimePower (q₀ : ℕ) : Prop :=
  ∀ q : ℕ, q.Prime → q₀ < q → ∀ f : ℕ, net0Pnd.FormalOK (q ^ f)

/-- Large-prime FormalOK, conditional only on the explicitly named residual
flag-basis/formal-label bridge. -/
theorem net0Pnd_FormalOK_large_of_bridge
    (net0Pnd_formalOK_of_FB0 : ∃ q₀ : ℕ, Net0PndFormalOKPrimePower q₀) :
    ∃ q₁ : ℕ, ∀ q, q.Prime → q₁ < q → ∀ f : ℕ, net0Pnd.FormalOK (q ^ f) := by
  exact net0Pnd_formalOK_of_FB0

end IntMul.Kappa.R8.Bit.Oppbank.Net0Pnd
