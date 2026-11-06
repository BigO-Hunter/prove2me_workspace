import Definitions.Def_IntMul_Kappa_RG_Defs
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMomPack
import Theorems.Thm_net0Pnd_EdgesOK
import Theorems.Thm_net0Pnd_FormalOK
import Theorems.Thm_bitR8_le_bitR7plain_mom
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

/-!
# Conditional final assembly of the round-seven plain moment rung

All finite assembly steps are proved here.  Two genuinely mathematical inputs
remain explicit hypotheses rather than hidden placeholders:

* `net0Pnd_formalOK_of_FB0`, the missing flag-basis/formal-label bridge;
* a one-sided network-to-`oppbankHist` moment bound.

The second input is deliberately one-sided.  Equality of the network moment
with `bitR8` is not a valid substitute: all `net0Pnd` run widths are odd,
whereas `bitR8` has positive multiplicities at even widths.
-/

namespace IntMul.Kappa.R8

open IntMul.Kappa
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Net0Pnd

/-- The full rung with `Tmp`, `net0Pnd`, its proved `RunsOK` and
`EdgesOK_large` certificates, and the two named residual hypotheses. -/
theorem bitNetR7plain_mom_final
    (net0Pnd_formalOK_of_FB0 : ∃ qF : ℕ, Net0PndFormalOKPrimePower qF)
    (net0Pnd_moment_le_oppbank :
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
        histMoment net0Pnd.hist 529 τ ≤ histMoment oppbankHist 529 τ) :
    BitNetMomStmtG 104719230 529 Jain.bitR7plain := by
  obtain ⟨qE, hE⟩ := net0Pnd_EdgesOK_large
  obtain ⟨qF, hF⟩ := net0Pnd_FormalOK_large_of_bridge net0Pnd_formalOK_of_FB0
  refine ⟨3217907, net0Pnd, max qE qF, net0Pnd_RunsOK, ?_, ?_⟩
  · intro q hq hqEF f
    have hqE : qE < q := lt_of_le_of_lt (Nat.le_max_left _ _) hqEF
    have hqF : qF < q := lt_of_le_of_lt (Nat.le_max_right _ _) hqEF
    exact ⟨hE q hq hqE f, hF q hq hqF f⟩
  · intro τ hτ hτ1
    calc
      histMoment net0Pnd.hist 529 τ ≤ histMoment oppbankHist 529 τ :=
        net0Pnd_moment_le_oppbank τ hτ hτ1
      _ = histMoment Jain.bitR8 529 τ :=
        MomPack.histMoment_oppbank_bitR8_529 τ
      _ ≤ histMoment Jain.bitR7plain 529 τ :=
        Jain.bitR8_le_bitR7plain_mom τ hτ hτ1

end IntMul.Kappa.R8
