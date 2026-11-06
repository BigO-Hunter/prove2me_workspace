import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000

/-!
# Measured divergence of the R8 stage words from the R6 block structure

Wound R2125607274.  R6's `GREC` had exactly 143 elements; R8's has 213.  The
`W1F`/`W2F` `mixFB` block partitions were carried over from R6 unretargeted
and end at 143, so the block runs cover only 36,608 of the 54,290 decoded
records.  The R6 word-decomposition premise (`Ag_blocks`: block gates = `Ag`)
is therefore FALSE for R8, and the R6 stage algebra does not transfer.  The
word nevertheless computes the correct scalar effect — certified by the
influence-mask reflection (`Thm_oneRunNB_mask.lean`), which is the proof path
for this lane; structural proof would require a retargeted partition plus
regeneration and re-verification of the generated data.

The facts below are pinned so no future port re-assumes the R6 premise.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.OneRunNB

open IntMul.Kappa.R8.Bit.Oppbank IntMul.Kappa.R8.Bit.Oppbank.NB
open IntMul.Kappa.R8.Bit.Oppbank.LocGrecDense

theorem grec_cardinality : GREC.length = 213 := by native_decide

theorem blk_coverage :
    (blkRecs 0 143).length = 36608 ∧ recs.length = 54290 ∧
      GREC.length - 143 = 70 := by native_decide

/-- **Immunization pin**: the R6 `Ag_blocks` premise is false for R8. -/
theorem Ag_blocks_ne :
    (blkRecs 0 143).flatMap recEl ≠ recs.flatMap recEl := by native_decide

end IntMul.Kappa.R8.Bit.Oppbank.OneRunNB
