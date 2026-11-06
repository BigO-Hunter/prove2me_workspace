import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Theorems.Thm_repaired_ch0R

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-!
# Genuine scheduled program for opposite-bank one-run edges

This is the frame-correct program shape: the published `NB.cs1`/`NB.cs2`
chunks and their gates are retained, while aux channels carry their slot and
edge families have the one-run shapes.  The simplified `sideProg` skeleton is
used only for histogram reconnaissance and is not the scalar-circuit target.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.OneRunNB

open IntMul.Kappa IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Repaired

/-- Stage-one block: genuine chunks followed by slot-dependent aux exits. -/
def blk1 (ch : Ch) (b : ℕ) : List NI :=
  NB.chunkProg (NB.ι1 b) (ch.e1 b) NB.cs1 ++
    (List.range' wEnt NR).map fun w =>
      Instr.edge (NB.ι1 b w) (ch.ex b (w - wEnt))

/-- Stage-two block: genuine entrance, chunks, and copy corrections. -/
def blk2 (ch : Ch) (a : ℕ) : List NI :=
  entI ch a ++ (NB.chunkProg (NB.ι2 a) (ch.e2 a) NB.cs2 ++ (List.range v).flatMap (corrI ch a))

/-- Full two-stage program with the genuine chunk gates. -/
def prog (ch : Ch) : List NI :=
  (List.range v).flatMap (blk1 ch) ++ (List.range v).flatMap (blk2 ch)

/-- The genuine scheduled network on `W=104719230`, `T=3217907`, `m=529`. -/
noncomputable def net (ch : Ch) : QHNet (ZMod 2) 104719230 3217907 529 :=
  ⟨prog ch, NB.ρ⟩

end IntMul.Kappa.R8.Bit.Oppbank.OneRunNB
