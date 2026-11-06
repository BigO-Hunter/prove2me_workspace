import Theorems.Thm_mom_eq_repaired
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-!
# Histogram and moment transport for opposite-bank one-run edges

The run shapes determine the histogram independently of the Bruhat factors.
Any `Repaired.Ch` satisfying `RunShapes` has exactly the repaired network's
widths and therefore exactly the `bitR8` raw moment.  The genuine gate
certificate can supply `EdgeQ` and formal correctness without another census.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.OneRun

open IntMul.Kappa IntMul.Kappa.R6.Bit IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Repaired

/-- The one-run shape obligations on an arbitrary repaired channel record. -/
structure RunShapes (ch : Ch) : Prop where
  e1 : ∀ b o r, (ch.e1 b o r).runs = [oneRun r]
  e2 : ∀ a o r, (ch.e2 a o r).runs = [oneRun r]
  ex : ∀ b s, (ch.ex b s).runs = [oneRun (auxWidth s)]
  en : ∀ a w, (ch.en a w).runs = [oneRun 484]
  ei : ∀ a s, (ch.ei a s).runs = [oneRun (auxWidth s)]
  ec : ∀ a s, (ch.ec a s).runs = [oneRun 1]

variable {ch : Ch} (hs : RunShapes ch)
include hs

theorem progWidths_side1_of_shapes (b : ℕ) :
    progWidths (sideProg (NB.ι1 b) (ch.e1 b) sideSchedule1) = sideSchedule1 := by
  unfold sideProg
  have he := progWidths_map_eq (R := ZMod 2) sideSchedule1
    (fun r => Instr.edge (NB.ι1 b 0) (ch.e1 b 0 r)) (fun r => [r])
    (by intro r hr; simp [instrWidths, hs.e1, oneRun])
  rw [he]
  exact flatMap_singleton_id _

theorem progWidths_side2_of_shapes (a : ℕ) :
    progWidths (sideProg (NB.ι2 a) (ch.e2 a) sideSchedule2) = sideSchedule2 := by
  unfold sideProg
  have he := progWidths_map_eq (R := ZMod 2) sideSchedule2
    (fun r => Instr.edge (NB.ι2 a 0) (ch.e2 a 0 r)) (fun r => [r])
    (by intro r hr; simp [instrWidths, hs.e2, oneRun])
  rw [he]
  exact flatMap_singleton_id _

theorem progWidths_entI_of_shapes (a : ℕ) :
    progWidths (entI ch a) = entranceWidths := by
  unfold entI entranceWidths
  have he := progWidths_map_eq (R := ZMod 2) (List.range wAuxEnd)
    (fun w => Instr.edge (NB.ι2 a w) (entE ch a w))
    (fun w => [entranceWidth w]) (by
      intro w hw
      simp only [instrWidths, entE, entranceWidth]
      split_ifs <;> simp [hs.en, hs.ei, auxWidth, oneRun])
  rw [he]
  simp [flatMap_singleton_map]

theorem progWidths_blk1_of_shapes (b : ℕ) :
    progWidths (blk1 ch b) = stage1Widths := by
  rw [blk1, progWidths_append, progWidths_side1_of_shapes (ch := ch) hs b]
  have he := progWidths_map_eq (R := ZMod 2) (List.range' wEnt NR)
    (fun w => Instr.edge (NB.ι1 b w) (ch.ex b (w - wEnt)))
    (fun w => [auxWidth (w - wEnt)]) (by intro w hw; simp [instrWidths, hs.ex, oneRun])
  rw [he]
  simp [stage1Widths, auxStartWidths, flatMap_singleton_map]

theorem progWidths_blk2_of_shapes (a : ℕ) :
    progWidths (blk2 ch a) = stage2Widths := by
  rw [blk2, progWidths_append, progWidths_entI_of_shapes (ch := ch) hs a, progWidths_append,
    progWidths_side2_of_shapes (ch := ch) hs a]
  unfold corrI stage2Widths correctionWidths
  rw [progWidths_flatMap]
  have he : ∀ s ∈ List.range v,
      progWidths ([NB.xorG (NB.ι2 a (wU s)) (NB.ι2 a (wY s)),
        Instr.edge (NB.ι2 a (wU s)) (ch.ec a s),
        NB.xorG (NB.ι2 a (wX s)) (NB.ι2 a (wU s))]) = [1] := by
    intro s hs'
    simp [progWidths, instrWidths, hs.ec, oneRun, NB.xorG]
  rw [flatMap_congr' _ _ _ he]
  simp [flatMap_singleton_map]

/-- Run shapes alone force exactly the repaired width list. -/
theorem net_widths_eq_repaired_of_shapes :
    (net ch).widths = repairedNet.widths := by
  change (progEdges (prog ch)).flatMap
    (fun e => e.runs.map fun ρ => ρ.2.2) = repairedNet.widths
  rw [widths_eq_progWidths, prog, progWidths_append, progWidths_flatMap,
    progWidths_flatMap]
  simp only [progWidths_blk1_of_shapes (ch := ch) hs, progWidths_blk2_of_shapes (ch := ch) hs]
  exact repairedNet_widths.symm

/-- The raw QHNet moment is bitR8 for every one-run channel, before any gate or
formal-correctness certificate is used. -/
theorem net_mom_eq_of_shapes (τ : ℝ) :
    histMoment (net ch).hist 529 τ = histMoment IntMul.Kappa.Jain.bitR8 529 τ := by
  have hw : (net ch).hist = repairedNet.hist := by
    simp only [QHNet.hist, net_widths_eq_repaired_of_shapes (ch := ch) hs]
  rw [hw]
  exact repairedNet_mom_eq τ

/-- `EdgeQ` already includes run validity, so a per-edge existence certificate
immediately gives `RunsOK` for the one-run network. -/
theorem net_RunsOK_of_edgeQ
    (hQ : ∀ e ∈ (net ch).edges, ∃ q, EdgeQ e q) : (net ch).RunsOK := by
  intro e he ρ hρ
  obtain ⟨q, hq⟩ := hQ e he
  exact hq.1 ρ hρ

end IntMul.Kappa.R8.Bit.Oppbank.OneRun
