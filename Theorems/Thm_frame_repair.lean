import Theorems.Thm_repaired_formalOK
import Solutions.partial_bitR8_mom_gap
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 200000

/-!
# A genuine full-swap frame for the repaired aux role

The original `repairedNet` is unchanged: `not_RepairedFormalOKLarge` proves that
its conditional assembler cannot be satisfied.  This file isolates the minimal
local frame repair.  `auxFullNet` is the original program with exactly its
stage-one slot-zero aux instruction replaced by the two-run full-swap edge
`R8.Gap.uEdge` (widths `528` and `1`).

We prove that the replacement edge really has matrix `swapMat`, that the
selected aux output is formally correct at every modulus, and that the whole
modified program still passes `RunsOK` and `EdgesOK`.  We also compute the exact
price: the replaced one-run edge had width `506`, so the raw rank sum increases
by `23`.  Thus the local frame repair does **not** preserve the `bitR8`
histogram, and the old conditional assembler cannot close the rung.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.FrameRepair

open IntMul.Kappa
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Repaired

/-- The genuine full chunk interchange, decomposed into valid runs of widths
`528` and `1`. -/
abbrev fullSwapEdge : Edge 529 := IntMul.Kappa.R8.Gap.uEdge

theorem edgeMat_fullSwapEdge (M : ℕ) : edgeMat M fullSwapEdge = AModel.swapMat :=
  IntMul.Kappa.R8.Gap.edgeMat_uEdge M

theorem fullSwapEdge_RunsOK : ∀ ρ ∈ fullSwapEdge.runs, RunOK 529 ρ :=
  IntMul.Kappa.R8.Gap.uEdge_RunsOK

theorem fullSwapEdge_EdgeOK (M : ℕ) : EdgeOK M fullSwapEdge :=
  IntMul.Kappa.R8.Gap.uEdge_EdgeOK M

/-- Typed append rule for the repaired program's instruction alias. -/
theorem progEdges_append_ni (p q : List NI) :
    progEdges (p ++ q) = progEdges p ++ progEdges q := by
  unfold progEdges
  rw [List.filterMap_append]

/-- The replacement instruction, on the same wire as the old aux instruction. -/
noncomputable def auxFullInstr : NI := .edge (NB.ι1 0 wEnt) fullSwapEdge

/-- The original repaired program with exactly one instruction replaced. -/
noncomputable def auxFullNet : QHNet (ZMod 2) 104719230 3217907 529 :=
  ⟨auxPre ++ auxFullInstr :: auxPost, NB.ρ⟩

theorem auxFullNet_edges :
    auxFullNet.edges = progEdges auxPre ++ fullSwapEdge :: progEdges auxPost := by
  change progEdges (auxPre ++ auxFullInstr :: auxPost) = _
  rw [progEdges_append_ni]
  rfl

theorem repairedNet_edges_split :
    repairedNet.edges = progEdges auxPre ++ oneEdge (auxWidth 0) :: progEdges auxPost := by
  change progEdges (prog ch0R) = _
  rw [show prog ch0R = auxPre ++ auxInstr :: auxPost from repaired_prog_split,
    progEdges_append_ni]
  rfl

/-- Every new edge is either the full-swap replacement or an old repaired edge. -/
theorem edge_of_auxFullNet {e : Edge 529} (he : e ∈ auxFullNet.edges) :
    e = fullSwapEdge ∨ e ∈ repairedNet.edges := by
  rw [auxFullNet_edges] at he
  rcases List.mem_append.1 he with he | he
  · exact Or.inr (by rw [repairedNet_edges_split]; exact List.mem_append.2 (Or.inl he))
  · rcases List.mem_cons.1 he with rfl | he
    · exact Or.inl rfl
    · exact Or.inr (by
        rw [repairedNet_edges_split]
        exact List.mem_append.2 (Or.inr (List.mem_cons.2 (Or.inr he))))

/-- The local frame replacement does not damage run validity. -/
theorem auxFullNet_RunsOK : auxFullNet.RunsOK := by
  intro e he ρ hρ
  rcases edge_of_auxFullNet he with rfl | heOld
  · exact fullSwapEdge_RunsOK ρ hρ
  · exact repairedNet_RunsOK e heOld ρ hρ

/-- The local frame replacement does not damage edge admissibility. -/
theorem auxFullNet_EdgesOK (M : ℕ) : auxFullNet.EdgesOK M := by
  intro e he
  rcases edge_of_auxFullNet he with rfl | heOld
  · exact fullSwapEdge_EdgeOK M
  · exact repairedNet_EdgesOK M e heOld

/-- Formal evaluation on the selected aux wire after the frame replacement. -/
theorem auxFullNet_fold_aux (M : ℕ) :
    (auxFullNet.prog.foldl (fStep M) (QHNet.fInit M)) auxWire =
      lmulF (edgeMat M fullSwapEdge)
        (Finsupp.single ((1 : FMat 529 M), auxRole) 1) := by
  change (List.foldl (fStep M) (QHNet.fInit M) (auxPre ++ auxFullInstr :: auxPost)) auxWire = _
  rw [List.foldl_append, List.foldl_cons]
  rw [foldl_avoids M auxWire _ auxPost avoids_auxPost]
  have hw : NB.ι1 0 wEnt = auxWire := (iota1_eq_auxWire_iff (by decide)).2 ⟨rfl, rfl⟩
  simp only [auxFullInstr, fStep, hw, Function.update_self]
  rw [foldl_avoids M auxWire _ auxPre avoids_auxPre]
  simp [QHNet.fInit, auxWire]

/-- The repaired aux role really ends with the full-swap frame, at every modulus. -/
theorem auxFullNet_auxRole_formal (M : ℕ) :
    (auxFullNet.prog.foldl (fStep M) (QHNet.fInit M)) (.inl (auxFullNet.ρ auxRole)) =
      Finsupp.single (AModel.swapMat, auxRole) 1 := by
  change (auxFullNet.prog.foldl (fStep M) (QHNet.fInit M)) (.inl (NB.ρ auxRole)) = _
  rw [auxRole_merge]
  change (auxFullNet.prog.foldl (fStep M) (QHNet.fInit M)) auxWire = _
  rw [auxFullNet_fold_aux, lmulF_single, edgeMat_fullSwapEdge, Matrix.mul_one]

/-- The slot-zero aux width is `506`, not the `529` total width of a full swap. -/
theorem auxWidth_zero : auxWidth 0 = 506 := by rfl

theorem auxFullNet_widths :
    auxFullNet.widths = (progWidths auxPre ++ [528, 1]) ++ progWidths auxPost := by
  change (progEdges (auxPre ++ auxFullInstr :: auxPost)).flatMap
    (fun e => e.runs.map fun ρ => ρ.2.2) = _
  rw [widths_eq_progWidths]
  simp [progWidths, auxFullInstr, instrWidths, fullSwapEdge,
    IntMul.Kappa.R8.Gap.uEdge, List.append_assoc]

theorem repairedNet_widths_split :
    repairedNet.widths = (progWidths auxPre ++ [auxWidth 0]) ++ progWidths auxPost := by
  change (progEdges (prog ch0R)).flatMap (fun e => e.runs.map fun ρ => ρ.2.2) = _
  rw [widths_eq_progWidths]
  rw [show prog ch0R = auxPre ++ auxInstr :: auxPost from repaired_prog_split]
  simp [progWidths, auxInstr, instrWidths, ch0R, oneEdge, oneRun, List.append_assoc]

/-- The exact histogram change at width one. -/
theorem auxFullNet_count_one :
    auxFullNet.widths.count 1 = repairedNet.widths.count 1 + 1 := by
  rw [auxFullNet_widths, repairedNet_widths_split]
  simp [auxWidth_zero]
  omega

theorem auxFullNet_widths_ne : auxFullNet.widths ≠ repairedNet.widths := by
  intro h
  have hc := congrArg (List.count 1) h
  rw [auxFullNet_count_one] at hc
  omega

theorem auxFullNet_hist_ne : auxFullNet.hist ≠ repairedNet.hist := by
  intro h
  apply auxFullNet_widths_ne
  have hf := congrArg (List.map Prod.fst) h
  simpa [QHNet.hist, List.map_map, Function.comp_def] using hf

/-- Raw rank sum is the sum of the network's child widths. -/
theorem histRankSum_raw {W T : ℕ} (C : QHNet (ZMod 2) W T 529) :
    histRankSum C.hist = C.widths.sum := by
  simp [histRankSum, QHNet.hist, List.map_map, Function.comp_def]

/-- Exact price of the local full-swap repair: `528 + 1 - 506 = 23`. -/
theorem auxFullNet_rankSum :
    histRankSum auxFullNet.hist = histRankSum repairedNet.hist + 23 := by
  rw [histRankSum_raw, histRankSum_raw, auxFullNet_widths, repairedNet_widths_split]
  simp only [List.sum_append]
  have hnew : [528, 1].sum = 529 := by decide
  have hold : [auxWidth 0].sum = 506 := by simp [auxWidth_zero]
  rw [hnew, hold]
  omega

/-- The already compiled negative result remains decisive for the original
`RepairedFormalOKLarge` expected by `bitNetR7plain_mom_repaired_of_formalOK`. -/
theorem original_RepairedFormalOKLarge_false : ¬ IntMul.Kappa.R8.RepairedFormalOKLarge :=
  not_RepairedFormalOKLarge

end IntMul.Kappa.R8.Bit.Oppbank.FrameRepair
