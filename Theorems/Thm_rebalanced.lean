import Theorems.Thm_rebalanced_facts
import Solutions.partial_bitR8_mom_gap
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 200000

/-!
# A histogram-neutral full-swap frame repair

The full-swap aux repair is compensated by two independent local edits:

* the first side instruction, formerly `oneEdge 1`, becomes an identity edge
  with no runs (so its one width-1 child disappears);
* the stage-one slot-four aux instruction, formerly `oneEdge 528`, becomes
  `oneEdge 506`.

Together with replacing the slot-zero `oneEdge 506` by the two-run full swap
`[528,1]`, these edits preserve every width multiplicity.  They do not change
any instruction wire, so the selected aux role retains its genuine full-swap
formal evaluation.

All-role `FormalOK` is nevertheless false for this particular redesigned net:
the stage-one slot-four output remains a one-run width-506 frame.  The final
section proves that obstruction at every prime, so the conditional assembler
in `Thm_bitNetR7plain_mom_rebalanced` is not misreported as a closed rung.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.Rebalanced

open IntMul.Kappa
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Repaired

/-- The genuine full chunk interchange. -/
abbrev fullSwapEdge : Edge 529 := IntMul.Kappa.R8.Gap.uEdge

/-- An identity Bruhat edge carrying no children. -/
def emptyEdge : Edge 529 := ⟨1, [], 1⟩

noncomputable def fullAuxInstr : NI := .edge (NB.ι1 0 wEnt) fullSwapEdge
noncomputable def sideFirstInstr : NI := .edge (NB.ι1 0 0) (oneEdge 1)
noncomputable def sideSkipInstr : NI := .edge (NB.ι1 0 0) emptyEdge
noncomputable def old528Instr : NI := .edge (NB.ι1 0 (wEnt + 4)) (oneEdge 528)
noncomputable def new506Instr : NI := .edge (NB.ι1 0 (wEnt + 4)) (oneEdge 506)

noncomputable def sideRestProg : List NI :=
  sideProg (NB.ι1 0) (ch0R.e1 0) (sideSchedule1.drop 1)

noncomputable def earlyAuxProg : List NI :=
  (List.range' (wEnt + 1) 3).map fun w =>
    Instr.edge (NB.ι1 0 w) (ch0R.ex 0 (w - wEnt))

noncomputable def lateAuxProg : List NI :=
  (List.range' (wEnt + 5) (NR - 5)).map fun w =>
    Instr.edge (NB.ι1 0 w) (ch0R.ex 0 (w - wEnt))

noncomputable def rebalancedPre : List NI := sideSkipInstr :: sideRestProg
noncomputable def rebalancedTail1 : List NI := earlyAuxProg ++ new506Instr :: lateAuxProg
noncomputable def rebalancedPost : List NI := rebalancedTail1 ++ (auxRest1 ++ auxRest2)

/-- The redesigned program.  Only the three instructions above differ from
`repairedNet`; all wires and all other instructions are unchanged. -/
noncomputable def rebalancedNet : QHNet (ZMod 2) 104719230 3217907 529 :=
  ⟨rebalancedPre ++ fullAuxInstr :: rebalancedPost, NB.ρ⟩

noncomputable def rebalanced : Reconstruction := ⟨rebalancedNet⟩

/-- Typed append rule for program edges. -/
theorem progEdges_append_ni (p q : List NI) :
    progEdges (p ++ q) = progEdges p ++ progEdges q := by
  unfold progEdges
  rw [List.filterMap_append]

/-- Edge instructions expose their edge without expanding the remaining program. -/
theorem progEdges_edge_cons (w : Wr) (e : Edge 529) (p : List NI) :
    progEdges (.edge w e :: p) = e :: progEdges p := by
  rfl

theorem progWidths_append_ni (p q : List NI) :
    progWidths (p ++ q) = progWidths p ++ progWidths q := by
  exact List.flatMap_append

theorem progWidths_cons_ni (i : NI) (p : List NI) :
    progWidths (i :: p) = instrWidths i ++ progWidths p := by
  rfl

/-! ## The three local decompositions -/

theorem auxTail_range_split :
    List.range' (wEnt + 1) (NR - 1) =
      List.range' (wEnt + 1) 3 ++
        (wEnt + 4) :: List.range' (wEnt + 5) (NR - 5) := by
  have h1 : NR - 1 = 3 + (NR - 4) := by norm_num [NR]
  have h2 : NR - 4 = (NR - 5) + 1 := by norm_num [NR]
  have hs : wEnt + 1 + 1 * 3 = wEnt + 4 := by omega
  have h3 : List.range' (wEnt + 4) (NR - 4) =
      (wEnt + 4) :: List.range' (wEnt + 5) (NR - 5) := by
    rw [h2, List.range'_succ]
  calc
    List.range' (wEnt + 1) (NR - 1) = List.range' (wEnt + 1) (3 + (NR - 4)) := by rw [h1]
    _ = List.range' (wEnt + 1) 3 ++ List.range' (wEnt + 1 + 1 * 3) (NR - 4) :=
      List.range'_append.symm
    _ = List.range' (wEnt + 1) 3 ++ List.range' (wEnt + 4) (NR - 4) := by rw [hs]
    _ = _ := by rw [h3]

theorem auxPre_rebalanced_split : auxPre = sideFirstInstr :: sideRestProg := by
  unfold auxPre
  rw [sideSchedule1_split]
  unfold sideProg
  rw [List.map_cons]
  rfl

theorem auxTail1_rebalanced_split :
    auxTail1 = earlyAuxProg ++ old528Instr :: lateAuxProg := by
  unfold auxTail1 earlyAuxProg lateAuxProg old528Instr
  rw [auxTail_range_split]
  simp only [List.map_append, List.map_cons]
  have hslot : wEnt + 4 - wEnt = 4 := by omega
  have hex : ch0R.ex 0 4 = oneEdge 528 := by
    change oneEdge (auxWidth 4) = oneEdge 528
    rw [auxWidth_four]
  rw [hslot, hex]

theorem repaired_prog_rebalanced_split :
    repairedNet.prog =
      (sideFirstInstr :: sideRestProg) ++ auxInstr ::
        ((earlyAuxProg ++ old528Instr :: lateAuxProg) ++ (auxRest1 ++ auxRest2)) := by
  rw [repaired_prog_split, auxPre_rebalanced_split]
  simp only [auxPost]
  rw [auxTail1_rebalanced_split]

theorem rebalanced_prog_aux4_split :
    rebalancedNet.prog =
      (rebalancedPre ++ fullAuxInstr :: earlyAuxProg) ++
        new506Instr :: (lateAuxProg ++ (auxRest1 ++ auxRest2)) := by
  change rebalancedPre ++ fullAuxInstr ::
      ((earlyAuxProg ++ new506Instr :: lateAuxProg) ++ (auxRest1 ++ auxRest2)) =
    (rebalancedPre ++ fullAuxInstr :: earlyAuxProg) ++
      new506Instr :: (lateAuxProg ++ (auxRest1 ++ auxRest2))
  simp only [List.append_assoc, List.cons_append]

/-! ## Histogram neutrality -/

theorem repaired_widths_rebalanced_shape :
    repairedNet.widths =
      [1] ++ progWidths sideRestProg ++ [506] ++
        ((progWidths earlyAuxProg ++ [528] ++ progWidths lateAuxProg) ++
          (progWidths auxRest1 ++ progWidths auxRest2)) := by
  change (progEdges repairedNet.prog).flatMap
    (fun e => e.runs.map fun ρ => ρ.2.2) = _
  have hw : (progEdges repairedNet.prog).flatMap (fun e => e.runs.map fun ρ => ρ.2.2) =
      progWidths repairedNet.prog := widths_eq_progWidths _
  rw [hw, repaired_prog_rebalanced_split]
  have haux : ch0R.ex 0 0 = oneEdge 506 := by
    change oneEdge (auxWidth 0) = oneEdge 506
    rfl
  have h1 : (oneEdge 1).runs.map (fun ρ => ρ.2.2) = [1] := by rfl
  have h506 : (oneEdge 506).runs.map (fun ρ => ρ.2.2) = [506] := by rfl
  have h528 : (oneEdge 528).runs.map (fun ρ => ρ.2.2) = [528] := by rfl
  simp only [progWidths_append_ni, progWidths_cons_ni, sideFirstInstr, auxInstr,
    old528Instr, haux, instrWidths, oneEdge, oneRun, List.map_cons, List.map_nil,
    List.append_nil, List.nil_append, List.append_assoc, h1, h506, h528]

theorem rebalanced_widths_shape :
    rebalancedNet.widths =
      [] ++ progWidths sideRestProg ++ [528, 1] ++
        ((progWidths earlyAuxProg ++ [506] ++ progWidths lateAuxProg) ++
          (progWidths auxRest1 ++ progWidths auxRest2)) := by
  change (progEdges rebalancedNet.prog).flatMap
    (fun e => e.runs.map fun ρ => ρ.2.2) = _
  have hw : (progEdges rebalancedNet.prog).flatMap (fun e => e.runs.map fun ρ => ρ.2.2) =
      progWidths rebalancedNet.prog := widths_eq_progWidths _
  rw [hw]
  change progWidths (rebalancedPre ++ fullAuxInstr :: rebalancedPost) = _
  have hpre : progWidths rebalancedPre = [] ++ progWidths sideRestProg := by
    unfold rebalancedPre
    rw [progWidths_cons_ni]
    have hs : instrWidths sideSkipInstr = [] := by rfl
    rw [hs]
  have hfull : instrWidths fullAuxInstr = [528, 1] := by rfl
  have htail : progWidths rebalancedTail1 =
      progWidths earlyAuxProg ++ [506] ++ progWidths lateAuxProg := by
    unfold rebalancedTail1
    rw [progWidths_append_ni, progWidths_cons_ni]
    have hn : instrWidths new506Instr = [506] := by rfl
    rw [hn]
    simp only [List.append_assoc]
  have hpost : progWidths rebalancedPost =
      (progWidths earlyAuxProg ++ [506] ++ progWidths lateAuxProg) ++
        (progWidths auxRest1 ++ progWidths auxRest2) := by
    unfold rebalancedPost
    calc
      progWidths (rebalancedTail1 ++ (auxRest1 ++ auxRest2)) =
          progWidths rebalancedTail1 ++ progWidths (auxRest1 ++ auxRest2) :=
        progWidths_append_ni _ _
      _ = (progWidths earlyAuxProg ++ [506] ++ progWidths lateAuxProg) ++
            progWidths (auxRest1 ++ auxRest2) := by rw [htail]
      _ = (progWidths earlyAuxProg ++ [506] ++ progWidths lateAuxProg) ++
            (progWidths auxRest1 ++ progWidths auxRest2) := by
        rw [progWidths_append_ni]
  calc
    progWidths (rebalancedPre ++ fullAuxInstr :: rebalancedPost) =
        progWidths rebalancedPre ++ progWidths (fullAuxInstr :: rebalancedPost) :=
      progWidths_append_ni _ _
    _ = ([] ++ progWidths sideRestProg) ++
          (instrWidths fullAuxInstr ++ progWidths rebalancedPost) := by
      rw [hpre, progWidths_cons_ni]
    _ = ([] ++ progWidths sideRestProg) ++
          ([528, 1] ++ ((progWidths earlyAuxProg ++ [506] ++ progWidths lateAuxProg) ++
            (progWidths auxRest1 ++ progWidths auxRest2))) := by
      rw [hfull, hpost]
    _ = _ := by exact (List.append_assoc _ _ _).symm

/-- The compensation is exact at every width, not merely in rank sum. -/
theorem rebalanced_width_count (w : ℕ) :
    rebalancedNet.widths.count w = repairedNet.widths.count w := by
  rw [rebalanced_widths_shape, repaired_widths_rebalanced_shape]
  simp only [List.count_append, List.count_nil, List.count_cons, Nat.zero_add]
  split_ifs <;> omega

theorem rebalanced_census : rebalanced.hist = repaired.hist := by
  change census (rebalancedNet.hist.map Prod.fst) = census (repairedNet.hist.map Prod.fst)
  have hnew : rebalancedNet.hist.map Prod.fst = rebalancedNet.widths := by
    simp only [QHNet.hist, List.map_map, Function.comp_def, List.map_id']
  have hold : repairedNet.hist.map Prod.fst = repairedNet.widths := by
    simp only [QHNet.hist, List.map_map, Function.comp_def, List.map_id']
  rw [hnew, hold]
  change censusWith (fun w => rebalancedNet.widths.count w) =
    censusWith (fun w => repairedNet.widths.count w)
  have hf : (fun w => rebalancedNet.widths.count w) =
      (fun w => repairedNet.widths.count w) := by
    funext w
    exact rebalanced_width_count w
  rw [hf]

theorem rebalanced_hist_eq_bitR8 : rebalanced.hist = IntMul.Kappa.Jain.bitR8 :=
  rebalanced_census.trans repaired_hist_eq_bitR8

theorem rebalancedNet_width_lt {w : ℕ} (hw : w ∈ rebalancedNet.widths) : w < 529 := by
  by_contra h
  have hz : repairedNet.widths.count w = 0 := List.count_eq_zero.2 (by
    intro hm
    exact h (repairedNet_width_lt hm))
  have hn : rebalancedNet.widths.count w = 0 := by
    rw [rebalanced_width_count, hz]
  exact (List.count_eq_zero.1 hn) hw

/-- The raw QHNet moment is again exactly the `bitR8` moment. -/
theorem rebalancedNet_mom_eq (τ : ℝ) :
    histMoment rebalancedNet.hist 529 τ = histMoment IntMul.Kappa.Jain.bitR8 529 τ := by
  calc
    histMoment rebalancedNet.hist 529 τ =
        histMoment (census (rebalancedNet.hist.map Prod.fst)) 529 τ :=
      histMoment_raw_eq_census rebalancedNet (fun w hw => rebalancedNet_width_lt hw) τ
    _ = histMoment rebalanced.hist 529 τ := rfl
    _ = histMoment IntMul.Kappa.Jain.bitR8 529 τ := by rw [rebalanced_hist_eq_bitR8]

/-! ## Run and edge certificates -/

theorem repaired_edges_rebalanced_shape :
    repairedNet.edges =
      (oneEdge 1 :: progEdges sideRestProg) ++ oneEdge 506 ::
        ((progEdges earlyAuxProg ++ oneEdge 528 :: progEdges lateAuxProg) ++
          (progEdges auxRest1 ++ progEdges auxRest2)) := by
  change progEdges repairedNet.prog = _
  rw [repaired_prog_rebalanced_split]
  have haux : ch0R.ex 0 0 = oneEdge 506 := by
    change oneEdge (auxWidth 0) = oneEdge 506
    rfl
  simp only [sideFirstInstr, auxInstr, old528Instr, haux]
  have hlist :
      progEdges
        (Instr.edge (NB.ι1 0 0) (oneEdge 1) :: sideRestProg ++
          Instr.edge (NB.ι1 0 wEnt) (oneEdge 506) ::
            (earlyAuxProg ++ Instr.edge (NB.ι1 0 (wEnt + 4)) (oneEdge 528) ::
              lateAuxProg ++ (auxRest1 ++ auxRest2))) =
        oneEdge 1 :: progEdges sideRestProg ++ oneEdge 506 ::
          (progEdges earlyAuxProg ++ oneEdge 528 ::
            progEdges lateAuxProg ++ (progEdges auxRest1 ++ progEdges auxRest2)) := by
    simp only [progEdges_append_ni, progEdges_edge_cons, List.append_assoc]
  exact hlist

theorem rebalancedNet_edges :
    rebalancedNet.edges =
      (emptyEdge :: progEdges sideRestProg) ++ fullSwapEdge ::
        ((progEdges earlyAuxProg ++ oneEdge 506 :: progEdges lateAuxProg) ++
          (progEdges auxRest1 ++ progEdges auxRest2)) := by
  change (rebalancedPre ++ fullAuxInstr :: rebalancedPost).filterMap Instr.edgeOf = _
  simp only [rebalancedPre, rebalancedPost, rebalancedTail1, List.filterMap_append,
    List.filterMap_cons, List.filterMap_nil, progEdges, sideSkipInstr, fullAuxInstr,
    new506Instr, Instr.edgeOf]

theorem old_edge_of_sideRest {e : Edge 529} (he : e ∈ progEdges sideRestProg) :
    e ∈ repairedNet.edges := by
  rw [repaired_edges_rebalanced_shape]
  exact List.mem_append.2 (Or.inl (List.mem_cons.2 (Or.inr he)))

theorem old_edge_of_early {e : Edge 529} (he : e ∈ progEdges earlyAuxProg) :
    e ∈ repairedNet.edges := by
  rw [repaired_edges_rebalanced_shape]
  exact List.mem_append.2 (Or.inr (List.mem_cons.2 (Or.inr
    (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl he)))))))

theorem old_edge_of_late {e : Edge 529} (he : e ∈ progEdges lateAuxProg) :
    e ∈ repairedNet.edges := by
  rw [repaired_edges_rebalanced_shape]
  exact List.mem_append.2 (Or.inr (List.mem_cons.2 (Or.inr
    (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr
      (List.mem_cons.2 (Or.inr he)))))))))

theorem old_edge_of_rest {e : Edge 529}
    (he : e ∈ progEdges auxRest1 ++ progEdges auxRest2) : e ∈ repairedNet.edges := by
  rw [repaired_edges_rebalanced_shape]
  exact List.mem_append.2 (Or.inr (List.mem_cons.2 (Or.inr
    (List.mem_append.2 (Or.inr he)))))

/-- Every redesigned edge is either one of the three local replacements or an
old repaired edge. -/
theorem edge_of_rebalancedNet {e : Edge 529} (he : e ∈ rebalancedNet.edges) :
    e = emptyEdge ∨ e = fullSwapEdge ∨ e = oneEdge 506 ∨ e ∈ repairedNet.edges := by
  rw [rebalancedNet_edges] at he
  rcases List.mem_append.1 he with he | he
  · rcases List.mem_cons.1 he with rfl | he
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inr (old_edge_of_sideRest he)))
  · rcases List.mem_cons.1 he with rfl | he
    · exact Or.inr (Or.inl rfl)
    · rcases List.mem_append.1 he with he | he
      · rcases List.mem_append.1 he with he | he
        · exact Or.inr (Or.inr (Or.inr (old_edge_of_early he)))
        · rcases List.mem_cons.1 he with rfl | he
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr (old_edge_of_late he)))
      · exact Or.inr (Or.inr (Or.inr (old_edge_of_rest he)))

theorem emptyEdge_RunsOK : ∀ ρ ∈ emptyEdge.runs, RunOK 529 ρ := by
  intro ρ hρ
  simpa [emptyEdge] using hρ

theorem emptyEdge_EdgeOK (M : ℕ) : EdgeOK M emptyEdge := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij
    show (1 : QMat2 529) i j = 0
    exact Matrix.one_apply_ne (ne_of_lt hij)
  · intro i j hij
    show (1 : QMat2 529) i j = 0
    exact Matrix.one_apply_ne (ne_of_lt hij)
  · intro i
    show IsUnit (AModelFac.redQ M ((1 : QMat2 529) i i))
    rw [Matrix.one_apply_eq, redQ_one]
    exact isUnit_one
  · intro i
    show IsUnit (AModelFac.redQ M ((1 : QMat2 529) i i))
    rw [Matrix.one_apply_eq, redQ_one]
    exact isUnit_one

theorem rebalancedNet_RunsOK : rebalancedNet.RunsOK := by
  intro e he ρ hρ
  rcases edge_of_rebalancedNet he with rfl | rfl | rfl | heOld
  · exact emptyEdge_RunsOK ρ hρ
  · exact IntMul.Kappa.R8.Gap.uEdge_RunsOK ρ hρ
  · exact validOneEdge_runsOK ⟨506, by norm_num, by norm_num, rfl⟩ ρ hρ
  · exact repairedNet_RunsOK e heOld ρ hρ

theorem rebalancedNet_EdgesOK (M : ℕ) : rebalancedNet.EdgesOK M := by
  intro e he
  rcases edge_of_rebalancedNet he with rfl | rfl | rfl | heOld
  · exact emptyEdge_EdgeOK M
  · exact IntMul.Kappa.R8.Gap.uEdge_EdgeOK M
  · exact oneEdge_EdgeOK M 506
  · exact repairedNet_EdgesOK M e heOld

/-! ## The selected aux role remains a genuine full swap -/

theorem avoids_rebalancedPre : ∀ i ∈ rebalancedPre, Avoids auxWire i := by
  intro i hi
  rcases List.mem_cons.1 hi with rfl | hi
  · exact avoids_edge1 (by decide) (by norm_num [wEnt]) _
  · apply avoids_auxPre i
    rw [auxPre_rebalanced_split]
    exact List.mem_cons.2 (Or.inr hi)

theorem avoids_earlyAuxProg : ∀ i ∈ earlyAuxProg, Avoids auxWire i := by
  intro i hi
  apply avoids_auxTail1 i
  rw [auxTail1_rebalanced_split]
  exact List.mem_append.2 (Or.inl hi)

theorem avoids_lateAuxProg : ∀ i ∈ lateAuxProg, Avoids auxWire i := by
  intro i hi
  apply avoids_auxTail1 i
  rw [auxTail1_rebalanced_split]
  exact List.mem_append.2 (Or.inr (List.mem_cons.2 (Or.inr hi)))

theorem avoids_new506 : Avoids auxWire new506Instr := by
  have hm : old528Instr ∈ auxTail1 := by
    rw [auxTail1_rebalanced_split]
    exact List.mem_append.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))
  simpa [old528Instr, new506Instr, Avoids] using avoids_auxTail1 old528Instr hm

theorem avoids_rebalancedPost : ∀ i ∈ rebalancedPost, Avoids auxWire i := by
  intro i hi
  rcases List.mem_append.1 hi with hi | hi
  · rcases List.mem_append.1 hi with hi | hi
    · exact avoids_earlyAuxProg i hi
    · rcases List.mem_cons.1 hi with rfl | hi
      · exact avoids_new506
      · exact avoids_lateAuxProg i hi
  · apply avoids_auxPost i
    exact List.mem_append.2 (Or.inr hi)

theorem rebalancedNet_fold_aux (M : ℕ) :
    (rebalancedNet.prog.foldl (fStep M) (QHNet.fInit M)) auxWire =
      lmulF (edgeMat M fullSwapEdge)
        (Finsupp.single ((1 : FMat 529 M), auxRole) 1) := by
  change (List.foldl (fStep M) (QHNet.fInit M)
    (rebalancedPre ++ fullAuxInstr :: rebalancedPost)) auxWire = _
  rw [List.foldl_append, List.foldl_cons]
  rw [foldl_avoids M auxWire _ rebalancedPost avoids_rebalancedPost]
  have hw : NB.ι1 0 wEnt = auxWire := (iota1_eq_auxWire_iff (by decide)).2 ⟨rfl, rfl⟩
  simp only [fullAuxInstr, fStep, hw, Function.update_self]
  rw [foldl_avoids M auxWire _ rebalancedPre avoids_rebalancedPre]
  simp [QHNet.fInit, auxWire]

theorem rebalancedNet_auxRole_formal (M : ℕ) :
    (rebalancedNet.prog.foldl (fStep M) (QHNet.fInit M)) (.inl (rebalancedNet.ρ auxRole)) =
      Finsupp.single (AModel.swapMat, auxRole) 1 := by
  change (rebalancedNet.prog.foldl (fStep M) (QHNet.fInit M)) (.inl (NB.ρ auxRole)) = _
  rw [auxRole_merge]
  change (rebalancedNet.prog.foldl (fStep M) (QHNet.fInit M)) auxWire = _
  rw [rebalancedNet_fold_aux, lmulF_single, IntMul.Kappa.R8.Gap.edgeMat_uEdge,
    Matrix.mul_one]

/-! ## A second output role still fails formal correctness -/

/-- The stage-one slot-four output role.  Unlike `auxRole`, it is still wired to
an ordinary one-run edge after rebalancing. -/
def role4 : Fin W := ⟨2 * N + 4, by norm_num [N, W]⟩
def wire4 : Wr := .inl role4

theorem role4_merge : NB.ρ role4 = role4 := by
  apply Fin.ext
  simp [NB.ρ, ρn, role4, N]

theorem two_N_add_four_lt_W : 2 * N + 4 < W := by norm_num [N, W]

theorem gw_eq_wire4_iff {g : ℕ} (hg : g < W) : NB.gw g = wire4 ↔ g = 2 * N + 4 := by
  simp [NB.gw, wire4, role4, hg, Fin.ext_iff]

theorem gw_ne_wire4_of_ge_W {g : ℕ} (hg : W ≤ g) : NB.gw g ≠ wire4 := by
  simp [NB.gw, not_lt_of_ge hg, wire4]

theorem g1_eq_role4_iff {b w : ℕ} (hb : b < v) :
    g1 b w = 2 * N + 4 ↔ b = 0 ∧ w = wEnt + 4 := by
  have hv : v = 1771 := rfl
  have hN : N = 3136441 := rfl
  have hW : W = 104719230 := rfl
  have hNR : NR = 27794 := rfl
  have hEnt : wEnt = 3542 := rfl
  have hAux : wAuxEnd = 31336 := rfl
  unfold g1
  split_ifs <;> simp only [hv, hN, hW, hNR, hEnt, hAux] at * <;> omega

theorem g2_ne_role4 {a w : ℕ} (ha : a < v) : g2 a w ≠ 2 * N + 4 := by
  have hv : v = 1771 := rfl
  have hN : N = 3136441 := rfl
  have hW : W = 104719230 := rfl
  have hNR : NR = 27794 := rfl
  have hEnt : wEnt = 3542 := rfl
  have hAux : wAuxEnd = 31336 := rfl
  have hNL : NL = 31359 := rfl
  unfold g2
  split_ifs <;> simp only [hv, hN, hW, hNR, hEnt, hAux, hNL] at * <;> omega

theorem iota1_eq_wire4_iff {b w : ℕ} (hb : b < v) :
    NB.ι1 b w = wire4 ↔ b = 0 ∧ w = wEnt + 4 := by
  by_cases hg : g1 b w < W
  · rw [show NB.ι1 b w = NB.gw (g1 b w) from rfl, gw_eq_wire4_iff hg,
      g1_eq_role4_iff hb]
  · have hne := gw_ne_wire4_of_ge_W (g := g1 b w) (Nat.le_of_not_gt hg)
    constructor
    · intro h
      exact absurd h hne
    · intro h
      have he := (g1_eq_role4_iff hb).2 h
      rw [he] at hg
      exact absurd two_N_add_four_lt_W hg

theorem iota2_ne_wire4 {a w : ℕ} (ha : a < v) : NB.ι2 a w ≠ wire4 := by
  by_cases hg : g2 a w < W
  · intro h
    exact g2_ne_role4 ha ((gw_eq_wire4_iff hg).1 h)
  · exact gw_ne_wire4_of_ge_W (Nat.le_of_not_gt hg)

theorem avoids_edge1_wire4 {b w : ℕ} (hb : b < v)
    (h : ¬ (b = 0 ∧ w = wEnt + 4)) (e : Edge 529) :
    Avoids wire4 (.edge (NB.ι1 b w) e) := by
  change NB.ι1 b w ≠ wire4
  intro heq
  exact h ((iota1_eq_wire4_iff hb).1 heq)

theorem avoids_edge2_wire4 {a w : ℕ} (ha : a < v) (e : Edge 529) :
    Avoids wire4 (.edge (NB.ι2 a w) e) :=
  iota2_ne_wire4 ha

theorem avoids_xor2_wire4 {a : ℕ} (ha : a < v) (d s : ℕ) :
    Avoids wire4 (NB.xorG (NB.ι2 a d) (NB.ι2 a s)) := by
  change wire4 ∉ ({NB.ι2 a d, NB.ι2 a s} : Finset Wr)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨Ne.symm (iota2_ne_wire4 ha), Ne.symm (iota2_ne_wire4 ha)⟩

theorem avoids_blk1_wire4 {b : ℕ} (hb : b < v) (hb0 : b ≠ 0) :
    ∀ i ∈ blk1 ch0R b, Avoids wire4 i := by
  intro i hi
  rcases List.mem_append.1 hi with hi | hi
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hi
    exact avoids_edge1_wire4 hb (fun h => hb0 h.1) _
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hi
    exact avoids_edge1_wire4 hb (fun h => hb0 h.1) _

theorem avoids_blk2_wire4 {a : ℕ} (ha : a < v) : ∀ i ∈ blk2 ch0R a, Avoids wire4 i := by
  intro i hi
  rcases List.mem_append.1 hi with hi | hi
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hi
    exact avoids_edge2_wire4 ha _
  rcases List.mem_append.1 hi with hi | hi
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hi
    exact avoids_edge2_wire4 ha _
  obtain ⟨s, hs, hi⟩ := List.mem_flatMap.1 hi
  rcases List.mem_cons.1 hi with rfl | hi
  · exact avoids_xor2_wire4 ha _ _
  rcases List.mem_cons.1 hi with rfl | hi
  · exact avoids_edge2_wire4 ha _
  rcases List.mem_cons.1 hi with rfl | hi
  · exact avoids_xor2_wire4 ha _ _
  · exact absurd hi List.not_mem_nil

theorem avoids_rebalancedPre_wire4 : ∀ i ∈ rebalancedPre, Avoids wire4 i := by
  intro i hi
  rcases List.mem_cons.1 hi with rfl | hi
  · exact avoids_edge1_wire4 (by decide) (by norm_num [wEnt]) _
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hi
    exact avoids_edge1_wire4 (by decide) (by norm_num [wEnt]) _

theorem avoids_fullAux_wire4 : Avoids wire4 fullAuxInstr := by
  exact avoids_edge1_wire4 (by decide) (by norm_num [wEnt]) _

theorem avoids_earlyAuxProg_wire4 : ∀ i ∈ earlyAuxProg, Avoids wire4 i := by
  intro i hi
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hi
  obtain ⟨k, hk, hwk⟩ := List.mem_range'.1 hw
  apply avoids_edge1_wire4 (by decide)
  intro h
  have hwe := h.2
  omega

theorem avoids_lateAuxProg_wire4 : ∀ i ∈ lateAuxProg, Avoids wire4 i := by
  intro i hi
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hi
  obtain ⟨k, hk, hwk⟩ := List.mem_range'.1 hw
  apply avoids_edge1_wire4 (by decide)
  intro h
  have hwe := h.2
  omega

theorem avoids_role4Pre : ∀ i ∈ rebalancedPre ++ fullAuxInstr :: earlyAuxProg,
    Avoids wire4 i := by
  intro i hi
  rcases List.mem_append.1 hi with hi | hi
  · exact avoids_rebalancedPre_wire4 i hi
  · rcases List.mem_cons.1 hi with rfl | hi
    · exact avoids_fullAux_wire4
    · exact avoids_earlyAuxProg_wire4 i hi

theorem avoids_role4Post : ∀ i ∈ lateAuxProg ++ (auxRest1 ++ auxRest2), Avoids wire4 i := by
  intro i hi
  rcases List.mem_append.1 hi with hi | hi
  · exact avoids_lateAuxProg_wire4 i hi
  · rcases List.mem_append.1 hi with hi | hi
    · obtain ⟨b, hb, hi⟩ := List.mem_flatMap.1 hi
      obtain ⟨k, hk, hbk⟩ := List.mem_range'.1 hb
      have hv : 0 < v := by decide
      exact avoids_blk1_wire4 (by omega) (by omega) i hi
    · obtain ⟨a, ha, hi⟩ := List.mem_flatMap.1 hi
      exact avoids_blk2_wire4 (List.mem_range.1 ha) i hi

/-- Slot four is touched only by `new506Instr`, so its final frame is that
edge's matrix, not the full swap. -/
theorem rebalancedNet_fold_role4 (M : ℕ) :
    (rebalancedNet.prog.foldl (fStep M) (QHNet.fInit M)) wire4 =
      lmulF (edgeMat M (oneEdge 506)) (Finsupp.single ((1 : FMat 529 M), role4) 1) := by
  rw [rebalanced_prog_aux4_split]
  change (List.foldl (fStep M) (QHNet.fInit M)
    ((rebalancedPre ++ fullAuxInstr :: earlyAuxProg) ++
      new506Instr :: (lateAuxProg ++ (auxRest1 ++ auxRest2)))) wire4 = _
  rw [List.foldl_append, List.foldl_cons]
  rw [foldl_avoids M wire4 _ (lateAuxProg ++ (auxRest1 ++ auxRest2)) avoids_role4Post]
  have hw : NB.ι1 0 (wEnt + 4) = wire4 := (iota1_eq_wire4_iff (by decide)).2 ⟨rfl, rfl⟩
  simp only [new506Instr, fStep, hw, Function.update_self]
  rw [foldl_avoids M wire4 _ (rebalancedPre ++ fullAuxInstr :: earlyAuxProg) avoids_role4Pre]
  simp [QHNet.fInit, wire4]

theorem edgeMat_role4_of_formalOK {M : ℕ} (h : rebalancedNet.FormalOK M) :
    edgeMat M (oneEdge 506) = AModel.swapMat := by
  have hh := h role4
  change (rebalancedNet.prog.foldl (fStep M) (QHNet.fInit M)) (.inl (NB.ρ role4)) = _ at hh
  rw [role4_merge] at hh
  change (rebalancedNet.prog.foldl (fStep M) (QHNet.fInit M)) wire4 = _ at hh
  rw [rebalancedNet_fold_role4, lmulF_single, Matrix.mul_one] at hh
  have hp := (Finsupp.single_left_injective (b := (1 : ZMod 2)) (by decide)) hh
  exact congrArg Prod.fst hp

/-- The rebalanced program is still not formally correct at any prime modulus:
slot four has width `506 < 529`, and its one-run permutation fixes the top
coordinate `506`, whereas the full swap has a zero diagonal there. -/
theorem rebalancedNet_not_FormalOK_prime {q : ℕ} (hq : q.Prime) :
    ¬ rebalancedNet.FormalOK q := by
  intro h
  have he := edgeMat_role4_of_formalOK h
  exact oneEdge_ne_swapMat q 506 hq.one_lt (by norm_num) he

/-- The exact all-role certificate needed by the generalized assembler. -/
def RebalancedFormalOKLarge : Prop :=
  ∃ q₀ : ℕ, ∀ q, q.Prime → q₀ < q → ∀ f : ℕ, rebalancedNet.FormalOK (q ^ f)

theorem not_RebalancedFormalOKLarge : ¬ RebalancedFormalOKLarge := by
  intro h
  obtain ⟨q₀, hq₀⟩ := h
  obtain ⟨q, hqge, hq⟩ := Nat.exists_infinite_primes (q₀ + 1)
  have hqgt : q₀ < q := by omega
  have hf := hq₀ q hq hqgt 1
  exact rebalancedNet_not_FormalOK_prime hq (by simpa using hf)

end IntMul.Kappa.R8.Bit.Oppbank.Rebalanced
