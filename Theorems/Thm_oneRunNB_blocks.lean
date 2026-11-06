import Theorems.Thm_oneRunNB_scalar
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 200000

/-!
# Block-level scalar semantics for the genuine R8 program
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.OneRunNB

open IntMul.Kappa IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank IntMul.Kappa.R8.Bit.Oppbank.NB
open IntMul.Kappa.R8.Bit.Oppbank.Repaired

/-- Stage one, conditional on the generated gate-list certificate. -/
theorem blk1_sc_of_gates
    {ch : Repaired.Ch} {N : ℕ} [Module (ZMod 2) (FVN N)]
    (hcs1 : ∀ ch ∈ NB.cs1, ∀ p ∈ ch.2.2, p.1 < NL ∧ p.2 < NL ∧ p.1 ≠ p.2)
    {b : ℕ} (hb : b < v) (v : Repaired.Wr → FVN N) (u : ℕ → FVN N)
    (hv : ∀ w, w < NL → v (NB.ι1 b w) = u w) :
    (∀ w, w < NL → (blk1 ch b).foldl scalarStepM v (NB.ι1 b w) =
      xrL gateList1 u w) ∧
    ∀ x, (∀ w, w < NL → NB.ι1 b w ≠ x) → (blk1 ch b).foldl scalarStepM v x = v x := by
  have hshape : blk1 ch b =
      NB.chunkProg (NB.ι1 b) (ch.e1 b) NB.cs1 ++
        ((List.range' wEnt NR).map fun w =>
          Instr.edge (NB.ι1 b w) (ch.ex b (w - wEnt))) := rfl
  have hedges : ∀ v0 : Repaired.Wr → FVN N,
      ((List.range' wEnt NR).map fun w =>
        (Instr.edge (NB.ι1 b w) (ch.ex b (w - wEnt)) :
          Instr Repaired.Wr (ZMod 2) 529)).foldl scalarStepM v0 = v0 := by
    intro v0
    have generic : ∀ l : List ℕ,
        ((l.map fun w => (Instr.edge (NB.ι1 b w) (ch.ex b (w - wEnt)) :
          Instr Repaired.Wr (ZMod 2) 529)).foldl scalarStepM v0) = v0 := by
      intro l
      induction l with
      | nil => rfl
      | cons w ws ih => simpa [scalarStepM] using ih
    exact generic _
  obtain ⟨c1, c2⟩ := chunkProg_scalar (ι := NB.ι1 b) (D := (· < NL))
    (E := ch.e1 b) (fun w w' hw hw' e => (ι1_inj hb hb hw hw' e).2)
    NB.cs1 hcs1 v u hv
  rw [hshape, List.foldl_append, hedges]
  exact ⟨c1, c2⟩

/-- A single edge instruction is a scalar no-op at any state. -/
theorem edge_step_id {N : ℕ} [Module (ZMod 2) (FVN N)] (w : Repaired.Wr) (e : Edge 529)
    (v0 : Repaired.Wr → FVN N) :
    scalarStepM v0 ((Instr.edge w e : Instr Repaired.Wr (ZMod 2) 529)) = v0 := rfl

/-- Entrance edges of stage two are scalar no-ops at any state. -/
theorem entI_scalar {ch : Repaired.Ch} {N : ℕ} [Module (ZMod 2) (FVN N)] (a : ℕ) :
    ∀ (v0 : Repaired.Wr → FVN N), (Repaired.entI ch a).foldl scalarStepM v0 = v0 := by
  intro v0
  have generic : ∀ l : List ℕ,
      ((l.map fun w => (Instr.edge (NB.ι2 a w) (Repaired.entE ch a w) :
        Instr Repaired.Wr (ZMod 2) 529)).foldl scalarStepM v0) = v0 := by
    intro l
    induction l with
    | nil => rfl
    | cons w ws ih =>
      rw [List.map_cons, List.foldl_cons, edge_step_id]
      exact ih
  exact generic _

/-- Correction gate index pairs of one segment. -/
def corrIdx (s : ℕ) : List (ℕ × ℕ) := [(wU s, wY s), (wX s, wU s)]

/-- All correction gate index pairs of stage two. -/
def corrIdxAll : List (ℕ × ℕ) := (List.range v).flatMap corrIdx

/-- The correction gates of stage two as a gate-only instruction list. -/
def corrGateList (a : ℕ) : List (Instr Repaired.Wr (ZMod 2) 529) :=
  corrIdxAll.map fun p => NB.xorG (NB.ι2 a p.1) (NB.ι2 a p.2)

theorem corrIdx_bounded : ∀ p ∈ corrIdxAll, p.1 < NL + v ∧ p.2 < NL + v ∧ p.1 ≠ p.2 := by
  intro p hp
  simp only [corrIdxAll, corrIdx, List.mem_flatMap, List.mem_cons] at hp
  obtain ⟨s, hs, hp⟩ := hp
  have hs' : s < v := by simpa using hs
  rcases hp with rfl | rfl | h
  · simp only [wU, wY, NL, v] at hs' ⊢; omega
  · simp only [wU, wX, NL, v] at hs' ⊢; omega
  · cases h

/-- One correction segment: the interleaved edge is a scalar no-op. -/
theorem corrI_foldl_scalar (ch : Repaired.Ch) (a s : ℕ) {N : ℕ} [Module (ZMod 2) (FVN N)]
    (v0 : Repaired.Wr → FVN N) :
    (Repaired.corrI ch a s).foldl scalarStepM v0 =
      ((corrIdx s).map fun p => NB.xorG (NB.ι2 a p.1) (NB.ι2 a p.2)).foldl scalarStepM v0 := by
  simp only [Repaired.corrI, corrIdx, List.map_cons, List.map_nil, List.foldl_cons,
    List.foldl_nil, edge_step_id]

/-- The correction block's fold agrees with the gate-only fold, at any state. -/
theorem corr_flatMap_fusion (ch : Repaired.Ch) (a : ℕ) {N : ℕ} [Module (ZMod 2) (FVN N)] :
    ∀ (l : List ℕ) (v0 : Repaired.Wr → FVN N),
      (l.flatMap (Repaired.corrI ch a)).foldl scalarStepM v0 =
      (l.flatMap fun s => (corrIdx s).map fun p => NB.xorG (NB.ι2 a p.1) (NB.ι2 a p.2)).foldl
        scalarStepM v0
  | [], _ => rfl
  | s :: ls, v0 => by
    simp only [List.flatMap_cons, List.foldl_append]
    rw [corrI_foldl_scalar, corr_flatMap_fusion ch a ls _]

theorem corr_fuse (a : ℕ) :
    (List.range v).flatMap (fun s => (corrIdx s).map
        fun p => NB.xorG (NB.ι2 a p.1) (NB.ι2 a p.2))
      = corrGateList a := by
  have gen : ∀ l : List ℕ,
      (l.flatMap fun s => (corrIdx s).map fun p => NB.xorG (NB.ι2 a p.1) (NB.ι2 a p.2))
        = (l.flatMap corrIdx).map fun p => NB.xorG (NB.ι2 a p.1) (NB.ι2 a p.2) := by
    intro l
    induction l with
    | nil => rfl
    | cons s ls ih => rw [List.flatMap_cons, List.flatMap_cons, List.map_append, ih]
  rw [gen, corrGateList, corrIdxAll]

/-- Stage two, conditional on the generated gate-list certificate. -/
theorem blk2_sc_of_gates
    {ch : Repaired.Ch} {N : ℕ} [Module (ZMod 2) (FVN N)]
    (hcs2 : ∀ c ∈ NB.cs2, ∀ p ∈ c.2.2, p.1 < NL + v ∧ p.2 < NL + v ∧ p.1 ≠ p.2)
    {a : ℕ} (ha : a < v) (val : Repaired.Wr → FVN N) (u : ℕ → FVN N)
    (hv : ∀ w, w < NL + v → val (NB.ι2 a w) = u w) :
    (∀ w, w < NL + v → (blk2 ch a).foldl scalarStepM val (NB.ι2 a w) =
      xrL (gateList2 ++ corrIdxAll) u w) ∧
    ∀ x, (∀ w, w < NL + v → NB.ι2 a w ≠ x) → (blk2 ch a).foldl scalarStepM val x = val x := by
  have hshape : blk2 ch a =
      Repaired.entI ch a ++ (NB.chunkProg (NB.ι2 a) (ch.e2 a) NB.cs2 ++
        (List.range v).flatMap (Repaired.corrI ch a)) := rfl
  have hinj : ∀ w w', w < NL + v → w' < NL + v → NB.ι2 a w = NB.ι2 a w' → w = w' :=
    fun w w' hw hw' e => (ι2_inj ha ha hw hw' e).2
  obtain ⟨c1, c2⟩ := chunkProg_scalar (ι := NB.ι2 a) (D := (· < NL + v))
    (E := ch.e2 a) hinj NB.cs2 hcs2 val u hv
  have hcorrFold : ∀ v0 : Repaired.Wr → FVN N,
      ((List.range v).flatMap (Repaired.corrI ch a)).foldl scalarStepM v0
        = (corrGateList a).foldl scalarStepM v0 := fun v0 => by
    rw [corr_flatMap_fusion ch a (List.range v) v0, corr_fuse a]
  obtain ⟨d1, d2⟩ := xorGs_scalar (ι := NB.ι2 a) (D := (· < NL + v))
    hinj corrIdxAll corrIdx_bounded
    ((NB.chunkProg (NB.ι2 a) (ch.e2 a) NB.cs2).foldl scalarStepM val)
    (xrL gateList2 u) c1
  rw [hshape, List.foldl_append, entI_scalar a, List.foldl_append, hcorrFold]
  refine ⟨fun w hw => ?_, fun x hx => ?_⟩
  · rw [xrL_append]; exact d1 w hw
  · exact (d2 x hx).trans (c2 x hx)

end IntMul.Kappa.R8.Bit.Oppbank.OneRunNB
