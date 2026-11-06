import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankAuxF
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankHist
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMomPack
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

namespace IntMul.Kappa.R8.Bit.Oppbank.Repaired

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank

/-- One contiguous reversed-bank run of width w. -/
def oneRun (w : ℕ) : ℕ × ℕ × ℕ := (0, 529 - w, w)

/-- An edge carrying exactly one reversed-bank run. -/
def oneEdge (w : ℕ) : Edge 529 := ⟨1, [oneRun w], 1⟩

/-- Slot-dependent aux width: 529 - auxCorner s = 506 + auxF s on the schedule. -/
def auxWidth (s : ℕ) : ℕ := 529 - auxCorner s

/-- Repaired channel record; ex and ei carry the aux slot explicitly. -/
structure Ch where
  S : Matrix (Fin 529) Pnd.Pr23 ℚ
  Si : Matrix Pnd.Pr23 (Fin 529) ℚ
  e1 : ℕ → ℕ → ℕ → Edge 529
  e2 : ℕ → ℕ → ℕ → Edge 529
  ex : ℕ → ℕ → Edge 529
  en : ℕ → ℕ → Edge 529
  ei : ℕ → ℕ → Edge 529
  ec : ℕ → ℕ → Edge 529

/-- One-run repaired channels.  The third side argument is the residual rank. -/
noncomputable def ch0R : Ch where
  S := Pnd.S0
  Si := Pnd.Si0
  e1 _ _ r := oneEdge r
  e2 _ _ r := oneEdge r
  ex _ s := oneEdge (auxWidth s)
  en _ _ := oneEdge 484
  ei _ s := oneEdge (auxWidth s)
  ec _ _ := oneEdge 1

abbrev Wr := NB.Wr
abbrev NI := NB.NI

/-- The chunk-A per-block side census, excluding the separate width-1 copy correction. -/
def sideHistPerBlock : List (ℕ × ℕ) :=
  [(1, 123546), (2, 146768), (3, 21868), (4, 27862), (5, 13896), (6, 4556),
   (7, 2156), (8, 2702), (9, 1690), (10, 684), (11, 816), (12, 752),
   (13, 610), (14, 378), (15, 1556), (16, 2180), (17, 1092), (18, 206),
   (19, 7560), (20, 332), (21, 1000), (22, 66)]

/-- Expand only the 22 aggregated side pairs, never the 1771-block network. -/
def expandHist (h : List (ℕ × ℕ)) : List ℕ :=
  h.flatMap fun p => List.replicate p.2 p.1

def sideSchedule : List ℕ := expandHist sideHistPerBlock
def sideSchedule1 : List ℕ := sideSchedule.take (sideSchedule.length / 2)
def sideSchedule2 : List ℕ := sideSchedule.drop (sideSchedule.length / 2)

/-- Emit a side family from its aggregated residual-rank schedule. -/
def sideProg (ι : ℕ → Wr) (E : ℕ → ℕ → Edge 529) (rs : List ℕ) : List NI :=
  rs.map fun r => Instr.edge (ι 0) (E 0 r)

def entE (ch : Ch) (a w : ℕ) : Edge 529 :=
  if w < v then ch.en a w
  else if w < wEnt then ch.en a (w - v)
  else ch.ei a (w - wEnt)

def blk1 (ch : Ch) (b : ℕ) : List NI :=
  sideProg (NB.ι1 b) (ch.e1 b) sideSchedule1 ++
    (List.range' wEnt NR).map fun w =>
      Instr.edge (NB.ι1 b w) (ch.ex b (w - wEnt))

def entI (ch : Ch) (a : ℕ) : List NI :=
  (List.range wAuxEnd).map fun w => Instr.edge (NB.ι2 a w) (entE ch a w)

def corrI (ch : Ch) (a s : ℕ) : List NI :=
  [NB.xorG (NB.ι2 a (wU s)) (NB.ι2 a (wY s)),
    Instr.edge (NB.ι2 a (wU s)) (ch.ec a s),
    NB.xorG (NB.ι2 a (wX s)) (NB.ι2 a (wU s))]

def blk2 (ch : Ch) (a : ℕ) : List NI :=
  entI ch a ++
    (sideProg (NB.ι2 a) (ch.e2 a) sideSchedule2 ++ (List.range v).flatMap (corrI ch a))

def prog (ch : Ch) : List NI :=
  (List.range v).flatMap (blk1 ch) ++ (List.range v).flatMap (blk2 ch)

/-- Repaired reconstruction on W=104719230, T=3217907, m=529. -/
noncomputable def net (ch : Ch) : QHNet (ZMod 2) 104719230 3217907 529 :=
  ⟨prog ch, NB.ρ⟩

noncomputable def repairedNet : QHNet (ZMod 2) 104719230 3217907 529 := net ch0R

structure Reconstruction where
  net : QHNet (ZMod 2) 104719230 3217907 529

noncomputable def repaired : Reconstruction := ⟨repairedNet⟩

/-- Widths contributed by one instruction. -/
def instrWidths {R : Type*} : Instr Wr R 529 → List ℕ
  | .gate _ _ => []
  | .edge _ e => e.runs.map fun ρ => ρ.2.2

def progWidths {R : Type*} (p : List (Instr Wr R 529)) : List ℕ :=
  p.flatMap instrWidths

theorem widths_eq_progWidths {R : Type*} [CommRing R]
    (p : List (Instr Wr R 529)) :
    (progEdges p).flatMap (fun e => e.runs.map fun ρ => ρ.2.2) = progWidths p := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    cases i with
    | gate g S => exact ih
    | edge w e =>
      change e.runs.map (fun ρ => ρ.2.2) ++ (progEdges p).flatMap (fun e => e.runs.map fun ρ => ρ.2.2) =
        e.runs.map (fun ρ => ρ.2.2) ++ progWidths p
      rw [ih]

theorem flatMap_map' {α β γ : Type*} (l : List α) (f : α → β) (g : β → List γ) :
    (l.map f).flatMap g = l.flatMap (fun x => g (f x)) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.flatMap_cons, ih]

theorem flatMap_singleton_id {α : Type*} (l : List α) :
    l.flatMap (fun x => [x]) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, ih]; rfl

theorem flatMap_singleton_map {α β : Type*} (l : List α) (f : α → β) :
    l.flatMap (fun x => [f x]) = l.map f := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, List.map_cons, ih]; rfl

theorem flatMap_congr' {α β : Type*} (l : List α) (f g : α → List β)
    (h : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, h x (by simp),
      ih (fun y hy => h y (List.mem_cons.2 (Or.inr hy)))]

theorem progWidths_map_eq {α : Type*} {R : Type*} (xs : List α)
    (f : α → Instr Wr R 529) (g : α → List ℕ)
    (h : ∀ x ∈ xs, instrWidths (f x) = g x) :
    progWidths (xs.map f) = xs.flatMap g := by
  unfold progWidths
  rw [flatMap_map']
  exact flatMap_congr' xs _ g h

theorem progWidths_append {R : Type*} (p q : List (Instr Wr R 529)) :
    progWidths (p ++ q) = progWidths p ++ progWidths q :=
  List.flatMap_append

theorem progWidths_flatMap {α : Type*} {R : Type*} (xs : List α)
    (f : α → List (Instr Wr R 529)) :
    progWidths (xs.flatMap f) = xs.flatMap (fun x => progWidths (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [progWidths_append, ih]

/-- Width templates for one b-block and one a-block. -/
def auxStartWidths : List ℕ :=
  (List.range' wEnt NR).map fun w => auxWidth (w - wEnt)

def entranceWidth (w : ℕ) : ℕ :=
  if w < v then 484 else if w < wEnt then 484 else auxWidth (w - wEnt)

def entranceWidths : List ℕ := (List.range wAuxEnd).map entranceWidth
def correctionWidths : List ℕ := (List.range v).map fun _ => 1
def stage1Widths : List ℕ := sideSchedule1 ++ auxStartWidths
def stage2Widths : List ℕ := entranceWidths ++ (sideSchedule2 ++ correctionWidths)
def templateWidths : List ℕ := stage1Widths ++ stage2Widths

theorem progWidths_side1 (b : ℕ) :
    progWidths (sideProg (NB.ι1 b) (ch0R.e1 b) sideSchedule1) = sideSchedule1 := by
  unfold sideProg
  have he := progWidths_map_eq (R := ZMod 2) sideSchedule1
    (fun r => Instr.edge (NB.ι1 b 0) (ch0R.e1 b 0 r)) (fun r => [r])
    (by intro r hr; rfl)
  rw [he]
  exact flatMap_singleton_id _

theorem progWidths_side2 (a : ℕ) :
    progWidths (sideProg (NB.ι2 a) (ch0R.e2 a) sideSchedule2) = sideSchedule2 := by
  unfold sideProg
  have he := progWidths_map_eq (R := ZMod 2) sideSchedule2
    (fun r => Instr.edge (NB.ι2 a 0) (ch0R.e2 a 0 r)) (fun r => [r])
    (by intro r hr; rfl)
  rw [he]
  exact flatMap_singleton_id _

theorem progWidths_entI (a : ℕ) :
    progWidths (entI ch0R a) = entranceWidths := by
  unfold entI entranceWidths
  have he := progWidths_map_eq (R := ZMod 2) (List.range wAuxEnd)
    (fun w => Instr.edge (NB.ι2 a w) (entE ch0R a w))
    (fun w => [entranceWidth w]) (by
      intro w hw
      simp only [instrWidths, entE, entranceWidth]
      split_ifs <;> rfl)
  rw [he]
  simp [flatMap_singleton_map]

theorem progWidths_blk1 (b : ℕ) :
    progWidths (blk1 ch0R b) = stage1Widths := by
  rw [blk1, progWidths_append, progWidths_side1]
  have he := progWidths_map_eq (R := ZMod 2) (List.range' wEnt NR)
    (fun w => Instr.edge (NB.ι1 b w) (ch0R.ex b (w - wEnt)))
    (fun w => [auxWidth (w - wEnt)]) (by intro w hw; rfl)
  rw [he]
  simp [stage1Widths, auxStartWidths, flatMap_singleton_map]

theorem progWidths_blk2 (a : ℕ) :
    progWidths (blk2 ch0R a) = stage2Widths := by
  rw [blk2, progWidths_append, progWidths_entI, progWidths_append, progWidths_side2]
  unfold corrI stage2Widths correctionWidths
  rw [progWidths_flatMap]
  have he : ∀ s ∈ List.range v,
      progWidths ([NB.xorG (NB.ι2 a (wU s)) (NB.ι2 a (wY s)),
        Instr.edge (NB.ι2 a (wU s)) (ch0R.ec a s),
        NB.xorG (NB.ι2 a (wX s)) (NB.ι2 a (wU s))]) = [1] := by
    intro s hs
    rfl
  rw [flatMap_congr' _ _ _ he]
  simp [flatMap_singleton_map]

theorem repairedNet_widths :
    repairedNet.widths =
      (List.range v).flatMap (fun _ => stage1Widths) ++
        (List.range v).flatMap (fun _ => stage2Widths) := by
  change (progEdges (prog ch0R)).flatMap
    (fun e => e.runs.map fun ρ => ρ.2.2) = _
  rw [widths_eq_progWidths, prog, progWidths_append, progWidths_flatMap,
    progWidths_flatMap]
  simp only [progWidths_blk1, progWidths_blk2]

theorem count_flatMap_range_const (w v : ℕ) (xs : List ℕ) :
    List.count w ((List.range v).flatMap (fun _ => xs)) = v * xs.count w := by
  rw [List.count_flatMap]
  simp [Function.comp_def]

theorem repaired_width_count (w : ℕ) :
    repairedNet.widths.count w = v * templateWidths.count w := by
  rw [repairedNet_widths, List.count_append, count_flatMap_range_const,
    count_flatMap_range_const, templateWidths, List.count_append, Nat.mul_add]

/-- Side and non-side families used for the finite census. -/
def sideWidths : List ℕ := sideSchedule
def otherWidths : List ℕ := auxStartWidths ++ (entranceWidths ++ correctionWidths)

def countAt (w : ℕ) (h : List (ℕ × ℕ)) : ℕ :=
  ((h.filter fun p => p.1 = w).map Prod.snd).sum

def sideTargetCount (w : ℕ) : ℕ :=
  if w < 23 then countAt w sideHistPerBlock else 0

/-- Non-side per-block counts: copy at 1, data at 484, and the two aux channels. -/
def otherTargetCount (w : ℕ) : ℕ :=
  if w < 529 then
    if w = 1 then v
    else if w = 484 then 2 * v
    else if 506 ≤ w then
      2 * ((List.range NR).filter fun s => auxWidth s = w).length
    else 0
  else 0

theorem sideSpecs :
    (∀ x ∈ sideWidths, x < 23) ∧
      (∀ w : Fin 23, sideWidths.count w.val = sideTargetCount w.val) := by
  native_decide

theorem otherSpecs :
    (∀ x ∈ otherWidths, x < 529) ∧
      (∀ w : Fin 529, otherWidths.count w.val = otherTargetCount w.val) := by
  native_decide

theorem sideWidths_bound : ∀ x ∈ sideWidths, x < 23 := sideSpecs.1
theorem otherWidths_bound : ∀ x ∈ otherWidths, x < 529 := otherSpecs.1

theorem side_count (w : ℕ) : sideWidths.count w = sideTargetCount w := by
  by_cases h : w < 23
  · exact sideSpecs.2 ⟨w, h⟩
  · have hz : sideWidths.count w = 0 := List.count_eq_zero.2 (by
      intro hm
      exact h (sideWidths_bound w hm))
    rw [hz]
    simp [sideTargetCount, h]

theorem other_count (w : ℕ) : otherWidths.count w = otherTargetCount w := by
  by_cases h : w < 529
  · exact otherSpecs.2 ⟨w, h⟩
  · have hz : otherWidths.count w = 0 := List.count_eq_zero.2 (by
      intro hm
      exact h (otherWidths_bound w hm))
    rw [hz]
    simp [otherTargetCount, h]

theorem sideSchedule_split : sideSchedule1 ++ sideSchedule2 = sideSchedule := by
  simp [sideSchedule1, sideSchedule2]

theorem template_count (w : ℕ) :
    templateWidths.count w = sideWidths.count w + otherWidths.count w := by
  have hs := congrArg (List.count w) sideSchedule_split
  simp only [List.count_append] at hs
  simp only [templateWidths, stage1Widths, stage2Widths, sideWidths, otherWidths,
    List.count_append]
  omega

theorem repaired_width_count_explicit (w : ℕ) :
    repairedNet.widths.count w = v * (sideTargetCount w + otherTargetCount w) := by
  rw [repaired_width_count, template_count, side_count, other_count]

/-- Census of a width list, with zero entries omitted. -/
def censusWith (f : ℕ → ℕ) : List (ℕ × ℕ) :=
  (List.range 529).filterMap fun w =>
    if f w = 0 then none else some (w, f w)

def census (xs : List ℕ) : List (ℕ × ℕ) := censusWith (fun w => xs.count w)

namespace Reconstruction

/-- Aggregated histogram of the raw per-child QHNet histogram. -/
noncomputable def hist (r : Reconstruction) : List (ℕ × ℕ) :=
  census (r.net.hist.map Prod.fst)

end Reconstruction

/-- Finite aggregated computation: no 1771-fold or 749446467-child expansion. -/
def computedRepairedHist : List (ℕ × ℕ) :=
  censusWith (fun w => v * (sideTargetCount w + otherTargetCount w))

theorem repaired_census : repaired.hist = computedRepairedHist := by
  change census (repairedNet.hist.map Prod.fst) = computedRepairedHist
  have hfst : repairedNet.hist.map Prod.fst = repairedNet.widths := by
    simp [QHNet.hist, List.map_map, Function.comp_def]
  rw [hfst]
  unfold census computedRepairedHist censusWith
  simp only [repaired_width_count_explicit]

theorem computedRepairedHist_eq_oppbankHist :
    computedRepairedHist = oppbankHist := by
  native_decide

theorem repaired_hist_eq_oppbankHist : repaired.hist = oppbankHist :=
  repaired_census.trans computedRepairedHist_eq_oppbankHist

theorem repaired_hist_eq_bitR8 : repaired.hist = IntMul.Kappa.Jain.bitR8 :=
  repaired_hist_eq_oppbankHist.trans MomPack.oppbankHist_eq_bitR8

theorem repaired_net_eq : repaired.net = net ch0R := rfl

end IntMul.Kappa.R8.Bit.Oppbank.Repaired
