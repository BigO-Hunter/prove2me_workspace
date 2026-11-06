import Theorems.Thm_oneRunNB_wires
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-!
# Scalar semantics of genuine chunk programs
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.OneRunNB

open IntMul.Kappa IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank IntMul.Kappa.R8.Bit.Oppbank.NB
open IntMul.Kappa.R8.Bit.Oppbank.Repaired

section Scalar

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

theorem xrL_cons (p : ℕ × ℕ) (l : List (ℕ × ℕ)) (u : ℕ → M) :
    xrL l (Function.update u p.1 (u p.1 + u p.2)) = xrL (p :: l) u := rfl

theorem xrL_append (l l' : List (ℕ × ℕ)) (u : ℕ → M) : xrL (l ++ l') u = xrL l' (xrL l u) := by
  simp [xrL, List.foldl_append]

theorem gateVecM_xorG {d s : Repaired.Wr} (hds : d ≠ s) (v : Repaired.Wr → M) :
    gateVecM (fun x y => if x = y then (1 : ZMod 2) else if x = d ∧ y = s then 1 else 0) {d, s} v =
      Function.update v d (v d + v s) := by
  funext w
  simp only [gateVecM, Finset.mem_insert, Finset.mem_singleton]
  by_cases hwd : w = d
  · subst hwd
    rw [Finset.sum_pair hds]
    simp
  · by_cases hws : w = s
    · subst hws
      rw [Finset.sum_pair hds]
      simp [hwd]
    · simp [hwd, hws]

variable (ι : ℕ → Repaired.Wr) (D : ℕ → Prop) (E : ℕ → ℕ → Edge 529)

theorem edges_scalar (l : List (Repaired.Wr × Edge 529)) (v : Repaired.Wr → M) :
    (l.map fun p => (Instr.edge p.1 p.2 : Instr Repaired.Wr (ZMod 2) 529)).foldl scalarStepM v = v := by
  induction l with
  | nil => rfl
  | cons p l ih => simpa [scalarStepM] using ih

theorem xorGs_scalar (hι : ∀ w w', D w → D w' → ι w = ι w' → w = w') :
    ∀ (l : List (ℕ × ℕ)), (∀ p ∈ l, D p.1 ∧ D p.2 ∧ p.1 ≠ p.2) → ∀ (v : Repaired.Wr → M) (u : ℕ → M),
      (∀ w, D w → v (ι w) = u w) →
      (∀ w, D w → (l.map fun p => (NB.xorG (ι p.1) (ι p.2) : Instr Repaired.Wr (ZMod 2) 529)).foldl scalarStepM v (ι w) =
        xrL l u w) ∧
      ∀ x, (∀ w, D w → ι w ≠ x) → (l.map fun p => (NB.xorG (ι p.1) (ι p.2) : Instr Repaired.Wr (ZMod 2) 529)).foldl scalarStepM v x = v x
  | [], v, u, _, h => ⟨h, fun _ _ => rfl⟩
  | p :: l, hl, v, u, h => by
    obtain ⟨hd, hs, hds⟩ := hl p (by simp)
    have hds' : ι p.1 ≠ ι p.2 := fun e => hds (hι _ _ hd hs e)
    simp only [List.map_cons, List.foldl_cons]
    have hstep : scalarStepM v (NB.xorG (ι p.1) (ι p.2) : Instr Repaired.Wr (ZMod 2) 529) =
        Function.update v (ι p.1) (v (ι p.1) + v (ι p.2)) := gateVecM_xorG hds' v
    rw [hstep, ← xrL_cons]
    have hcall :
        (∀ w, D w → (l.map fun p => (NB.xorG (ι p.1) (ι p.2) : Instr Repaired.Wr (ZMod 2) 529)).foldl
          scalarStepM (Function.update v (ι p.1) (v (ι p.1) + v (ι p.2))) (ι w) =
            xrL l (Function.update u p.1 (u p.1 + u p.2)) w) ∧
        ∀ x, (∀ w, D w → ι w ≠ x) →
          (l.map fun p => (NB.xorG (ι p.1) (ι p.2) : Instr Repaired.Wr (ZMod 2) 529)).foldl
            scalarStepM (Function.update v (ι p.1) (v (ι p.1) + v (ι p.2))) x =
          Function.update v (ι p.1) (v (ι p.1) + v (ι p.2)) x := by
      apply OneRunNB.xorGs_scalar
      · exact hι
      · intro q hq
        exact hl q (by simp [hq])
      · intro w hw
        by_cases hwp : w = p.1
        · subst hwp; simp [h _ hd, h _ hs]
        · rw [Function.update_of_ne (fun e => hwp (hι _ _ hw hd e)), Function.update_of_ne hwp, h w hw]
    obtain ⟨h1, h2⟩ := hcall
    refine ⟨h1, fun x hx => ?_⟩
    rw [h2 x hx, Function.update_of_ne (fun e => hx _ hd e.symm)]

/-- Scalar run of a genuine chunk program: the local XOR run of its gates. -/
theorem chunkProg_scalar (hι : ∀ w w', D w → D w' → ι w = ι w' → w = w') :
    ∀ (cs : List LChunk), (∀ ch ∈ cs, ∀ p ∈ ch.2.2, D p.1 ∧ D p.2 ∧ p.1 ≠ p.2) →
      ∀ (v : Repaired.Wr → M) (u : ℕ → M), (∀ w, D w → v (ι w) = u w) →
        (∀ w, D w → (NB.chunkProg ι E cs).foldl scalarStepM v (ι w) =
          xrL (cs.flatMap fun ch => ch.2.2) u w) ∧
        ∀ x, (∀ w, D w → ι w ≠ x) → (NB.chunkProg ι E cs).foldl scalarStepM v x = v x
  | [], _, v, u, h => ⟨h, fun _ _ => rfl⟩
  | ch :: cs, hcs, v, u, h => by
    have hprog : NB.chunkProg ι E (ch :: cs) =
        (ch.2.1.map fun mv => (ι mv.1, E mv.2 ch.1)).map (fun p => (Instr.edge p.1 p.2 : Instr Repaired.Wr (ZMod 2) 529)) ++
          ((ch.2.2.map fun p => (NB.xorG (ι p.1) (ι p.2) : Instr Repaired.Wr (ZMod 2) 529)) ++ NB.chunkProg ι E cs) := by
      simp [NB.chunkProg, NB.chunkInstrs, List.flatMap_cons, List.append_assoc, Function.comp_def]
    rw [hprog, List.foldl_append, edges_scalar, List.foldl_append]
    have hgate :
        (∀ w, D w → (ch.2.2.map fun p => (NB.xorG (ι p.1) (ι p.2) : Instr Repaired.Wr (ZMod 2) 529)).foldl
          scalarStepM v (ι w) = xrL ch.2.2 u w) ∧
        ∀ x, (∀ w, D w → ι w ≠ x) →
          (ch.2.2.map fun p => (NB.xorG (ι p.1) (ι p.2) : Instr Repaired.Wr (ZMod 2) 529)).foldl scalarStepM v x = v x := by
      apply OneRunNB.xorGs_scalar
      · exact hι
      · exact hcs ch (by simp)
      · exact h
    obtain ⟨g1, g2⟩ := hgate
    set v' := List.foldl scalarStepM v (ch.2.2.map fun p => (NB.xorG (ι p.1) (ι p.2) : Instr Repaired.Wr (ZMod 2) 529))
    set u' := xrL ch.2.2 u
    have hcall :
        (∀ w, D w → (NB.chunkProg ι E cs).foldl scalarStepM v' (ι w) =
          xrL (cs.flatMap fun ch => ch.2.2) u' w) ∧
        ∀ x, (∀ w, D w → ι w ≠ x) → (NB.chunkProg ι E cs).foldl scalarStepM v' x = v' x := by
      apply OneRunNB.chunkProg_scalar
      · exact hι
      · intro c hc
        exact hcs c (by simp [hc])
      · exact g1
    obtain ⟨r1, r2⟩ := hcall
    refine ⟨fun w hw => ?_, fun x hx => ?_⟩
    · rw [List.flatMap_cons, xrL_append, r1 w hw]
    · rw [r2 x hx, g2 x hx]

end Scalar

end IntMul.Kappa.R8.Bit.Oppbank.OneRunNB
