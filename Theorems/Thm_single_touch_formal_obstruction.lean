import Theorems.Thm_oneEdge_ne_swapMat_general
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-!
# Formal-correctness obstruction for a single-touch output role

Frame-sharing design constraint for R2125607035.  If an output role is touched
by exactly one edge instruction, with every earlier and later instruction
avoiding its wire, formal correctness forces that edge matrix to be the full
chunk interchange.  A one-run edge of width below `m` therefore cannot be the
terminal frame of such a role.  The redesign must alter this decomposition,
not merely compensate its child-width histogram.
-/

namespace IntMul.Kappa.R6.Bit.SingleTouch

open IntMul.Kappa AModel AModelFac Matrix
open IntMul.Kappa.R6.Bit.OneEdgeObstruction

variable {R : Type*} [CommRing R] [Nontrivial R]

/-- An instruction that cannot change one selected wire. -/
def Avoids {W T m : ℕ} (z : Fin W ⊕ Fin T) : Instr (Fin W ⊕ Fin T) R m → Prop
  | .gate _ S => z ∉ S
  | .edge w _ => w ≠ z

theorem fStep_avoids {W T m M : ℕ} (z : Fin W ⊕ Fin T)
    (f : (Fin W ⊕ Fin T) → FV R (Fin W) m M)
    (i : Instr (Fin W ⊕ Fin T) R m) (h : Avoids z i) :
    fStep M f i z = f z := by
  cases i with
  | gate g S =>
      simp only [Avoids] at h
      simp [fStep, gateVecM, h]
  | edge w e =>
      simp only [Avoids] at h
      simp [fStep, Function.update_apply, Ne.symm h]

theorem foldl_avoids {W T m M : ℕ} (z : Fin W ⊕ Fin T)
    (f : (Fin W ⊕ Fin T) → FV R (Fin W) m M)
    (p : List (Instr (Fin W ⊕ Fin T) R m)) (h : ∀ i ∈ p, Avoids z i) :
    (p.foldl (fStep M) f) z = f z := by
  induction p generalizing f with
  | nil => rfl
  | cons i p ih =>
      rw [List.foldl_cons, ih]
      · exact fStep_avoids z f i (h i (by simp))
      · intro j hj
        exact h j (by simp [hj])

theorem lmulF_single {W m M : ℕ} (L F : FMat m M) (u : Fin W) (c : R) :
    lmulF L (Finsupp.single (F, u) c) = Finsupp.single (L * F, u) c := by
  simp [lmulF, Finsupp.lmapDomain]

/-- A single-touch output role forces its unique edge to carry the full swap. -/
theorem edgeMat_eq_swapMat_of_formalOK {W T m M : ℕ}
    {C : QHNet R W T m} (hFormal : C.FormalOK M) (w : Fin W)
    {e : Edge m} {pre post : List (Instr (Fin W ⊕ Fin T) R m)}
    (hprog : C.prog = pre ++ .edge (.inl (C.ρ w)) e :: post)
    (hpre : ∀ i ∈ pre, Avoids (.inl (C.ρ w)) i)
    (hpost : ∀ i ∈ post, Avoids (.inl (C.ρ w)) i) :
    edgeMat M e = AModel.swapMat := by
  have hh := hFormal w
  rw [hprog, List.foldl_append, List.foldl_cons,
    foldl_avoids (.inl (C.ρ w)) _ post hpost] at hh
  simp only [fStep, Function.update_self] at hh
  rw [foldl_avoids (.inl (C.ρ w)) _ pre hpre] at hh
  simp only [QHNet.fInit, Sum.elim_inl] at hh
  rw [lmulF_single, Matrix.mul_one] at hh
  exact congrArg Prod.fst (Finsupp.single_left_injective (b := (1 : R)) one_ne_zero hh)

/-- No one-run edge of width below `m` can be the unique frame of an output role. -/
theorem not_formalOK_of_singleEdge {W T m M : ℕ}
    (hM : 1 < M) {w₀ : ℕ} (hw₀ : w₀ < m)
    {C : QHNet R W T m} (w : Fin W)
    {pre post : List (Instr (Fin W ⊕ Fin T) R m)}
    (hprog : C.prog = pre ++ .edge (.inl (C.ρ w)) (singleEdge m w₀) :: post)
    (hpre : ∀ i ∈ pre, Avoids (.inl (C.ρ w)) i)
    (hpost : ∀ i ∈ post, Avoids (.inl (C.ρ w)) i) :
    ¬ C.FormalOK M := by
  intro hFormal
  have he := edgeMat_eq_swapMat_of_formalOK hFormal w hprog hpre hpost
  exact singleEdge_ne_swapMat m M w₀ hM hw₀ he

end IntMul.Kappa.R6.Bit.SingleTouch
