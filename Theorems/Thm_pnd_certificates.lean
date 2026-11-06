import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNet0Pnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNetFB
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

/-!
# Certificates for the densified `Pnd` network

The line-label certificates are unconditional.  The projector algebra is also
proved unconditionally.  The final `Dm`/`Pis0` certificates are parameterized
by `DensifiedSupportOK`, which names precisely the finite support facts absent
from the published `SupG`/`ChkBitArg` data files.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.Net0Pnd

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB (AuxE SideE DataE)
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG
open Matrix Module
open scoped Kronecker

/-- The two copies of the line geometry in `ProjB` and `Pnd` are
definitionally equal, so the kernel-checked `NetFB` certificates transfer. -/
theorem pnd_yx {T : ℕ} (hT : T < 1771) : yv T ⬝ᵥ xv T = 1 :=
  NetFB.yx hT

theorem pnd_Pl_idem {T : ℕ} (hT : T < 1771) : Pl T * Pl T = Pl T :=
  NetFB.Pl_idem hT

/-- Requested label certificate. -/
theorem pnd_hLab0 : ∀ p ∈ Pnd.Lab0, p.2 ⬝ᵥ p.1 = 1 := by
  intro p hp
  unfold Pnd.Lab0 at hp
  obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hp
  exact pnd_yx (Finset.mem_range.1 hT)

/-- Rank of an idempotent equals its trace (over `ℚ`). -/
theorem pnd_rank_idem {n : ℕ} {P : Matrix (Fin n) (Fin n) ℚ} (h : P * P = P) :
    (P.rank : ℚ) = P.trace := by
  have he : IsIdempotentElem (Matrix.toLin' P) := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, h]
  have ht := LinearMap.IsProj.trace (LinearMap.IsIdempotentElem.isProj_range _ he)
  rw [Matrix.trace_toLin'_eq] at ht
  rw [ht]
  rfl

/-- Requested rank-one line-projector certificate. -/
theorem pnd_Pl_rank {b : ℕ} (hb : b < 1771) : (Pnd.Pl b).rank = 1 := by
  have h := pnd_rank_idem (pnd_Pl_idem hb)
  rw [Pnd.Pl, Matrix.trace_vecMulVec, dotProduct_comm, pnd_yx hb] at h
  exact_mod_cast h

theorem pnd_one_sub_idem {n : ℕ} {P : Matrix (Fin n) (Fin n) ℚ} (h : P * P = P) :
    (1 - P) * (1 - P) = 1 - P := by
  rw [sub_mul, mul_sub, mul_sub, h]
  simp

theorem pnd_compl_rank {T : ℕ} (hT : T < 1771) : (1 - Pl T).rank = 22 := by
  have h := pnd_rank_idem (pnd_one_sub_idem (pnd_Pl_idem hT))
  rw [Matrix.trace_sub, Matrix.trace_one, ← pnd_rank_idem (pnd_Pl_idem hT),
    pnd_Pl_rank hT] at h
  simp at h
  norm_num at h
  exact_mod_cast h

/-! ## Abstract `Pnd` projector algebra -/

theorem pnd_decomp {V : Submodule ℚ V23} (h : IsCompl V (Bf.orthogonal V)) (u : V23) :
    ∃ a ∈ V, ∃ b ∈ Bf.orthogonal V, u = a + b := by
  have hu : u ∈ V ⊔ Bf.orthogonal V := by rw [h.sup_eq_top]; trivial
  obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 hu
  exact ⟨a, ha, b, hb, e.symm⟩

theorem pnd_mat_ext {P Q : M23} (h : ∀ u, P *ᵥ u = Q *ᵥ u) : P = Q := by
  apply Matrix.toLin'.injective
  exact LinearMap.ext fun u => by rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h]

theorem pnd_IsPrj_eq {V : Submodule ℚ V23} (h : IsCompl V (Bf.orthogonal V))
    {P Q : M23} (hP : IsPrj P V) (hQ : IsPrj Q V) : P = Q := by
  apply pnd_mat_ext
  intro u
  obtain ⟨a, ha, b, hb, rfl⟩ := pnd_decomp h u
  rw [mulVec_add, mulVec_add, hP.1 a ha, hQ.1 a ha, hP.2 b hb, hQ.2 b hb]

theorem pnd_IsPrj_mem {V : Submodule ℚ V23} (h : IsCompl V (Bf.orthogonal V))
    {P : M23} (hP : IsPrj P V) (u : V23) :
    P *ᵥ u ∈ V ∧ u - P *ᵥ u ∈ Bf.orthogonal V := by
  obtain ⟨a, ha, b, hb, rfl⟩ := pnd_decomp h u
  rw [mulVec_add, hP.1 a ha, hP.2 b hb, add_zero, add_sub_cancel_left]
  exact ⟨ha, hb⟩

theorem pnd_IsPrj_idem {V : Submodule ℚ V23} (h : IsCompl V (Bf.orthogonal V))
    {P : M23} (hP : IsPrj P V) : P * P = P :=
  pnd_IsPrj_eq h ⟨fun v hv => by rw [← mulVec_mulVec, hP.1 v hv, hP.1 v hv],
    fun w hw => by rw [← mulVec_mulVec, hP.2 w hw, mulVec_zero]⟩ hP

theorem pnd_IsPrj_nested {V V' : Submodule ℚ V23} (hVV : V ≤ V')
    (h : IsCompl V (Bf.orthogonal V)) (h' : IsCompl V' (Bf.orthogonal V'))
    {P P' : M23} (hP : IsPrj P V) (hP' : IsPrj P' V') :
    P' * P = P ∧ P * P' = P := by
  have horth : Bf.orthogonal V' ≤ Bf.orthogonal V :=
    LinearMap.BilinForm.orthogonal_le hVV
  constructor
  · exact pnd_IsPrj_eq h
      ⟨fun v hv => by rw [← mulVec_mulVec, hP.1 v hv, hP'.1 v (hVV hv)],
        fun w hw => by rw [← mulVec_mulVec, hP.2 w hw, mulVec_zero]⟩ hP
  · refine pnd_IsPrj_eq h
      ⟨fun v hv => by rw [← mulVec_mulVec, hP'.1 v (hVV hv), hP.1 v hv],
        fun w hw => ?_⟩ hP
    rw [← mulVec_mulVec]
    have hm := (pnd_IsPrj_mem h' hP' w).2
    have he : P' *ᵥ w = w - (w - P' *ᵥ w) := by abel
    rw [he, mulVec_sub, hP.2 w hw, hP.2 _ (horth hm), sub_zero]

theorem pnd_IsPrj_rank {V : Submodule ℚ V23} (h : IsCompl V (Bf.orthogonal V))
    {P : M23} (hP : IsPrj P V) : P.rank = finrank ℚ V := by
  have hr : LinearMap.range P.mulVecLin = V := by
    ext v
    constructor
    · rintro ⟨u, rfl⟩
      exact (pnd_IsPrj_mem h hP u).1
    · intro hv
      exact ⟨v, hP.1 v hv⟩
  rw [Matrix.rank, hr]

theorem pnd_prjM_spec (V : Submodule ℚ V23) (h : IsCompl V (Bf.orthogonal V)) :
    IsPrj (prjM V h) V := by
  refine ⟨fun v hv => ?_, fun w hw => ?_⟩
  · rw [prjM, LinearMap.toMatrix'_mulVec, ← Submodule.coe_projectionOnto_apply,
      Submodule.projectionOnto_apply_of_mem_left h hv]
  · rw [prjM, LinearMap.toMatrix'_mulVec, ← Submodule.coe_projectionOnto_apply,
      Submodule.projectionOnto_apply_of_mem_right h hw]
    rfl

theorem pnd_Pnd_prj {sup : ℕ} (h : HasCentre sup) : IsPrj (Pnd.Pnd sup) (spanS sup) := by
  rw [Pnd.Pnd, dif_pos h]
  exact pnd_prjM_spec _ _

theorem pnd_Pnd_idem {sup : ℕ} (h : HasCentre sup) : Pnd.Pnd sup * Pnd.Pnd sup = Pnd.Pnd sup :=
  pnd_IsPrj_idem (compl_spanS h) (pnd_Pnd_prj h)

theorem pnd_Pnd_rank {sup : ℕ} (h : HasCentre sup) :
    (Pnd.Pnd sup).rank = finrank ℚ (spanS sup) :=
  pnd_IsPrj_rank (compl_spanS h) (pnd_Pnd_prj h)

theorem pnd_Pnd_nested {a b : ℕ} (ha : HasCentre a) (hb : HasCentre b)
    (hab : spanS a ≤ spanS b) :
    Pnd.Pnd b * Pnd.Pnd a = Pnd.Pnd a ∧ Pnd.Pnd a * Pnd.Pnd b = Pnd.Pnd a :=
  pnd_IsPrj_nested hab (compl_spanS ha) (compl_spanS hb) (pnd_Pnd_prj ha) (pnd_Pnd_prj hb)

theorem pnd_Pnd_orth {sup T : ℕ} (h : HasCentre sup) (hT : T < 1771)
    (horth : ∀ v ∈ spanS sup, bfF (xv T) v = 0) :
    (1 - Pl T) * Pnd.Pnd sup = Pnd.Pnd sup ∧ Pnd.Pnd sup * (1 - Pl T) = Pnd.Pnd sup := by
  have hP := pnd_Pnd_prj h
  have hc := compl_spanS h
  have hPl (v : V23) : Pl T *ᵥ v = (bfF (xv T) v / 2) • xv T := by
    rw [Pnd.Pl, vecMulVec_mulVec]
    have hy : yv T ⬝ᵥ v = bfF (xv T) v / 2 := NetFB.yv_dot T v
    rw [hy, op_smul_eq_smul]
  have h1 : Pl T * Pnd.Pnd sup = 0 := by
    apply pnd_mat_ext
    intro u
    rw [← mulVec_mulVec, hPl, horth _ (pnd_IsPrj_mem hc hP u).1, zero_mulVec]
    simp
  have h2 : Pnd.Pnd sup * Pl T = 0 := by
    apply pnd_mat_ext
    intro u
    rw [← mulVec_mulVec, hPl, mulVec_smul,
      hP.2 (xv T) (mem_orth.2 fun v hv => by rw [bfF_comm]; exact horth v hv),
      smul_zero, zero_mulVec]
  constructor
  · rw [sub_mul, one_mul, h1, sub_zero]
  · rw [mul_sub, mul_one, h2, sub_zero]

/-! ## Orthogonality is certified by the executable masks -/

private abbrev pndOrthHit (c T : ℕ) : Prop :=
  ptsL T 0 = c ∨ ptsL T 1 = c ∨ ptsL T 2 = c

private theorem pnd_nlor (x y : ℕ) : Nat.lor x y = x ||| y := rfl
private theorem pnd_nland (x y : ℕ) : Nat.land x y = x &&& y := rfl
private theorem pnd_nxor (x y : ℕ) : Nat.xor x y = x ^^^ y := rfl

theorem pnd_star_fold (c : ℕ) (l : List ℕ) : ∀ (acc i : ℕ),
    ((l.foldl (fun acc T => if pndOrthHit c T then Nat.lor acc (Nat.shiftLeft 1 T) else acc)
      acc).testBit i = true) ↔
      (acc.testBit i = true ∨ ∃ T ∈ l, i = T ∧ pndOrthHit c T) := by
  induction l with
  | nil => intro acc i; simp
  | cons T l ih =>
      intro acc i
      simp only [List.foldl_cons]
      rw [ih]
      by_cases hT : pndOrthHit c T
      · simp [hT, pnd_nlor, Nat.testBit_lor, Nat.one_shiftLeft, Nat.testBit_two_pow,
          or_assoc, or_left_comm]
        constructor
        · rintro (h | h | ⟨hil, hi⟩)
          · subst i
            exact Or.inr ⟨Or.inl rfl, hT⟩
          · exact Or.inl h
          · exact Or.inr ⟨Or.inr hil, hi⟩
        · rintro (h | ⟨hmem, hi⟩)
          · exact Or.inr (Or.inl h)
          · rcases hmem with h' | hil
            · exact Or.inl h'.symm
            · exact Or.inr (Or.inr ⟨hil, hi⟩)
      · simp [hT, or_assoc]
        constructor
        · rintro (h | ⟨hil, hi⟩)
          · exact Or.inl h
          · exact Or.inr ⟨Or.inr hil, hi⟩
        · rintro (h | ⟨hmem, hi⟩)
          · exact Or.inl h
          · rcases hmem with rfl | hil
            · exact absurd hi hT
            · exact Or.inr ⟨hil, hi⟩

theorem pnd_starL_spec (c i : ℕ) :
    (Pnd.starL c).testBit i = true ↔ ∃ T < 1771, i = T ∧ pndOrthHit c T := by
  unfold Pnd.starL
  rw [pnd_star_fold]
  simp [List.mem_range]

theorem pnd_triL_bit (T p : ℕ) :
    (triL T).testBit p =
      (decide (ptsL T 0 = p) || decide (ptsL T 1 = p) || decide (ptsL T 2 = p)) := by
  simp [triL, pnd_nlor, Nat.testBit_lor, Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem pnd_star_bit {c i : ℕ} (h : (Pnd.starL c).testBit i = true) :
    i < 1771 ∧ (triL i).testBit c = true := by
  obtain ⟨T, hT, rfl, hh⟩ := (pnd_starL_spec c i).1 h
  refine ⟨hT, ?_⟩
  rw [pnd_triL_bit]
  simpa [pndOrthHit, or_assoc] using hh

theorem pnd_star_of_tri {c i : ℕ} (hi : i < 1771) (h : (triL i).testBit c = true) :
    (Pnd.starL c).testBit i = true := by
  apply (pnd_starL_spec c i).2
  refine ⟨i, hi, rfl, ?_⟩
  rw [pnd_triL_bit] at h
  simpa [pndOrthHit, or_assoc] using h

theorem pnd_mem_F {m : ℕ} {p : Fin 23} : p ∈ NetFB.F m ↔ m.testBit p.val = true := by
  simp [NetFB.F]

theorem pnd_exclTL_bit {c t1 t2 i : ℕ} :
    (exclTL c t1 t2).testBit i =
      ((Pnd.starL c).testBit i && !((Pnd.starL t1).testBit i || (Pnd.starL t2).testBit i)) := by
  rw [exclTL, pnd_nxor, pnd_nland, pnd_nlor, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_or]
  cases (Pnd.starL c).testBit i <;> cases (Pnd.starL t1).testBit i <;>
    cases (Pnd.starL t2).testBit i <;> rfl

theorem pnd_not_tri_of_star {c i : ℕ} (hi : i < 1771)
    (h : (Pnd.starL c).testBit i = false) : (triL i).testBit c = false := by
  by_contra h'
  rw [Bool.not_eq_false] at h'
  rw [pnd_star_of_tri hi h'] at h
  exact absurd h (by decide)

theorem pnd_orth_excl {T i k0 k1 k2 : ℕ} (hT : T < 1771)
    (hk : ∀ p, pndOrthHit p T ↔ p = k0 ∨ p = k1 ∨ p = k2)
    (h0 : k0 < 23) (_h1 : k1 < 23) (_h2 : k2 < 23)
    (h : (exclTL k0 k1 k2).testBit i = true) :
    i < 1771 ∧ bfF (xv T) (tvQ i) = 0 := by
  rw [pnd_exclTL_bit, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff] at h
  obtain ⟨ha, hb, hc⟩ := h
  obtain ⟨hi, ha'⟩ := pnd_star_bit ha
  have hb' := pnd_not_tri_of_star hi hb
  have hc' := pnd_not_tri_of_star hi hc
  refine ⟨hi, ?_⟩
  have hset : NetFB.F (triL T) ∩ NetFB.F (triL i) = {⟨k0, h0⟩} := by
    ext p
    simp only [Finset.mem_inter, pnd_mem_F, Finset.mem_singleton, pnd_triL_bit T,
      Bool.or_eq_true, decide_eq_true_eq]
    rw [or_assoc]
    change (pndOrthHit p.val T ∧ _) ↔ _
    rw [hk p.val]
    constructor
    · rintro ⟨hp | hp | hp, hq⟩
      · exact Fin.ext hp
      · rw [hp] at hq
        rw [hq] at hb'
        exact absurd hb' (by decide)
      · rw [hp] at hq
        rw [hq] at hc'
        exact absurd hc' (by decide)
    · rintro rfl
      exact ⟨Or.inl rfl, ha'⟩
  have hb : bfF (tvQ T) (tvQ i) =
      ((NetFB.F (triL T) ∩ NetFB.F (triL i)).card : ℚ) - 1 := NetFB.bf_tvQ hT hi
  rw [Pnd.xv, hb, hset]
  simp

/-- Kernel check of the three point coordinates, using the same packed table
as the already-published `NetFB.tri_chk`. -/
theorem pnd_pts_chk :
    NetFB.allN 1771 (fun i => Nat.blt (ptsL i 0) 23 && Nat.blt (ptsL i 1) 23 &&
      Nat.blt (ptsL i 2) 23) = true := by
  decide +kernel

theorem pnd_pts_lt {T : ℕ} (hT : T < 1771) :
    ptsL T 0 < 23 ∧ ptsL T 1 < 23 ∧ ptsL T 2 < 23 := by
  have h := NetFB.allN_spec pnd_pts_chk T hT
  simpa only [Bool.and_eq_true, NetFB.blt_dec, decide_eq_true_eq, and_assoc] using h

theorem pnd_orthTL_bit {T i : ℕ} (hT : T < 1771) (h : (orthTL T).testBit i = true) :
    i < 1771 ∧ bfF (xv T) (tvQ i) = 0 := by
  obtain ⟨p0, p1, p2⟩ := pnd_pts_lt hT
  rw [orthTL, pnd_nlor, pnd_nlor, Nat.testBit_lor, Nat.testBit_lor, Bool.or_eq_true,
    Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · exact pnd_orth_excl hT (fun p => by constructor <;> intro hh <;> omega) p0 p1 p2 h
  · exact pnd_orth_excl hT (fun p => by constructor <;> intro hh <;> omega) p1 p0 p2 h
  · exact pnd_orth_excl hT (fun p => by constructor <;> intro hh <;> omega) p2 p0 p1 h

theorem pnd_spanS_orth {sup T : ℕ}
    (h : ∀ i, sup.testBit i = true → bfF (xv T) (tvQ i) = 0) :
    ∀ v ∈ spanS sup, bfF (xv T) v = 0 := by
  have hle : spanS sup ≤ LinearMap.ker (Bf (xv T)) := by
    rw [spanS, Submodule.span_le]
    rintro v ⟨i, hi, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, Bf_apply]
    exact h i hi
  intro v hv
  have hv' := hle hv
  rwa [LinearMap.mem_ker, Bf_apply] at hv'

/-- Soundness of the densified orthogonality mask, with no extra support
certificate required. -/
theorem pnd_orthOK_sound {n T : ℕ} (hT : T < 1771) (h : orthOK n T = true) :
    ∀ v ∈ spanS (SupG.densSupG n), bfF (xv T) v = 0 := by
  apply pnd_spanS_orth
  intro i hi
  simp only [orthOK, Nat.beq_eq] at h
  have hi' : (Nat.land (SupG.densSupG n) (orthTL T)).testBit i = true := by
    rw [h]
    exact hi
  rw [pnd_nland, Nat.testBit_and, Bool.and_eq_true] at hi'
  exact (pnd_orthTL_bit hT hi'.2).2

/-! ## The exact finite support interface needed by `Dm` -/

/-- Product relations for nested projectors. -/
def ProjLe (A B : M23) : Prop := B * A = A ∧ A * B = A

/-- The finite facts not supplied by `BitOppbankSupG` or `ChkBitArg`.
The first component combines the dimension and centre records; the second is
support inclusion for an argument relation.  Orthogonality is not an
assumption: it is proved above as `pnd_orthOK_sound`. -/
def DensifiedSupportOK : Prop :=
  (∀ n < nNodes, finrank ℚ (spanS (densSupG n)) = dimF n ∧ HasCentre (densSupG n)) ∧
  (∀ a n, n < nNodes → argRel a n = true → spanS (densSupG a) ≤ spanS (densSupG n))

theorem pnd_nd_facts_of_support (hS : DensifiedSupportOK) {c : ℕ}
    (h1 : 1773 ≤ c) (h2 : c < codeBound) :
    Pc c = Pnd.Pnd (densSupG (c - 1773)) ∧ HasCentre (densSupG (c - 1773)) ∧
      (Pc c).rank = dimCF c := by
  have hP : Pc c = Pnd.Pnd (densSupG (c - 1773)) := by
    rw [Pc, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rfl
  have hn : c - 1773 < nNodes := by
    rw [SupG.codeBound_eq] at h2
    omega
  obtain ⟨hd, hc⟩ := hS.1 (c - 1773) hn
  refine ⟨hP, hc, ?_⟩
  rw [hP, pnd_Pnd_rank hc, hd]
  simp [dimCF, show c ≠ 0 by omega, show c ≠ 1 by omega, show ¬c < 1773 by omega]

theorem pnd_pt_facts {c : ℕ} (h1 : 2 ≤ c) (h2 : c < 1773) :
    Pc c = 1 - Pl (c - 2) ∧ c - 2 < 1771 ∧ (Pc c).rank = dimCF c := by
  have hP : Pc c = 1 - Pl (c - 2) := by
    rw [Pc, if_neg (by omega), if_neg (by omega), if_pos h2]
  refine ⟨hP, by omega, ?_⟩
  rw [hP, pnd_compl_rank (by omega)]
  simp [dimCF, show c ≠ 0 by omega, show c ≠ 1 by omega, h2]

theorem pnd_Pc_idem_of_support (hS : DensifiedSupportOK) {c : ℕ} (hc : c < codeBound) :
    Pc c * Pc c = Pc c := by
  by_cases h0 : c = 0
  · subst c
    simp [Pc]
  by_cases h1 : c = 1
  · subst c
    simp [Pc]
  by_cases h2 : c < 1773
  · rw [(pnd_pt_facts (by omega) h2).1]
    exact pnd_one_sub_idem (pnd_Pl_idem (by omega))
  · obtain ⟨e, hc', -⟩ := pnd_nd_facts_of_support hS (by omega) hc
    rw [e]
    exact pnd_Pnd_idem hc'

theorem pnd_Pc_rank_of_support (hS : DensifiedSupportOK) {c : ℕ} (hc : c < codeBound) :
    (Pc c).rank = dimCF c := by
  by_cases h0 : c = 0
  · subst c
    simp [Pc, dimCF]
  by_cases h1 : c = 1
  · subst c
    rw [show Pc 1 = 1 by simp [Pc], Matrix.rank_one, Fintype.card_fin]
    rfl
  by_cases h2 : c < 1773
  · exact (pnd_pt_facts (by omega) h2).2.2
  · exact (pnd_nd_facts_of_support hS (by omega) hc).2.2

theorem pnd_le_zero (B : M23) : ProjLe 0 B := by simp [ProjLe]
theorem pnd_le_one (A : M23) : ProjLe A 1 := by simp [ProjLe]

theorem pnd_node_bound {x : ℕ} (hx : x < codeBound) : x - 1773 < nNodes := by
  rw [SupG.codeBound_eq] at hx
  rw [SupG.nNodes_eq] at hx ⊢
  omega

theorem pnd_nest_sound_of_support (hS : DensifiedSupportOK) {o c : ℕ}
    (ho : o < codeBound) (hc : c < codeBound) (h : nestOK o c = true) :
    ProjLe (Pc o) (Pc c) ∨ ProjLe (Pc c) (Pc o) := by
  simp only [nestOK, isND, isPT, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq,
    NetFB.blt_dec, decide_eq_true_eq] at h
  rcases h with (((ho1 | hc1) | ⟨⟨⟨ho1, -⟩, hc1, -⟩, ha⟩) |
    ⟨⟨⟨ho1, -⟩, hc1, hc2⟩, hor⟩) | ⟨⟨⟨ho1, ho2⟩, hc1, -⟩, hor⟩
  · rcases (show o = 0 ∨ o = 1 by omega) with rfl | rfl
    · left
      rw [show Pc 0 = 0 by simp [Pc]]
      exact pnd_le_zero _
    · right
      rw [show Pc 1 = 1 by simp [Pc]]
      exact pnd_le_one _
  · rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
    · right
      rw [show Pc 0 = 0 by simp [Pc]]
      exact pnd_le_zero _
    · left
      rw [show Pc 1 = 1 by simp [Pc]]
      exact pnd_le_one _
  · obtain ⟨eo, hco, -⟩ := pnd_nd_facts_of_support hS ho1 ho
    obtain ⟨ec, hcc, -⟩ := pnd_nd_facts_of_support hS hc1 hc
    rw [eo, ec]
    rcases ha with ha | ha
    · left
      exact pnd_Pnd_nested hco hcc (hS.2 _ _ (pnd_node_bound hc) (by simpa using ha))
    · right
      exact pnd_Pnd_nested hcc hco (hS.2 _ _ (pnd_node_bound ho) (by simpa using ha))
  · obtain ⟨eo, hco, -⟩ := pnd_nd_facts_of_support hS ho1 ho
    obtain ⟨ec, hT, -⟩ := pnd_pt_facts hc1 hc2
    rw [eo, ec]
    left
    exact pnd_Pnd_orth hco hT (pnd_orthOK_sound hT (by simpa using hor))
  · obtain ⟨ec, hcc, -⟩ := pnd_nd_facts_of_support hS hc1 hc
    obtain ⟨eo, hT, -⟩ := pnd_pt_facts ho1 ho2
    rw [eo, ec]
    right
    exact pnd_Pnd_orth hcc hT (pnd_orthOK_sound hT (by simpa using hor))

/-! ## Idempotent algebra and ranks -/

theorem pnd_le_sub_idem {A B : M23} (hA : A * A = A) (hB : B * B = B)
    (h : ProjLe A B) : (B - A) * (B - A) = B - A := by
  obtain ⟨h1, h2⟩ := h
  rw [sub_mul, mul_sub, mul_sub, hA, hB, h1, h2]
  abel

theorem pnd_le_rank {A B : M23} (hA : A * A = A) (hB : B * B = B)
    (h : ProjLe A B) : A.rank ≤ B.rank ∧ (B - A).rank = B.rank - A.rank := by
  have hD := pnd_le_sub_idem hA hB h
  have e := pnd_rank_idem hD
  rw [Matrix.trace_sub, ← pnd_rank_idem hA, ← pnd_rank_idem hB] at e
  have hle : A.rank ≤ B.rank := by
    have hz : (0 : ℚ) ≤ (B.rank : ℚ) - A.rank := by rw [← e]; positivity
    exact_mod_cast (sub_nonneg.1 hz)
  refine ⟨hle, ?_⟩
  have he : ((B - A).rank : ℚ) = ((B.rank - A.rank : ℕ) : ℚ) := by
    rw [e, Nat.cast_sub hle]
  exact_mod_cast he

theorem pnd_le_eq_of_rank {A B : M23} (hA : A * A = A) (hB : B * B = B)
    (h : ProjLe A B) (hr : B.rank ≤ A.rank) : B = A := by
  have h0 : (B - A).rank = 0 := by rw [(pnd_le_rank hA hB h).2]; omega
  have h1 : LinearMap.range (B - A).mulVecLin = ⊥ := Submodule.finrank_eq_zero.1 h0
  have h2 : (B - A).mulVecLin = 0 := LinearMap.range_eq_bot.1 h1
  have hz : B - A = 0 := by
    ext i j
    have hij := congrArg (fun f => f (Pi.single j 1) i) h2
    simpa [Matrix.mulVec_single] using hij
  exact sub_eq_zero.1 hz

/-- All move facts, conditional only on `DensifiedSupportOK`. -/
theorem pnd_move_facts_of_support (hS : DensifiedSupportOK) {o c : ℕ}
    (ho : o < codeBound) (hc : c < codeBound) (h : nestOK o c = true) :
    Dm o c * Dm o c = Dm o c ∧ Dm o c + Pc o - 2 * (Dm o c * Pc o) = Pc c ∧
      (Dm o c).rank = rkC o c := by
  have hio := pnd_Pc_idem_of_support hS ho
  have hic := pnd_Pc_idem_of_support hS hc
  have hrk : rkC o c = if dimCF o < dimCF c then dimCF c - dimCF o else dimCF o - dimCF c := rfl
  rcases pnd_nest_sound_of_support hS ho hc h with hle | hle
  · obtain ⟨hr, hD⟩ := pnd_le_rank hio hic hle
    rw [pnd_Pc_rank_of_support hS ho, pnd_Pc_rank_of_support hS hc] at hr hD
    rw [Dm, if_pos hr]
    refine ⟨pnd_le_sub_idem hio hic hle, ?_, ?_⟩
    · rw [sub_mul, hle.1, hio, sub_self, mul_zero, sub_zero, sub_add_cancel]
    · rw [hD, hrk]
      split_ifs <;> omega
  · obtain ⟨hr, hD⟩ := pnd_le_rank hic hio hle
    rw [pnd_Pc_rank_of_support hS ho, pnd_Pc_rank_of_support hS hc] at hr hD
    by_cases heq : dimCF o ≤ dimCF c
    · have e : Pc o = Pc c := pnd_le_eq_of_rank hic hio hle (by
        rw [pnd_Pc_rank_of_support hS ho, pnd_Pc_rank_of_support hS hc]
        exact heq)
      rw [Dm, if_pos heq, e]
      refine ⟨by simp, by simp, ?_⟩
      rw [sub_self, Matrix.rank_zero, hrk]
      split_ifs <;> omega
    · rw [Dm, if_neg heq]
      refine ⟨pnd_le_sub_idem hic hio hle, ?_, ?_⟩
      · rw [sub_mul, hle.2, hio, two_mul]
        abel
      · rw [hD, hrk]
        split_ifs <;> omega

attribute [local semireducible] Pnd.idxD Pnd.Pis0

theorem pnd_mem_idxD (p : ℕ × ℕ) :
    p ∈ Pnd.idxD ↔ ((p.1 < codeBound ∧ p.2 < codeBound) ∧ nestOK p.1 p.2 = true) := by
  unfold Pnd.idxD
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]

attribute [local irreducible] Pnd.idxD Pnd.Pis0

/-- Conditional form of the requested `Dm` rank certificate. -/
theorem pnd_Dm_rank_of_support (hS : DensifiedSupportOK) {o c : ℕ}
    (hoc : (o, c) ∈ Pnd.idxD) : (Pnd.Dm o c).rank = Pnd.rkC o c := by
  obtain ⟨⟨ho, hc⟩, hnest⟩ := (pnd_mem_idxD (o, c)).1 hoc
  exact (pnd_move_facts_of_support hS ho hc hnest).2.2

theorem pnd_Dm_idem_of_support (hS : DensifiedSupportOK) {o c : ℕ}
    (hoc : (o, c) ∈ Pnd.idxD) : Pnd.Dm o c * Pnd.Dm o c = Pnd.Dm o c := by
  obtain ⟨⟨ho, hc⟩, hnest⟩ := (pnd_mem_idxD (o, c)).1 hoc
  exact (pnd_move_facts_of_support hS ho hc hnest).1

/-- Conditional form of the requested `Pis0` idempotence certificate. -/
theorem pnd_hPis0_of_support (hS : DensifiedSupportOK) : ∀ A ∈ Pnd.Pis0, A * A = A := by
  intro A hA
  rw [Pnd.Pis0, Finset.mem_union] at hA
  rcases hA with hA | hA
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hA
    exact pnd_Dm_idem_of_support hS hp
  · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hA
    exact pnd_Pl_idem (Finset.mem_range.1 hb)

/-! ## FB0 and the six chosen edge-frame specifications -/

theorem pnd_mem_Lab0 {T : ℕ} (hT : T < 1771) : (xv T, yv T) ∈ Pnd.Lab0 := by
  unfold Pnd.Lab0
  exact Finset.mem_image_of_mem _ (Finset.mem_range.2 hT)

theorem pnd_mem_Pis0_Dm {o c : ℕ} (ho : o < codeBound) (hc : c < codeBound)
    (h : nestOK o c = true) : Dm o c ∈ Pnd.Pis0 := by
  rw [Pnd.Pis0, Finset.mem_union, Finset.mem_image]
  exact Or.inl ⟨(o, c), (pnd_mem_idxD _).2 ⟨⟨ho, hc⟩, h⟩, rfl⟩

theorem pnd_mem_Pis0_Pl {b : ℕ} (hb : b < 1771) : Pl b ∈ Pnd.Pis0 := by
  rw [Pnd.Pis0, Finset.mem_union]
  exact Or.inr (Finset.mem_image_of_mem _ (Finset.mem_range.2 hb))

/-- Once the absent generic flag-basis theorem supplies an inhabitant, the
published epsilon-selected basis satisfies `FB0`. -/
theorem pnd_spec0 (h : ∃ S Sinv, Pnd.FB0 S Sinv) : Pnd.FB0 Pnd.S0 Pnd.Si0 :=
  Classical.epsilon_spec (p := fun Sinv => Pnd.FB0 Pnd.S0 Sinv) (Classical.epsilon_spec h)

theorem pnd_pickE_spec {P : Edge 529 → Prop} (h : ∃ e, P e) : P (Pnd.pickE P) := by
  unfold Pnd.pickE
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem pnd_aux_PE {q : Matrix (Fin 529) (Fin 529) ℚ} (h : AuxE (h := 19) q) :
    ∃ e, Pnd.PE q Pnd.AuxR e := by
  obtain ⟨e, h1, h2⟩ := h
  exact ⟨e, h1, h2⟩

theorem pnd_side_PE {q : Matrix (Fin 529) (Fin 529) ℚ} {r : ℕ} (h : SideE (h := 19) q r) :
    ∃ e, Pnd.PE q (Pnd.SideR r) e := by
  obtain ⟨e, h1, rs', h2, h3, h4⟩ := h
  exact ⟨e, h1, rs', h2, h3, h4⟩

theorem pnd_data_PE {q : Matrix (Fin 529) (Fin 529) ℚ} (h : DataE (h := 19) q) :
    ∃ e, Pnd.PE q Pnd.DataR e := by
  obtain ⟨e, h1, rs', h2, h3, h4⟩ := h
  exact ⟨e, h1, rs', h2, h3, h4⟩

theorem pnd_fb_aux1 (hFB : Pnd.FB0 Pnd.S0 Pnd.Si0) {b : ℕ} (hb : b < 1771) :
    ∃ e, Pnd.PE (Pnd.K Pnd.S0 Pnd.Si0 1 (1 - Pl b)) Pnd.AuxR e :=
  pnd_aux_PE (hFB.2.2.1 (xv b, yv b) (pnd_mem_Lab0 hb)).1

theorem pnd_fb_aux2 (hFB : Pnd.FB0 Pnd.S0 Pnd.Si0) {a : ℕ} (ha : a < 1771) :
    ∃ e, Pnd.PE (Pnd.K Pnd.S0 Pnd.Si0 (1 - Pl a) 1) Pnd.AuxR e :=
  pnd_aux_PE (hFB.2.2.1 (xv a, yv a) (pnd_mem_Lab0 ha)).2

theorem pnd_fb_side1 (hFB : Pnd.FB0 Pnd.S0 Pnd.Si0) {b : ℕ} (hb : b < 1771)
    {A : M23} (hA : A ∈ Pnd.Pis0) :
    ∃ e, Pnd.PE (Pnd.K Pnd.S0 Pnd.Si0 A (Pl b)) (Pnd.SideR A.rank) e :=
  pnd_side_PE (hFB.2.2.2.1 (xv b, yv b) (pnd_mem_Lab0 hb) A hA).1

theorem pnd_fb_side2 (hFB : Pnd.FB0 Pnd.S0 Pnd.Si0) {a : ℕ} (ha : a < 1771)
    {A : M23} (hA : A ∈ Pnd.Pis0) :
    ∃ e, Pnd.PE (Pnd.K Pnd.S0 Pnd.Si0 (Pl a) A) (Pnd.SideR A.rank) e :=
  pnd_side_PE (hFB.2.2.2.1 (xv a, yv a) (pnd_mem_Lab0 ha) A hA).2

theorem pnd_fb_data (hFB : Pnd.FB0 Pnd.S0 Pnd.Si0) {a t : ℕ}
    (ha : a < 1771) (ht : t < 1771) :
    ∃ e, Pnd.PE (Pnd.K Pnd.S0 Pnd.Si0 (1 - Pl a) (1 - Pl t)) Pnd.DataR e :=
  pnd_data_PE (hFB.2.2.2.2 (xv a, yv a) (pnd_mem_Lab0 ha) (xv t, yv t) (pnd_mem_Lab0 ht))

theorem pnd_e1_spec (hFB : Pnd.FB0 Pnd.S0 Pnd.Si0) (hS : DensifiedSupportOK)
    {b o c : ℕ} (hb : b < 1771) (ho : o < codeBound) (hc : c < codeBound)
    (h : nestOK o c = true) :
    Pnd.PE (Pnd.K Pnd.S0 Pnd.Si0 (Dm o c) (Pl b)) (Pnd.SideR (rkC o c))
      (Pnd.ch0P.e1 b o c) := by
  show Pnd.PE _ _ (if b < 1771 ∧ o < codeBound ∧ c < codeBound then _ else _)
  rw [if_pos ⟨hb, ho, hc⟩]
  have he := pnd_fb_side1 hFB hb (pnd_mem_Pis0_Dm ho hc h)
  rw [(pnd_move_facts_of_support hS ho hc h).2.2] at he
  exact pnd_pickE_spec he

theorem pnd_e2_spec (hFB : Pnd.FB0 Pnd.S0 Pnd.Si0) (hS : DensifiedSupportOK)
    {a o c : ℕ} (ha : a < 1771) (ho : o < codeBound) (hc : c < codeBound)
    (h : nestOK o c = true) :
    Pnd.PE (Pnd.K Pnd.S0 Pnd.Si0 (Pl a) (Dm o c)) (Pnd.SideR (rkC o c))
      (Pnd.ch0P.e2 a o c) := by
  show Pnd.PE _ _ (if a < 1771 ∧ o < codeBound ∧ c < codeBound then _ else _)
  rw [if_pos ⟨ha, ho, hc⟩]
  have he := pnd_fb_side2 hFB ha (pnd_mem_Pis0_Dm ho hc h)
  rw [(pnd_move_facts_of_support hS ho hc h).2.2] at he
  exact pnd_pickE_spec he

theorem pnd_ex_spec (hFB : Pnd.FB0 Pnd.S0 Pnd.Si0) {b : ℕ} (hb : b < 1771) :
    Pnd.PE (Pnd.K Pnd.S0 Pnd.Si0 1 (1 - Pl b)) Pnd.AuxR (Pnd.ch0P.ex b) := by
  show Pnd.PE _ _ (if b < 1771 then _ else _)
  rw [if_pos hb]
  exact pnd_pickE_spec (pnd_fb_aux1 hFB hb)

theorem pnd_ei_spec (hFB : Pnd.FB0 Pnd.S0 Pnd.Si0) {a : ℕ} (ha : a < 1771) :
    Pnd.PE (Pnd.K Pnd.S0 Pnd.Si0 (1 - Pl a) 1) Pnd.AuxR (Pnd.ch0P.ei a) := by
  show Pnd.PE _ _ (if a < 1771 then _ else _)
  rw [if_pos ha]
  exact pnd_pickE_spec (pnd_fb_aux2 hFB ha)

theorem pnd_en_spec (hFB : Pnd.FB0 Pnd.S0 Pnd.Si0) {a t : ℕ}
    (ha : a < 1771) (ht : t < 1771) :
    Pnd.PE (Pnd.K Pnd.S0 Pnd.Si0 (1 - Pl a) (1 - Pl t)) Pnd.DataR (Pnd.ch0P.en a t) := by
  show Pnd.PE _ _ (if a < 1771 ∧ t < 1771 then _ else _)
  rw [if_pos ⟨ha, ht⟩]
  exact pnd_pickE_spec (pnd_fb_data hFB ha ht)

theorem pnd_ec_spec (hFB : Pnd.FB0 Pnd.S0 Pnd.Si0) {a s : ℕ}
    (ha : a < 1771) (hs : s < 1771) :
    Pnd.PE (Pnd.K Pnd.S0 Pnd.Si0 (Pl a) (Pl s)) (Pnd.SideR 1) (Pnd.ch0P.ec a s) := by
  show Pnd.PE _ _ (if a < 1771 ∧ s < 1771 then _ else _)
  rw [if_pos ⟨ha, hs⟩]
  have he := pnd_fb_side1 hFB hs (pnd_mem_Pis0_Pl ha)
  rw [pnd_Pl_rank ha] at he
  exact pnd_pickE_spec he

end IntMul.Kappa.R8.Bit.Oppbank.Net0Pnd
