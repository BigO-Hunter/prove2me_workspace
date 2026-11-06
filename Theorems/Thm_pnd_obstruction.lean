import Theorems.Thm_pnd_certificates
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

/-!
# A concrete obstruction in the published densified `Pis0`

The first two densified supports are the distinct singleton triple masks `7`
and `11`, while `argRel 0 1` is true.  Consequently `(1773,1774)` belongs
to `idxD`, although its two rank-one projectors are not nested.  This file
proves that the requested universal `hPis0` and `Dm_rank` statements are
false as the definitions currently stand.  It does `not` assert that
`FormalOK` itself is false; it shows that the prescribed `FB0` route cannot
be used without correcting the densified nest/support data.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.Net0Pnd

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG
open Matrix Module

theorem spanS_pow (T : ℕ) : spanS (2 ^ T) = ℚ ∙ tvQ T := by
  unfold spanS
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro v ⟨i, hi, rfl⟩
    rw [Nat.testBit_two_pow] at hi
    have hTi : T = i := by simpa using hi
    subst i
    exact Submodule.mem_span_singleton_self _
  · apply Submodule.span_mono
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    subst v
    exact ⟨T, by simp, rfl⟩

theorem tvQ_ne {T : ℕ} (hT : T < 1771) : tvQ T ≠ 0 := by
  intro h
  have hs : ∑ p : Fin 23, tvQ T p = 3 := NetFB.sum_tvQ hT
  rw [h] at hs
  simp at hs

theorem finrank_spanS_pow {T : ℕ} (hT : T < 1771) : finrank ℚ (spanS (2 ^ T)) = 1 := by
  rw [spanS_pow, finrank_span_singleton (tvQ_ne hT)]

theorem hasCentre_single {T c : ℕ} (hc : c < 23) (hT : T < 1771)
    (hct : (triL T).testBit c = true) : HasCentre (2 ^ T) := by
  refine ⟨c, hc, ?_⟩
  intro i hi
  rw [Nat.testBit_two_pow] at hi
  have hTi : T = i := by simpa using hi
  subst i
  exact ⟨hT, hct, NetFB.sum_tvQ hT⟩

theorem tvQ0_not_mem_span1 : tvQ 0 ∉ spanS (2 ^ 1) := by
  intro hv
  let j : Fin 23 := ⟨2, by decide⟩
  let H : Submodule ℚ V23 :=
    { carrier := {v | v j = 0}
      add_mem' := by
        intro a b ha hb
        change a j = 0 at ha
        change b j = 0 at hb
        simp [ha, hb]
      zero_mem' := by simp
      smul_mem' := by
        intro r a ha
        change a j = 0 at ha
        simp [ha] }
  have hle : spanS (2 ^ 1) ≤ H := by
    rw [spanS, Submodule.span_le]
    rintro v ⟨i, hi, rfl⟩
    rw [Nat.testBit_two_pow] at hi
    have hTi : 1 = i := by simpa using hi
    subst i
    show tvQ 1 j = 0
    decide +kernel
  have hz : tvQ 0 j = 0 := hle hv
  have ho : tvQ 0 j = 1 := by decide +kernel
  rw [ho] at hz
  exact one_ne_zero hz

theorem dens0_eq : SupG.densSupG 0 = 2 ^ 0 := by decide +kernel
theorem dens1_eq : SupG.densSupG 1 = 2 ^ 1 := by decide +kernel

theorem centre0 : HasCentre (SupG.densSupG 0) := by
  rw [dens0_eq]
  exact hasCentre_single (c := 0) (by decide) (by decide) (by decide +kernel)

theorem centre1 : HasCentre (SupG.densSupG 1) := by
  rw [dens1_eq]
  exact hasCentre_single (c := 0) (by decide) (by decide) (by decide +kernel)

theorem Pc1773_eq : Pc 1773 = Pnd.Pnd (SupG.densSupG 0) := by
  simpa [PndD] using Pc_of_ND 0 (by decide)

theorem Pc1774_eq : Pc 1774 = Pnd.Pnd (SupG.densSupG 1) := by
  simpa [PndD] using Pc_of_ND 1 (by decide)

theorem Pc1773_rank : (Pc 1773).rank = 1 := by
  rw [Pc1773_eq, dens0_eq, pnd_Pnd_rank (by simpa [dens0_eq] using centre0),
    finrank_spanS_pow (by decide)]

theorem Pc1774_rank : (Pc 1774).rank = 1 := by
  rw [Pc1774_eq, dens1_eq, pnd_Pnd_rank (by simpa [dens1_eq] using centre1),
    finrank_spanS_pow (by decide)]

theorem Pc1773_idem : Pc 1773 * Pc 1773 = Pc 1773 := by
  rw [Pc1773_eq]
  exact pnd_Pnd_idem centre0

theorem Pc1774_idem : Pc 1774 * Pc 1774 = Pc 1774 := by
  rw [Pc1774_eq]
  exact pnd_Pnd_idem centre1

theorem Pc1774_ne_Pc1773 : Pc 1774 ≠ Pc 1773 := by
  intro heq
  have hp0 : IsPrj (Pc 1773) (spanS (SupG.densSupG 0)) := by
    rw [Pc1773_eq]
    exact pnd_Pnd_prj centre0
  have hp1 : IsPrj (Pc 1774) (spanS (SupG.densSupG 1)) := by
    rw [Pc1774_eq]
    exact pnd_Pnd_prj centre1
  have hv0 : Pc 1773 *ᵥ tvQ 0 = tvQ 0 := by
    apply hp0.1
    apply Submodule.subset_span
    exact ⟨0, by rw [dens0_eq]; simp, rfl⟩
  have hv : tvQ 0 ∈ spanS (SupG.densSupG 1) := by
    have hm := (pnd_IsPrj_mem (compl_spanS centre1) hp1 (tvQ 0)).1
    rw [heq, hv0] at hm
    exact hm
  rw [dens1_eq] at hv
  exact tvQ0_not_mem_span1 hv

theorem nest_1773_1774 : nestOK 1773 1774 = true := by decide +kernel

theorem idxD_1773_1774 : (1773, 1774) ∈ Pnd.idxD :=
  (pnd_mem_idxD _).2 ⟨⟨by decide, by decide⟩, nest_1773_1774⟩

theorem Dm_1773_1774 : Dm 1773 1774 = Pc 1774 - Pc 1773 := by
  have hd : dimCF 1773 = dimCF 1774 := by decide +kernel
  rw [Dm, if_pos (Nat.le_of_eq hd)]

theorem eq_of_sub_rank_zero {A B : M23} (h : (B - A).rank = 0) : B = A := by
  have hrange : LinearMap.range (B - A).mulVecLin = ⊥ := Submodule.finrank_eq_zero.1 h
  have hlin : (B - A).mulVecLin = 0 := LinearMap.range_eq_bot.1 hrange
  have hz : B - A = 0 := by
    ext i j
    have hij := congrArg (fun f => f (Pi.single j 1) i) hlin
    simpa [Matrix.mulVec_single] using hij
  exact sub_eq_zero.1 hz

/-- The requested `pnd_hPis0` proposition is false. -/
theorem not_hPis0 : ¬ (∀ A ∈ Pnd.Pis0, A * A = A) := by
  intro hall
  have hmem : Dm 1773 1774 ∈ Pnd.Pis0 :=
    pnd_mem_Pis0_Dm (by decide) (by decide) nest_1773_1774
  have hid := hall _ hmem
  rw [Dm_1773_1774] at hid
  have ht := pnd_rank_idem hid
  rw [Matrix.trace_sub, ← pnd_rank_idem Pc1774_idem, ← pnd_rank_idem Pc1773_idem,
    Pc1773_rank, Pc1774_rank] at ht
  norm_num at ht
  have hr : (Pc 1774 - Pc 1773).rank = 0 := by exact_mod_cast ht
  exact Pc1774_ne_Pc1773 (eq_of_sub_rank_zero hr)

/-- The requested `pnd_Dm_rank` proposition is also false at the same pair. -/
theorem not_Dm_rank :
    ¬ (∀ {o c : ℕ}, (o, c) ∈ Pnd.idxD → (Pnd.Dm o c).rank = Pnd.rkC o c) := by
  intro hall
  have hr := hall idxD_1773_1774
  have hrk : rkC 1773 1774 = 0 := by decide +kernel
  rw [Dm_1773_1774, hrk] at hr
  exact Pc1774_ne_Pc1773 (eq_of_sub_rank_zero hr)

/-- Hence the exact support interface used in the conditional development is
not a merely unfinished certificate: it cannot be inhabited for these data. -/
theorem not_DensifiedSupportOK : ¬ DensifiedSupportOK := by
  intro h
  exact not_hPis0 (pnd_hPis0_of_support h)

end IntMul.Kappa.R8.Bit.Oppbank.Net0Pnd
