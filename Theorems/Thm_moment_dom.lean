import Definitions.Def_IntMul_KappaFramework
import Theorems.Thm_IntMul_Kappa_histMoment_one

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace IntMul.Kappa

private def widthBin {α : Type*} [AddCommMonoid α] (h : List (ℕ × ℕ))
    (F : ℕ × ℕ → α) (w : ℕ) : α :=
  ((h.filter (fun p => p.1 = w)).map F).sum

private lemma sum_widthBins {α : Type*} [AddCommMonoid α] (h : List (ℕ × ℕ))
    (F : ℕ × ℕ → α) (n : ℕ) (hn : ∀ p ∈ h, p.1 < n) :
    (∑ w ∈ range n, widthBin h F w) = (h.map F).sum := by
  induction h with
  | nil => simp [widthBin]
  | cons p h ih =>
      have hp : p.1 < n := hn p (by simp)
      have hh : ∀ q ∈ h, q.1 < n := by
        intro q hq
        exact hn q (by simp [hq])
      calc
        (∑ w ∈ range n, widthBin (p :: h) F w) =
            ∑ w ∈ range n, ((if p.1 = w then F p else 0) + widthBin h F w) := by
          apply Finset.sum_congr rfl
          intro w hw
          by_cases hpw : p.1 = w <;> simp [widthBin, hpw]
        _ = (∑ w ∈ range n, if p.1 = w then F p else 0) +
            ∑ w ∈ range n, widthBin h F w := Finset.sum_add_distrib
        _ = F p + ∑ w ∈ range n, widthBin h F w := by
          rw [Finset.sum_ite_eq]
          simp [Finset.mem_range, hp]
        _ = F p + (h.map F).sum := by rw [ih hh]
        _ = ((p :: h).map F).sum := by simp

private def widthMass (h : List (ℕ × ℕ)) (w : ℕ) : ℕ :=
  widthBin h (fun p => p.1 * p.2) w

private def cumMass (h : List (ℕ × ℕ)) (x : ℕ) : ℕ :=
  (h.filter (fun p => p.1 ≤ x)).map (fun p => p.1 * p.2) |>.sum

private lemma sum_widthMass (h : List (ℕ × ℕ)) (x : ℕ) :
    (∑ w ∈ range (x + 1), widthMass h w) = cumMass h x := by
  let hx := h.filter (fun p => p.1 ≤ x)
  have hbound : ∀ p ∈ hx, p.1 < x + 1 := by
    intro p hp
    have hp' : p.1 ≤ x := by
      exact of_decide_eq_true (List.mem_filter.mp hp).2
    omega
  have hs := sum_widthBins hx (fun p => p.1 * p.2) (x + 1) hbound
  change (∑ w ∈ range (x + 1), widthMass h w) = (hx.map (fun p => p.1 * p.2)).sum
  rw [← hs]
  apply Finset.sum_congr rfl
  intro w hw
  apply congrArg (fun l : List (ℕ × ℕ) => (l.map (fun p => p.1 * p.2)).sum)
  simp only [hx, widthMass, widthBin, List.filter_filter]
  apply List.filter_congr
  intro p hp
  have hwx : w ≤ x := by
    simp only [Finset.mem_range] at hw
    omega
  by_cases hpw : p.1 = w
  · simp [hpw, hwx]
  · simp [hpw]


private lemma widthBin_cons {α : Type*} [AddCommMonoid α] (p : ℕ × ℕ)
    (h : List (ℕ × ℕ)) (F : ℕ × ℕ → α) (w : ℕ) :
    widthBin (p :: h) F w = if p.1 = w then F p + widthBin h F w else widthBin h F w := by
  by_cases hp : p.1 = w <;> simp [widthBin, hp]

private lemma widthMass_cons (p : ℕ × ℕ) (h : List (ℕ × ℕ)) (w : ℕ) :
    widthMass (p :: h) w =
      if p.1 = w then p.1 * p.2 + widthMass h w else widthMass h w := by
  simpa only [widthMass] using widthBin_cons p h (fun p => p.1 * p.2) w

private lemma widthMass_zero (h : List (ℕ × ℕ)) : widthMass h 0 = 0 := by
  induction h with
  | nil => rfl
  | cons p h ih =>
      rw [widthMass_cons]
      by_cases hp : p.1 = 0 <;> simp [hp, ih]

private lemma widthMoment_zero (h : List (ℕ × ℕ)) (m : ℕ) (τ : ℝ) (hτ : 0 < τ) :
    widthBin h (fun p => (p.2 : ℝ) * ((p.1 : ℝ) / m) ^ τ) 0 = 0 := by
  induction h with
  | nil => rfl
  | cons p h ih =>
      rw [widthBin_cons]
      by_cases hp : p.1 = 0
      · simp [hp, ih, Real.zero_rpow (ne_of_gt hτ)]
      · simp [hp, ih]

private lemma widthMoment_eq (h : List (ℕ × ℕ)) (m : ℕ) (hm : 0 < m)
    (τ : ℝ) (w : ℕ) (hw : 0 < w) :
    widthBin h (fun p => (p.2 : ℝ) * ((p.1 : ℝ) / m) ^ τ) w =
      (widthMass h w : ℝ) * ((w : ℝ) ^ (τ - 1) / (m : ℝ) ^ τ) := by
  have hfactor : ∀ p : ℕ × ℕ, p.1 = w →
      (p.2 : ℝ) * ((p.1 : ℝ) / m) ^ τ =
        ((p.1 * p.2 : ℕ) : ℝ) * ((w : ℝ) ^ (τ - 1) / (m : ℝ) ^ τ) := by
    intro p hp
    subst w
    have hwR : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast hw
    rw [Nat.cast_mul, Real.div_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _),
      Real.rpow_sub hwR, Real.rpow_one]
    field_simp [ne_of_gt hwR]
  induction h with
  | nil => simp [widthBin, widthMass]
  | cons p h ih =>
      rw [widthBin_cons, widthMass_cons]
      by_cases hp : p.1 = w
      · rw [if_pos hp, if_pos hp, Nat.cast_add, hfactor p hp, ih]
        ring
      · rw [if_neg hp, if_neg hp, ih]

private lemma cumMass_eq_rankSum (h : List (ℕ × ℕ)) (x : ℕ)
    (hx : ∀ p ∈ h, p.1 ≤ x) : cumMass h x = histRankSum h := by
  have hf : h.filter (fun p => p.1 ≤ x) = h := by
    apply List.filter_eq_self.mpr
    intro p hp
    simp [hx p hp]
  simp only [cumMass, histRankSum, hf]


private lemma momentWeight_antitone (m : ℕ) (τ : ℝ) (hτ : τ < 1)
    {i j : ℕ} (hi : 0 < i) (hij : i ≤ j) :
    (j : ℝ) ^ (τ - 1) / (m : ℝ) ^ τ ≤ (i : ℝ) ^ (τ - 1) / (m : ℝ) ^ τ := by
  apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg m) τ)
  apply (Real.rpow_le_rpow_iff_of_neg (by exact_mod_cast (lt_of_lt_of_le hi hij))
    (by exact_mod_cast hi) (by linarith)).2
  exact_mod_cast hij

/-- Abel summation turns cumulative weighted-mass domination into domination of
concave child-width moments.  Zero-filled width bins let us sum over an initial
segment of the naturals; no additional sorting construction is needed. -/
theorem moment_dom (hA hB : List (ℕ × ℕ)) (m : ℕ) (hm : 0 < m)
    (h_cum : ∀ x : ℕ,
      ((hA.filter (fun p : ℕ × ℕ => p.1 ≤ x)).map (fun p : ℕ × ℕ => p.1 * p.2)).sum ≤
      ((hB.filter (fun p : ℕ × ℕ => p.1 ≤ x)).map (fun p : ℕ × ℕ => p.1 * p.2)).sum)
    (h_total : histRankSum hA = histRankSum hB) :
    ∀ τ : ℝ, 0 < τ → τ ≤ 1 → histMoment hA m τ ≤ histMoment hB m τ := by
  intro τ hτ hτ1
  rcases eq_or_lt_of_le hτ1 with heq | hlt
  · subst τ
    rw [histMoment_one hA m hm, histMoment_one hB m hm, h_total]
  · let M := (hA.map Prod.fst).sum + (hB.map Prod.fst).sum
    have hA_bound : ∀ p ∈ hA, p.1 ≤ M := by
      intro p hp
      have hle : p.1 ≤ (hA.map Prod.fst).sum := by
        apply List.single_le_sum (fun x hx => Nat.zero_le x) p.1
        exact List.mem_map.mpr ⟨p, hp, rfl⟩
      dsimp [M]
      omega
    have hB_bound : ∀ p ∈ hB, p.1 ≤ M := by
      intro p hp
      have hle : p.1 ≤ (hB.map Prod.fst).sum := by
        apply List.single_le_sum (fun x hx => Nat.zero_le x) p.1
        exact List.mem_map.mpr ⟨p, hp, rfl⟩
      dsimp [M]
      omega
    have hA_bound' : ∀ p ∈ hA, p.1 < M + 1 := by
      intro p hp
      have hle := hA_bound p hp
      omega
    have hB_bound' : ∀ p ∈ hB, p.1 < M + 1 := by
      intro p hp
      have hle := hB_bound p hp
      omega
    let f : ℕ → ℝ := fun w => (w : ℝ) ^ (τ - 1) / (m : ℝ) ^ τ
    let g : ℕ → ℝ := fun w => (widthMass hA w : ℝ) - (widthMass hB w : ℝ)
    have hG (x : ℕ) : (∑ w ∈ range (x + 1), g w) =
        (cumMass hA x : ℝ) - (cumMass hB x : ℝ) := by
      dsimp [g]
      rw [Finset.sum_sub_distrib, ← Nat.cast_sum, ← Nat.cast_sum,
        sum_widthMass, sum_widthMass]
    have hG_nonpos (i : ℕ) : (∑ w ∈ range (i + 1), g w) ≤ 0 := by
      rw [hG]
      apply sub_nonpos.mpr
      exact_mod_cast h_cum i
    have hG_one : (∑ w ∈ range 1, g w) = 0 := by
      simp [g, widthMass_zero]
    have hG_total : (∑ w ∈ range (M + 1), g w) = 0 := by
      rw [hG, cumMass_eq_rankSum hA M hA_bound, cumMass_eq_rankSum hB M hB_bound,
        h_total]
      simp
    have hmA : (∑ w ∈ range (M + 1),
        widthBin hA (fun p => (p.2 : ℝ) * ((p.1 : ℝ) / m) ^ τ) w) =
        histMoment hA m τ := by
      exact sum_widthBins hA _ (M + 1) hA_bound'
    have hmB : (∑ w ∈ range (M + 1),
        widthBin hB (fun p => (p.2 : ℝ) * ((p.1 : ℝ) / m) ^ τ) w) =
        histMoment hB m τ := by
      exact sum_widthBins hB _ (M + 1) hB_bound'
    have hmoment : histMoment hA m τ - histMoment hB m τ =
        ∑ i ∈ range (M + 1), f i * g i := by
      rw [← hmA, ← hmB, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hi0 : i = 0
      · subst i
        rw [widthMoment_zero hA m τ hτ, widthMoment_zero hB m τ hτ]
        simp [g, widthMass_zero]
      · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
        rw [widthMoment_eq hA m hm τ i hipos, widthMoment_eq hB m hm τ i hipos]
        dsimp [f, g]
        ring
    have hterm (i : ℕ) : 0 ≤ (f (i + 1) - f i) * ∑ w ∈ range (i + 1), g w := by
      by_cases hi0 : i = 0
      · subst i
        simp [g, widthMass_zero]
      · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
        have hf : f (i + 1) ≤ f i := by
          dsimp [f]
          exact momentWeight_antitone m τ hlt hipos (Nat.le_succ i)
        exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hf) (hG_nonpos i)
    have hsum_nonneg : 0 ≤
        ∑ i ∈ range M, (f (i + 1) - f i) * ∑ w ∈ range (i + 1), g w := by
      exact Finset.sum_nonneg (fun i hi => hterm i)
    have hAbel := Finset.sum_range_by_parts f g (M + 1)
    have hAbel' : (∑ i ∈ range (M + 1), f i * g i) =
        -∑ i ∈ range M, (f (i + 1) - f i) * ∑ w ∈ range (i + 1), g w := by
      simpa only [smul_eq_mul, hG_total, mul_zero, zero_sub, Nat.add_sub_cancel] using hAbel
    have hdiff : histMoment hA m τ - histMoment hB m τ ≤ 0 := by
      rw [hmoment, hAbel']
      linarith
    linarith

end IntMul.Kappa
