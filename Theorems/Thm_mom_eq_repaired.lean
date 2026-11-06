import Theorems.Thm_repaired_ch0R
import Theorems.Thm_bitR8_le_bitR7plain_mom
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 200000

/-!
# Raw-network moment and elementary certificates for the repaired net

`Repaired.repaired.hist` is the aggregated census, whereas `QHNet.hist` stores
one pair `(w, 1)` per child.  The list/Finset lemmas below identify their
moments, so the compiled census equality really does prove the raw network's
`mom_eq` obligation.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.Repaired

open IntMul.Kappa
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank

/-- Sum over a list range as a Finset sum. -/
theorem sum_list_range (f : ℕ → ℝ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ w ∈ Finset.range n, f w := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.range_succ, ih, Finset.sum_range_succ]

/-- A bounded list's weighted sum is its census-weighted sum. -/
theorem sum_map_eq_count_sum (g : ℕ → ℝ) :
    ∀ xs : List ℕ, (∀ w ∈ xs, w < 529) →
      (xs.map g).sum = ∑ w ∈ Finset.range 529, (xs.count w : ℝ) * g w := by
  intro xs
  induction xs with
  | nil => intro h; simp
  | cons x xs ih =>
      intro hbound
      have hx : x < 529 := hbound x (by simp)
      have hxs : ∀ w ∈ xs, w < 529 := by
        intro w hw
        exact hbound w (by simp [hw])
      simp only [List.map_cons, List.sum_cons]
      rw [ih hxs]
      have hpoint : ∀ w : ℕ, (((x :: xs).count w : ℕ) : ℝ) * g w =
          (xs.count w : ℝ) * g w + if x = w then g w else 0 := by
        intro w
        rw [List.count_cons]
        by_cases hxw : x = w
        · subst w
          simp [add_mul]
        · have hbeq : (x == w) = false := by simp [hxw]
          simp [hbeq, hxw]
      rw [Finset.sum_congr rfl (fun w _ => hpoint w), Finset.sum_add_distrib]
      have hsingle : (∑ w ∈ Finset.range 529, if x = w then g w else 0) = g x := by
        simp [hx]
      rw [hsingle]
      ring

/-- The aggregated census has the same range-count moment formula. -/
theorem histMoment_census (xs : List ℕ) (m : ℕ) (τ : ℝ) :
    histMoment (census xs) m τ =
      ((List.range 529).map fun w =>
        (xs.count w : ℝ) * (((w : ℝ) / m) ^ τ)).sum := by
  unfold census censusWith histMoment
  generalize List.range 529 = ws
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      simp only [List.filterMap_cons, List.map_cons, List.sum_cons]
      by_cases h : xs.count w = 0
      · simp [h, ih]
      · simp [h, ih]

/-- The one-per-child histogram of any width list has the unweighted width sum. -/
theorem histMoment_map_one (xs : List ℕ) (m : ℕ) (τ : ℝ) :
    histMoment (xs.map fun w => (w, 1)) m τ =
      (xs.map (fun w : ℕ => (((w : ℝ) / m) ^ τ))).sum := by
  unfold histMoment
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro w hw
  simp

/-- Every raw repaired width lies in the census range. -/
theorem repairedNet_width_lt {w : ℕ} (hw : w ∈ repairedNet.widths) : w < 529 := by
  by_contra h
  have hn : repairedNet.widths.count w ≠ 0 := by
    intro hz
    exact (List.count_eq_zero.1 hz) hw
  apply hn
  rw [repaired_width_count_explicit]
  have h23 : ¬ w < 23 := by omega
  simp [sideTargetCount, otherTargetCount, h, h23]

/-- Generic raw-to-census moment bridge.  Keeping the network symbolic here is
important: unification never expands the repaired program. -/
theorem histMoment_raw_eq_census {W T : ℕ}
    (C : QHNet (ZMod 2) W T 529) (hbound : ∀ w ∈ C.widths, w < 529) (τ : ℝ) :
    histMoment C.hist 529 τ = histMoment (census (C.hist.map Prod.fst)) 529 τ := by
  change histMoment (C.widths.map fun w => (w, 1)) 529 τ =
    histMoment (census ((C.widths.map fun w => (w, 1)).map Prod.fst)) 529 τ
  have hfst : (C.widths.map fun w => (w, 1)).map Prod.fst = C.widths := by
    simp [List.map_map, Function.comp_def]
  rw [hfst]
  calc
    histMoment (C.widths.map fun w => (w, 1)) 529 τ =
        (C.widths.map (fun w : ℕ => (((w : ℝ) / 529) ^ τ))).sum :=
      histMoment_map_one _ _ _
    _ = ∑ w ∈ Finset.range 529, (C.widths.count w : ℝ) *
        (((w : ℝ) / 529) ^ τ) := sum_map_eq_count_sum _ _ hbound
    _ = ((List.range 529).map fun w => (C.widths.count w : ℝ) *
        (((w : ℝ) / 529) ^ τ)).sum := (sum_list_range _ _).symm
    _ = histMoment (census C.widths) 529 τ := (histMoment_census _ _ _).symm

/-- **mom_eq for the repaired raw QHNet**, not merely for its aggregated census. -/
theorem repairedNet_mom_eq (τ : ℝ) :
    histMoment repairedNet.hist 529 τ = histMoment IntMul.Kappa.Jain.bitR8 529 τ := by
  calc
    histMoment repairedNet.hist 529 τ =
        histMoment (census (repairedNet.hist.map Prod.fst)) 529 τ :=
      histMoment_raw_eq_census repairedNet (fun w hw => repairedNet_width_lt hw) τ
    _ = histMoment repaired.hist 529 τ := rfl
    _ = histMoment IntMul.Kappa.Jain.bitR8 529 τ := by rw [repaired_hist_eq_bitR8]

/-- The same identity phrased directly for `net ch0R`. -/
theorem net_ch0R_mom_eq (τ : ℝ) :
    histMoment (net ch0R).hist 529 τ = histMoment IntMul.Kappa.Jain.bitR8 529 τ :=
  repairedNet_mom_eq τ

/-! Elementary bounds and one-run certificates, used by RunsOK/EdgesOK. -/

theorem sideSchedule1_valid : ∀ w ∈ sideSchedule1, 0 < w ∧ w < 529 := by
  native_decide

theorem sideSchedule2_valid : ∀ w ∈ sideSchedule2, 0 < w ∧ w < 529 := by
  native_decide

theorem auxWidth_valid : ∀ s ∈ List.range NR, 0 < auxWidth s ∧ auxWidth s < 529 := by
  native_decide

/-- A one-run edge whose width satisfies the repaired census bounds. -/
def ValidOneEdge (e : Edge 529) : Prop :=
  ∃ w, 0 < w ∧ w < 529 ∧ e = oneEdge w

theorem runOK_oneRun {w : ℕ} (h0 : 0 < w) (hm : w < 529) : RunOK 529 (oneRun w) := by
  show 0 < w ∧ w < 529 ∧ 0 + w ≤ 529 ∧ (529 - w) + w ≤ 529
  omega

theorem validOneEdge_runsOK {e : Edge 529} (he : ValidOneEdge e) :
    ∀ ρ ∈ e.runs, RunOK 529 ρ := by
  obtain ⟨w, h0, hm, rfl⟩ := he
  intro ρ hρ
  have hρ' : ρ = oneRun w := by simpa [oneEdge] using hρ
  subst ρ
  exact runOK_oneRun h0 hm

theorem redQ_one (N : ℕ) : AModelFac.redQ N 1 = 1 := by
  have hd : Nat.Coprime ((1 : ℚ).den) N := by
    rw [Rat.den_one]
    exact Nat.coprime_one_left N
  unfold AModelFac.redQ AModelFac.toGood
  rw [dif_pos hd]
  show AModelFac.redHom N (⟨(1 : ℚ), hd⟩ : AModelFac.goodSub N) = 1
  exact (AModelFac.redHom N).map_one

theorem oneEdge_EdgeOK (N : ℕ) (w : ℕ) : EdgeOK N (oneEdge w) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij
    show (1 : QMat2 529) i j = 0
    exact Matrix.one_apply_ne (ne_of_lt hij)
  · intro i j hij
    show (1 : QMat2 529) i j = 0
    exact Matrix.one_apply_ne (ne_of_lt hij)
  · intro i
    have h : ((1 : QMat2 529) i i) = 1 := by simp
    show IsUnit (AModelFac.redQ N ((1 : QMat2 529) i i))
    rw [h, redQ_one]
    exact isUnit_one
  · intro i
    have h : ((1 : QMat2 529) i i) = 1 := by simp
    show IsUnit (AModelFac.redQ N ((1 : QMat2 529) i i))
    rw [h, redQ_one]
    exact isUnit_one

/-- Every program edge of the repaired network is a bounded one-run edge. -/
theorem repairedNet_valid_edges : ∀ e ∈ repairedNet.edges, ValidOneEdge e := by
  intro e he
  obtain ⟨i, hi, hie⟩ := List.mem_filterMap.1 he
  change i ∈ (List.range v).flatMap (blk1 ch0R) ++
    (List.range v).flatMap (blk2 ch0R) at hi
  rcases List.mem_append.1 hi with hi | hi
  · obtain ⟨b, hb, hi⟩ := List.mem_flatMap.1 hi
    unfold blk1 at hi
    rcases List.mem_append.1 hi with hi | hi
    · unfold sideProg at hi
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hi
      obtain ⟨h0, hm⟩ := sideSchedule1_valid r hr
      refine ⟨r, h0, hm, ?_⟩
      simpa [ch0R] using (Option.some.inj hie).symm
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hi
      obtain ⟨k, hk, hwk⟩ := List.mem_range'.1 hw
      have hs : w - wEnt ∈ List.range NR := by
        apply List.mem_range.mpr
        omega
      obtain ⟨h0, hm⟩ := auxWidth_valid (w - wEnt) hs
      refine ⟨auxWidth (w - wEnt), h0, hm, ?_⟩
      simpa [ch0R] using (Option.some.inj hie).symm
  · obtain ⟨a, ha, hi⟩ := List.mem_flatMap.1 hi
    unfold blk2 at hi
    rcases List.mem_append.1 hi with hi | hi
    · unfold entI at hi
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hi
      have heq : e = entE ch0R a w := (Option.some.inj hie).symm
      unfold entE at heq
      split_ifs at heq with hvw hwent
      · exact ⟨484, by norm_num, by norm_num, by simpa [ch0R] using heq⟩
      · exact ⟨484, by norm_num, by norm_num, by simpa [ch0R] using heq⟩
      · have hw' : w < wAuxEnd := List.mem_range.1 hw
        have hwe : wEnt ≤ w := Nat.le_of_not_gt hwent
        have hs : w - wEnt ∈ List.range NR := by
          apply List.mem_range.mpr
          simp only [wAuxEnd, wEnt, NR] at hw' hwe ⊢
          omega
        obtain ⟨h0, hm⟩ := auxWidth_valid (w - wEnt) hs
        exact ⟨auxWidth (w - wEnt), h0, hm, by simpa [ch0R] using heq⟩
    rcases List.mem_append.1 hi with hi | hi
    · unfold sideProg at hi
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hi
      obtain ⟨h0, hm⟩ := sideSchedule2_valid r hr
      refine ⟨r, h0, hm, ?_⟩
      simpa [ch0R] using (Option.some.inj hie).symm
    · obtain ⟨s, hs, hi⟩ := List.mem_flatMap.1 hi
      unfold corrI at hi
      rcases List.mem_cons.1 hi with rfl | hi
      · cases hie
      rcases List.mem_cons.1 hi with rfl | hi
      · refine ⟨1, by norm_num, by norm_num, ?_⟩
        simpa [ch0R] using (Option.some.inj hie).symm
      rcases List.mem_cons.1 hi with rfl | hi
      · cases hie
      · exact absurd hi List.not_mem_nil

/-- All runs of the repaired network satisfy `RunOK`. -/
theorem repairedNet_RunsOK : repairedNet.RunsOK := by
  intro e he ρ hρ
  exact validOneEdge_runsOK (repairedNet_valid_edges e he) ρ hρ

theorem net_ch0R_RunsOK : (net ch0R).RunsOK := repairedNet_RunsOK

/-- Trivial identity Bruhat factors pass `EdgeOK` at every modulus. -/
theorem repairedNet_EdgesOK (N : ℕ) : repairedNet.EdgesOK N := by
  intro e he
  obtain ⟨w, h0, hm, rfl⟩ := repairedNet_valid_edges e he
  exact oneEdge_EdgeOK N w

/-- Uniform large-prime clearance; in fact the repaired edge checks hold at
every modulus, so the bound is zero. -/
theorem repairedNet_EdgesOK_large :
    ∃ q₀ : ℕ, ∀ q, q.Prime → q₀ < q → ∀ f : ℕ, repairedNet.EdgesOK (q ^ f) := by
  exact ⟨0, fun q hq hq₀ f => repairedNet_EdgesOK (q ^ f)⟩

theorem net_ch0R_EdgesOK_large :
    ∃ q₀ : ℕ, ∀ q, q.Prime → q₀ < q → ∀ f : ℕ, (net ch0R).EdgesOK (q ^ f) :=
  repairedNet_EdgesOK_large

end IntMul.Kappa.R8.Bit.Oppbank.Repaired
