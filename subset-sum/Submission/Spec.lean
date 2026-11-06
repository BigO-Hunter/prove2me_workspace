import Submission.SubsetSumStatement
set_option autoImplicit true

/-!
# The mathematical core: MITM correctness (R2125607414, spec layer)

Program-independent theorems.  `isSum a n t` says: some subset of the first
`n` values of `a` (as a Boolean choice, eventually false) sums to `t`.
Everything here is Nat arithmetic and `List.range`/`List.sum` splits —
deliberately `Fin`-free.
-/

namespace SubsetSum.MITM.Spec

open BigOSpeedrun.SubsetSum

/-- The choice-sum of `S` over the first `n` indices. -/
def choiceSum (a : Nat → Nat) (S : Nat → Bool) (n : Nat) : Nat :=
  ((List.range n).map fun i => if S i then a i else 0).sum

/-- `t` is a subset sum of the first `n` values of `a`. -/
def isSum (a : Nat → Nat) (n t : Nat) : Prop :=
  ∃ S : Nat → Bool, (∀ i, n ≤ i → S i = false) ∧ choiceSum a S n = t

/-! ## Step lemmas -/

theorem choiceSum_succ (a : Nat → Nat) (S : Nat → Bool) (n : Nat) :
    choiceSum a S (n + 1) = (if S n then a n else 0) + choiceSum a S n := by
  simp only [choiceSum, List.range_succ]
  rw [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
  exact Nat.add_comm _ _

theorem isSum_zero (a : Nat → Nat) (t : Nat) : isSum a 0 t ↔ t = 0 := by
  constructor
  · rintro ⟨S, _, h⟩
    simp only [choiceSum, List.range_zero, List.map_nil, List.sum_nil] at h
    exact h.symm
  · intro ht
    subst ht
    exact ⟨fun _ => false, by simp, by simp [choiceSum]⟩

theorem isSum_succ (a : Nat → Nat) (n t : Nat) :
    isSum a (n + 1) t ↔ isSum a n t ∨ ∃ t', isSum a n t' ∧ t' + a n = t := by
  constructor
  · rintro ⟨S, hS, hSum⟩
    rw [choiceSum_succ] at hSum
    -- S restricted: index n forced false — the isSum-a-n witness either way
    have hS2 : ∀ i, n ≤ i → (fun i => if i = n then false else S i) i = false := by
      intro i hi
      by_cases h : i = n
      · subst h; simp
      · simp only [if_neg h]; exact hS i (by omega)
    have hc : choiceSum a (fun i => if i = n then false else S i) n = choiceSum a S n := by
      simp only [choiceSum]
      congr 1
      exact List.map_congr_left fun i hi => by
            have hlt := List.mem_range.mp hi
            by_cases h : i = n
            · omega
            · simp [h]
    by_cases h : S n
    · right
      rw [if_pos h] at hSum
      refine ⟨t - a n, ⟨fun i => if i = n then false else S i, hS2, by omega⟩, by omega⟩
    · left
      rw [if_neg h] at hSum
      have hz : choiceSum a S n = t := by omega
      exact ⟨fun i => if i = n then false else S i, hS2, hc ▸ hz⟩
  · rintro (⟨S, hS, hSum⟩ | ⟨t', ⟨S, hS, hSum'⟩, ht'⟩)
    · refine ⟨fun i => if i = n then false else S i, ?_, ?_⟩
      · intro i hi
        by_cases h : i = n
        · omega
        · simp only [if_neg h]; exact hS i (by omega)
      · rw [choiceSum_succ, if_neg (by simp)]
        have hc : choiceSum a (fun i => if i = n then false else S i) n
            = choiceSum a S n := by
          simp only [choiceSum]
          congr 1
          exact List.map_congr_left fun i hi => by
            have hlt := List.mem_range.mp hi
            by_cases h : i = n
            · omega
            · simp [h]
        rw [hc]
        omega
    · refine ⟨fun i => if i = n then true else S i, ?_, ?_⟩
      · intro i hi
        by_cases h : i = n
        · omega
        · simp only [if_neg h]; exact hS i (by omega)
      · rw [choiceSum_succ, if_pos (by simp)]
        have hc : choiceSum a (fun i => if i = n then true else S i) n
            = choiceSum a S n := by
          simp only [choiceSum]
          congr 1
          exact List.map_congr_left fun i hi => by
            have hlt := List.mem_range.mp hi
            by_cases h : i = n
            · omega
            · simp [h]
        rw [hc, hSum']
        omega

/-! ## The split -/

theorem choiceSum_split (a : Nat → Nat) (S : Nat → Bool) (h n : Nat) :
    choiceSum a S (h + n) = choiceSum a S h
      + choiceSum (fun i => a (i + h)) (fun i => S (i + h)) n := by
  induction n with
  | zero => simp [choiceSum]
  | succ k ih =>
      have e1 : h + (k + 1) = (h + k) + 1 := by omega
      have e2 : k + h = h + k := by omega
      rw [e1, choiceSum_succ, ih]
      have e3 : choiceSum (fun i => a (i + h)) (fun i => S (i + h)) (k + 1)
          = (if S (k + h) then a (k + h) else 0)
            + choiceSum (fun i => a (i + h)) (fun i => S (i + h)) k :=
        choiceSum_succ _ _ _
      rw [e3, e2]
      omega

/-- THE split: a subset sum over `h + n` indices decomposes into a
first-half sum `s ≤ t` and a second-half sum `t - s` over the shifted
family, and conversely. -/
theorem isSum_split (a : Nat → Nat) (h n t : Nat) :
    isSum a (h + n) t ↔ ∃ s, s ≤ t ∧ isSum a h s
      ∧ isSum (fun i => a (i + h)) n (t - s) := by
  constructor
  · rintro ⟨S, hS, hSum⟩
    rw [choiceSum_split] at hSum
    refine ⟨choiceSum a S h, by omega, ?_, ?_⟩
    · refine ⟨fun i => if i < h then S i else false, ?_, ?_⟩
      · intro i hi
        by_cases hl : i < h
        · simp only [if_pos hl]
          have : h ≤ i := by omega
          omega
        · simp only [if_neg hl]
      · simp only [choiceSum]
        congr 1
        exact List.map_congr_left fun i hi => by simp [List.mem_range.mp hi]
    refine ⟨fun i => S (i + h), by intro i hi; exact hS (i + h) (by omega), ?_⟩
    -- the shifted sum: hSum gives it by arithmetic
    omega
  · rintro ⟨s, hsle, ⟨S₁, hS₁, hS1⟩, S₂part⟩
    obtain ⟨S₂, hS₂, hS2⟩ := S₂part
    refine ⟨fun i => if i < h then S₁ i else S₂ (i - h), by
      intro i hi
      by_cases hlt : i < h
      · simp only [if_pos hlt]
        exact hS₁ i (by omega)
      · simp only [if_neg hlt]
        exact hS₂ (i - h) (by omega), ?_⟩
    rw [choiceSum_split]
    have first : choiceSum a (fun i => if i < h then S₁ i else S₂ (i - h)) h
        = choiceSum a S₁ h := by
      simp only [choiceSum]
      congr 1
      exact List.map_congr_left fun i hi => by simp [List.mem_range.mp hi]
    have second : choiceSum (fun i => a (i + h))
        (fun i => (fun i => if i < h then S₁ i else S₂ (i - h)) (i + h)) n
        = choiceSum (fun i => a (i + h)) S₂ n := by
      simp only [choiceSum]
      congr 1
      exact List.map_congr_left fun i _ => by
        have hnl : ¬ (i + h < h) := by omega
        simp only [if_neg hnl]
        by_cases hb : S₂ i <;> simp [hb]
    rw [first, second, hS1, hS2]
    omega

end SubsetSum.MITM.Spec
