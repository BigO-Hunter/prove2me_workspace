import Submission.Spec
set_option autoImplicit true

/-!
# Spec-level sort layer (R2125607414)

`halfSums a k` is EXACTLY the array Phase A builds: the sorted list of all
subset sums of `a 0..k-1`, grown by doubling merges — round `k` merges the
previous round's array with its `+ a k` shifted copy (the program's
`blt`-merge: take from the shifted side only when strictly smaller).

The contract `mem_halfSums` — membership in the array IS `isSum` — is what
Phase A's loop invariant carries and Phase B's search consumes.
-/

namespace SubsetSum.MITM

open BigOSpeedrun.SubsetSum SubsetSum.MITM.Spec

/-- The program's merge: take from the right list only when strictly
smaller (`jblt rVJ rVI LTAKEJ`), else from the left. -/
def mmerge : List Nat → List Nat → List Nat
  | [], r => r
  | l, [] => l
  | a :: l', b :: r' => if b < a then b :: mmerge (a :: l') r' else a :: mmerge l' (b :: r')

/-! ## Membership — by strong induction on total length -/

theorem mem_mmerge_aux : ∀ (N : Nat) (l r : List Nat) (x : Nat),
    l.length + r.length ≤ N → (x ∈ mmerge l r ↔ x ∈ l ∨ x ∈ r) := by
  intro N
  induction N with
  | zero =>
    intro l r x hlen
    cases l with
    | nil =>
      cases r with
      | nil => simp [mmerge]
      | cons b r' => exact absurd hlen (by simp only [List.length_cons]; omega)
    | cons a l' => exact absurd hlen (by simp only [List.length_cons]; omega)
  | succ N ih =>
    intro l r x hlen
    cases l with
    | nil => simp [mmerge]
    | cons a l' =>
      cases r with
      | nil => simp [mmerge]
      | cons b r' =>
        rw [mmerge]
        by_cases h : b < a
        · rw [if_pos h]
          have ih2 := ih (a :: l') r' x
            (by simp only [List.length_cons] at hlen ⊢; omega)
          simp only [List.mem_cons] at ih2 ⊢
          rw [ih2]
          constructor
          · rintro (h1 | h2 | h3)
            · exact Or.inr (Or.inl h1)
            · exact Or.inl h2
            · exact Or.inr (Or.inr h3)
          · rintro ((h1 | h2) | (h3 | h4))
            · exact Or.inr (Or.inl (Or.inl h1))
            · exact Or.inr (Or.inl (Or.inr h2))
            · exact Or.inl h3
            · exact Or.inr (Or.inr h4)
        · rw [if_neg h]
          have ih2 := ih l' (b :: r') x
            (by simp only [List.length_cons] at hlen ⊢; omega)
          simp only [List.mem_cons] at ih2 ⊢
          rw [ih2]
          constructor
          · rintro (h1 | h2 | h3 | h4)
            · exact Or.inl (Or.inl h1)
            · exact Or.inl (Or.inr h2)
            · exact Or.inr (Or.inl h3)
            · exact Or.inr (Or.inr h4)
          · rintro ((h1 | h2) | (h3 | h4))
            · exact Or.inl h1
            · exact Or.inr (Or.inl h2)
            · exact Or.inr (Or.inr (Or.inl h3))
            · exact Or.inr (Or.inr (Or.inr h4))

theorem mem_mmerge (l r : List Nat) (x : Nat) :
    x ∈ mmerge l r ↔ x ∈ l ∨ x ∈ r :=
  mem_mmerge_aux (l.length + r.length) l r x (Nat.le_refl _)

/-! ## Sortedness (as `List.Pairwise (· ≤ ·)`) -/

theorem mmerge_sorted_aux : ∀ (N : Nat) (l r : List Nat),
    l.length + r.length ≤ N → List.Pairwise (· ≤ ·) l → List.Pairwise (· ≤ ·) r →
    List.Pairwise (· ≤ ·) (mmerge l r) := by
  intro N
  induction N with
  | zero =>
    intro l r hlen hl hr
    cases l with
    | nil =>
      cases r with
      | nil => simpa [mmerge] using hr
      | cons b r' => exact absurd hlen (by simp only [List.length_cons]; omega)
    | cons a l' => exact absurd hlen (by simp only [List.length_cons]; omega)
  | succ N ih =>
    intro l r hlen hl hr
    cases l with
    | nil => simpa [mmerge] using hr
    | cons a l' =>
      cases r with
      | nil => simpa [mmerge] using hl
      | cons b r' =>
        rw [mmerge]
        by_cases h : b < a
        · rw [if_pos h]
          refine List.Pairwise.cons ?_ (ih (a :: l') r'
            (by simp only [List.length_cons] at hlen ⊢; omega) hl
            (List.pairwise_cons.mp hr).2)
          intro x hx
          rcases (mem_mmerge _ _ x).mp hx with h1 | h2
          · rcases List.mem_cons.mp h1 with h1 | h1
            · omega
            · have hax : a ≤ x := (List.pairwise_cons.mp hl).1 x h1
              omega
          · -- h2 : x ∈ r' directly
            exact (List.pairwise_cons.mp hr).1 x h2
        · rw [if_neg h]
          refine List.Pairwise.cons ?_ (ih l' (b :: r')
            (by simp only [List.length_cons] at hlen ⊢; omega)
            (List.pairwise_cons.mp hl).2 hr)
          intro x hx
          rcases (mem_mmerge _ _ x).mp hx with h1 | h2
          · exact (List.pairwise_cons.mp hl).1 x h1
          · rcases List.mem_cons.mp h2 with h2 | h2
            · omega
            · have hbx : b ≤ x := (List.pairwise_cons.mp hr).1 x h2
              omega

theorem mmerge_sorted (l r : List Nat) (hl : List.Pairwise (· ≤ ·) l)
    (hr : List.Pairwise (· ≤ ·) r) : List.Pairwise (· ≤ ·) (mmerge l r) :=
  mmerge_sorted_aux (l.length + r.length) l r (Nat.le_refl _) hl hr

/-! ## Length -/

theorem length_mmerge_aux : ∀ (N : Nat) (l r : List Nat),
    l.length + r.length ≤ N → (mmerge l r).length = l.length + r.length := by
  intro N
  induction N with
  | zero =>
    intro l r hlen
    cases l with
    | nil =>
      cases r with
      | nil => simp [mmerge]
      | cons b r' => exact absurd hlen (by simp only [List.length_cons]; omega)
    | cons a l' => exact absurd hlen (by simp only [List.length_cons]; omega)
  | succ N ih =>
    intro l r hlen
    cases l with
    | nil => simp [mmerge]
    | cons a l' =>
      cases r with
      | nil => simp [mmerge, List.length_cons]
      | cons b r' =>
        rw [mmerge]
        by_cases h : b < a
        · rw [if_pos h, List.length_cons,
            ih (a :: l') r' (by simp only [List.length_cons] at hlen ⊢; omega),
            List.length_cons]
          simp only [List.length_cons] at hlen ⊢
          omega
        · rw [if_neg h, List.length_cons,
            ih l' (b :: r') (by simp only [List.length_cons] at hlen ⊢; omega),
            List.length_cons]
          simp only [List.length_cons] at hlen ⊢
          omega

theorem length_mmerge (l r : List Nat) :
    (mmerge l r).length = l.length + r.length :=
  length_mmerge_aux (l.length + r.length) l r (Nat.le_refl _)

/-! ## The doubling construction -/

/-- The sorted subset sums of `a 0 .. k-1`, by the program's doubling
merges: round `k` merges the previous array with its `+ a k` copy. -/
def halfSums (a : Nat → Nat) : Nat → List Nat
  | 0 => [0]
  | k + 1 => mmerge (halfSums a k) ((halfSums a k).map fun x => x + a k)

theorem pairwise_map_add {l : List Nat} (c : Nat) (hl : List.Pairwise (· ≤ ·) l) :
    List.Pairwise (· ≤ ·) (l.map fun x => x + c) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a l' ih =>
    rw [List.map_cons]
    refine List.Pairwise.cons ?_ (ih (List.pairwise_cons.mp hl).2)
    intro x hx
    rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hay : a ≤ y := (List.pairwise_cons.mp hl).1 y hy
    omega

theorem halfSums_sorted (a : Nat → Nat) (k : Nat) :
    List.Pairwise (· ≤ ·) (halfSums a k) := by
  induction k with
  | zero => exact List.Pairwise.cons (by simp) List.Pairwise.nil
  | succ k ih => exact mmerge_sorted _ _ ih (pairwise_map_add _ ih)

theorem length_halfSums (a : Nat → Nat) (k : Nat) :
    (halfSums a k).length = 2 ^ k := by
  induction k with
  | zero => simp [halfSums]
  | succ k ih =>
    rw [halfSums, length_mmerge, List.length_map, ih]
    omega

/-- THE contract: membership in the sorted array IS being a subset sum. -/
theorem mem_halfSums (a : Nat → Nat) (k x : Nat) :
    x ∈ halfSums a k ↔ isSum a k x := by
  induction k generalizing x with
  | zero =>
    rw [isSum_zero]
    simp [halfSums]
  | succ k ih =>
    rw [halfSums, mem_mmerge, List.mem_map, isSum_succ]
    simp only [ih]

end SubsetSum.MITM
