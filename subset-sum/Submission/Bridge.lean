import Submission.Spec
set_option autoImplicit true

/-!
# The bridge: statement shape ↔ spec shape (R2125607414)

`Instance.yes` speaks `Fin n → Bool` + `List.ofFn` sums; `Spec.isSum`
speaks `Nat → Bool` + `List.range` sums.  One reshaping lemma connects
them; every downstream phase proof consumes this and never touches `Fin`
again.
-/

namespace SubsetSum.MITM

open BigOSpeedrun.SubsetSum SubsetSum.MITM.Spec

/-- The input array read at a `Nat` index (0 past the end). -/
def instA {n : Nat} (x : Instance n) : Nat → Nat :=
  fun i => if h : i < n then x.a ⟨i, h⟩ else 0

/-- The Nat-indexed choice function of a `Fin`-indexed one (false past n). -/
def liftS {n : Nat} (S : Fin n → Bool) : Nat → Bool :=
  fun i => if h : i < n then S ⟨i, h⟩ else false

theorem ofFn_val_eq_map_range (g : Nat → Nat) (n : Nat) :
    (List.ofFn fun i : Fin n => g i.val) = (List.range n).map g := by
  apply List.ext_get
  · simp [List.length_ofFn, List.length_map, List.length_range]
  · intro i h1 h2
    simp [List.getElem_ofFn, List.getElem_map, List.getElem_range]

/-- On a `Fin` index the lifted choice reads the original. -/
theorem liftS_val {n : Nat} (S : Fin n → Bool) (i : Fin n) :
    liftS S i.val = S i := by
  unfold liftS
  rw [dif_pos i.isLt]

/-- On a `Fin` index the Nat-read of the array is the original entry. -/
theorem instA_val {n : Nat} (x : Instance n) (i : Fin n) :
    instA x i.val = x.a i := by
  unfold instA
  rw [dif_pos i.isLt]

/-- Both sum-shapes agree. -/
theorem sum_reshape {n : Nat} (x : Instance n) (S : Fin n → Bool) :
    ((List.range n).map fun i => if liftS S i then instA x i else 0).sum
      = (List.ofFn fun i : Fin n => if S i then x.a i else 0).sum := by
  have h1 : (List.range n).map (fun i => if liftS S i then instA x i else 0)
      = List.ofFn fun i : Fin n => if liftS S i.val then instA x i.val else 0 :=
    (ofFn_val_eq_map_range
      (g := fun i => if liftS S i then instA x i else 0) n).symm
  have h2 : (List.ofFn fun i : Fin n => if liftS S i.val then instA x i.val else 0)
      = List.ofFn fun i : Fin n => if S i then x.a i else 0 := by
    congr 1
    funext i
    rw [liftS_val, instA_val]
  rw [h1, h2]

/-- THE bridge: the challenge's `Instance.yes` is the spec's `isSum` on the
Nat-indexed read of the input. -/
theorem instance_yes_iff {n : Nat} (x : Instance n) :
    x.yes ↔ isSum (instA x) n x.t := by
  constructor
  · rintro ⟨S, hS⟩
    refine ⟨liftS S, ?_, ?_⟩
    · intro i hi
      unfold liftS
      rw [dif_neg (by omega : ¬ i < n)]
    · calc choiceSum (instA x) (liftS S) n
          = ((List.range n).map fun i => if liftS S i then instA x i else 0).sum := rfl
        _ = (List.ofFn fun i : Fin n => if S i then x.a i else 0).sum := sum_reshape x S
        _ = x.t := hS
  · rintro ⟨S, hS, hSum⟩
    refine ⟨fun i => S i.val, ?_⟩
    have h1 : (List.ofFn fun i : Fin n => if S i.val then x.a i else 0).sum
        = ((List.range n).map fun i => if S i then instA x i else 0).sum := by
      rw [← ofFn_val_eq_map_range (g := fun i => if S i then instA x i else 0) n]
      congr 1
      congr 1
      funext i
      rw [instA_val]
    calc (List.ofFn fun i : Fin n => if S i.val then x.a i else 0).sum
          = ((List.range n).map fun i => if S i then instA x i else 0).sum := h1
        _ = choiceSum (instA x) S n := rfl
        _ = x.t := hSum

end SubsetSum.MITM
