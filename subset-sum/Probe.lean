import Submission.SubsetSumStatement

namespace BigOSpeedrun.SubsetSum

-- CRITICAL: does 75/100 normalize to 3/4 ?
example : ((75/100 : Rat)).den = 4 := by rfl
example : (((75/100 : Rat)).num).toNat = 3 := by rfl

-- core lemma signature probes
#check @Nat.pow_le_pow_left
#check @Nat.pow_le_pow_right
#check @Nat.mul_le_mul_left
#check @Nat.mul_le_mul
#check @Nat.pow_add
#check @Nat.pow_mul
#check @Nat.one_le_two_pow
#check @Nat.le_add_left
#check @List.all_eq_true
#check @of_decide_eq_true
#check @List.mem_range
#check @List.mem_map

-- is implication decidable in core?
example : (List.range 128).all (fun m => decide (64 ≤ m → 8 * Nat.log2 m + 8 ≤ m)) = true := by rfl

-- AC simp for mul_pow
example (a b : Nat) (k : Nat) : (a * b) ^ k = a ^ k * b ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, ih]
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

end BigOSpeedrun.SubsetSum
