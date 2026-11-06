import Submission.SubsetSumStatement

-- gcd on literals: kernel-computable?
example : Nat.gcd 4 3 = 1 := by decide
example : (Rat.mkRat 3 4).den = 4 := by decide
example : (((Rat.mkRat 3 4)).num).toNat = 3 := by decide

-- the full chain
example : (75/100 : Rat) = Rat.mkRat 3 4 := by
  rw [Rat.div_def, Rat.inv_def, Rat.mul_def', Rat.num_ofNat, Rat.den_ofNat,
      Rat.num_ofNat, Rat.den_ofNat, Rat.divInt_ofNat]
  rw [Rat.mkRat_mul_right (by decide : (25 : Nat) ≠ 0)]
  rfl
