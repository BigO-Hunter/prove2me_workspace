import Submission.SubsetSumStatement

-- can decide compute the reduced form pieces?
example : (mkRat 3 4).den = 4 := by decide
example : (mkRat 3 4).num = 3 := by decide

-- full chain to mkRat 3 4
example : (75/100 : Rat) = mkRat 3 4 := by
  rw [Rat.div_def, Rat.inv_def, Rat.mul_def',
      Rat.num_ofNat, Rat.den_ofNat, Rat.num_ofNat, Rat.den_ofNat,
      Rat.divInt_ofNat, Rat.num_ofNat, Rat.den_ofNat,
      num_mkRat, den_mkRat]
  simp only [Nat.gcd_comm, Nat.gcd_one_right, if_false, if_true]
  rw [Nat.div_one, Nat.div_one, Int.mul_one, Int.one_mul,
      show (75 : Int) = 3 * 25 by decide, show (100 : Nat) = 4 * 25 by decide]
  exact (mkRat_mul_right (by decide : (25 : Nat) ≠ 0)).symm
