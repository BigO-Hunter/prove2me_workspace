import Submission.SubsetSumStatement

example : (75/100 : Rat) = mkRat 3 4 := by
  rw [Rat.div_def, Rat.inv_def, Rat.mul_def',
      Rat.num_ofNat, Rat.den_ofNat, Rat.num_ofNat, Rat.den_ofNat]
  show mkRat (75 * (mkRat 1 100).num) (1 * (mkRat 1 100).den) = mkRat 3 4
  rw [Rat.num_mkRat, Rat.den_mkRat]
  simp only [Nat.gcd_one_right, Nat.div_one, Int.natAbs_ofNat, if_false]
  rw [Int.mul_one, Int.one_mul, show (75 : Int) = 3 * 25 by decide,
      show (100 : Nat) = 4 * 25 by decide]
  exact (mkRat_mul_right (by decide : (25 : Nat) ≠ 0)).symm
