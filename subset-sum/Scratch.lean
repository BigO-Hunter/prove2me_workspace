namespace Scratch

-- (A) 0 < 2^w for arbitrary w  -- WORKS (induction)
example (w : Nat) : 0 < 2 ^ w := by
  induction w with
  | zero => decide
  | succ k ih => rw [Nat.pow_succ]; omega

-- (B) 2^w >= 1
example (w : Nat) : 1 ≤ 2 ^ w := by
  have h := Scratch.show_pos w
  omega

-- (C) does `up_fit` need v < 2^w, or v <= 2^w? check the exact signature
-- (up_fit hfit (by omega)) where the goal is 0 < 2^w  => needs 0 < 2^w
-- so the REAL issue is `2 ^ w` being opaque to omega.

-- (D) Can omega see 2^w if we give it the fact as a hypothesis?
example (w : Nat) (h : 0 < 2 ^ w) : 0 < 2 ^ w := by omega

-- (E) `Nat.pow_le_pow_right`?
example (a b : Nat) (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := by
  exact Nat.pow_le_pow_right (by omega) (by omega)

-- (F) 2^k = 2 * 2^(k-1) for k>=1
example (k : Nat) (hk : 1 ≤ k) : 2 ^ k = 2 * 2 ^ (k - 1) := by
  rw [show k = (k - 1) + 1 from by omega, Nat.pow_succ, Nat.mul_comm]

-- (G) 2 * L ≤ 2^h given L = 2^(k-1), k ≤ h
example (L k h : Nat) (hL : L = 2 ^ (k - 1)) (hk : 1 ≤ k) (hkh : k ≤ h) :
    2 * L ≤ 2 ^ h := by
  rw [hL]
  have h1 : 2 ^ (k - 1) ≤ 2 ^ (h - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : 2 ^ (h - 1) * 2 = 2 ^ h := by
    rw [show h = (h - 1) + 1 from by omega, Nat.pow_succ, Nat.mul_comm]
  omega

end Scratch
