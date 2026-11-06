import Submission.Fit
set_option autoImplicit true

/-!
# Runtime bound (R2125607414)

## Part 1: polynomial-vs-exponential, from first principles

`poly_le_exp`: for `2^(E+3) ≤ n`, `(n+2)^E ≤ 2^(n+2)` — any fixed power of
`n` is eventually below `2^n`.  The proof runs on the dyadic window
`[2^j, 2^(j+1))` with `j = Nat.log2 n`: `(n+2)^E ≤ (2^(j+2))^E = 2^(E*(j+2))`
and `E*(j+2) ≤ 2^j + 2 ≤ n + 2` (induction on `j`; each step adds `E ≤ 2^j`).

## Part 2: the horizon `Runtime.stepBound`

`stepBound n = 2^(n/2+20) * (n+2)^8` is the explicit step horizon the
exec-walk lanes dominate.  The BigO obligation at `α = 75/100` (which core
`Rat` normalizes to `3/4`, so `α.den = 4` and `α.num.toNat = 3`) is
`(stepBound n + constOverhead)^4 ≤ K * 2^(3n)`: the `2^(n/2+21)` factor
contributes `2^(4*(n/2+21))`, `poly_le_exp` at `E = 32` absorbs
`(n+2)^32 ≤ 2^(n+2)` once `2^35 ≤ n`, and `4*(n/2+21) + (n+2) ≤ 3n + 86`;
smaller `n` fall to monotonicity into `K`.
-/

namespace SubsetSum.MITM

open BigOSpeedrun.SubsetSum

/-! ## Elementary powers -/

theorem le_two_pow_self : ∀ E : Nat, E ≤ 2 ^ E := by
  intro E
  induction E with
  | zero => exact Nat.zero_le _
  | succ E ih =>
    have h1 : (1:Nat) ≤ 2 ^ E := Nat.one_le_two_pow
    have h2 : (2:Nat) ^ (E + 1) = 2 ^ E + 2 ^ E := by
      rw [Nat.pow_succ]; omega
    omega

theorem succ_le_two_pow : ∀ j : Nat, j + 1 ≤ 2 ^ j := by
  intro j
  induction j with
  | zero => omega
  | succ j ih =>
    have hp : (2:Nat) ^ (j + 1) = 2 ^ j + 2 ^ j := by rw [Nat.pow_succ]; omega
    have h1 : (1:Nat) ≤ 2 ^ j := Nat.one_le_two_pow
    omega

/-! ## `Nat.log2`: the lower half of the window -/

theorem two_pow_log2_le_aux : ∀ k m : Nat, m ≤ k → 0 < m → 2 ^ Nat.log2 m ≤ m := by
  intro k
  induction k with
  | zero => intro m hm hpos; omega
  | succ k ih =>
    intro m hm hpos
    by_cases h2 : 2 ≤ m
    · rw [log2_two_step h2]
      have hdpos : 0 < m / 2 := by omega
      have hdm : 2 * (m / 2) ≤ m := Nat.mul_div_le m 2
      have hmk : m / 2 ≤ k := by omega
      have hdlt : m / 2 < m := by omega
      have hih : 2 ^ Nat.log2 (m / 2) ≤ m / 2 := ih (m / 2) hmk hdpos
      calc 2 ^ (Nat.log2 (m / 2) + 1)
          = 2 * 2 ^ Nat.log2 (m / 2) := by rw [Nat.pow_succ]; omega
        _ ≤ 2 * (m / 2) := Nat.mul_le_mul_left 2 hih
        _ ≤ m := hdm
    · have hm1 : m = 1 := by omega
      subst hm1
      rw [log2_one]
      exact Nat.le_refl _

theorem two_pow_log2_le (m : Nat) (h : 0 < m) : 2 ^ Nat.log2 m ≤ m :=
  two_pow_log2_le_aux (m + 1) m (by omega) h

/-- The lower window bound: `2^k <= n` puts `k` at or below the logarithm. -/
theorem log2_ge_of_le : ∀ k n : Nat, 2 ^ k ≤ n → k ≤ Nat.log2 n := by
  intro k
  induction k with
  | zero => intro n _; exact Nat.zero_le _
  | succ k ih =>
    intro n h
    have h2pos : (0:Nat) < 2 ^ k := Nat.two_pow_pos k
    have hkey : (2:Nat) ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
    rw [hkey] at h
    have h2 : 2 ≤ n := by omega
    rw [log2_two_step h2]
    have hdiv : 2 ^ k ≤ n / 2 := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      omega
    have hih := ih (n / 2) hdiv
    omega

/-! ## Growth: `E*(j+2) ≤ 2^j + 2` on the dyadic window -/

/-- Base of the growth induction: `E^2 + 5E` fits under `2^(E+2) + 2`. -/
theorem growth_base : ∀ E : Nat, 1 ≤ E → E * E + 5 * E ≤ 2 ^ (E + 2) + 2 := by
  intro E
  induction E with
  | zero => intro h; omega
  | succ E ih =>
    intro h
    by_cases hE : 1 ≤ E
    · have h21 : E + 1 ≤ 2 ^ E := succ_le_two_pow E
      have hp2 : (2:Nat) ^ (E + 2) = 4 * 2 ^ E := by rw [Nat.pow_add]; omega
      have hp3 : (2:Nat) ^ (E + 1 + 2) = 2 ^ (E + 2) + 2 ^ (E + 2) := by
        have h0 : E + 1 + 2 = (E + 2) + 1 := by omega
        rw [h0, Nat.pow_succ]
        omega
      have hih := ih hE
      have hexp1 : (E + 1) * (E + 1) = E * E + 2 * E + 1 := by
        have a : (E + 1) * (E + 1) = (E + 1) * E + (E + 1) :=
          Nat.mul_succ (E + 1) E
        have b : (E + 1) * E = E * E + 1 * E := Nat.add_mul E 1 E
        omega
      omega
    · have hE0 : E = 0 := by omega
      subst hE0
      decide

/-- On `j ≥ E+3`, the line `E*(j+2)` stays under `2^j + 2` (each step adds
`E ≤ 2^j` to the left, `2^j` to the right). -/
theorem growth2_step : ∀ (E : Nat), 1 ≤ E → ∀ j : Nat, E + 3 ≤ j → E * (j + 2) ≤ 2 ^ j + 2 := by
  intro E hE j
  induction j with
  | zero => intro h; omega
  | succ j ih =>
    intro h
    by_cases hj : E + 3 ≤ j
    · have hih := ih hj
      have hEj : E ≤ 2 ^ j :=
        Nat.le_trans (le_two_pow_self E)
          (Nat.pow_le_pow_right (n := 2) (by omega) (by omega))
      have hp : (2:Nat) ^ (j + 1) = 2 ^ j + 2 ^ j := by rw [Nat.pow_succ]; omega
      have hlin : E * (j + 1 + 2) = E * (j + 2) + E := by
        have ha : E * (j + 1 + 2) = E * (j + 1) + E * 2 := Nat.mul_add E (j + 1) 2
        have hb : E * (j + 2) = E * (j + 1) + E := Nat.mul_succ E (j + 1)
        omega
      show E * (j + 1 + 2) ≤ 2 ^ (j + 1) + 2
      omega
    · have hj2 : j = E + 2 := by omega
      subst hj2
      have hgb := growth_base E hE
      have hp : (2:Nat) ^ (E + 2 + 1) = 2 ^ (E + 2) + 2 ^ (E + 2) := by
        rw [Nat.pow_succ]; omega
      have hexpand : E * (E + 2 + 1 + 2) = E * E + 5 * E := by
        have h1 : E * (E + 2 + 1 + 2) = E * E + E * 5 := Nat.mul_add E E 5
        omega
      show E * (E + 2 + 1 + 2) ≤ 2 ^ (E + 2 + 1) + 2
      omega

/-- The master polynomial-vs-exponential bound. -/
theorem poly_le_exp : ∀ E n : Nat, 2 ^ (E + 3) ≤ n → (n + 2) ^ E ≤ 2 ^ (n + 2) := by
  intro E n hn
  by_cases hE0 : E = 0
  · subst hE0
    rw [Nat.pow_zero]
    exact Nat.one_le_two_pow
  · have hE1 : 1 ≤ E := by omega
    have hpos : 0 < n := by
      have := Nat.two_pow_pos (E + 3)
      omega
    have hjge : E + 3 ≤ Nat.log2 n := log2_ge_of_le (E + 3) n hn
    have hlow : 2 ^ Nat.log2 n ≤ n := two_pow_log2_le n hpos
    have htop : E * (Nat.log2 n + 2) ≤ 2 ^ Nat.log2 n + 2 :=
      growth2_step E hE1 (Nat.log2 n) hjge
    have hexp : E * (Nat.log2 n + 2) ≤ n + 2 := by omega
    have hwindow : n + 2 ≤ 2 ^ (Nat.log2 n + 2) := by
      have hhigh : n < 2 ^ (Nat.log2 n + 1) := log2_lt hpos
      have hp : (2:Nat) ^ (Nat.log2 n + 1) = 2 ^ Nat.log2 n + 2 ^ Nat.log2 n := by
        rw [Nat.pow_succ]; omega
      have hp2 : (2:Nat) ^ (Nat.log2 n + 2) = 2 * 2 ^ (Nat.log2 n + 1) := by
        rw [Nat.pow_succ]; omega
      have h1 : (1:Nat) ≤ 2 ^ Nat.log2 n := Nat.one_le_two_pow
      omega
    have hstep1 : (n + 2) ^ E ≤ 2 ^ (E * (Nat.log2 n + 2)) := by
      have hpowmul : (n + 2) ^ E ≤ (2 ^ (Nat.log2 n + 2)) ^ E :=
        Nat.pow_le_pow_left hwindow E
      have hexpform : (2 ^ (Nat.log2 n + 2)) ^ E = 2 ^ (E * (Nat.log2 n + 2)) := by
        rw [Nat.mul_comm, ← Nat.pow_mul]
      rw [← hexpform]
      exact hpowmul
    calc (n + 2) ^ E ≤ 2 ^ (E * (Nat.log2 n + 2)) := hstep1
      _ ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (n := 2) (by omega) hexp

/-! ## The horizon function -/

namespace Runtime

/-- The explicit step horizon: `2^(n/2+20) * (n+2)^8` dominates every run of
the program on inputs of length `n` (prologue + Phase A + Phase B trip
counts; the exec-walk lanes compose into this).  Constants are generous. -/
def stepBound (n : Nat) : Nat := 2 ^ (n / 2 + 20) * (n + 2) ^ 8

/-- Constant setup cost folded into the horizon used by `Race.lean`. -/
def constOverhead : Nat := 2 ^ 12

theorem one_le_poly8 (n : Nat) : (1:Nat) ≤ (n + 2) ^ 8 := by
  have h1 : (1:Nat) ≤ n + 2 := by omega
  have h := Nat.pow_le_pow_left h1 8
  rwa [Nat.one_pow] at h

theorem stepBound_mono {a b : Nat} (h : a ≤ b) : stepBound a ≤ stepBound b := by
  have h1 : a / 2 ≤ b / 2 := Nat.div_le_div_right h
  have h2 : (2:Nat) ^ (a / 2 + 20) ≤ 2 ^ (b / 2 + 20) :=
    Nat.pow_le_pow_right (n := 2) (by omega) (by omega)
  have h3 : (a + 2) ^ 8 ≤ (b + 2) ^ 8 := Nat.pow_le_pow_left (by omega) 8
  unfold stepBound
  exact Nat.mul_le_mul h2 h3

theorem constOverhead_le_stepBound (n : Nat) : constOverhead ≤ stepBound n := by
  have h1 : (2:Nat) ^ 12 ≤ 2 ^ 20 := by decide
  have h2 : (2:Nat) ^ 20 ≤ 2 ^ (n / 2 + 20) :=
    Nat.pow_le_pow_right (n := 2) (by omega) (by omega)
  have h3 : (2:Nat) ^ (n / 2 + 20) ≤ stepBound n := by
    unfold stepBound
    exact Nat.le_mul_of_pos_right _ (one_le_poly8 n)
  exact Nat.le_trans (Nat.le_trans h1 h2) h3

theorem T_le (n : Nat) : stepBound n + constOverhead ≤ 2 ^ (n / 2 + 21) * (n + 2) ^ 8 := by
  have h1 := constOverhead_le_stepBound n
  have h2 : stepBound n + constOverhead ≤ stepBound n + stepBound n :=
    Nat.add_le_add_left h1 _
  have h3 : stepBound n + stepBound n = 2 * stepBound n := (Nat.two_mul _).symm
  have h4 : 2 * stepBound n = 2 ^ (n / 2 + 21) * (n + 2) ^ 8 := by
    have e : (2:Nat) ^ (n / 2 + 21) = 2 * 2 ^ (n / 2 + 20) := by
      have h0 : n / 2 + 21 = (n / 2 + 20) + 1 := by omega
      rw [h0, Nat.pow_succ]
      omega
    unfold stepBound
    rw [← Nat.mul_assoc, ← e]
  calc stepBound n + constOverhead ≤ stepBound n + stepBound n := h2
    _ = 2 * stepBound n := h3
    _ = 2 ^ (n / 2 + 21) * (n + 2) ^ 8 := h4

theorem T_mono {a b : Nat} (h : a ≤ b) :
    stepBound a + constOverhead ≤ stepBound b + constOverhead :=
  Nat.add_le_add_right (stepBound_mono h) _

/-! ### The `Rat` digits of `75/100` (core `Rat` normalizes to `3/4`) -/

open Rat in
theorem den_75_100 : ((75 : Rat) / 100).den = 4 := by
  rw [Rat.div_def, Rat.inv_def,
    show (75 : Rat) = (75 : Int) /. 1 from (Rat.num_divInt_den 75).symm,
    Rat.divInt_mul_divInt, Rat.den_divInt]
  simp
  rfl

open Rat in
theorem num_75_100 : (((75 : Rat) / 100).num).toNat = 3 := by
  rw [Rat.div_def, Rat.inv_def,
    show (75 : Rat) = (75 : Int) /. 1 from (Rat.num_divInt_den 75).symm,
    Rat.divInt_mul_divInt, Rat.num_divInt]
  simp
  rfl

/-- **The runtime bound**: the horizon is `O(2^(3n/4))`, i.e. `BigO` at
`α = 75/100` (normalized by `Rat` to `3/4`): for every `n ≥ 2`,
`(stepBound n + constOverhead)^4 ≤ K * 2^(3n)`. -/
theorem runtime_bigO : BigO (fun n => stepBound n + constOverhead) (75 / 100 : Rat) := by
  refine ⟨2 ^ 86 + (stepBound (2 ^ 35) + constOverhead) ^ 4, fun n _hn => ?_⟩
  rw [den_75_100, num_75_100]
  by_cases hN : (2:Nat) ^ 35 ≤ n
  · -- large n: the exponential crushes the polynomial
    have hE : (2:Nat) ^ (32 + 3) ≤ n := hN
    have hT := T_le n
    have hp1 : (stepBound n + constOverhead) ^ 4
        ≤ (2 ^ (n / 2 + 21) * (n + 2) ^ 8) ^ 4 :=
      Nat.pow_le_pow_left hT 4
    have hp2 : (2 ^ (n / 2 + 21) * (n + 2) ^ 8) ^ 4
        = (2 ^ (n / 2 + 21)) ^ 4 * ((n + 2) ^ 8) ^ 4 :=
      Nat.mul_pow _ _ _
    have he1 : ((2:Nat) ^ (n / 2 + 21)) ^ 4 = 2 ^ (4 * (n / 2 + 21)) := by
      rw [(Nat.pow_mul 2 (n / 2 + 21) 4).symm, Nat.mul_comm]
    have he3 : (8:Nat) * 4 = 32 := rfl
    have he2 : ((n + 2) ^ 8) ^ 4 = (n + 2) ^ 32 := by
      rw [(Nat.pow_mul (n + 2) 8 4).symm, he3]
    have hpl := poly_le_exp 32 n hE
    have hcomb : 2 ^ (4 * (n / 2 + 21)) * 2 ^ (n + 2)
        = 2 ^ (4 * (n / 2 + 21) + (n + 2)) :=
      (Nat.pow_add 2 (4 * (n / 2 + 21)) (n + 2)).symm
    have hlin : 4 * (n / 2 + 21) + (n + 2) ≤ 3 * n + 86 := by omega
    have hsplit : 2 ^ (3 * n + 86) = 2 ^ 86 * 2 ^ (3 * n) := by
      rw [Nat.add_comm, Nat.pow_add]
    calc (stepBound n + constOverhead) ^ 4
        ≤ (2 ^ (n / 2 + 21)) ^ 4 * ((n + 2) ^ 8) ^ 4 := Nat.le_trans hp1 (Nat.le_of_eq hp2)
      _ = 2 ^ (4 * (n / 2 + 21)) * (n + 2) ^ 32 := by rw [he1, he2]
      _ ≤ 2 ^ (4 * (n / 2 + 21)) * 2 ^ (n + 2) := Nat.mul_le_mul (Nat.le_refl _) hpl
      _ = 2 ^ (4 * (n / 2 + 21) + (n + 2)) := hcomb
      _ ≤ 2 ^ (3 * n + 86) := Nat.pow_le_pow_right (n := 2) (by omega) hlin
      _ = 2 ^ 86 * 2 ^ (3 * n) := hsplit
      _ ≤ (2 ^ 86 + (stepBound (2 ^ 35) + constOverhead) ^ 4) * 2 ^ (3 * n) :=
          Nat.mul_le_mul_right _ (by omega)
  · -- small n: monotone into the constant
    have hnN : n ≤ 2 ^ 35 := by omega
    have hmono := T_mono hnN
    have hp : (stepBound n + constOverhead) ^ 4
        ≤ (stepBound (2 ^ 35) + constOverhead) ^ 4 :=
      Nat.pow_le_pow_left hmono 4
    have h1 : (1:Nat) ≤ 2 ^ (3 * n) := Nat.one_le_two_pow
    have h2 : (stepBound (2 ^ 35) + constOverhead) ^ 4
        ≤ 2 ^ 86 + (stepBound (2 ^ 35) + constOverhead) ^ 4 := by omega
    calc (stepBound n + constOverhead) ^ 4
        ≤ (stepBound (2 ^ 35) + constOverhead) ^ 4 := hp
      _ ≤ (2 ^ 86 + (stepBound (2 ^ 35) + constOverhead) ^ 4) * 2 ^ (3 * n) :=
          Nat.le_trans h2 (Nat.le_mul_of_pos_right _ h1)

end Runtime

end SubsetSum.MITM
