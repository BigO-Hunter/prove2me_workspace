import Submission.Prog2Final
set_option autoImplicit true

/-!
# The α = 1/2 summit: `bigO_T2` + `Race_bound'` (R2125607749 Lane 4)

`BigO T (1/2)` is `∃ K, ∀ n ≥ 2, T n ^ 2 ≤ K * 2 ^ n` (core `Rat` keeps
`1/2` reduced: `den = 2`, `num.toNat = 1`).  The horizon `T2` has two
branches, both absorbed by the single constant `K = 2^80`:

* `n ∈ {2,3}` (the filed `stepBound` branch): `T2` is monotone into
  `T2 3 = 2^21 * 5^8 + 2^12 < 2^40`, so `(T2 n)^2 ≤ (T2 3)^2 ≤ 2^82 =
  K * 2^2 ≤ K * 2^n` — one `decide`-checked numeral fact.
* `n ≥ 4`: `n + 2 ≤ 2n ≤ 2 * 2^(n - n/2) ≤ 4 * 2^(n/2)` (via
  `n ≤ 2^(n - n/2)` = `n ≤ 2^⌈n/2⌉`, a pair induction), so
  `T2 n = 256 * 2^(n/2) + 300 * (n + 2) ≤ 1456 * 2^(n/2)` and
  `(T2 n)^2 ≤ 1456^2 * (2^(n/2))^2 ≤ 1456^2 * 2^n ≤ 2^80 * 2^n`,
  using `(2^(n/2))^2 = 2^(n/2 + n/2) ≤ 2^n` carried EXPLICITLY through
  `Nat.pow_two`/`Nat.pow_add`/`Nat.pow_le_pow_right` (omega treats powers
  as atoms).

`Race_bound'` then assembles `SolvedInTime (1/2)` exactly the way the
filed `Race_bound` (α = 3/4) did: `⟨prog2, prog2_correct, fun c =>
⟨T2, bigO_T2, halts⟩⟩` — the bound is independent of `c`, as precedent
allows, and `(1 / 2 : Rat)` is already the reduced literal the verifier's
target expects (no rat bridge needed).
-/

namespace SubsetSum.MITM

open BigOSpeedrun.SubsetSum

/-! ## The `Rat` digits of `1/2` -/

open Rat in
theorem den_half : ((1 : Rat) / 2).den = 2 := by
  rw [Rat.div_def, Rat.inv_def,
    show (1 : Rat) = (1 : Int) /. 1 from (Rat.num_divInt_den 1).symm,
    Rat.divInt_mul_divInt, Rat.den_divInt]
  simp

open Rat in
theorem num_half : (((1 : Rat) / 2).num).toNat = 1 := by
  rw [Rat.div_def, Rat.inv_def,
    show (1 : Rat) = (1 : Int) /. 1 from (Rat.num_divInt_den 1).symm,
    Rat.divInt_mul_divInt, Rat.num_divInt]
  simp
  rfl

/-! ## Growth supports: `n ≤ 2^⌈n/2⌉` and friends -/

/-- The pair induction behind `n ≤ 2^(n - n/2)`: on evens `2k ≤ 2^k`,
on odds `2k+1 ≤ 2^(k+1)`. -/
theorem ceil_half_pair : ∀ k : Nat, 2 * k ≤ 2 ^ k ∧ 2 * k + 1 ≤ 2 ^ (k + 1) := by
  intro k
  induction k with
  | zero => exact ⟨Nat.zero_le _, by omega⟩
  | succ k ih =>
    have hp : (2:Nat) ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    have hp2 : (2:Nat) ^ (k + 2) = 2 ^ (k + 1) + 2 ^ (k + 1) := by
      have e : k + 1 + 1 = k + 2 := by omega
      rw [← e, Nat.pow_succ]
      omega
    refine ⟨?_, ?_⟩
    · show 2 * (k + 1) ≤ 2 ^ (k + 1)
      by_cases hk : k = 0
      · subst hk; decide
      · have h1 : (1:Nat) ≤ k := by omega
        have hpow1 : (2:Nat) ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) h1
        have e1 : (2:Nat) ^ 1 = 2 := by decide
        have h2 : (2:Nat) ≤ 2 ^ k := by omega
        omega
    · show 2 * (k + 1) + 1 ≤ 2 ^ (k + 2)
      have h1 : (1:Nat) ≤ 2 ^ k := Nat.one_le_two_pow
      have h2 : (2:Nat) ≤ 2 ^ (k + 1) := by omega
      omega

/-- `n ≤ 2^⌈n/2⌉`, written as `n ≤ 2^(n - n/2)`. -/
theorem n_le_pow_ceil (n : Nat) : n ≤ 2 ^ (n - n / 2) := by
  have hpair := ceil_half_pair (n / 2)
  have hd : n - n / 2 = n / 2 ∨ n - n / 2 = n / 2 + 1 := by omega
  rcases hd with hd | hd
  · rw [hd]; omega
  · rw [hd]; omega

/-! ## The BigO obligation at α = 1/2 -/

/-- **The runtime bound**: `T2` is `O(2^(n/2))`, i.e. `BigO` at `α = 1/2`:
for every `n ≥ 2`, `(T2 n)^2 ≤ 2^80 * 2^n`. -/
theorem bigO_T2 : BigO T2 (1 / 2 : Rat) := by
  refine ⟨2 ^ 80, fun n hn => ?_⟩
  rw [den_half, num_half, Nat.one_mul]
  rcases Nat.lt_or_ge n 4 with hsmall | hbig
  · -- small n: the filed stepBound branch is monotone into the n = 3 numeral
    have hn3 : n ≤ 3 := by omega
    rw [T2_small n hn3]
    have hmono : Runtime.stepBound n + Runtime.constOverhead
        ≤ Runtime.stepBound 3 + Runtime.constOverhead :=
      Nat.add_le_add_right (Runtime.stepBound_mono (by omega)) _
    have hsq : (Runtime.stepBound n + Runtime.constOverhead) ^ 2
        ≤ (Runtime.stepBound 3 + Runtime.constOverhead) ^ 2 :=
      Nat.pow_le_pow_left hmono 2
    have hdec : (Runtime.stepBound 3 + Runtime.constOverhead) ^ 2 ≤ 2 ^ 80 * 2 ^ 2 := by
      decide
    have hpow : (2:Nat) ^ 80 * 2 ^ 2 ≤ 2 ^ 80 * 2 ^ n :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
    exact Nat.le_trans hsq (Nat.le_trans hdec hpow)
  · -- large n: 256·2^(n/2) + 300·(n+2) ≤ 1456·2^(n/2), then square
    rw [T2_big n hbig]
    have hA : n + 2 ≤ 2 * 2 ^ (n - n / 2) := by
      have h1 : n ≤ 2 ^ (n - n / 2) := n_le_pow_ceil n
      omega
    have hB : 2 ^ (n - n / 2) ≤ 2 * 2 ^ (n / 2) := by
      have h1 : (2:Nat) ^ (n - n / 2) ≤ 2 ^ (n / 2 + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have h2 : (2:Nat) ^ (n / 2 + 1) = 2 * 2 ^ (n / 2) := by rw [Nat.pow_succ]; omega
      omega
    have hC : 300 * (n + 2) ≤ 1200 * 2 ^ (n / 2) := by
      have h1 := hA
      have h2 := hB
      omega
    have hD : 256 * 2 ^ (n / 2) + 300 * (n + 2) ≤ 1456 * 2 ^ (n / 2) :=
      calc 256 * 2 ^ (n / 2) + 300 * (n + 2)
          ≤ 256 * 2 ^ (n / 2) + 1200 * 2 ^ (n / 2) :=
            Nat.add_le_add (Nat.le_refl _) hC
        _ = (256 + 1200) * 2 ^ (n / 2) := (Nat.add_mul _ _ _).symm
        _ = 1456 * 2 ^ (n / 2) := by rfl
    have hE : ((2:Nat) ^ (n / 2)) ^ 2 ≤ 2 ^ n := by
      have h1 : ((2:Nat) ^ (n / 2)) ^ 2 = 2 ^ (n / 2) * 2 ^ (n / 2) := by
        rw [Nat.pow_two]
      have h2 : (2:Nat) ^ (n / 2) * 2 ^ (n / 2) = 2 ^ (n / 2 + n / 2) :=
        (Nat.pow_add _ _ _).symm
      have h3 : n / 2 + n / 2 ≤ n := by omega
      calc ((2:Nat) ^ (n / 2)) ^ 2 = 2 ^ (n / 2 + n / 2) := by rw [h1, h2]
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) h3
    have hF : (1456:Nat) ^ 2 ≤ 2 ^ 80 := by decide
    calc (256 * 2 ^ (n / 2) + 300 * (n + 2)) ^ 2
        ≤ (1456 * 2 ^ (n / 2)) ^ 2 := Nat.pow_le_pow_left hD 2
      _ = 1456 ^ 2 * (2 ^ (n / 2)) ^ 2 := Nat.mul_pow 1456 (2 ^ (n / 2)) 2
      _ ≤ 1456 ^ 2 * 2 ^ n := Nat.mul_le_mul (Nat.le_refl _) hE
      _ ≤ 2 ^ 80 * 2 ^ n := Nat.mul_le_mul_right _ hF

/-! ## The summit -/

/-- THE SUMMIT (α = 1/2): one finite program, correct on every instance
with `n ≥ 2`, running in `O(2^(n/2))` — no polynomial factor. -/
theorem Race_bound' : SolvedInTime (1 / 2 : Rat) :=
  ⟨prog2, prog2_correct,
    fun _c => ⟨T2, bigO_T2, fun n x hn _hb ρ => prog2_halts_all n x hn ρ⟩⟩

end SubsetSum.MITM
