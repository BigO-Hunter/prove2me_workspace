import Definitions.Def_IntMul_HvdH_RealExp

/-! Fixed-point approximation of the resampling map `S' = S / 2` by truncated Gaussian sums
(Harvey–van der Hoeven Lemma 4.9). Gaussian integers are pairs `(re, im) : ℤ × ℤ`, and a
fixed-point vector of precision `p` is `U : ℕ → ℤ × ℤ` standing for `2^{-p} U`. -/

namespace IntMul.HvdH

/-- `⌈√p⌉`. -/
def ceilSqrt (p : ℕ) : ℕ := if Nat.sqrt p * Nat.sqrt p < p then Nat.sqrt p + 1 else Nat.sqrt p

/-- Truncation half-width `m = ⌈√p⌉ α` of Lemma 4.9. -/
def sWidth (p α : ℕ) : ℕ := ceilSqrt p * α

/-- `⌊2^p / (2α)⌋`, the fixed-point value of `β = 1/(2α)`. -/
def betaT (p α : ℕ) : ℤ := ((2 ^ p / (2 * α) : ℕ) : ℤ)

/-- One term `ρ(β̃ x̃_j u_j)` of the truncated sum, where `x̃_j ≈ 2^p e^{-π(j - sk/t)²/α²}`
is computed by `expNeg` (Lemma 2.13) and the product is rounded towards zero. -/
def sTerm (p s t α k : ℕ) (U : ℕ → ℤ × ℤ) (j : ℤ) : ℤ × ℤ :=
  let w := betaT p α * expNeg p (α ^ 2 * t ^ 2) ((t * j - s * k : ℤ).natAbs ^ 2)
  let V := U (j % s).toNat
  ((w * V.1).tdiv (2 ^ (2 * p)), (w * V.2).tdiv (2 ^ (2 * p)))

/-- Lemma 4.9: `(S̃' U)_k = ∑_{|j - c| ≤ m} sTerm j` with `c = ⌈sk/t⌉`, i.e. the sum over
`j = c - m + i` for `i < 2m + 1`. -/
def Sapprox (p s t α : ℕ) (U : ℕ → ℤ × ℤ) (k : ℕ) : ℤ × ℤ :=
  let m : ℕ := sWidth p α
  let c : ℤ := ((s * k + t - 1) / t : ℕ)
  (∑ i ∈ Finset.range (2 * m + 1), (sTerm p s t α k U (c - m + i)).1,
    ∑ i ∈ Finset.range (2 * m + 1), (sTerm p s t α k U (c - m + i)).2)

/-- The exact map `(S' u)_k = (2α)⁻¹ ∑_{j ∈ ℤ} e^{-π (j - sk/t)² / α²} u_{j mod s}`. -/
noncomputable def Sexact (s t α : ℕ) (u : ℕ → ℂ) (k : ℕ) : ℂ :=
  ∑' j : ℤ, (((2 * α : ℝ)⁻¹ * Real.exp (-(Real.pi * (j - (s * k : ℝ) / t) ^ 2 / α ^ 2)) : ℝ) : ℂ) *
    u (j % s).toNat

end IntMul.HvdH
