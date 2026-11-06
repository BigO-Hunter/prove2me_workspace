import Definitions.Def_IntMul_HvdH_RealExp

/-! Fixed-point approximation of the diagonal map `D' = D / 2^{2α²-2}` of Gaussian resampling
(Harvey–van der Hoeven Lemma 4.8). Gaussian integers are pairs `(re, im) : ℤ × ℤ`, and a
fixed-point vector of precision `p` is `U : ℕ → ℤ × ℤ` standing for `2^{-p} U`. -/

namespace IntMul.HvdH

/-- `k_ℓ = (tℓ - s·round(tℓ/s))²`, so that `α² β_ℓ² = α² k_ℓ / s²`. -/
def kOf (s t l : ℕ) : ℕ :=
  (((t * l : ℕ) : ℤ) - (s : ℤ) * (((2 * t * l + s) / (2 * s) : ℕ) : ℤ)).natAbs ^ 2

/-- Approximation of `2^p d'_ℓ = 2^p e^{πα²β_ℓ²} / 2^{2α²-2}` via `expPos` (Lemma 2.14). -/
def dTilde (p s t α l : ℕ) : ℤ := expPos p (s ^ 2) (α ^ 2 * kOf s t l) (2 * α ^ 2 - 2)

/-- Lemma 4.8: `(D̃' U)_ℓ = ρ(d̃'_ℓ U_ℓ)`, rounding each component towards zero. -/
def Dapprox (p s t α : ℕ) (U : ℕ → ℤ × ℤ) (l : ℕ) : ℤ × ℤ :=
  ((dTilde p s t α l * (U l).1).tdiv (2 ^ p), (dTilde p s t α l * (U l).2).tdiv (2 ^ p))

end IntMul.HvdH
