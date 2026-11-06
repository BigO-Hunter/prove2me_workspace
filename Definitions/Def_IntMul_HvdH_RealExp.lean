import Definitions.Def_IntMul_HvdH_Numeric
import Definitions.Def_IntMul_HvdH_ExpApprox

/-! Fixed-point real exponentials `e^{-πj/k}` and `2^{-σ} e^{πj/k}`
(Harvey–van der Hoeven Lemmas 2.13 and 2.14). -/

namespace IntMul.HvdH

/-- Approximation of `2^n exp(X / 2^M)` for `X ≤ 0`: write `X / 2^M = z - τ log 2` with
`z ∈ (-log 2, 0]` (using the `M`-bit approximation `log2Bits M`), approximate `2^M e^z` with
`expBits`, and divide by `2^{M - n + τ}` with rounding to nearest. -/
def expNegFix (n M : ℕ) (X : ℤ) : ℤ :=
  let L := log2Bits M
  let τ := (-X) / L
  let u := (expBits M (X + τ * L) 0).1
  let s := M - n - 1 + τ.toNat
  (u + 2 ^ s) / 2 ^ (s + 1)

/-- Approximation of `2^n e^{-πj/k}` (Lemma 2.13). -/
def expNeg (n k j : ℕ) : ℤ :=
  if k * n < j then 0
  else expNegFix n (2 * n + 10) (-(piBits (2 * n + 10) * j / k))

/-- Approximation of `2^n · 2^{-σ} e^{πj/k}`, meaningful when `e^{πj/k} ≤ 2^σ` (Lemma 2.14). -/
def expPos (n k j σ : ℕ) : ℤ :=
  expNegFix n (2 * n + 10)
    (min 0 (piBits (2 * n + 10) * j / k - σ * log2Bits (2 * n + 10)))

end IntMul.HvdH
