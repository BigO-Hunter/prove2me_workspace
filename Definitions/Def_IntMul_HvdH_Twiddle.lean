import Definitions.Def_IntMul_HvdH_Numeric
import Definitions.Def_IntMul_HvdH_ExpApprox

/-! Fixed-point roots of unity `e^{2πij/k}` (Harvey–van der Hoeven Lemma 2.12), computed by
reduction to an angle in `[0, π/4]` followed by the Taylor approximation `expBits`. -/

namespace IntMul.HvdH

/-- Multiplication by `i` on Gaussian integers `(re, im)`. -/
def mulI (p : ℤ × ℤ) : ℤ × ℤ := (-p.2, p.1)

/-- Complex conjugation on Gaussian integers `(re, im)`. -/
def conjZ (p : ℤ × ℤ) : ℤ × ℤ := (p.1, -p.2)

/-- Approximation of `2^n e^{iπa/(4k)}` for `0 ≤ a ≤ k`: the angle is computed to `n+4` bits from
`piBits`, exponentiated with `expBits`, and rounded to precision `n`. -/
def octExp (n k a : ℕ) : ℤ × ℤ :=
  let φ : ℤ := piBits (n + 4) * a / (4 * k)
  let u := expBits (n + 4) 0 φ
  ((u.1 + 2 ^ 3) / 2 ^ 4, (u.2 + 2 ^ 3) / 2 ^ 4)

/-- Approximation of `2^n e^{2πij/k}`. With `j' = j mod k` and `8j' = qk + r`, `q = 2m` or
`q = 2m+1`, use `e^{2πij/k} = i^m e^{iπr/(4k)}` or `i^{m+1} conj(e^{iπ(k-r)/(4k)})`. -/
def twiddle (n k j : ℕ) : ℤ × ℤ :=
  let j' := j % k
  let q := 8 * j' / k
  let r := 8 * j' % k
  if q % 2 = 0 then mulI^[q / 2] (octExp n k r)
  else mulI^[q / 2 + 1] (conjZ (octExp n k (k - r)))

end IntMul.HvdH
