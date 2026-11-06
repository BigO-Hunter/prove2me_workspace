import Definitions.Def_IntMul_HvdH_EApprox

/-! Fixed-point approximation of `J' = N⁻¹ / 2 = (I + E)⁻¹ / 2` by the truncated Neumann series
`v - Ev + E²v - ⋯` with `v = u / 2` (Harvey–van der Hoeven Lemma 4.12). Gaussian integers are
pairs `(re, im) : ℤ × ℤ`, and a fixed-point vector of precision `p` is `U : ℕ → ℤ × ℤ` standing
for `2^{-p} U`. -/

namespace IntMul.HvdH

/-- `ṽ⁽⁰⁾ = ρ(U / 2)`, halving each component with rounding towards zero. -/
def halfFP (U : ℕ → ℤ × ℤ) (i : ℕ) : ℤ × ℤ := ((U i).1.tdiv 2, (U i).2.tdiv 2)

/-- Number of Neumann terms `n = ⌈ps / (α²(t - s))⌉ = ⌈p / (α²θ)⌉`. -/
def jIter (p s t α : ℕ) : ℕ := (p * s + α ^ 2 * (t - s) - 1) / (α ^ 2 * (t - s))

/-- The iterates `ṽ⁽ʲ⁾ = Ẽ ṽ⁽ʲ⁻¹⁾` (Lemma 4.11 applied `j` times to `ṽ⁽⁰⁾`). -/
def vIter (p s t α : ℕ) (U : ℕ → ℤ × ℤ) : ℕ → ℕ → ℤ × ℤ
  | 0 => halfFP U
  | j + 1 => Eapprox p s t α (vIter p s t α U j)

/-- Lemma 4.12: `J̃' U = ṽ⁽⁰⁾ - ṽ⁽¹⁾ + ⋯ ± ṽ⁽ⁿ⁻¹⁾`. -/
def Japprox (p s t α : ℕ) (U : ℕ → ℤ × ℤ) (l : ℕ) : ℤ × ℤ :=
  (∑ j ∈ Finset.range (jIter p s t α), (-1) ^ j * (vIter p s t α U j l).1,
    ∑ j ∈ Finset.range (jIter p s t α), (-1) ^ j * (vIter p s t α U j l).2)

end IntMul.HvdH
