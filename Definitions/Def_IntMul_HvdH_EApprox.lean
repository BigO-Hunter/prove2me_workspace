import Definitions.Def_IntMul_HvdH_SApprox

/-! Fixed-point approximation of the off-diagonal part `E = N - I` of the normalised resampling
system (Harvey–van der Hoeven Lemma 4.11). Gaussian integers are pairs `(re, im) : ℤ × ℤ`, and a
fixed-point vector of precision `p` is `U : ℕ → ℤ × ℤ` standing for `2^{-p} U`. -/

namespace IntMul.HvdH

/-- `b_ℓ = tℓ - s·round(tℓ/s) = s β_ℓ`, with `round(x) = ⌊x + 1/2⌋`. -/
def bOf (s t : ℕ) (l : ℤ) : ℤ := t * l - s * ((2 * t * l + s) / (2 * s))

/-- `K_{ℓ,h} = (th + b_ℓ)² - b_{ℓ+h}²`, so that the entry of `E` is `e^{-πα² K_{ℓ,h}/s²}`. -/
def eKz (s t : ℕ) (l h : ℤ) : ℤ := (t * h + bOf s t l) ^ 2 - bOf s t (l + h) ^ 2

/-- Truncation half-width `m = ⌈⌈√p⌉/α⌉ + 1` of Lemma 4.11. -/
def eWidth (p α : ℕ) : ℕ := (ceilSqrt p + α - 1) / α + 1

/-- One term `ρ(x̃_h U_{ℓ+h})` of the truncated sum (zero for `h = 0`), where
`x̃_h ≈ 2^p e^{-πα² K_{ℓ,h}/s²}` is computed by `expNeg` (Lemma 2.13) and the product is rounded
towards zero. -/
def eTerm (p s t α l : ℕ) (U : ℕ → ℤ × ℤ) (h : ℤ) : ℤ × ℤ :=
  if h = 0 then (0, 0) else
  let x := expNeg p (s ^ 2) (α ^ 2 * (eKz s t l h).toNat)
  let V := U ((l + h) % s).toNat
  ((x * V.1).tdiv (2 ^ p), (x * V.2).tdiv (2 ^ p))

/-- Lemma 4.11: `(Ẽ U)_ℓ = ∑_{0 < |h| ≤ m} eTerm h`, i.e. the sum over `h = i - m` for
`i < 2m + 1` (the term `h = 0` vanishes). -/
def Eapprox (p s t α : ℕ) (U : ℕ → ℤ × ℤ) (l : ℕ) : ℤ × ℤ :=
  let m : ℕ := eWidth p α
  (∑ i ∈ Finset.range (2 * m + 1), (eTerm p s t α l U ((i : ℤ) - m)).1,
    ∑ i ∈ Finset.range (2 * m + 1), (eTerm p s t α l U ((i : ℤ) - m)).2)

/-- The exact entries `e_{ℓ,h} = e^{-πα² K_{ℓ,h}/s²}` for `h ≠ 0`, and `0` for `h = 0`. -/
noncomputable def eEx (s t α : ℕ) (l h : ℤ) : ℝ :=
  if h = 0 then 0 else Real.exp (-(Real.pi * α ^ 2 * (eKz s t l h : ℝ) / s ^ 2))

/-- The exact map `(E u)_ℓ = ∑_{h ≠ 0} e^{-πα²((th/s + β_ℓ)² - β_{ℓ+h}²)} u_{(ℓ+h) mod s}`. -/
noncomputable def Eexact (s t α : ℕ) (u : ℕ → ℂ) (l : ℕ) : ℂ :=
  ∑' h : ℤ, ((eEx s t α l h : ℝ) : ℂ) * u ((l + h) % s).toNat

end IntMul.HvdH
