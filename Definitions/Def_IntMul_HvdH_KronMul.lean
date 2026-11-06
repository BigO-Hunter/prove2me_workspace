import Mathlib

/-! Kronecker substitution and fixed-point multiplication in `R = ℂ[y]/(y^r + 1)`
(Harvey–van der Hoeven Lemma 2.5). Polynomials are lists of coefficients, constant term first. -/

namespace IntMul.HvdH

/-- Evaluate a coefficient list at `B`: `kpack B [c₀, c₁, …] = c₀ + c₁ B + ⋯`. -/
def kpack (B : ℤ) : List ℤ → ℤ
  | [] => 0
  | c :: cs => c + B * kpack B cs

/-- Read off `n` balanced base-`B` digits (each in `[-B/2, B/2)`), least significant first. -/
def kunpack (B : ℤ) : ℕ → ℤ → List ℤ
  | 0, _ => []
  | n + 1, W =>
    let c := (W + B / 2) % B - B / 2
    c :: kunpack B n ((W - c) / B)

/-- Schoolbook product of coefficient lists: the `k`-th coefficient is `∑_{i ≤ k} aᵢ b_{k-i}`. -/
def polyMul (a b : List ℤ) : List ℤ :=
  (List.range (a.length + b.length - 1)).map
    (fun k => ∑ i ∈ Finset.range (k + 1), a.getD i 0 * b.getD (k - i) 0)

/-- Reduce a coefficient list modulo `y^r + 1`: `i ↦ lᵢ - l_{i+r}` (enough for length `≤ 2r`). -/
def negFold (r : ℕ) (l : List ℤ) : List ℤ :=
  (List.range r).map (fun i => l.getD i 0 - l.getD (i + r) 0)

/-- Coefficientwise sum and difference of two coefficient lists of length `n`. -/
def listAdd (n : ℕ) (a b : List ℤ) : List ℤ := (List.range n).map (fun i => a.getD i 0 + b.getD i 0)
def listSub (n : ℕ) (a b : List ℤ) : List ℤ := (List.range n).map (fun i => a.getD i 0 - b.getD i 0)

/-- Lemma 2.5, specification: with `2^p u = U₀ + i U₁` and `2^p v = V₀ + i V₁` in `ℤ[i][y]/(y^r+1)`,
the coefficients of `2^{2p} r · (uv / r) = W₀ + i W₁`, each divided by `2^p r` with rounding towards
zero. -/
def mulRSpec (p r : ℕ) (U0 U1 V0 V1 : List ℤ) : List (ℤ × ℤ) :=
  let W0 := negFold r (listSub (2 * r - 1) (polyMul U0 V0) (polyMul U1 V1))
  let W1 := negFold r (listAdd (2 * r - 1) (polyMul U0 V1) (polyMul U1 V0))
  (List.range r).map (fun l => ((W0.getD l 0).tdiv (2 ^ p * r), (W1.getD l 0).tdiv (2 ^ p * r)))

/-- Product of two length-`r` coefficient lists by Kronecker substitution at `2^{3p}`:
one integer multiplication, then `2r - 1` balanced digits. -/
def kronMul (p r : ℕ) (a b : List ℤ) : List ℤ :=
  kunpack (2 ^ (3 * p)) (2 * r - 1) (kpack (2 ^ (3 * p)) a * kpack (2 ^ (3 * p)) b)

/-- Lemma 2.5, algorithm: as `mulRSpec`, with the four polynomial products computed by
Kronecker substitution (four integer multiplications of `3rp`-bit integers). -/
def mulR (p r : ℕ) (U0 U1 V0 V1 : List ℤ) : List (ℤ × ℤ) :=
  let W0 := negFold r (listSub (2 * r - 1) (kronMul p r U0 V0) (kronMul p r U1 V1))
  let W1 := negFold r (listAdd (2 * r - 1) (kronMul p r U0 V1) (kronMul p r U1 V0))
  (List.range r).map (fun l => ((W0.getD l 0).tdiv (2 ^ p * r), (W1.getD l 0).tdiv (2 ^ p * r)))

end IntMul.HvdH
