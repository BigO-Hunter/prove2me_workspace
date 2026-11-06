import Mathlib

/-! Integer approximations of π and log 2 (Harvey–van der Hoeven §2.8 / Lemma 2.12–2.13 style). -/

namespace IntMul.HvdH

open Finset

/-- Integer approximation of `2^N arctan(1/x)` from `K` series terms, each rounded down. -/
def atanInv (x N K : ℕ) : ℤ :=
  ∑ k ∈ range K, (-1) ^ k * ((2 ^ N / ((2 * k + 1) * x ^ (2 * k + 1)) : ℕ) : ℤ)

/-- Integer approximation of `2^N artanh(1/x)` from `K` series terms, each rounded down. -/
def atanhInv (x N K : ℕ) : ℤ :=
  ∑ k ∈ range K, ((2 ^ N / ((2 * k + 1) * x ^ (2 * k + 1)) : ℕ) : ℤ)

/-- Machin: integer approximation of `2^M π`. -/
def piApprox (M : ℕ) : ℤ := 16 * atanInv 5 M M - 4 * atanInv 239 M M

/-- `n`-bit approximation of `π`: `|piBits n / 2^n - π| ≤ 2^{-n}`. -/
def piBits (n : ℕ) : ℤ := (piApprox (2 * n + 9) + 2 ^ (n + 8)) / 2 ^ (n + 9)

/-- Integer approximation of `2^M log 2` (`log 2 = 2 artanh(1/3)`). -/
def log2Approx (M : ℕ) : ℤ := 2 * atanhInv 3 M M

/-- `n`-bit approximation of `log 2`: `|log2Bits n / 2^n - log 2| ≤ 2^{-n}`. -/
def log2Bits (n : ℕ) : ℤ := (log2Approx (2 * n + 9) + 2 ^ (n + 8)) / 2 ^ (n + 9)

end IntMul.HvdH
