import Mathlib

/-!
# Exponent bookkeeping of the community κ-improvements (Colkitt framework)

Shared vocabulary for the conditional κ-improvement witnesses built on the OpenAI manuscript
*Integer multiplication below n log n* and D. Colkitt's `integer-mult-bounds`.

* A finite linear network is summarised by its child-width histogram: `n_w` recursive child
  calls of width `w` (out of the full width `m`), on a network with `W` roles.  The recursive
  saving `a` of the network is certified by the moment inequality
  `∑_w n_w (w/m)^(1-a) < W` (`histMoment`).
* `CrudeAssembly` is the assembly of `scripts/certificate_round3.py` of
  S. Jain's `integer-mult-kappa` with the crude depth guard: from the bit saving `a_b`, the
  complex saving `a_c` and the parameters `β, ε, x, C₁`, every strict constraint holds and
  every cost margin exceeds `κ`.
-/

namespace IntMul.Kappa

/-- The moment `∑ n_w (w/m)^τ` of a child-width histogram, given as a list of pairs
`(w, n_w)`. -/
noncomputable def histMoment (h : List (ℕ × ℕ)) (m : ℕ) (τ : ℝ) : ℝ :=
  (h.map fun p => (p.2 : ℝ) * ((p.1 : ℝ) / m) ^ τ).sum

/-- The rank sum `s = ∑ w n_w` of a child-width histogram: the total width of all child
calls. -/
def histRankSum (h : List (ℕ × ℕ)) : ℕ :=
  (h.map fun p => p.1 * p.2).sum

/-- The crude-guard assembly of `certificate_round3.py` (with `y = ε`): with
`τ = 1 - a_b`, `σ = 1 - a_c`, `χ = τ + (1-β) max(σ-τ, 0)`, `leaf = σ + β(1-σ)`,
`λ = max(τ, σ, χ) + 10⁻¹⁶`, `λ' = max(λ, leaf) + 10⁻¹⁶`, `δ = 10⁻²²/x` and
`poly = (1+x)δ`, all constraints of the stack hold and `κ` lies strictly below each of
the cost margins `1-ε`, `ε(1-λ')`, `1-ε-poly`, `ε` and `max(ε,1-ε)(1-τ)`. Here `m_c` and
`s_c` are the width and rank sum of the complex network. -/
def CrudeAssembly (ab ac β ε x C₁ κ : ℝ) (mc sc : ℕ) : Prop :=
  let τ := 1 - ab
  let σ := 1 - ac
  let χ := τ + (1 - β) * max (σ - τ) 0
  let leaf := σ + β * (1 - σ)
  let lam := max (max τ σ) χ + 1 / 10 ^ 16
  let lamp := max lam leaf + 1 / 10 ^ 16
  let δ := 1 / 10 ^ 22 / x
  let poly := (1 + x) * δ
  (0 < β ∧ β < 1) ∧
  2 + (mc : ℝ) * Real.log sc ≤ C₁ ∧
  lamp < 1 ∧
  ε * (2 - lamp) < 1 ∧
  ε * C₁ < 1 + x ∧
  2 * ε + ε < 1 + x ∧
  0 < ε ∧ ε < 1 ∧
  2 * ε - 1 < lamp * ε ∧
  (0 < δ ∧ δ < 1 / 8) ∧
  κ < 1 - ε ∧
  κ < ε * (1 - lamp) ∧
  κ < 1 - ε - poly ∧
  κ < ε ∧
  κ < max ε (1 - ε) * (1 - τ)

end IntMul.Kappa
