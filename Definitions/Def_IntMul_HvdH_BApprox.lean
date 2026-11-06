import Definitions.Def_IntMul_HvdH_JApprox
import Definitions.Def_IntMul_HvdH_DiagApprox

/-! The fixed-point approximation `B̃ = P̃_s⁻¹ D̃' J̃' C̃ P̃_t` of the map `B` in Gaussian resampling
(Harvey–van der Hoeven Proposition 4.7(ii)). Gaussian integers are pairs `(re, im) : ℤ × ℤ`, and
a fixed-point vector of precision `p` is `U : ℕ → ℤ × ℤ` standing for `2^{-p} U`; a vector in
`ℂ^n` is stored in the entries `0, …, n - 1`. -/

namespace IntMul.HvdH

/-- `(P̃_t V)_k = V_{-sk mod t}`. -/
def ptPerm (s t : ℕ) (V : ℕ → ℤ × ℤ) (k : ℕ) : ℤ × ℤ :=
  V (-((s : ZMod t) * (k : ZMod t))).val

/-- `(C̃ V)_ℓ = V_{round(tℓ'/s) mod t}` with `ℓ' = ℓ mod s` (the output is `s`-periodic). -/
def cSel (s t : ℕ) (V : ℕ → ℤ × ℤ) (l : ℕ) : ℤ × ℤ :=
  V ((((2 * t * (l % s) + s) / (2 * s) : ℕ) : ZMod t)).val

/-- `(P̃_s⁻¹ W)_j = W_{t⁻¹ j mod s}`. -/
def psInvPerm (s t : ℕ) (W : ℕ → ℤ × ℤ) (j : ℕ) : ℤ × ℤ :=
  W ((t : ZMod s)⁻¹ * (j : ZMod s)).val

/-- `B̃ = P̃_s⁻¹ D̃' J̃' C̃ P̃_t` (Lemmas 4.8 and 4.12 and data rearrangements). -/
def Bapprox (p s t α : ℕ) (V : ℕ → ℤ × ℤ) : ℕ → ℤ × ℤ :=
  psInvPerm s t (Dapprox p s t α (Japprox p s t α (cSel s t (ptPerm s t V))))

end IntMul.HvdH
