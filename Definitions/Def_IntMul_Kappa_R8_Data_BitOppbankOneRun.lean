import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankAuxF

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Opposite-bank one-run edge interface

Waypoint for R2125607035 (2026-10-29).  The audited upstream export at commit
`d48a892d1ef0a194f9643142172e17bb0881b63f` produces 122504 charged steps and
4231 aux sigma frames.  Its one-run compile has the following run shapes.  The
`PEOne` predicate deliberately keeps the full `EdgeQ` requirement, including
nontrivial Bruhat factors: the identity-frame `oneEdge` stub is not a formally
correct reconstruction.  Existence of these edges is the separate gate
certificate; this file only fixes the interface.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.OneRun

open IntMul.Kappa IntMul.Kappa.R6.Bit IntMul.Kappa.R6.Bit.NB

/-- A side residual of rank `r` becomes one reversed-bank child of width `r`. -/
def SideR (r : ℕ) (rs : List (ℕ × ℕ × ℕ)) : Prop :=
  rs = [(0, 529 - r, r)]

/-- A slot aux edge merged with its corner becomes one child of width
`529 - auxCorner s`, which is `506 + auxF s` on the frozen schedule. -/
def AuxR (s : ℕ) (rs : List (ℕ × ℕ × ℕ)) : Prop :=
  rs = [(0, auxCorner s, 529 - auxCorner s)]

/-- The round-six data entrance becomes one child of width 484. -/
def DataR (rs : List (ℕ × ℕ × ℕ)) : Prop :=
  rs = [(0, 529 - 484, 484)]

/-- A copy correction remains one child of width one. -/
def CopyR (rs : List (ℕ × ℕ × ℕ)) : Prop :=
  rs = [(0, 529 - 1, 1)]

/-- An edge with its complete rational partial-swap certificate and its run
shape.  In particular, `EdgeQ` still requires lower-triangular Bruhat factors
with nonzero diagonals and the correct transformed matrix. -/
def PEOne (q : Matrix (Fin 529) (Fin 529) ℚ)
    (R : List (ℕ × ℕ × ℕ) → Prop) (e : Edge 529) : Prop :=
  EdgeQ e q ∧ R e.runs

theorem auxRun_width (s : ℕ) (hf : auxF s ≤ 23) :
    529 - auxCorner s = 506 + auxF s := by
  simp only [auxCorner]
  omega

theorem dataRun_start : 529 - 484 = 45 := by decide

theorem copyRun_start : 529 - 1 = 528 := by decide

end IntMul.Kappa.R8.Bit.Oppbank.OneRun
