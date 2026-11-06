import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Function.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R8 opp-bank label generator (`genF`) @ `NL = 31359`

Port of `R6Chk.Bit.Loc.genF` / `codeOf` / `mvF` / `genStepF` from
`IntMul_Kappa_R6_Defs51` onto R8 geometry (`NR = 27794`, `NL = 31359`).
`genF` itself is geometry-agnostic; `ValidOn` / `packCodes` use `NL`.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.Gen

def NL : ℕ := 31359

def fieldOf (X w i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight X (Nat.mul w i)) (Nat.sub (Nat.shiftLeft 1 w) 1)

def catB (B : ℕ) (l : List ℕ) : ℕ :=
  l.foldr (fun x acc => x ||| (acc <<< B)) 0

def packL (l : List Nat) : Nat := catB 65536 l

abbrev LInstr := ℕ × List ℕ × List (ℕ × ℕ)
abbrev LChunk := ℕ × List (ℕ × ℕ) × List (ℕ × ℕ)

def mvF (c : ℕ) (acc : (ℕ → ℕ) × List (ℕ × ℕ)) (w : ℕ) :
    (ℕ → ℕ) × List (ℕ × ℕ) :=
  if acc.1 w = c then acc
  else (fun x => if x = w then c else acc.1 x, (w, acc.1 w) :: acc.2)

def genStepF (acc : (ℕ → ℕ) × List LChunk) (i : LInstr) :
    (ℕ → ℕ) × List LChunk :=
  let r := i.2.1.foldl (mvF i.1) (acc.1, [])
  (r.1, (i.1, r.2.reverse, i.2.2) :: acc.2)

/-- Label generator (specification of `genP`). -/
def genF (f : ℕ → ℕ) (W : List LInstr) : (ℕ → ℕ) × List LChunk :=
  let r := W.foldl genStepF (f, [])
  (r.1, r.2.reverse)

def codeOf (S : ℕ) : ℕ → ℕ := fun w => fieldOf S 16 w

def packCodes (f : ℕ → ℕ) : ℕ :=
  catB 16 ((List.range NL).map f)

/-- Codes on local wires fit the R8 label alphabet bound used by R6 Fits-style checks. -/
def ValidOn (f : ℕ → ℕ) : Prop := ∀ w < NL, f w < 65536

end IntMul.Kappa.R8.Bit.Oppbank.Gen
