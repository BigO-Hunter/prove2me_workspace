import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunNB
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-!
# Scalar values and labels for the genuine R8 one-run program

Frame data is abstract: `Pl` and `Pc` are parameters, so the raw-zero Pnd data
is not baked into the scalar circuit.  Stage boundaries are the R8 values
`wAuxEnd = 31336` and `NL = 31359`.  Final codes are read directly from `genF`,
so no missing `SG1_11` or `SG2_10` constants are needed.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.OneRunNB

open IntMul.Kappa IntMul.Kappa.R6.Bit IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R8.Bit.Oppbank IntMul.Kappa.R8.Bit.Oppbank.NB
open IntMul.Kappa.R8.Bit.Oppbank.Repaired IntMul.Kappa.R8.Bit.Oppbank.GenData

/-- Projector data consumed by the frame labels. -/
structure FrameData where
  Pl : ℕ → Matrix (Fin 23) (Fin 23) ℚ
  Pc : ℕ → Matrix (Fin 23) (Fin 23) ℚ

noncomputable def lab1 (fd : FrameData) (S : Matrix (Fin 529) Pnd.Pr23 ℚ)
    (Si : Matrix Pnd.Pr23 (Fin 529) ℚ) (N b c : ℕ) : FMat 529 N :=
  redM N (pswQ (Pnd.K S Si (fd.Pc c) (fd.Pl b)))

noncomputable def lab2 (fd : FrameData) (S : Matrix (Fin 529) Pnd.Pr23 ℚ)
    (Si : Matrix Pnd.Pr23 (Fin 529) ℚ) (N a c : ℕ) : FMat 529 N :=
  redM N (pswQ ((1 : Matrix (Fin 529) (Fin 529) ℚ) - Pnd.K S Si (fd.Pl a) (fd.Pc c)))

/-- Final labels of stage one. -/
noncomputable def fin1 (fd : FrameData) (ch : Repaired.Ch) (N b w : ℕ) : FMat 529 N :=
  if wEnt ≤ w ∧ w < wAuxEnd then AModel.swapMat
  else lab1 fd ch.S ch.Si N b ((genF (Gen.codeOf Gen.SG1_0) W1F).1 w)

/-- Stage-two labels before stage two. -/
noncomputable def pre2 (fd : FrameData) (ch : Repaired.Ch) (N a w : ℕ) : FMat 529 N :=
  if w < v then lab1 fd ch.S ch.Si N w (cPT a)
  else if w < wEnt then lab1 fd ch.S ch.Si N (w - v) cHIGH
  else if w < wAuxEnd then 1
  else if w < NL then lab2 fd ch.S ch.Si N a ((genF (Gen.codeOf GenData.SG2_0) W2F).1 w)
  else AModel.swapMat

/-- Final labels of stage two. -/
noncomputable def fin2 (fd : FrameData) (ch : Repaired.Ch) (N a w : ℕ) : FMat 529 N :=
  if w < NL then lab2 fd ch.S ch.Si N a ((genF (Gen.codeOf GenData.SG2_0) W2F).1 w)
  else lab2 fd ch.S ch.Si N a (cND (w - NL + 1))

/-- Correction-wire labels before and after the correction. -/
noncomputable def cf (fd : FrameData) (ch : Repaired.Ch) (N a s j : ℕ) : FMat 529 N :=
  if j = 0 then AModel.swapMat else if j = 1 then AModel.swapMat
  else lab2 fd ch.S ch.Si N a (cND (s + 1))

noncomputable def cg (fd : FrameData) (ch : Repaired.Ch) (N a s j : ℕ) : FMat 529 N :=
  if j = 1 then AModel.swapMat else lab2 fd ch.S ch.Si N a (cND (s + 1))

/-- Initial labels. -/
noncomputable def L0 (fd : FrameData) (ch : Repaired.Ch) (N : ℕ) : Repaired.Wr → FMat 529 N
  | .inl g => if g.val < N then lab1 fd ch.S ch.Si N (g.val % v) (cND (g.val / v + 1)) else 1
  | .inr t =>
      if t.val < 23 * v then
        lab1 fd ch.S ch.Si N (t.val / 23) ((genF (Gen.codeOf Gen.SG1_0) W1F).1 (wAuxEnd + t.val % 23))
      else if t.val < 2 * (23 * v) then
        lab2 fd ch.S ch.Si N ((t.val - 23 * v) / 23)
          ((genF (Gen.codeOf GenData.SG2_0) W2F).1 (wAuxEnd + (t.val - 23 * v) % 23))
      else AModel.swapMat

abbrev FVN (N : ℕ) := FV (ZMod 2) (Fin W) 529 N

/-- Initial scalar values. -/
noncomputable def φ0 (fd : FrameData) (ch : Repaired.Ch) (N : ℕ) : Repaired.Wr → FVN N
  | .inl g => if g.val < N then Finsupp.single (L0 fd ch N (.inl g), g) 1 else Finsupp.single (1, g) 1
  | .inr _ => 0

noncomputable def u1 (fd : FrameData) (ch : Repaired.Ch) (N b w : ℕ) : FVN N := φ0 fd ch N (NB.ι1 b w)

/-- Stage-two initial local scalar values. -/
noncomputable def u2 (fd : FrameData) (ch : Repaired.Ch) (N a w : ℕ) : FVN N :=
  if w < v then φ0 fd ch N (NB.ι1 w (wY a)) + φ0 fd ch N (NB.ι1 w (wX a)) else φ0 fd ch N (NB.ι2 a w)

/-- The genuine gate lists of the two chunk programs. -/
def gateList1 : List (ℕ × ℕ) := NB.cs1.flatMap fun ch => ch.2.2
def gateList2 : List (ℕ × ℕ) := NB.cs2.flatMap fun ch => ch.2.2

/-- Local XOR run: `u_d ← u_d + u_s` for each gate `(d, s)`. -/
def xrL {M : Type*} [AddCommGroup M] (l : List (ℕ × ℕ)) (u : ℕ → M) : ℕ → M :=
  l.foldl (fun u p => Function.update u p.1 (u p.1 + u p.2)) u

/-- Scalar values before and after one copy correction. -/
noncomputable def cfS (fd : FrameData) (ch : Repaired.Ch) (N a s j : ℕ) : FVN N :=
  if j = 0 then 0 else if j = 1 then xrL gateList2 (u2 fd ch N a) (wY s) else xrL gateList2 (u2 fd ch N a) (wX s)

noncomputable def cgS (fd : FrameData) (ch : Repaired.Ch) (N a s j : ℕ) : FVN N :=
  if j = 0 then xrL gateList2 (u2 fd ch N a) (wY s)
  else if j = 1 then xrL gateList2 (u2 fd ch N a) (wY s)
  else xrL gateList2 (u2 fd ch N a) (wX s) + xrL gateList2 (u2 fd ch N a) (wY s)

/-- Final scalar values of stage two. -/
noncomputable def fin2S (fd : FrameData) (ch : Repaired.Ch) (N a w : ℕ) : FVN N :=
  if w < v then xrL gateList2 (u2 fd ch N a) w + xrL gateList2 (u2 fd ch N a) (wY w)
  else if w < NL then xrL gateList2 (u2 fd ch N a) w
  else xrL gateList2 (u2 fd ch N a) (wY (w - NL))

end IntMul.Kappa.R8.Bit.Oppbank.OneRunNB
