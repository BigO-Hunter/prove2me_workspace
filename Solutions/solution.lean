import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNet0P
import Definitions.Def_IntMul_KappaJainData

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open IntMul.Kappa
open IntMul.Kappa.R8.Bit.Oppbank.Net0P
open IntMul.Kappa.Jain

theorem solution : ∀ τ : ℝ, histMoment net0P.hist 529 τ = histMoment bitR8 529 τ := by
  intro τ
  have h : net0P.hist = bitR8 := by decide
  rw [h]
