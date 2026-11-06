import Definitions.Def_IntMul_Kappa_R6_Defs16
import Definitions.Def_IntMul_Kappa_R6_Defs23

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Round-six machine interfaces, parametric in the two networks

xuanji's round-six development (`IntMul.Kappa.R6`) builds a multitape multiplier from a bit
network (`Bit.QHNet (ZMod 2) W T m`) and a complex network (`Cx.Prop8IfaceH W T m h`). Its two
network interfaces `Bit.BitNetR6MomStmt` and `P14Need6` fix Jain's round-six constants
(`W = 148225616, m = 529` for the bit network, `W = 207387136, m = 576, h = Jain.cxR6` for the
complex network). The definitions below are the same statements with the widths, role counts and
histograms as parameters:

* `Bit.BitNetMomStmtG Wb mb hb`: a bit network `C : QHNet (ZMod 2) Wb T mb` with valid runs,
  `EdgesOK` and `FormalOK` at every prime power `q^f` with `q > q₀`, whose child-width moment is
  dominated by that of the histogram `hb` at every exponent in `(0, 1]`. At
  `(148225616, 529, Jain.bitR6)` this is literally `Bit.BitNetR6MomStmt`.
* `P14NeedG Wc mc hc P`: the uniform Proposition 14 (`IL3.P14UH'`) at a polynomial guard
  (`EwOK6`), from a canonical Lemma 12 code and any complex network
  `J : Cx.Prop8IfaceH Wc T mc hc` in the gate class `IL3H.GClassH J A` with the moment bound
  `histMoment hc mc σ < Wc` and the crude depth guard `2 + mc log(histRankSum hc) ≤ C1`. At
  `(207387136, 576, Jain.cxR6)` this is literally `P14Need6`.
-/

namespace IntMul.Kappa.R6.Bit

/-- **Moment-dominance bit-network statement, parametric in `(Wb, mb, hb)`.** -/
def BitNetMomStmtG (Wb mb : ℕ) (hb : List (ℕ × ℕ)) : Prop :=
  ∃ (T : ℕ) (C : QHNet (ZMod 2) Wb T mb) (q₀ : ℕ), C.RunsOK ∧
    (∀ q, q.Prime → q₀ < q → ∀ f, C.EdgesOK (q ^ f) ∧ C.FormalOK (q ^ f)) ∧
    ∀ τ : ℝ, 0 < τ → τ ≤ 1 → histMoment C.hist mb τ ≤ histMoment hb mb τ

end IntMul.Kappa.R6.Bit

namespace IntMul.Kappa.R6

open IntMul NLogN NLogN.KIL NLogN.KFB NLogN.KFH NLogN.KFM IntMul.OpenAI.RT AModel

/-- **The uniform Proposition 14, parametric in the complex network `(Wc, mc, hc)`.** -/
def P14NeedG (Wc mc : ℕ) (hc : List (ℕ × ℕ)) (P : Prm) : Prop :=
  ∀ (tab : Fin 1 → IStmt HS 1) (l12 : IStmt HS 1), IL.L12Canon tab l12 P.τ →
  ∀ (T : ℕ) (J : Cx.Prop8IfaceH Wc T mc hc) (A : ℕ), IL3H.GClassH J A →
    histMoment hc mc P.σ < Wc →
    2 + mc * Real.log (histRankSum hc) ≤ P.C1 →
    ∃ Ew : ℕ → ℕ, EwOK6 P Ew ∧ IL3.P14UH' tab Ew P.lamp

end IntMul.Kappa.R6
