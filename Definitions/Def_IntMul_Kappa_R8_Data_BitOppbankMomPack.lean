import Mathlib
import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_KappaJainData
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankHist
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSideRanks
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankGenCN

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# Opp-bank mom_eq packaging pieces (GenCN + SideRanks + Hist)

Histogram identity for open `oppbank_net`:
`oppbankHist = Jain.bitR8`, hence equal `histMoment` at every τ.
Also: SideRanks count, GenCN `nNodes`/`codeBound`, and per-rank `cnField`
extractor for densified `cntF` packs (Defs51 `RS*_eq` retarget).
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.MomPack

open IntMul.Kappa
open IntMul.Kappa.Jain
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.GenCN

/-- Densified opp-bank one-run histogram matches platform `Jain.bitR8`. -/
theorem oppbankHist_eq_bitR8 : oppbankHist = bitR8 := by decide

/-- Moment identity used by `mom_eq` packaging (histogram level). -/
theorem histMoment_oppbank_eq_bitR8 (m : ℕ) (τ : ℝ) :
    histMoment oppbankHist m τ = histMoment bitR8 m τ := by
  rw [oppbankHist_eq_bitR8]

theorem histMoment_oppbank_bitR8_529 (τ : ℝ) :
    histMoment oppbankHist 529 τ = histMoment bitR8 529 τ :=
  histMoment_oppbank_eq_bitR8 529 τ

theorem sideRanks_count : sideChainRankHist_count = 162155 := sideChainRankHist_count_eq

theorem genCN_nNodes : nNodes = 62478 := nNodes_eq

theorem genCN_codeBound : 1773 + nNodes = 64251 := by
  simp [nNodes]

/-- 32-bit field extractor for packed `cntF` rank counts (Defs51). -/
def cnField (P i : ℕ) : ℕ := P / 2 ^ (32 * i) % 2 ^ 32

theorem cnField_lt (P i : ℕ) : cnField P i < 2 ^ 32 :=
  Nat.mod_lt _ (by decide : 0 < 2 ^ 32)

/-- Additive stage-1 rank histogram from GenCN `CN1_*` packs. -/
def DC1 (r : ℕ) : ℕ :=
  cnField CN1_0 r + cnField CN1_1 r + cnField CN1_2 r + cnField CN1_3 r +
    cnField CN1_4 r + cnField CN1_5 r + cnField CN1_6 r + cnField CN1_7 r +
    cnField CN1_8 r + cnField CN1_9 r + cnField CN1_10 r

/-- Additive stage-2 rank histogram from GenCN `CN2_*` packs. -/
def DC2 (r : ℕ) : ℕ :=
  cnField CN2_0 r + cnField CN2_1 r + cnField CN2_2 r + cnField CN2_3 r +
    cnField CN2_4 r + cnField CN2_5 r + cnField CN2_6 r + cnField CN2_7 r +
    cnField CN2_8 r + cnField CN2_9 r

theorem DC1_0 : DC1 0 = 17008 := by decide
theorem DC1_1 : DC1 1 = 32991 := by decide
theorem DC2_0 : DC2 0 = 17008 := by decide

/-- Combined stage rank count (feed for `side_total` / `RS*_eq`). -/
def DC (r : ℕ) : ℕ := DC1 r + DC2 r

theorem DC_0 : DC 0 = 34016 := by
  simp only [DC, DC1_0, DC2_0]

end IntMul.Kappa.R8.Bit.Oppbank.MomPack
