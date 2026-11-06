import Mathlib.Data.Nat.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Side-chain rank multiset of Jain round-7 witness 2

`rk` from `certificate_round7.build`: counts of charged h-space chain steps by rank.
Used by both plain and opp-bank histogram rebuilds. Schedule metadata for BitNB transplant.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank

def sideChainRankHist : List (ℕ × ℕ) :=
  [(1, 50763), (2, 71662), (3, 9939), (4, 13176), (5, 6400), (6, 1869), (7, 703), (8, 1127), (9, 585), (10, 219), (11, 235), (12, 243), (13, 188), (14, 141), (15, 668), (16, 1009), (17, 473), (18, 36), (19, 2219), (21, 500)]

def sideChainRankHist_count : ℕ := (sideChainRankHist.map (·.2)).sum

theorem sideChainRankHist_count_eq :
    sideChainRankHist_count = 162155 := by decide

end IntMul.Kappa.R8.Bit.Oppbank
