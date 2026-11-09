import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_KappaJainData

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000

/-!
# Round-seven staircase certificate: the child-width histogram, transcribed (milestone M2)

**Construction: S. Jain**, *integer-mult-kappa* round seven — ported and verified here.
This module is the transcription certificate for staircase step ②: the child-width
histogram of his witness-1 side program (`R = 28866` slots, PR #62 producer with PR #44's
moment-weighted link choice), rebuilt from his frozen schedule
(`certificates/round7/{deferred,witness}_23.json.gz` at `Swapnil-jain/integer-mult-kappa`
@ `c05adfe1`) and pinned against the workspace transcription `Jain.bitR7` in the kernel.

The derivation is upstream `scripts/certificate_round7.py` (his own checker, stdlib):
slot frame chains from `hold`/`start`/`late`, frame dims from the data file
(`node_dims`/`late_dims`/`sigma`/`vleaf_start`), chain ranks, deferred readout levels on
every target from the garbage-coefficient supports (`adjoint`/`ylevels`), `X_S` chains
from the V-gate order (`xs_order`), then the batched two-stage interchange histogram with
the staircase entrance corner (runs `(h-2, h-5, 1^6)`, certified at the integer point by
his `independent/deferred-readout/check_stair.py`).  The committed generator
`Solutions/gen_stair_r7.py` reproduces this file byte-for-byte from the pinned schedule
(sha256 recorded there); the kernel re-checks every identity below by `decide`.

Inputs (sha256):
  deferred_23.json.gz  8c38e947ff9e021e308000dd82bb5e2194eb265d8b75194e22ce783d3e75317c
  witness_23.json.gz   b2486aa2bb222bacea6e52162a3920780e45dd8edc5d7cb03eabea336a1c6588

The acceptance test of the staircase port (spec §3) is `stair_hist = Jain.bitR7` as
multisets, pinned here as a list equality; with it, domination at every `τ` is equality.
-/

namespace IntMul.Kappa.R7.StairHist

/-! ## The transcribed certificate -/

/-- The staircase-corner child-width histogram of Jain's round-seven witness 1,
rebuilt from his frozen schedule.  `width, count` pairs, sorted by width. -/
def stair_hist : List (ℕ × ℕ) :=
  [(1, 1690297301), (3, 1356586), (5, 354200), (7, 3580962), (9, 1526602), (11, 5093396), (13, 2164162), (15, 7948248), (17, 8476006), (18, 6272882), (19, 1639946), (21, 6906900), (23, 61280142), (439, 6272882), (483, 61280142), (485, 545468), (487, 173558), (489, 293986), (491, 580888), (493, 14168), (495, 322322), (497, 17710), (499, 1129898), (501, 127512), (503, 410872), (505, 99176), (507, 1186570), (509, 340032), (511, 322322), (513, 106260), (515, 1583274), (517, 626934), (519, 2854852), (521, 13711082), (523, 4629394), (525, 5653032), (527, 6233920)]

/-- **The certificate identity.**  The rebuilt histogram IS Jain's `bitR7` (his
`lean/Round7.lean` `bitHist`, "staircase entrance corner, witness 1"). -/
theorem stair_hist_eq_bitR7 : stair_hist = Jain.bitR7 := by rfl

/-! ## Certificate ledger (decide-checked derived quantities) -/

/-- Rank sum: exactly the fit-identity value `529·W − 1771·759` (M1 keystone). -/
theorem stair_hist_rankSum : histRankSum stair_hist = 57403754177 := by decide

/-- No child at full width `m = 529` (upstream assert `max(hist) < m`). -/
theorem stair_hist_widths_lt_m : (stair_hist.all fun p => p.1 < 529) = true := by decide

/-- Total child calls of the transcribed histogram (matches `bitR7_childCount`, M1). -/
theorem stair_hist_childCount : (stair_hist.map Prod.snd).sum = 1905413587 := by decide

/-- Entry count: the histogram has exactly the 37 width classes of `Jain.bitR7`. -/
theorem stair_hist_length : stair_hist.length = 37 := by decide

/-- Corner ranks `r_u = h − dim σ_u` over the `R = 28866` side slots
(the aux-edge corner multiset; feeds the run-profile assignment of step ③). -/
def corner_counts : List (ℕ × ℕ) :=
  [(1, 1760), (2, 1596), (3, 1307), (4, 3871), (5, 806), (6, 177), (7, 447), (8, 30), (9, 91), (10, 96), (11, 335), (12, 28), (13, 116), (14, 36), (15, 319), (16, 5), (17, 91), (18, 4), (19, 164), (20, 83), (21, 49), (22, 154), (23, 17301)]

/-- Every side slot carries a corner rank in `1..h-1`, and the counts total `R`. -/
theorem corner_counts_total : (corner_counts.map Prod.snd).sum = 28866 := by decide

/-- Chain-step ranks over all slot chains (`rk` of the derivation; the width-≤23 filler
ledger of step ③). -/
def chain_rank_counts : List (ℕ × ℕ) :=
  [(1, 55349), (2, 64873), (3, 13926), (4, 11248), (5, 6151), (6, 1617), (7, 883), (8, 1243), (9, 458), (10, 162), (11, 299), (12, 208), (13, 202), (14, 38), (15, 649), (16, 208), (17, 1309), (18, 599), (19, 533), (20, 2310), (21, 413)]

/-- The chain-rank ledger total (number of chain steps over all slots). -/
theorem chain_rank_counts_total : (chain_rank_counts.map Prod.snd).sum = 162678 := by decide

end IntMul.Kappa.R7.StairHist
