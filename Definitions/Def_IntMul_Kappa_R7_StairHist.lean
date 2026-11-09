import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_KappaJainData
import Definitions.Def_IntMul_Kappa_R7_Consts

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

/-! ## Deferred-level and X_S-chain ledgers -/

/-- Deferred-readout level diffs over all `v` targets: for each target, the consecutive
differences of `sorted(set([0] + levels + [h-1]))` (`ychains` levels of the derivation). -/
def ychain_diff_counts : List (ℕ × ℕ) :=
  [(1, 6325), (2, 2402), (3, 1121), (4, 1805), (5, 510), (6, 475), (7, 276), (8, 382), (9, 130), (10, 86), (11, 93), (12, 97), (13, 54), (14, 26), (15, 43), (16, 20), (17, 16), (18, 8), (19, 7), (21, 1), (22, 2)]

theorem ychain_diff_counts_total : (ychain_diff_counts.map Prod.snd).sum = 13879 := by decide

/-- `X_S` chain step widths over all leaves (`xs_order` V-gate chains; each leaf's diffs). -/
def xchain_diff_counts : List (ℕ × ℕ) :=
  [(1, 5061), (3, 23), (4, 208), (5, 11), (13, 11), (16, 198), (17, 22), (19, 1540)]

theorem xchain_diff_counts_total : (xchain_diff_counts.map Prod.snd).sum = 7074 := by decide

/-! ## Per-width derivation — the kernel rebuilds every count from the ledgers

Each equation is the batched two-stage interchange arithmetic (upstream `histogram()`):
each of the two stages contributes, per corner rank `r`, the big aux child `m − 2·r` and
the inner-corner decomposition `1^(h−r) ++ [2r−h]` (Jain's `inner` lemma, applied to
corner ranks, chain ranks, deferred-level diffs and `X_S` diffs over all `v` centres),
the `h`-cycle per stage contributes `inner(h−1, h) = [1, h−2]`, and the data entrance
contributes (once, stage-independent) the block `m − 4h + 2` with its staircase corner
runs `(h−2, h−5, 1^6)` and one copy-correction singleton per pair; the stage factor 2 is
written in each term.  `decide` re-derives each count from the ledger data above. -/
open IntMul.Kappa.R7.Stair

/-- Count of width `w` in a `(width, count)` ledger. -/
def lcnt (l : List (ℕ × ℕ)) (w : ℕ) : ℕ :=
  (l.filter fun p => p.1 = w).map Prod.snd |>.sum

/-- Corner-rank multiplicity (`r_u = h − dim σ_u` over the side slots). -/
def cc (r : ℕ) : ℕ := lcnt corner_counts r

/-- Chain-step rank multiplicity. -/
def rc (r : ℕ) : ℕ := lcnt chain_rank_counts r

/-- Deferred-level diff multiplicity over the targets. -/
def yd (d : ℕ) : ℕ := lcnt ychain_diff_counts d

/-- `X_S` chain diff multiplicity over the leaves. -/
def xd (d : ℕ) : ℕ := lcnt xchain_diff_counts d

theorem stair_count_1 : lcnt stair_hist 1 = 2 * v * cc 1 * 1 + 2 * v * cc 2 * 2 + 2 * v * cc 3 * 3 + 2 * v * cc 4 * 4 + 2 * v * cc 5 * 5 + 2 * v * cc 6 * 6 + 2 * v * cc 7 * 7 + 2 * v * cc 8 * 8 + 2 * v * cc 9 * 9 + 2 * v * cc 10 * 10 + 2 * v * cc 11 * 11 + 2 * v * cc 12 * 11 + 2 * v * cc 12 + 2 * v * cc 13 * 10 + 2 * v * cc 14 * 9 + 2 * v * cc 15 * 8 + 2 * v * cc 16 * 7 + 2 * v * cc 17 * 6 + 2 * v * cc 18 * 5 + 2 * v * cc 19 * 4 + 2 * v * cc 20 * 3 + 2 * v * cc 21 * 2 + 2 * v * cc 22 * 1 + 2 * v * cc 23 * 0 + 2 * v * rc 1 * 1 + 2 * v * rc 2 * 2 + 2 * v * rc 3 * 3 + 2 * v * rc 4 * 4 + 2 * v * rc 5 * 5 + 2 * v * rc 6 * 6 + 2 * v * rc 7 * 7 + 2 * v * rc 8 * 8 + 2 * v * rc 9 * 9 + 2 * v * rc 10 * 10 + 2 * v * rc 11 * 11 + 2 * v * rc 12 * 11 + 2 * v * rc 12 + 2 * v * rc 13 * 10 + 2 * v * rc 14 * 9 + 2 * v * rc 15 * 8 + 2 * v * rc 16 * 7 + 2 * v * rc 17 * 6 + 2 * v * rc 18 * 5 + 2 * v * rc 19 * 4 + 2 * v * rc 20 * 3 + 2 * v * rc 21 * 2 + 2 * v * h + 2 * v * yd 1 * 1 + 2 * v * yd 2 * 2 + 2 * v * yd 5 * 5 + 2 * v * yd 4 * 4 + 2 * v * yd 3 * 3 + 2 * v * yd 13 * 10 + 2 * v * yd 8 * 8 + 2 * v * yd 12 * 11 + 2 * v * yd 12 + 2 * v * yd 7 * 7 + 2 * v * yd 15 * 8 + 2 * v * yd 10 * 10 + 2 * v * yd 16 * 7 + 2 * v * yd 6 * 6 + 2 * v * yd 11 * 11 + 2 * v * yd 14 * 9 + 2 * v * yd 17 * 6 + 2 * v * yd 9 * 9 + 2 * v * yd 18 * 5 + 2 * v * yd 19 * 4 + 2 * v * yd 21 * 2 + 2 * v * yd 22 * 1 + 2 * v * xd 4 * 4 + 2 * v * xd 16 * 7 + 2 * v * xd 1 * 1 + 2 * v * xd 5 * 5 + 2 * v * xd 13 * 10 + 2 * v * xd 19 * 4 + 2 * v * xd 3 * 3 + 2 * v * xd 17 * 6 + 2 * N + 2 * N + 2 * N + 2 * N + 2 * N + 2 * N + N := by decide
theorem stair_count_3 : lcnt stair_hist 3 = 2 * v * cc 13 + 2 * v * rc 13 + 2 * v * yd 13 + 2 * v * xd 13 := by decide
theorem stair_count_5 : lcnt stair_hist 5 = 2 * v * cc 14 + 2 * v * rc 14 + 2 * v * yd 14 := by decide
theorem stair_count_7 : lcnt stair_hist 7 = 2 * v * cc 15 + 2 * v * rc 15 + 2 * v * yd 15 := by decide
theorem stair_count_9 : lcnt stair_hist 9 = 2 * v * cc 16 + 2 * v * rc 16 + 2 * v * yd 16 + 2 * v * xd 16 := by decide
theorem stair_count_11 : lcnt stair_hist 11 = 2 * v * cc 17 + 2 * v * rc 17 + 2 * v * yd 17 + 2 * v * xd 17 := by decide
theorem stair_count_13 : lcnt stair_hist 13 = 2 * v * cc 18 + 2 * v * rc 18 + 2 * v * yd 18 := by decide
theorem stair_count_15 : lcnt stair_hist 15 = 2 * v * cc 19 + 2 * v * rc 19 + 2 * v * yd 19 + 2 * v * xd 19 := by decide
theorem stair_count_17 : lcnt stair_hist 17 = 2 * v * cc 20 + 2 * v * rc 20 := by decide
theorem stair_count_18 : lcnt stair_hist 18 = 2 * N := by decide
theorem stair_count_19 : lcnt stair_hist 19 = 2 * v * cc 21 + 2 * v * rc 21 + 2 * v * yd 21 := by decide
theorem stair_count_21 : lcnt stair_hist 21 = 2 * v * cc 22 + 2 * v * h + 2 * v * yd 22 + 2 * N := by decide
theorem stair_count_23 : lcnt stair_hist 23 = 2 * v * cc 23 := by decide
theorem stair_count_439 : lcnt stair_hist 439 = 2 * N := by decide
theorem stair_count_483 : lcnt stair_hist 483 = 2 * v * cc 23 := by decide
theorem stair_count_485 : lcnt stair_hist 485 = 2 * v * cc 22 := by decide
theorem stair_count_487 : lcnt stair_hist 487 = 2 * v * cc 21 := by decide
theorem stair_count_489 : lcnt stair_hist 489 = 2 * v * cc 20 := by decide
theorem stair_count_491 : lcnt stair_hist 491 = 2 * v * cc 19 := by decide
theorem stair_count_493 : lcnt stair_hist 493 = 2 * v * cc 18 := by decide
theorem stair_count_495 : lcnt stair_hist 495 = 2 * v * cc 17 := by decide
theorem stair_count_497 : lcnt stair_hist 497 = 2 * v * cc 16 := by decide
theorem stair_count_499 : lcnt stair_hist 499 = 2 * v * cc 15 := by decide
theorem stair_count_501 : lcnt stair_hist 501 = 2 * v * cc 14 := by decide
theorem stair_count_503 : lcnt stair_hist 503 = 2 * v * cc 13 := by decide
theorem stair_count_505 : lcnt stair_hist 505 = 2 * v * cc 12 := by decide
theorem stair_count_507 : lcnt stair_hist 507 = 2 * v * cc 11 := by decide
theorem stair_count_509 : lcnt stair_hist 509 = 2 * v * cc 10 := by decide
theorem stair_count_511 : lcnt stair_hist 511 = 2 * v * cc 9 := by decide
theorem stair_count_513 : lcnt stair_hist 513 = 2 * v * cc 8 := by decide
theorem stair_count_515 : lcnt stair_hist 515 = 2 * v * cc 7 := by decide
theorem stair_count_517 : lcnt stair_hist 517 = 2 * v * cc 6 := by decide
theorem stair_count_519 : lcnt stair_hist 519 = 2 * v * cc 5 := by decide
theorem stair_count_521 : lcnt stair_hist 521 = 2 * v * cc 4 := by decide
theorem stair_count_523 : lcnt stair_hist 523 = 2 * v * cc 3 := by decide
theorem stair_count_525 : lcnt stair_hist 525 = 2 * v * cc 2 := by decide
theorem stair_count_527 : lcnt stair_hist 527 = 2 * v * cc 1 := by decide

end IntMul.Kappa.R7.StairHist
