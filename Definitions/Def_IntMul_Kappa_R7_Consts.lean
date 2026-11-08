import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic
import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_KappaJainData

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Round-seven staircase constants and the fit identity (milestone M1)

**Construction: S. Jain**, *integer-mult-kappa* round seven — the staircase-interchange bit
network, staircase entrance corner, witness 1 (`lean/Round7.lean` at commit `c05adfe`,
`bitHist`). Ported and verified here; every number below is transcribed from his published
certificate and re-pinned as a kernel-checked theorem.

Role layout: `W = 2·N + 2·v·NR` (two data banks of `N = 3,136,441` points, plus `2·v·NR`
side-program roles: `v = 1771` centres × `NR = 28,866` slots per bank). `NR = 28,866` is
the round-seven side program (Jain README "Round seven": "builds the side program
(`R = 28866` slots)" — PR #62's producer with PR #41's alternating order and links and
PR #44's moment-weighted choice of links). It retargets the round-six/round-eight layout
(`Def_IntMul_Kappa_R8_Data_BitOppbankNet.lean`, `NR = 27,794`) by the same slot boundary:
`wEnt = 2·v`, `wAuxEnd = wEnt + NR`, `NL = wAuxEnd + h`.

**The fit identity** (the acceptance test of the staircase port, pinned here as theorems):

    529 * 108516254 - 1344189 = 57403754177 = rankSum Jain.bitR7

with `1,344,189 = 1771 × 759` the copy-correction (Jain's late-copy gate sharing:
759 = 33·h saved transpositions per centre per block). Upstream proves the rank sum by
`decide` (`lean/Round7.lean:59`, `bit_rank_sum`); the README states the budget as
"s = Wm − N + L". The same deficit holds for `Jain.bitR6` at `W = 148225616` — structural,
not coincidental.

**Per-block census.** `W = 1771 × 61274` roles; every role wire carries exactly one big
child (width > 23): 3542 width-18 (data, the staircase-corner run `h−5`), 34602 width-483
(aux), and 23130 across the odd tail 485..527; widths ≤ 23 are completion/correction filler.
Per block the total run-width is `529 × 61274 − 759`, i.e. exactly 759 transpositions below
the full own-frame content — the gate-sharing budget.

**DATA DRIFT (do not reconcile mid-port):** workspace `Jain.bitR7plain = (1, 1792923209)`
is an OLDER transcription of witness 2 (rank sum 55,395,128,481 at W = 104,719,230); the
upstream c05adfe `bitplainHist` reads `(1, 1803209177)` (rank sum 57,403,754,177 at
W = 108,516,254). `Jain.bitR7` itself matches upstream `bitHist` VERBATIM — this module
only consumes `bitR7`. Nobody should "fix" `bitR7plain` against upstream while the
staircase port is in flight.
-/

namespace IntMul.Kappa.R7.Stair

/-- Working height: `m = h * h = 529` (Jain round seven, `h = 23`). -/
def h : ℕ := 23

/-- Centres (Jain round six/seven `v = 1771`; one block per centre). -/
def v : ℕ := 1771

/-- Data points per bank (unchanged from rounds six/eight). -/
def N : ℕ := 3136441

/-- Side-program slots per centre per bank: the round-seven value **28,866**
(Jain README "Round seven", `R = 28866`; r6/r8 used 27,794; Δ = 1,072). -/
def NR : ℕ := 28866

/-- Width of the interchange: `m = 529 = h * h`; runs live on `2m = 1058` fields. -/
def m : ℕ := 529

/-- First side-role slot boundary: `wEnt = 2 * v` (data roles are `w < wEnt`). -/
def wEnt : ℕ := 2 * v

/-- End of the side-slot region: `wAuxEnd = wEnt + NR` (r8: 31336 = 3542 + 27794). -/
def wAuxEnd : ℕ := wEnt + NR

/-- Next boundary: `NL = wAuxEnd + h` (r8: 31359 = 31336 + 23). -/
def NL : ℕ := wAuxEnd + h

/-- **Round-seven role count.** Jain round seven bit side, staircase entrance corner,
witness 1 (`lean/Round7.lean` `momentOK bitHist ... 108516254`). -/
def W : ℕ := 108516254

/-- Provisional temporaries count, r6/r8 pattern `Tmp = 2·h·v + N = 46·v + N`.
`T` is ∃-quantified in `BitNetMomStmtG`; re-pin from the program when it exists.
No theorem here depends on this value. -/
def Tmp : ℕ := 46 * v + N

/-- The wire-point layout, first point of role `w` (retarget of the r8 `g1`). -/
def g1 (b w : ℕ) : ℕ :=
  if w < v then w * v + b
  else if w < wEnt then N + (w - v) * v + b
  else if w < wAuxEnd then 2 * N + b * NR + (w - wEnt)
  else W + h * b + (w - wAuxEnd)

/-- The wire-point layout, second point of role `w` (retarget of the r8 `g2`). -/
def g2 (a w : ℕ) : ℕ :=
  if w < v then N + a * v + w
  else if w < wEnt then a * v + (w - v)
  else if w < wAuxEnd then 2 * N + v * NR + a * NR + (w - wEnt)
  else if w < NL then W + h * v + h * a + (w - wAuxEnd)
  else W + 2 * h * v + a * v + (w - NL)

/-- Role merge: the two data banks are swapped, the side roles are fixed
(retarget of the r8 `ρn`; only indices below `2 * N` move). -/
def ρn (g : ℕ) : ℕ :=
  if g < N then g + N else if g < 2 * N then g - N else g

end IntMul.Kappa.R7.Stair

namespace IntMul.Kappa.R7.Stair

/-! ## Keystone arithmetic (all kernel `decide`, house pattern) -/

theorem W_eq : W = 2 * N + 2 * v * NR := by decide

theorem m_eq : m = h * h := by decide

theorem wEnt_eq : wEnt = 3542 := by decide
theorem wAuxEnd_eq : wAuxEnd = 32408 := by decide
theorem NL_eq : NL = 32431 := by decide

theorem ρn_lt_W (g : ℕ) (hg : g < W) : ρn g < W := by
  simp only [ρn]
  split_ifs with h1 h2
  · have hN : 2 * N ≤ W := by decide
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_right h1 N) hN
  · have hge : N ≤ g := le_of_not_gt h1
    have hlt : g - N < N := Nat.sub_lt_left_of_lt_add hge (by
      have : N + N = 2 * N := by ring
      simpa [this] using h2)
    have hN : N ≤ W := by decide
    exact Nat.lt_of_lt_of_le hlt hN
  · exact hg

/-- Definitional pin of the merged role map (r8 shape: `ρ = ⟨ρn, ρn_lt_W⟩`). -/
def ρ (w : Fin W) : Fin W := ⟨ρn w.val, ρn_lt_W w.val w.isLt⟩

/-! ## The fit identity — the acceptance test of the port -/

/-- Upstream `lean/Round7.lean` proves `rankSum bitHist = 57403754177` by `decide`;
here against the workspace transcription of his histogram. -/
theorem bitR7_rankSum : histRankSum Jain.bitR7 = 57403754177 := by decide

theorem Wm_eq : 529 * W = 57405098366 := by decide

/-- **The fit identity.** The staircase's copy-correction is exactly `1771 × 759`:
759 = 33·h transpositions saved per centre per block (Jain's late-copy gate sharing). -/
theorem bitR7_deficit : 529 * W - histRankSum Jain.bitR7 = 1771 * 759 := by decide

theorem deficit_val : 529 * W - histRankSum Jain.bitR7 = 1344189 := by decide

/-- Same correction, per centre: the deficit divides out over the 1771 blocks. -/
theorem deficit_per_centre :
    (529 * W - histRankSum Jain.bitR7) / v = 759 := by decide

/-- Structural: the same deficit holds for round six at its own role count. -/
theorem bitR6_deficit : 529 * 148225616 - histRankSum Jain.bitR6 = 1771 * 759 := by decide

/-! ## τ = 1 exactness — the tight moment arm -/

/-- The τ = 1 moment of a histogram is `rankSum / m`; here it is an exact integer. -/
theorem bitR7_moment_one_exact : histRankSum Jain.bitR7 = 529 * 108513713 := by decide

/-- The framework premise's slack at τ = 1: `108513713 < W = 108516254`, slack 2541. -/
theorem moment_slack : 108513713 < W ∧ W - 108513713 = 2541 := by decide

/-! ## Per-block census -/

/-- Roles per block. -/
theorem W_per_centre : W / v = 61274 ∧ 61274 * v = W := by decide

/-- Total child calls of `Jain.bitR7`. -/
theorem bitR7_childCount : (Jain.bitR7.map Prod.snd).sum = 1905413587 := by decide

/-- Big-child census per block: one big child (width > 23) per role — 3542 width-18
(staircase-corner data runs), 34602 width-483 (aux), 23130 across the odd tail 485..527. -/
theorem block_census : 3542 + 34602 + 23130 = 61274 := by decide

/-- Per-block rank ledger: the block total run-width is exactly 759 below the full
own-frame content — the copy-correction budget per centre. -/
theorem block_rank : histRankSum Jain.bitR7 = v * (529 * 61274 - 759) := by decide

end IntMul.Kappa.R7.Stair
