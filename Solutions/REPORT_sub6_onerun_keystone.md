# Sub-agent #6 report — FOURTH summit attempt, keystone `IntMul.Kappa.R8.Bit.oppbank_net` (`1ebc5981`)

## (a) Verdict per rung

| rung | verdict | artifact |
|---|---|---|
| 1. onerun net defined + RunsOK | **LANDED** | `Solutions/onerun_net_rungs12.lean` :`onrNet`, :`onrNet_RunsOK` |
| 2. hist = oppbankHist (= bitR8) at every τ | **LANDED** | :`onerun_mom_eq`, :`onerun_mom_eq_oppbank`, :`oppbankHist_eq` |
| 3. EdgesOK / FormalOK | **half**: EdgesOK at EVERY N (q₀=0) ✅ :`onrNet_EdgesOK`; FormalOK **OPEN** (structural, see (d)) |
| 4. both bit leaves | not reached (hangs on Rung 3 FormalOK) |

Whole file compiles clean (`lake env lean`, ~74 s, zero sorry/warnings). Axiom audit:
`onerun_rung12`, `onerun_mom_eq`, `onrNet_RunsOK`, `onrNet_EdgesOK` → `[propext, Classical.choice,
Quot.sound]` only; `bitR8_rankSum`, `bitR8_deficit`, `bitR8_deficit_per_block`, `bitR8_block_census`
→ `[propext]` or none. Packaged near-keystone:

```
onerun_rung12 : ∃ (T C q₀), C.RunsOK ∧ (∀ q prime > q₀, ∀ f, C.EdgesOK (q^f)) ∧
                                ∀ τ ∈ (0,1], histMoment C.hist 529 τ = histMoment Jain.bitR8 529 τ
```
with `T = 0`, `q₀ = 0` — everything in leaf `1ebc5981` **except** the `FormalOK` conjunct, and the
edge half holds at *every* prime power, strictly stronger than "above q₀".

## (b) Reversed-child predicate design

- `revRun w = (0, 529 − w, w)` — ONE contiguous run reading the D-chunk from the opposite bank
  (pivots `H_k ↔ D_{529−w+k}`); `RunOK 529` holds exactly for `1 ≤ w ≤ 529` (`(529−w)+w = 529 ≤ 529`).
- Predicates for the `Ch` families (drop-in for `ProjB.SideR/DataR/AuxR`): `RevSideR r := rs = [revRun r]`,
  `RevDataR := [revRun 484]` (R6 data rank 439+21+24·1 = 484 preserved: `RevSideR_rank`),
  `RevAuxR := [revRun 506]` (rank 23+483 = 506). Width profile collapses to the single even width;
  rank is exactly preserved (a width-w run has w pivots).
- **Per-block census (decide-proved, `bitR8_block_census` / `bitR8_block_rank`)**: `W/1771 = 59130`
  roles = `3542` width-484 + `33744` width-506 + `21844` width-507..528 big runs — every role wire
  carries exactly ONE big reversed child; all widths 1..22 (364047 runs, total width 1035925) are
  completion/correction filler. Ledger: big 30243086 + small 1035925 = `529·59130 − 759` exactly.
- The onerun net places one `revEdge w = ⟨1, [revRun w], 1⟩` per run of the exact bitR8 expansion
  (`expHist`), so hist ≡ bitR8 by construction (`sum_expHist` regrouping + `h3` coercion bridge).

## (c) Obligation statuses (Solutions/onerun_net_rungs12.lean : line)

- `RunsOK` ✅ `onrNet_RunsOK` :204 (via `bitR8_bounds` :178 decide + `runOK_revRun` :118)
- `EdgesOK (q^f)` ✅ all N, `onrNet_EdgesOK` :216 / `revEdge_EdgeOK` :124 / `redQ_one` :101
- `histMoment = bitR8` ✅ `onerun_mom_eq` :246 (+ bridges :285 `oppbankHist_eq := rfl`,
  :288 `onerun_mom_eq_oppbank`; packaged in `onerun_rung12` :260)
- `FormalOK` ❌ OPEN — the 759/block deficit is structural (below)

## (d) Obstacles + next brief's first move

**Why FormalOK is the whole remaining game.** `histRankSum bitR8 = 529·W − 1771·759` (`bitR8_deficit`).
I proved to my satisfaction (informal, this session): with trivial Bruhat factors (E₁=E₂=1) every
edge matrix is a permutation matrix, and a wire whose formal frame is assembled from its own edges
needs its runs' transpositions to multiply to the block swap ⇒ **≥ 529 own width per role wire**
(the swap moves all 1058 points; each run transposition moves 2; Bruhat position of a unipotent-
sandwiched run product is the run permutation's position). The histogram is 1344189 = 1771·759 BELOW
529·W, so no pure-permutation own-frame witness exists — this also kills #4's uNet family for
EQUALITY, not just domination. Gate sharing (XOR zeroing of a wire's junk via a preserved self-copy
is free) cannot split a mixed-tag value: W output singles need W independent frame-s vectors — the
deficit is exactly Jain's 1771 copy-corrections per block.

**Three routes forward, ranked:**
1. **Unipotent Bruhat glue (fresh, no platform data):** a wire reaches `swapMat` through
   `U₁ P(σ₁) T P(σ₂) U₂` with |σ₁|+|σ₂| < 529 when `σ₁σ₂ ≥_Bruhat w_block` and a unipotent T drops
   the position to exactly `w_block`. **First move: build the d=1 saving gadget on a small analog
   (m = 4: explicit rational U, V via sympy, verify U P(σ₁) T P(σ₂) V = swap numerically), then
   formalize the m=4 instance in Lean before generalizing.**
2. **Certificate route (published skeleton `NB.net ch0`)** — blocked: `Theorems/Thm_pnd_obstruction.lean`
   proves `¬DensifiedSupportOK` (densified nest data defective at codes 1773/1774; `argRel 0 1` true
   but the two singleton projectors are non-nested). Needs corrected densified tables from the
   platform, or the `FB0` route rebuilt off `orthOK`-true stubs.
3. Report the data defect upstream — the published `TPTS/ARGT/DIMT` densification cannot support
   `pnd_hPis0`/`pnd_Dm_rank` as stated.

**Do NOT spend time on:** net0P (dead, #5), uniform witnesses (dead, #4 + this session's Bruhat
argument), MomPack CN packs (misdecoded, #5), re-deriving #3's MomEq disproof.

Durable artifacts: `Solutions/onerun_net_rungs12.lean` (the rungs 1–2 + EdgesOK core),
`Solutions/onerun_sanity.py`, `Solutions/rank_book.py`, this report.
