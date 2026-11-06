# FRONTIER notes — `IntMul.Kappa.R8.bitNetR8_mom` (BigO Lean strike, sub-agent #4)

Target (platform theorem `2e2fbbed-4b7d-41fb-805a-f7ccbd667355`, status Open):
`theorem solution : BitNetMomStmtG 104719230 529 Jain.bitR8`.

Delivered artifact: **`Solutions/partial_bitR8_mom_gap.lean`** — compiles clean
(`lake env lean`, no sorry, no warnings). It proves a COMPLETE analogous theorem
`cheap_witness_stmt : BitNetMomStmtG 104719230 529 hb0` with `hb0 = [(528,104719230),(1,104719230)]`,
plus the arithmetic gap lemmas.

## What the artifact proves

The **uniform cheap witness**: `uNet = ⟨(List.range W).map uInstr, id⟩` — one edge per role,
`E₁ = E₂ = 1`, runs `(0,0,528),(528,528,1)` (their pivot product is the full chunk swap).
At **every** modulus `N` (hence `q₀ = 0`):
- `uNet_RunsOK` (every run `RunOK 529`),
- `uNet_EdgesOK N` (identity Bruhat factors: zero above diagonal, unit diagonals),
- `uNet_FormalOK N` (each role's frame = `swapMat` exactly: `edgeMat N uEdge = AModel.swapMat`,
  via `uEdge_prod` (run permutation = block swap) + `permMatrix_swapE` + `redM_one`),
- exact histogram moment `histMoment uNet.hist 529 τ = W·((528/529)^τ + (1/529)^τ)`.

So obligations 2–3 (RunsOK, EdgesOK/FormalOK at prime powers) are NOT the bottleneck for a
cheap witness — the ONLY obstruction is the moment arm.

## The arithmetic gap (why the cheap witness cannot meet `Jain.bitR8`)

- `cheap_rank : histRankSum hb0 = 529 * 104719230 = 55396472670`
- `bitR8_rank : histRankSum Jain.bitR8 = 55395128481`
- `rank_gap : 529 * 104719230 > 55395128481`, deficit `deficit_factor = 1771 * 759 = 1344189`.
- `count_arm` is FINE: cheap children 2·104719230 = 209438460 ≤ 749446467 (bitR8's count).
τ=1 moment = rank/529, so the cheap witness loses only at τ near 1, by 2541 in moment terms.

**All three frozen histograms share the same deficit**: bitR6 rank = 529·148225616 − 1344189,
bitR7plain and bitR8 rank = 529·104719230 − 1344189. The 1344189 = v·759 (v = 1771) saving is
the certificate's gate-sharing.

## Structural result (prose, not formalized): cheap witnesses are IMPOSSIBLE

For any witness, `FormalOK N` forces each role's final frame = `swapMat`; combined with
`EdgesOK` (E₁,E₂ lower-triangular with unit diagonals), the Bruhat position of the frame
product equals the product of the run-permutation parts (triangular factors contribute
position `e`; `pos(AB) = pos(A)·pos(B)`, `pos(b) = e` for lower-triangular `b`). Over the
residue field F_q the final frame is `swapMat`, whose permutation is the full chunk swap —
transposition length exactly 529. So any role whose frame is assembled from its OWN edges
needs run-rank ≥ 529 ⇒ total ≥ 529·W = 55 396 472 670 > σ₁(bitR8). **Gate-sharing via
Jain's copy-correction is mathematically necessary**; the real witness must be the
certificate network (`net0P`-family), whose sharing saves exactly 1344189.

## Platform map (fetched via API)

- target `2e2fbbed` (Open) `bitNetR8_mom : BitNetMomStmtG 104719230 529 Jain.bitR8`
- `b40cfe62` (Open) `oppbank_mom_of_plain : BitNetMomStmtG 104719230 529 bitR7plain → BitNetMomStmtG 104719230 529 bitR8`
  (the "opposite bank" recompile: each rank-r residual becomes one contiguous reversed child).
- `fefc194e` (Open) `bitNetR7plain_mom : BitNetMomStmtG 104719230 529 Jain.bitR7plain`.
- PROVED `6d4ae477` `bitNetR6_mom` — xuanji's accepted witness, fetched to
  `Solutions/accepted_bitNetR6_mom.lean` (3100 lines): witness `⟨3217907, net ch0, q₀, …⟩`,
  `mom_eq : histMoment (net ch0).hist 529 τ = histMoment bitR6 529 τ` (EXACT equality),
  `net0_ok` imported from ~40 proved platform theorems (formalOK, good_edges, good_mats,
  flagBasis, stage1/2_seg, DagC/Loc/Dim checks). R8 needs the same bundle retargeted.
- PROVED `43926340` `BitNetMomStmtG_of_eq` — bridge (equality ⇒ domination), fetched to
  `Solutions/accepted_BitNetMomStmtG_of_eq.lean`.

## Numerics (Python, /tmp mom2.py)

`histMoment bitR8 529 τ < histMoment bitR7plain 529 τ` for ALL τ ∈ (0,1), EQUAL at τ=1
(both rank sums 55395128481; counts 749446467 vs 1993393325). So `oppbank_mom_of_plain`
must transform the NETWORK, not just compare moments.

## In-framework assets (Definitions/) for the real route

- `BitOppbankGoodPrimes.runsOK0 : net0P.RunsOK` — **proved**. Also `edges_E0`,
  `E0_Q : ∀ e ∈ E0, ∃ q, EdgeQ e q`. OPEN: `GoodPrimesStmt` / `Net0OkStmt`
  (EdgesOK + FormalOK at good primes — the R6 analogs were imported platform theorems
  `Thm_IntMul_Kappa_R6_Bit_NB_{formalOK,good_edges,good_mats}`).
- `BitOppbankMomPack.oppbankHist_eq_bitR8 : oppbankHist = bitR8` — **proved by decide**;
  `histMoment_oppbank_bitR8_529`. `NetMom.hist_target`, `MomEqStmt`, `momEq_of_hist_eq`.
  Predecessor (#3) proved `MomEqStmt` for `net0P` FALSE (mom_eq disproof,
  `Solutions/solution_mom_eq_disproof.lean`); the DOMINATION direction for net0P is open.
- `NetMom.EM_side/EM_aux/EM_data`, `sideV/auxV/dataV`, `sideRanks_count = 162155`,
  `DC₁/DC₂/DC` packs (MomPack) — the edge-moment algebra for a net0P moment computation.

## Recommended next move (priority order)

1. Compute/prove `histMoment net0P.hist 529 τ ≤ histMoment bitR8 529 τ` (or find the
   crossing) using NetMom's EM decomposition + the GenCN/SideRanks rank packs. If ≤ holds,
   the moment arm + RunsOK are done for net0P and the frontier is exactly `GoodPrimesStmt`.
2. Port R6's `formalOK`/`good_edges`/`good_mats` bundle to the R8 certificate
   (GoodPrimes already stages `M0`/`EM0` finite packs at `codeBound = 64251`).
3. Alternatively prove `oppbank_mom_of_plain` + `bitNetR7plain_mom` (platform-stated chain).
