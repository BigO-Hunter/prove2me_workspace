# Sub-agent #5 report — third summit attempt, `IntMul.Kappa.R8.bitNetR8_mom`

## (a) Verdict: **FRONTIER** — with a decisive negative result that reshapes the map.

`net0P` — the only constructed-network candidate in the framework — **fails the moment arm
against BOTH open bit leaves** (bitR8 and bitR7plain). The MomEq route was already dead (#3);
the ≤ route is now dead too, by exact computation on ground truth. No compile path to the
target exists yet; the honest remaining route is the **onerun/oppbank construction** (leaf
`1ebc5981`), for which the moment arm is already decide-proved at the hist level.

## (b) Domination truth table (ground truth, 50-digit precision; `truth_table_final.py`, `verify_crossing.py`)

net0P.hist (exact counts, from replicated `genF` over the frozen data):
widths → counts: 1→1,265,498,157; 3→1,707,244; 5→2,532,530; 7→1,048,432; 9→1,172,402;
11→1,229,074; 13→3,014,242; 15→1,813,504; 17→24,794; 19→17,408,930; 21→21,092,610;
23→136,363,458; 439→6,272,882; 483→98,446,348.
Total children **1,557,624,607**; rank sum **55,594,957,495**.

| comparison | τ→0⁺ (count) | τ ∈ (0,1) | τ = 1 (rank) | verdict |
|---|---|---|---|---|
| net0P vs **bitR8** | ✗ +808,178,140 | ✗ exceeds at ALL τ (τ=.001: +8.03e8; τ=.5: +4.64e7) | ✗ +199,829,014 rank | **FAIL everywhere** |
| net0P vs **bitR7plain** | ✓ −116,735,332 | ✗ exceeds on τ∈(0.3317, 0.7802), peak +3.65e6 at τ=0.5 | ✓ −1,583,793,730 rank | **FAIL (crossing)** |

Both endpoints pass vs bitR7plain yet the middle violates — a pure crossing, so no
endpoint-tightening can save it. The window and peak were confirmed with `Decimal` ln/exp
at 50 significant digits (not float noise: relative excess ~2e-3 of the window diff).

**Ground-truth anchors** (Lean `#eval`, `Solutions/EvalComp.lean`): `recs = 54290`,
`W1F.length = 237921`, `W1F touch total = 536840` — the Python replication
(`genf_ranks.py`) matches all three exactly, then folds `genF` with dicts (Lean's own
`genF` is quadratic-closure-slow: `cs1.length` did not finish in 9 min; do not retry).

**Rank histograms** (per pass; DC1 = DC2, both stages identical):
r: 0→13016, 1→25510, 2→25258, 3→2987, 4→10042, 5→3871, 6→2463, 7→2257, 8→1427, 9→5371,
10→1114, 11→1660, 12→941, 13→482, 14→715, 15→296, 16→331, 17→347, 18→851, 19→512,
20→7, 21→4915, 22→4184, 23→10705. Moves/pass 119,262; chunk runs/pass 337,239; chunk
rank/pass 774,109. Packed base-2^32 constant ready for Lean `decide`:
`ground_truth_DC.json:packed_cn_true`.
⚠ **The platform MomPack `CN1_*`/`CN2_*` packs do NOT decode to these values** (32-bit
field sums give billions at r=4..14). MomPack's DC1/DC2 are wrong or misaligned —
reprove `cntF cs1/cs2` against the pack above before using anything from MomPack.

Run-shape facts used (verified against `EM_side`/`sideRuns` in-framework): SideR-r edge,
r≤11 → r runs of width 1; 12≤r≤23 → one run of width 2r−23 plus 23−r runs of width 1
(runs total 24−r, rank total exactly r); r>23 unsatisfiable (none occur). DataR →
{439, 21, 24×1} (rank 484); AuxR → {23, 483} (rank 506); ec (SideR 1) → {1}.

## (c) Obligation status for the three candidate witnesses

| witness | RunsOK | EdgesOK/FormalOK | moment arm ≤ bitR8 |
|---|---|---|---|
| uNet uniform (#4, `partial_bitR8_mom_gap.lean`, compiles) | ✓ all N (file :522) | ✓ all N (:546, :553) | ✗ τ=1 only, by 2541 (rank deficit 1,344,189 = 1771·759, structural) |
| net0P (`NB.net (toNB ProjB.ch0P)`) | ✓ proved (`BitOppbankGoodPrimes.runsOK0`) | OPEN (`GoodPrimesStmt`/`Net0OkStmt`) — now moot | ✗ **FALSE** (this session; table above) |
| onerun/oppbank net (NOT YET BUILT) | — | — | hist = oppbankHist = bitR8 **already decide-proved** (`MomPack.oppbankHist_eq_bitR8`) |

## (d) Obstacles + next brief's first move

**Platform frontier (fetched read-only this session; mission 51a41d26 "Jain round eight"):
exactly 3 open leaves** — `dd643349` cxNetR8G (complex side), `fefc194e` bitNetR7plain_mom,
`1ebc5981` oppbank_net. The target `2e2fbbed` bitNetR8_mom is Open with a sketch above the leaves.

**The chain that closes BOTH bit leaves from ONE construction:**
1. `oppbank_net` (1ebc5981): ∃T C q₀, RunsOK ∧ EdgesOK/FormalOK ∧ histMoment = histMoment bitR8
   (EQUALITY). Natural-language statement reveals the geometry: *"each residual of rank r
   becomes one contiguous reversed child of width r"* — the DataR residual 439+21+24 → one
   width-484 child (bitR8's (484, 6272882) count = 3542·1771 exactly ✓); AuxR 23+483 →
   width-506 children (bitR8's (506, 59760624) = 1771·33744 ✓). Schedule/frames/payload
   unchanged; only address geometry recompiled.
2. → `bitNetR8_mom` via platform-PROVED `BitNetMomStmtG_of_eq` (43926340; shape verified).
3. → `bitNetR7plain_mom` via the same witness + `IntMul.Kappa.Jain.bitR8_le_bitR7plain_mom`
   — **compiled green locally this session** (`Theorems/Thm_bitR8_le_bitR7plain_mom.lean`,
   39.7 s, zero sorry; Abel-summation `moment_dom` in `Thm_moment_dom.lean`). NB it uses
   `native_decide` twice — the platform rejects that; convert to `decide` before submitting.

**First move next brief:** define the onerun edge families — new run predicates (one
contiguous run of width = residual width, reversed pivots) replacing SideR/DataR/AuxR in
the `Ch` structure of `Def_IntMul_Kappa_R8_Data_BitOppbankProjB.lean`, then port xuanji's
R6 decomposition (`accepted_bitNetR6_mom.lean:2900-3096`): `chunk_mom` → `RS1_eq/RS2_eq`
retargeted to the ground-truth pack above → hist = oppbankHist (equality via
`oppbankHist_eq_bitR8`) → RunsOK trivial → the EdgesOK/FormalOK bundle at good primes is
the remaining heavy lift (R6 needed ~40 platform-proved imports; the oppbank analogs must
be proved fresh on the reversed geometry).

**Do NOT spend time on:** net0P domination (dead, table above), MomEq for any odd-only
net (dead, #3), uniform witnesses (dead, #4, structural 1344189), re-running Lean `#eval`
on `cs1`/`genF` (quadratic; use the Python replication), MomPack's CN packs (misdecoded).

Durable artifacts: `genf_ranks.py`, `truth_table_final.py`, `verify_crossing.py`,
`ground_truth_DC.json`, `EvalComp.lean`, `EvalSizes.lean`, `api_leaves.py` (read-only
frontier probe), this report.
