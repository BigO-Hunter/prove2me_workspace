# Gap (B′) research notes — `bitR8_dom_witness` (2026-11-08)

## Verdict: the witness AS STATED (W = 108516254, ≤ bitR8) is unsatisfiable
Numerically precise obstruction; formal impossibility lemma named below.

- `bitR8` (= `oppbankHist`, rank sum **55,395,128,481**) has τ=1 moment
  `55395128481 / 529 = 104,716,689.0`.
- Any `FormalOK` net at **W = 108516254** (Jain r7 roles) has τ=1 moment ≥ W
  (each role frame must realize the full `swapMat` — ≥ 529 edge transpositions
  on its own line; Jain copy-correction shaves only the frozen 1,344,189 =
  1771×759): min rank sum ≥ `529 × 108516254 = 57,405,098,366`.
- Shortfall at W=108516254: **2,009,969,885** rank units (≈ 15× the entire
  copy-correction saving). At the r8 lane's W=104719230 the shortfall is
  exactly 1,344,189 — i.e. bitR8's scale is the **r8 role count**.

⟹ `bitNetMomStmtG_of_bitR8_dom` (MomentDom_tail, W = 108516254) has no
witness; the plug-in should be re-plumbed to W = 104719230, or `bitNetR7_mom`
must go back to direct bitR7-domination (the original r7 staircase witness).

## What exists (assets)
- `BitOppbankGoodPrimes.runsOK0` : `net0P.RunsOK` — **proved**, sorry-free.
- `GoodPrimesStmt` / `Net0OkStmt` (same file): **stated, open** — the
  EdgesOK/FormalOK-at-good-primes obligations for `net0P` (W = 104719230).
- r6 full assembly recovered at checkpoint `5126ec4`: `net ch0`, `net0_ok`
  (q₀ = 3217907), `mom_eq τ` (moment EQUALITY with bitR6),
  `bitNetR6_mom_sol_aux` — the proved template for the final assembly.
- `Solutions/api_keystone.py` + credentials: prove2.me API, keystone
  `1ebc5981 oppbank_net` fetchable (upstream source of truth).
- `Solutions/partial_bitR8_mom_gap.lean`: cheap-witness template
  (runs `(0,0,528),(528,528,1)`, q₀ = 0, obligations 2–3 proved at every
  modulus) — proves the τ=1 impossibility analysis at r8's W.

## Constraint characterization (for the witness at ANY W)
1. `RunsOK`: every run `(h, d, r)` with `0 < r < 529`, inside chunks.
2. `EdgesOK (q^f)`: Bruhat data admissible mod q^f (good-prime filter).
3. `FormalOK (q^f)`: role `ρ w` ends `= single (swapMat, w) 1` — the full
   529-transposition content per role; this is what forces the rank-sum
   lower bound above.
4. Domination: `histMoment C.hist 529 τ ≤ bitR8 τ` for τ ∈ (0,1] ⟺
   cumulative rank mass (moment_dom_cum), tightest at τ=1, i.e. total
   rank sum ≤ 55,395,128,481.

## Single next mathematical step
Prove `Net0OkStmt` (the EdgesOK/FormalOK-at-good-primes obligations for
`net0P`) → yields `BitNetMomStmtG 104719230 529 Jain.bitR8` (closes
`bitNetR8_mom`), then re-plumb the platform W: either retarget
`bitR8_dom_witness`/`bitNetMomStmtG_of_bitR8_dom` at W = 104719230, or
produce the original r7 staircase witness at W = 108516254 against bitR7.
Formal side-goal: a proved lemma `FormalOK C → (C.hist.map (·.1)).sum ≥
529 * W - 1344189` (per-role-frame lower bound) to turn the impossibility
above into a theorem.
