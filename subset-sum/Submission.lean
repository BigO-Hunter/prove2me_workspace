import Submission.SubsetSumStatement

/-!
# Subset-sum first-mover submission (R2125607414): deterministic MITM, α = 51/100

Target: `BigOSpeedrun.SubsetSum.SolvedInTime (51 / 100 : Rat)`.

## Plan (flock-strike decomposition)

1. **Program** — one `List Instr` for all `n` (reads `n` from cell 0):
   - Phase A: enumerate + store the `2^h` subset sums of the first half
     `h = ⌊n/2⌋` into an array via indirect `store` (memory is a total map).
   - Phase B: bottom-up merge sort of the stored sums (`2^h · h` compares —
     insertion sort is NOT acceptable at `O(4^h) = O(2^n)`).
   - Phase C: enumerate second-half sums; for each, binary-search `t - s` in
     the sorted half (h steps each); accept on hit, else reject.
2. **Invariants** — memory layout discipline; loop-carried `exec` invariants.
3. **Correctness** — enumeration completeness ∘ merge-sort correctness ∘
   binary-search completeness ⟹ `run P x ρ t = some x.yes` for every `ρ`
   (deterministic: `rand` never executed ⟹ the 2/3 tape condition at 100%).
4. **Runtime** — potential function ⟹ explicit `T n = C · 2^h · n²`;
   `BigO T (51/100)`: `T(n)^100 ≤ K · 2^(51·n)` with slack.
5. **Packaging** — vendored byte-exact statement (sha 80bc6d28…), `Race.bound`,
   the proven submission pipeline.

## Status

Scaffold. No theorems yet — build order: program def → step invariants →
correctness → runtime → `Race.bound`. No `sorry`, ever (their hygiene scan
and ours).
-/

-- The program, the invariants, and Race.bound land here.
