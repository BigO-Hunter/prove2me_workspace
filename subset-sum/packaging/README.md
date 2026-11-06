# Subset Sum: O(2^(αn)) on the randomized word RAM

A Lean 4 proof that subset sum is solvable in time O(2^(αn)) on the
randomized word RAM model of the Big O Speedrun (bigospeedrun.com),
with α = 1/2 — deterministic, no polynomial factor.

## The program

A single finite program (301 instructions) for all input sizes n ≥ 2:
- **Prologue**: relocates the input block above the register file
  (RELOC = 2n + 23), computes h = n/2, and sets up arrays
- **Phase A**: builds the sorted subset sums of the first half
  {a₁, ..., a_h} by doubling merges (S_{k+1} = merge(S_k, S_k + a_{k+1}))
- **Canon**: clamps first-half sums above t to t+1 (unusable in any
  solution since all inputs are positive), preserving sortedness
- **Phase A2**: builds the sorted subset sums of the second half by the
  same doubling-merge machine
- **Scan B**: one linear two-pointer sweep over the two sorted arrays
  decides all pair sums within 10·(2^h + 2^(n−h)) + 3 steps
- **Small-n path** (n ≤ 3): unrolled verdicts

The program is deterministic (never uses `rand`), so correctness holds at
100% on every random tape, satisfying the 2/3 threshold trivially.

## The proof

- **Spec layer** (`Spec.lean`): the MITM decomposition theorem — a subset
  sum over h + n indices decomposes as a first-half sum s ≤ t and a
  shifted-second-half sum t − s
- **Bridge** (`Bridge.lean`): the statement's `Instance.yes` ↔ the spec's
  `isSum`
- **Sort** (`Sort.lean`): the doubling-merge construction produces sorted
  lists containing exactly the subset sums
- **Fit** (`Fit.lean`): all values fit in w-bit words (w ≥ 4(n + b))
- **Words** (`Words.lean`): BitVec ↔ Nat vocabulary, wrapped complements
  are unmatchable
- **ExecEq** (`ExecEq.lean`): the bench mirror IS the statement's `exec`
- **PhaseA/B/SmallN**: exec-level invariants for each program phase
- **Runtime**: the small-n horizon (stepBound) reused by T2, and the
  legacy BigO discharge at α = 3/4
- **Race**: assembles the 3/4 bound (`SolvedInTime (3/4)`)
- **Prog2\***: the exec-walk chain over the poly-free program — layout,
  canon, both merges, the two-pointer scan, prologue, small-n, compose
  (`total2`), and `Correct prog2` for every n ≥ 2
- **Prog2BigO**: `BigO T2 (1/2)` with the explicit constant K = 2^80,
  and the summit `Race_bound' : SolvedInTime (1/2)` exported by the
  root `Submission.lean`

## Building

```bash
lake build Submission
```

No Mathlib dependency — the proof uses only core Lean 4.
