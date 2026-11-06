# Round-7 port: what is proved, and the exact obstruction for gap (B)

Branch `jain-r7-port-attempt`. Local only: no platform submissions, no pushes,
no milestone changes.

## The four isolated gaps in `Theorems/Thm_IntMul_Kappa_jain_round7_aux.lean`

| gap | lemma | status |
|---|---|---|
| A | `r7_normalize` | **PROVED** (this branch) |
| B | `bitNetR7_mom : BitNetMomStmtG 108516254 529 Jain.bitR7` | `sorry` — open on the platform too |
| C | `p14NeedG_cxR6` | `sorry` — gated on a dependency-closure build |
| D | `kappa_of_networks_G` | `sorry` — needs a parametric adaptation of `kappa_final6_at` |

## Gap (A) — closed

The recovered accepted solution `IntMul.Kappa.R6.rG_normalize_sol_aux`
(`Solutions/recovered/rG_normalize.b23cbd4f.lean`, landed as
`Theorems/Thm_IntMul_Kappa_R6_rG_normalize.lean`) is already the parametric form
the port needs — arbitrary complex width `mc` and rank sum `sc`:

```lean
theorem rG_normalize_sol_aux (mc sc : ℕ) (ab ac ε x C₁ κ : ℝ)
    (hτ : 0 < 1 - ab) (hσ : 0 < 1 - ac) (hab : 0 ≤ ab) (hac : 0 ≤ ac)
    (hasm : CrudeAssembly ab ac (1 / 1000) ε x C₁ κ mc sc) :
    ∃ P : Prm, P.Ok ∧ κ < P.gap ∧ P.τ = 1 - ab ∧ P.σ = 1 - ac ∧
      2 + mc * Real.log sc ≤ P.C1
```

so `r7_normalize` is a one-line instantiation at `(576, histRankSum Jain.cxR6)`.
It matches the gap statement shape exactly, including the `P.τ = 1 - ab` /
`P.σ = 1 - ac` equalities the round-six `r6_normalize` does not state.

## Gap (B) — the new math, and why it is not a moment problem

The statement demands a `QHNet (ZMod 2) 108516254 T 529` with `RunsOK`,
`EdgesOK`/`FormalOK` at all large prime powers, and child-width moments dominated
by `Jain.bitR7`.

### The moment side is free

`histMoment h m τ = Σ_{(w,n)} n * (w/m)^τ`, so the `τ → 0+` limit is the total
child-call count `Σ n_w`. Measured (`Solutions/mom_cmp_r7.py`, exact rational/
Decimal arithmetic):

| τ | bitR7 | bitR7plain | bitR8 |
|---|---|---|---|
| → 0+ | 1 905 413 587 | 1 993 393 325 | 749 446 467 |
| 0.5 | 198 644 802 | 197 308 120 | 145 903 323 |
| 1 | 108 513 713 | 104 716 689 | 104 716 689 |

* `bitR8 ≤ bitR7` at **every** τ in [0,1] — no crossing exists.
* `bitR7plain ≤ bitR7` only for τ ≥ ≈0.447296115, and **fails** below it.

So the moment bound is not the obstruction. A network whose histogram is
`oppbankHist` (= bitR8 in moment) already dominates `bitR7` everywhere; that
network exists as `Net0Pnd.net0Pnd`.

### The obstruction is the role count, and it is structural

`Net0Pnd.net0Pnd : QHNet (ZMod 2) 104719230 3217907 529`, and `W` is a **hardcoded
constant** in the `NB` construction (`Definitions/Def_IntMul_Kappa_R8_Data_BitOppbankQHNet.lean`:
`def net (ch : Ch) : QHNet (ZMod 2) W Tmp 529` with `theorem net0_W_val : W = 104719230`).
Nothing in the workspace has `W = 108516254`; `108516254` appears only in
`Def_IntMul_KappaJainData.lean` and the round-7 framework/aux files.

The obvious rescue — embed a `W = 104719230` network into a `W' = 108516254` one
by leaving the extra 3 797 024 roles idle — **is impossible**, and the reason is
`QHNet.FormalOK`:

```lean
def FormalOK (C : QHNet R W T m) (N : ℕ) : Prop :=
  ∀ w, C.prog.foldl (fStep N) (fInit N) (.inl (C.ρ w)) = Finsupp.single (swapMat, w) 1
```

It quantifies over **every** `w : Fin W` and demands each role carry the
`swapMat` label with its own index. An idle role keeps label `1`, so `FormalOK`
fails for every padded role. `RunsOK` and `EdgesOK` are `edges`-only and would
survive padding; `FormalOK` does not. Padding therefore cannot be a purely
combinatorial reindexing — the extra roles must be genuinely wired into the
interchange, i.e. it is a real network construction.

This is consistent with the platform: `IntMul.Kappa.R6.Bit.bitNetR7_mom`
(theorem id `e27d1a90-cfee-4b83-9b0b-b6c6f0ab652d`) is **status Open**, with no
accepted submission. Round 6's analogue at `W = 148225616` was proved; round 7's
was not.

### Sharpest obstruction statement

> `bitNetR7_mom` follows immediately from
> `∃ (T : ℕ) (C : QHNet (ZMod 2) 108516254 T 529) (q₀ : ℕ), C.RunsOK ∧
>   (∀ q prime > q₀, ∀ f, C.EdgesOK (q^f) ∧ C.FormalOK (q^f)) ∧
>   ∀ τ ∈ (0,1], histMoment C.hist 529 τ ≤ histMoment Jain.bitR8 529 τ`
>
> together with `Jain.bitR8_le_bitR7_mom : ∀ τ ∈ (0,1], 0 < τ →
> histMoment Jain.bitR8 529 τ ≤ histMoment Jain.bitR7 529 τ` (numerically true,
> table above; not yet formalised — `Theorems/Thm_moment_dom.lean`'s `moment_dom`
> requires `histRankSum` equality, which fails here: 55 395 128 481 vs
> 57 403 754 177, so a tail-count-dominance variant of `moment_dom` is needed).

The single missing artifact is a **`QHNet (ZMod 2) 108516254 T 529`** — the round-7
staircase bit interchange at its own role count. No recovered file provides it;
it is the genuine open mathematics.

## Gap (C) — recipe settled, blocked only on a dependency-closure build

`Solutions/recovered/p14NeedG_all.6e0c5732.lean` is the parametric uniform
Proposition 14 and is **sorry-free** (0 occurrences). Gap (C) is an instantiation:

```lean
p14NeedG_all 207387136 576 552 p₀ Jain.cxR6
  (by norm_num)   -- 16 ≤ mc
  (by norm_num)   -- mc ≤ 1000000
  (by norm_num)   -- 1 ≤ Wc
  (by decide)     -- wmax ≤ mc        (552 ≤ 576)
  (by decide)     -- every width w in cxR6 satisfies 1 ≤ w ≤ 552
  hnum            -- ∀ e, p₀ ≤ e → 2 * (S * 1105^e) ≤ 1152^e
  hp₀             -- (p₀ : ℝ) ≤ 2 + 576 * Real.log (histRankSum cxR6)
  (by norm_num)   -- 1 ≤ p₀
  P hOK
```

with `S = Σ n_w = 916 054 304`, `wmax = 552`, `histRankSum cxR6 = 119 453 132 304`.
`hnum` holds for `e ≥ ⌈ln(2S)/ln(1152/1105)⌉ = 513` and `hp₀` admits
`p₀ ≤ ⌊2 + 576 ln(119453132304)⌋ = 14693`, so the window **513 ≤ p₀ ≤ 14693** is
non-empty (verified: `Solutions/p0_window_cxR6.py`). Remaining Lean work for (C)
is only the induction proving `hnum` at a chosen `p₀`.

What blocks it today: `p14NeedG_all` imports three modules absent from the tree —
`Theorems.Thm_IntMul_Kappa_R6_IL2C_rowUCC_of`,
`Theorems.Thm_IntMul_Kappa_R6_IL2_swE_spec`,
`Theorems.Thm_IntMul_Kappa_R6_IL3H_p14UH_prime_of` — which pull `NLogN.KFM/KFN/KFH`
and the rest of the round-six tree. `Solutions/api_recover_fixpoint.py` recovers
them read-only; it reached 369 modules before this session ended and was still
expanding. Once it reaches a fixpoint, `lake build` of the three targets produces
the oleans and gap (C) becomes the `hnum` induction above.

## What was recovered, and how

`Solutions/api_recover_r6.py`, `Solutions/api_recover_closure.py` and
`Solutions/api_recover_fixpoint.py` are **read-only** clients of
`https://prove2.me/api/v1`: `POST /agent/refresh` (documented token exchange) plus
`GET /theorems`, `GET /theorems/{id}`, `GET /theorems/{id}/submissions`,
`GET /submissions/{id}/solution`. No submission, no mutation, no status change.

The module↔theorem mapping is exactly invertible and is the key trick:
a theorem's dotted name written with `.`→`_` **is** the module leaf, so
`Theorems.Thm_IntMul_Kappa_R6_IL2C_rowUCC_of` ↔ `IntMul.Kappa.R6.IL2C.rowUCC_of`.
Naive dot re-derivation fails on identifiers that themselves contain underscores
(`rowUCC_of`), which is what stalled the first attempt.
