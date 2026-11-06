# Round-7 port: closure-build verification (gap C) and gap B/D verdicts

Branch `jain-r7-port-attempt`, HEAD `bedca17` (+ this commit). Local only: no
platform submissions, no pushes, no milestone changes.

Supersedes nothing: `Solutions/REPORT_r7_gap_obstruction.md` remains the gap (B)
analysis. This document adds the **measured closure-build result**, which the
earlier report could only anticipate ("blocked only on a dependency-closure build").

## Gap (A) — confirmed closed

`Theorems/Thm_IntMul_Kappa_R6_rG_normalize.lean` exists (130 lines, 0 `sorry`),
exports `IntMul.Kappa.R6.rG_normalize_sol_aux` at arbitrary `(mc, sc)`, and its
olean is present. `Theorems/Thm_IntMul_Kappa_jain_round7_aux.lean:90` is a
one-line instantiation at `(576, histRankSum Jain.cxR6)`. No `sorry` remains in
`r7_normalize`.

## Task 1 — the closure does NOT build (measured)

Theorems modules present: **835** (`Theorems/*.lean`); `Solutions/recovered/`:
17 files (the 4 gap artifacts, several with multiple variants).

Build launched detached (`subprocess.Popen(start_new_session=True)`), log at
`/private/tmp/jain_r7_closure_build.log`:

```
lake build Theorems.Thm_IntMul_Kappa_R6_IL2C_rowUCC_of \
            Theorems.Thm_IntMul_Kappa_R6_IL2_swE_spec \
            Theorems.Thm_IntMul_Kappa_R6_IL3H_p14UH_prime_of
EXIT_CODE=1     jobs reached: [9012/9017]   165 `error:` lines
```

Outcome: **51 modules built, 23 failed (`✖`), 3 targets never attempted** (their
dependencies failed first). No olean exists for any of the three targets.

### Every failure is inside the targets' import cone

Computed the transitive import cone of the three targets (`/private/tmp/jain_r7_cone.py`):
**312 local modules**, and **all 23 failing modules are in it** — zero failures
outside. So the failures are not incidental; they are exactly the blockers.

### Two defect classes, one root cause

| class | count | example |
|---|---|---|
| `X has already been declared` | 115 (16 of them `solution`) | `NLogN.IRuns.seq`, `NLogN.KFW.Agree.congr`, `IL3H.Zc_ge` |
| `Unknown identifier X` (X exists as `solution` in its own module) | 10 | `zsz_le_of_lt`, `toUL_runs`, `KFH.layer_partner`, `sc_div_Wc_le`, `slot_add` |

Root cause of **both**: the skeleton-subtraction recovery did not run, so each
`Theorems/Thm_*.lean` is a *whole source module* (helpers copied in, colliding
with the `Definitions/` module it now imports) and each names its platform
theorem **`solution`** at root level instead of the theorem's real name.
**785 of the 835** Theorems modules still carry a root-level `theorem solution`.

Class 2 is verified to be pure naming, not missing content — each referenced name
has its own module, and each referencing file already imports it:

| missing name | module that should export it | currently named |
|---|---|---|
| `IL2C.slot_add` | `Thm_IntMul_Kappa_R6_IL2C_slot_add` | `solution` (l.155) |
| `NLogN.KFC.toUL_runs` | `Thm_NLogN_KFC_toUL_runs` | `solution` (l.462) |
| `NLogN.KFH.layer_partner` | `Thm_NLogN_KFH_layer_partner` | `solution` (l.199) |
| `NLogN.KFM.sc_div_Wc_le` | `Thm_NLogN_KFM_sc_div_Wc_le` | `solution` (l.51) |
| `NLogN.zsz_le_of_lt` | `Thm_NLogN_zsz_le_of_lt` | `solution` (l.72) |

### Repair recipe, and one validated instance

1. `theorem solution` → `theorem <platform leaf name>` (fixes all 16 collisions
   *and* the 5 missing-name classes at once). Safe: exactly **one** bare
   `solution` reference exists in the whole tree
   (`Thm_IntMul_Kappa_R6_Bit_NB_edge_of_pivs.lean:348`, needs a one-line retarget).
2. Delete each helper declaration that the module's import cone already provides
   (the 99 remaining errors).

Validated on the smallest blocker: `Theorems/Thm_NLogN_zsz_mono.lean` had 3 errors
(2 duplicated helpers + a colliding `solution`). After deleting the two helpers
and dropping the redundant `solution` wrapper, `lake build
Theorems.Thm_NLogN_zsz_mono` → **EXIT_CODE=0**, olean produced. The recipe works;
it has only been applied to this one module.

Estimated effort to a green closure: ~24 modules, ~115 deletions, then an
8900-job rebuild (≈15–20 min/attempt) and at most a few iterations. **Not
mathematical work** — recovery hygiene.

## Gap (C) — blocked, but recipe is complete and byte-identical

Blocked solely on the closure above. The proof is in hand:
`Solutions/recovered/p14NeedG_all.6e0c5732.lean` (908 lines, **0 `sorry`**) proves
`IntMul.Kappa.R6.IL3H.p14NeedG_all_sol_aux` at arbitrary `(Wc, mc, wmax, p₀, hc)`.
Instantiation is

```lean
p14NeedG_all_sol_aux 207387136 576 552 1024 Jain.cxR6
  (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide)
  hnum hp₀ (by norm_num) P hOK
```

Re-measured (`Solutions/p0_window_cxR6.py`, run this session): `S = Σ n_w = 916 054 304`,
`wmax = 552`, `histRankSum cxR6 = 119 453 132 304`, ratio `1152/1105 = 1.0425339366…`.
`hnum` needs `e ≥ ⌈ln(2S)/ln(1152/1105)⌉ = 513`; `hp₀` allows `p₀ ≤ ⌊2+576·ln(119453132304)⌋ = 14693`.
Window **513 ≤ p₀ ≤ 14693**, `p₀ = 1024` chosen. The only Lean content still to
write is the induction discharging `hnum` at `p₀ = 1024` (a `Nat` geometric
comparison; no new axioms, no `native_decide`, statement unchanged).

## Gap (B) — cannot be derived from recovered material; obstruction is exact

`bitNetR7_mom : BitNetMomStmtG 108516254 529 Jain.bitR7`.

### Moment side is free — verified independently this session

Recomputed from `Definitions/Def_IntMul_KappaJainData.lean` (37/36/46 pairs):

| τ | bitR7 | bitR7plain | bitR8 | bitR8 ≤ bitR7 |
|---|---|---|---|---|
| 0.05 | 1.4337e9 | 1.4957e9 | 5.9297e8 | yes |
| 0.25 | 5.0548e8 | 5.1834e8 | 2.6696e8 | yes |
| 0.447296115 | 2.3166e8 | 2.3166e8 | 1.5983e8 | yes |
| 0.5 | 1.9864e8 | 1.9731e8 | 1.4590e8 | yes |
| 1.0 | 1.0851e8 | 1.0472e8 | 1.0472e8 | yes |

`bitR8` (≡ `oppbankHist` in moment, `MomPack.histMoment_oppbank_bitR8_529`)
dominates `bitR7` everywhere; `bitR7plain` does **not** (fails for τ ≲ 0.4473).
So the correct base is `net0Pnd`, not `bitR7plain`.

### Both proposed rescues are arithmetically dead

* Tensor `529 ⊗ 576` → `529·576 = 304 704 ≠ 108 516 254`.
* "`bitR7plain` at `W = 104 719 230` plus 529 roles" → `108 516 254 − 104 719 230 = 3 797 024`,
  not 529. And `bitR7plain` is not moment-dominant for `bitR7` anyway.

### Why padding cannot work — structural, not informal

`QHNet R W T m = ⟨prog : List (Instr (Fin W ⊕ Fin T) R m), ρ : Fin W → Fin W⟩`
(`Def_IntMul_Kappa_R6_Defs4.lean:212`). Formal semantics are **role-index preserving**:

* `FV R U m N = (FMat m N × U) →₀ R` (`…Defs4:1280`) — every frame carries its
  origin role index `U = Fin W` as an immutable second component.
* `lmulF L` maps `(L * p.1, p.2)` (`…Defs4:1287`) — edges scale the matrix, **never** the index.
* `gateVecM g S v w = Σ w' ∈ S, g w w' • v w'` (`…Defs4:1300`) — gates only
  *combine existing* values; they cannot mint a new index.
* `fInit N (inl u) = Finsupp.single (1, u) 1` (`…Defs4:1342`); `FormalOK C N` demands
  `foldl (fStep N) (fInit N) (inl (ρ w)) = Finsupp.single (swapMat, w) 1` for **every** `w : Fin W`
  (`…Defs4:1346`).

Hence the role index of any frame is an invariant of its provenance. A width-`W′`
network obtained by lifting a width-`W` program (`W′ > W`) can only ever produce
role indices `< W`, because no instruction references registers `≥ W` and gates
cannot add indices. `FormalOK` at role `w′ ≥ W` is therefore unreachable — not
merely inconvenient. Padding with idle roles is impossible.

And the construction is not parametric in the width either:
`Definitions/Def_IntMul_Kappa_R8_Data_BitOppbankQHNet.lean:270`
`noncomputable def net (ch : Ch) : QHNet (ZMod 2) W Tmp 529 := ⟨prog ch, ρ⟩` with
`theorem net0_W_val : W = 104719230 := rfl` — `W` is a hardcoded constant, and
`ch` supplies instructions, not registers.

### Verdict

`bitNetR7_mom` is **not derivable** from recovered material. It requires a new
`QHNet (ZMod 2) 108516254 T 529` — genuinely wired, 3 797 024 roles beyond
`net0Pnd` — with its own `RunsOK`, `EdgesOK`, `FormalOK`, plus a moment bound.
Closest existing scaffolding (usable as the *shape* to imitate, not as a source):
`Theorems/Thm_bitNetR7plain_mom_final.lean` (59 lines, 0 `sorry`) assembles
`BitNetMomStmtG 104719230 529 Jain.bitR7plain` from `net0Pnd` in ~10 lines given
two named residuals (`Net0PndFormalOKPrimePower`, one-sided
network→`oppbankHist` moment). A round-7 analogue needs the width-`108516254`
network first. Consistent with the platform: theorem
`e27d1a90-cfee-4b83-9b0b-b6c6f0ab652d` is **Open** with no accepted submission.

## Gap (D) — "modest edits" is wrong; the statement is under-hypothesized

Recovered sources (both landed, both 0 `sorry`):
`Theorems/Thm_IntMul_Kappa_R6_kappaBound_of_machine6.lean` (231 lines) and
`Theorems/Thm_IntMul_Kappa_R6_kappa_final6_at.lean` (3077 lines).

`kappaBound_of_machine6` is the *machine-level* reduction: it consumes an
already-built `M : IntMul.MultitapeTM` with a time bound. The network→machine
construction lives in `kappa_final6_at_sol_aux`, whose signature is

```
(P) (hP : P.Ok) (hq : ∃ q : ℚ, P.ε = q) (κ) (hκ)
(hSet : SetupNeed6 P) (hCrt : CrtNeed6 P) (hFine : FineNeed6 P) (hLine : LineNeed6 P)
(hP14 : P14Need6 P) (hP18 : P18IL6 P) hJb hJc hC1 hBit hCx : KappaBound κ
```

Three separate obstacles, in increasing severity:

1. **Missing bit moment hypothesis.** `kappa_of_networks_G` (aux l.116) takes only
   `hbn`/`hp14` — no `histMoment Jain.bitR7 529 P.τ < 108516254`. The round-6 body
   uses exactly that at l.3000 to build the Lemma 12 table. `Prm.Ok`
   (`…R6_Defs1.lean:326`) does not imply it. The framework's call site already has
   `hbit` and `hτeq` in scope, so this is a 1-line statement fix.
2. **Bit-net parameterization: genuinely modest.** `NetIL C` follows immediately
   from `BitNetMomStmtG` (`m2 := by norm_num` at `m = 529`; `runs`, `ok` are
   conjuncts), and `Theorems/Thm_IntMul_Kappa_R6_IL_swapNeedtau_of_net.lean:263`
   `swapNeedτ_of_net_sol_aux {W T m} [NeZero W] (C) (NetIL C) …` is **already
   parametric in `W`, `T`, `m`**. So the substitution at
   `kappa_final6_at_sol_aux:3000` is ~20 lines.
3. **Five stack interfaces are unproved anywhere.** `SetupNeed6`, `CrtNeed6`,
   `FineNeed6`, `LineNeed6`, `P18IL6` are Prop-valued *definitions*
   (`…Defs16:871/930/970/1008`, `…Defs14:1642`); a tree-wide grep finds them
   **only** as hypotheses of `kappa_final6_{,at}_sol_aux`. Round 6's own top-level
   theorem is conditional on them. Gap (D) as stated has no such hypotheses, so
   proving it requires discharging all five — tens of thousands of lines of
   program-construction content (sieve setup, E′ CRT reversal, fine-bit exposure,
   line maps, Prop 18 from `P14UH`), not a parameterization.

**Effort estimate.** Parameterization alone: **~20 line diff** (`kappa_final6_at`
into a `…G` variant) + **1 statement line** for the missing moment hypothesis.
Discharging as stated: the five interfaces above — effectively the remaining
round-6 development, not an edit. Recommend restating gap (D) with the five
interfaces (or an `hp18`-style aggregate) as explicit hypotheses; that turns a
~10⁴-line gap into the ~20-line adaptation.

## Task 5 — sorry count

`lake env lean Theorems/Thm_IntMul_Kappa_jain_round7_aux.lean` → **EXIT=0**,
no errors, **3** `declaration uses sorry` warnings: l.99 `bitNetR7_mom` (B),
l.105 `p14NeedG_cxR6` (C), l.116 `kappa_of_networks_G` (D).
`Theorems/Thm_IntMul_Kappa_jain_round7_framework.lean` is sorry-free and compiles
against this interface.

## Single next action

`theorem solution` → platform leaf name across the 785 Theorems modules, then
delete the ~115 cone-duplicated helper declarations, then rebuild the three
targets. That is the one gate in front of a *known, sorry-free* proof of gap (C).
