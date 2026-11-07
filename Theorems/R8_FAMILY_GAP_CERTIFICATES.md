# R8-family gap certificates — the two residual hypotheses of `Thm_bitNetR7plain_mom_final.lean`

Lane finding, 2026-11-06 (darkhipo). Read with GAP_MAP.md / BUILD_PLAN.md (p2m-framework).

## The two hypotheses (exact)

File `Theorems/Thm_bitNetR7plain_mom_final.lean`, theorem `bitNetR7plain_mom_final`:

1. **H1** `net0Pnd_formalOK_of_FB0 : ∃ qF : ℕ, Net0PndFormalOKPrimePower qF`
   (=`∀ q prime, q₀ < q → ∀ f, net0Pnd.FormalOK (q^f)`); consumed at line 44 via
   `net0Pnd_FormalOK_large_of_bridge` (`Theorems/Thm_net0Pnd_FormalOK.lean`).
2. **H2** `net0Pnd_moment_le_oppbank : ∀ τ ∈ (0,1], histMoment net0Pnd.hist 529 τ ≤
   histMoment oppbankHist 529 τ`; consumed at line 52.

## Verdict H1 — GAP NAMED (proved obstruction in the data, not open math)

`Theorems/Thm_pnd_obstruction.lean` **proves** the prescribed FB0 route false as the
definitions stand: densSupG maps supports 0,1 to singleton triple masks 7, 11 with
`argRel 0 1` true, so `(1773,1774) ∈ idxD` although the two rank-one projectors
`spanS 7`, `spanS 11` are distinct lines (non-nested); `Dm 1773 1774` is not idempotent
(`Dm_1773_1774_not_idem`), and `DmRawZero_1773_1774_ne_Dm` shows the repair does not
touch `Pnd.ch0P`. So FB0's SideE/DataE clauses for `Pis0` are unprovable without
correcting `densSupG`/`nestOK` (nest = true nesting of the densified rank-one supports).
Route: fix the densified support data (or restrict idxD by true nesting), rebuild the
FB0 witness, port the r6 `NB_formalOK` formal-label calculus. Same gap blocks
`mom_eq`'s consumer edges (ProjB.ch0P has the same pickE/FB0 layer).

## Verdict H2 — FALSE (offline certificate, verified by simulation)

`r8_sim.py` (this directory) replicates `chunkDec`/`genF`/`mvF`/`W1F`/`W2F` and the
edge-family specs (`SideR r` = exactly r children; `DataR` = 26; `AuxR` = 2 at widths
{23, 483}) over the real GREC/INJ/RETS/RETN/SRC/TPTS/DIMT packs. Fidelity anchors:
54,290 records (matches the documented count); both Lean-proved facts
`stage2_requires_1773_1774` and `stage1_requires_1774_1773` reproduce.

Exact child multiset of `net0Pnd` (v=1771 blocks):

- children: **1,712,831,505** vs `oppbankHist_childCount` **749,446,467** ⇒ H2 fails as
  τ → 0⁺ (each (w/529)^τ → 1).
- rank sum: **55,476,226,113** vs `oppbankHist_rankSum` **55,395,128,481** ⇒ H2 fails at
  τ = 1 (moment₁ = rankSum/529 exactly, since `net0Pnd.hist` has multiplicity 1 per child).

Same counting refutes `Thm_R8_Bit_Oppbank_mom_eq.mom_eq` (net0P shares the ProjB/Pnd
edge-family specs, so its histogram explodes identically).

Caveat (stated): the chunk contribution (1.343G children) comes from the simulation; the
structural families alone give 369,396,951 children. In-Lean, H2's falsehood is
conditional on the pickE ∃-halves (AuxE/DataE/SideE instances) — the same FB0-shaped
layer as H1. Sharp consequence: **H1 and H2 cannot both hold** — any non-degenerate
resolution of the family specs (needed to drive the formal calculus) violates the moment
bound; a degenerate all-dfltE resolution trivializes RunsOK and empties the histogram.
The net0P/net0Pnd witness line is a dead end for the moment clause.

## Leaf impact (4 leaves behind the 2 hypotheses)

| Leaf | Local stub | Status |
|---|---|---|
| R8.bitNetR7plain_mom (fefc194e) | `Thm_R8_bitNetR7plain_mom.lean` (1 sorry, statement = platform `BitNetMomStmtG 104719230 529 Jain.bitR7plain` verbatim) | blocked: needs a witness network whose histogram is bitR8/7plain-dominated; net0Pnd route refuted |
| R8.Bit.oppbank_net (1ebc5981/b40cfe62 family) | `Thm_R8_Bit_oppbank_net.lean` (1 sorry) | blocked: H2-class (its own mom-equality route refuted) + H1-class (FB0) |
| R8.bitNetR8_mom (2e2fbbed) | `Thm_R8_bitNetR8_mom.lean` (1 sorry) | blocked: same two classes |
| R8.cxNetR8G (dd643349) | not yet stubbed locally | to stub verbatim at next authoring pass |

Unblocked count by closing the 2 hypotheses: 0 (H1 gap-named, H2 false). The named gap:
**construct an oppbank witness whose child-width histogram matches/dominates bitR8** —
the current pickE specs overproduce by 2.29× in child count (1.71G vs 749M) while
`Jain.bitR8 ≤ Jain.bitR7plain` and `oppbankHist = bitR8` (`MomPack`, decided) remain
proved and reusable.

## axcheck receipt (sorryAx road, per leaf, Platform-only)

All four stubs are single-`sorry` leaf statements matching the platform theorem shapes
verbatim (`BitNetMomStmtG` / `oppbank_net`); no auxiliary sorryAx modules are introduced
by the R8 line beyond `Thm_bitNetR7plain_mom_final` (hypothesis-driven, zero sorries —
its two inputs are explicit named hypotheses, not `sorry`s). Per-leaf stub count: 1, 1,
1, 0 (cxNetR8 pending stub).
