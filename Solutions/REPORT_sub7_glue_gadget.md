# Sub-agent #7 report — FIFTH summit attempt: the unipotent Bruhat-glue gadget — **DECISIVE NEGATIVE (proved in Lean)**

## (a) Stage-1 verdict: the gadget does NOT exist. The saving is exactly ZERO, at every m.

**The mechanism that kills it (rank-potential lemma).** A wire's frame product over its own
edges has the form `F = L_t · P(σ_t) · V_t · ⋯ · V_2 · P(σ_1) · V_1` (each `edgeMat =
redM E₁ · P(runs) · redM E₂`; adjacent `E₂·E₁` merge into one lower-triangular `V`; every
run pivot is a CROSS transposition `(top a) ↔ (bottom m+b)` — `runPiv` builds exactly these,
so each pivot moves one top and one bottom index). Take `B M` = the **top-right m×m block**
of `M`. Then:

- `B 1 = 0`, `B swapMat = I_m` (the block swap `[[0,I],[I,0]]`);
- right-mult by lower-triangular `V`: right-half columns receive only from *higher-indexed
  right-half* columns (col `k += c·col i` needs `k < i`), so `B (M·V) = B M · DR V` — rank **≤**;
- left-mult by lower-triangular `L`: top rows read only top rows, so `B (L·M) = AL L · B M` — rank **≤**;
- one cross-pivot as a right mult: exchanges ONE left column into the right half — `B`
  changes in one column — rank **≤ +1**.

So `rank B` starts 0, ends `m`, and grows by ≤ 1 per pivot ⟹ **total run width on any wire
whose edge product equals `swapMat` is ≥ m.** Lower-triangular (unipotent-type) `E₁/E₂`
sandwiches — single or interleaved — save nothing. The Bruhat double-coset argument
(single sandwich needs σ = swap exactly) was only the tip; the rank potential kills every
interleaving. And it needs NO invertibility hypotheses — only the `EdgeOK` triangular shape.

**sympy evidence** (`gadget_stage1.py`, exact):
- m=2, one pivot: `det(B) = 0` symbolically for all 4 transpositions (need 1) — impossible;
- m=3, two interleaved pivots: **all 81 τ-pairs have identically-zero 3×3 minor of B**
  (rank ≤ 2 < 3) — impossible, checked symbolically;
- 1200 random interleaved products at width m−1 (m=3..6): 0 hits; 600 rank-lemma
  validations: 0 violations;
- positive control: width exactly m works trivially (offset-0 runs covering the swap; also
  with the diag-unipotent cancellation identity `E₁=diag(A,D), E₂=diag(D⁻¹,A⁻¹)`) at m=2..8.

**Scaling to m=529 with #6's decide-proved census: NO.** Per block: 59130 roles, available
width `529·59130 − 759`; own-assembly needs ≥ 529 per role wire ⟹ short by exactly 759
per block (= 1771·759 total, #6's `bitR8_deficit`). Verified by `decide` inside the Lean file.

## (b) Stage-2: the Lean file COMPILES GREEN — the negative is now a theorem

`Solutions/gadget_rank_lemma.lean` (302 lines, `lake env lean` clean, **zero sorry/warnings**;
`#print axioms BruhatGlue.no_glue` → `[propext, Classical.choice, Quot.sound]` only):

- `BruhatGlue.Glue K m M w` — inductive word model of any wire product: `one | mulLeft L
  (IsLowerTri L) | mulRight V (IsLowerTri V) | pivot a b` (cost +1). `IsLowerTri` is exactly
  the `EdgeOK` shape `∀ i j, i < j → E i j = 0`.
- `BruhatGlue.glue_rank : Glue K m M w → (B K m M).rank ≤ w` — the rank-potential induction.
- **`BruhatGlue.no_glue : Glue K m (blkSwap K m) w → m ≤ w`** — the decisive negative, at
  every m, over any field.

Framework transfer (two lines, arguable in the report; not yet formalized): `edgeMat N`
reduces FIXED rational matrices mod `N`; if a wire identity `F = swapMat` held over `ZMod (q^f)`
for infinitely many prime powers (as FormalOK above any q₀ requires), it holds over ℚ for the
same rational word, contradicting `no_glue` at `K = ℚ`. Denominators have finitely many prime
divisors, so all but finitely many q are coprime to all of them.

## (c) Stage-3 assembly state: the route is closed; onerun own-assembly is dead

Rungs 1–2 + EdgesOK (#6, compiled) remain intact. What my result adds: the ONLY way left to
close `FormalOK` for the onerun net was nontrivial `E₁/E₂`, and that is now provably useless
for assembling `swapMat` below 529 width per wire. Also note (from the same analysis):

- **Gates do not rescue own-assembly**: `fStep` edges touch one wire; a wire with no edges
  keeps frame `1`; `ρ` must be a bijection for FormalOK to be satisfiable.
- **Gate sharing has a precise structural obstruction** (re-derived here, matches #6): two
  different payloads at the same (wire, frame) cell are inseparable forever (all dynamics are
  linear maps acting identically on the cell's payload-vector); a shared "highway" whose
  product is `swapMat` ends with ALL riders co-located at (highway, swapMat) — fatal. Riders
  must leave with distinct partial products `P_j` and each finish with `P_j⁻¹·swapMat` on
  separate wires/time windows — exactly Jain's copy-correction bookkeeping. The platform's own
  R6 FormalOK (`Thm_IntMul_Kappa_R6_Bit_NB_formalOK`, imported by the accepted R6 witness) went
  through the published chunk programs; the R8 densified analog is proved defective
  (`Thm_pnd_obstruction`: ¬DensifiedSupportOK).

## (d) Honest bottom line

**The keystone is NOT provable with this gadget — for any unipotent-Bruhat-glue family, at any
census. This is a theorem, not a judgement call.** Route 1 of #6's three routes is closed with
proof. What remains for the mission, in order:

1. **Certificate route (platform data)**: corrected densified TPTS/ARGT/DIMT tables, or `FB0`
   rebuilt off `orthOK`-true stubs — the only known mechanism (Jain copy-corrections) that
   legitimately spends less than 529 per role.
2. **Report the data defect upstream** (#6's route 3) — the published densification cannot
   support `pnd_hPis0`/`pnd_Dm_rank`.
3. A genuinely new witness class — but any class whose FormalOK relies on per-wire edge
   assembly of `swapMat` now carries a proved ≥ 529-per-role floor (`no_glue`); savings must
   come from the gate layer, and the gate layer is exactly what the defective data blocks.

Durable artifacts: `Solutions/gadget_rank_lemma.lean` (compiled negative theorem),
`Solutions/gadget_stage1.py` (sympy evidence), this report.
