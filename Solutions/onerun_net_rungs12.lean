import Definitions.Def_IntMul_Kappa_RG_Defs
import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_K_Defs2
import Definitions.Def_IntMul_KappaJainData
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankHist
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

/-!
# R8 oppbank onerun net — Rungs 1–2 (+ the `EdgesOK` half of Rung 3)

Target leaf `IntMul.Kappa.R8.Bit.oppbank_net` (`1ebc5981`): a QH-net over `ZMod 2` with
`W = 104719230` roles, width `m = 529`, that is `RunsOK`, passes `EdgesOK`/`FormalOK` at
every large prime power, and whose child-width moments **equal** `Jain.bitR8`'s exactly on
`(0, 1]`.

This file delivers a self-contained witness for **all obligations except `FormalOK`**:

* `onerun_rung12` — `∃ T C q₀, C.RunsOK ∧ (∀ q prime > q₀, ∀ f, C.EdgesOK (q^f)) ∧
  ∀ τ ∈ (0,1], histMoment C.hist 529 τ = histMoment Jain.bitR8 529 τ` with `q₀ = 0`.

## The reversed-child run design (deliverable (b))

Each residual of rank `r` becomes ONE contiguous run anchored at the opposite bank:

* `revRun w = (0, 529 - w, w)` — pivots `H_k ↔ D_{529 - w + k}` (`k < w`), so the child
  reads the D-chunk from the *opposite end*: the "opposite bank order" of the statement.
  `RunOK 529` holds exactly for `1 ≤ w ≤ 528` (`(529 - w) + w = 529 ≤ 529`).
* `RevSideR r`, `RevDataR`, `RevAuxR` — the run predicates replacing `SideR`/`DataR`/`AuxR`
  in the `Ch` edge families: a rank-`r` side residual → `[revRun r]`; the data residual
  (R6 rank `439 + 21 + 24·1 = 484`) → `[revRun 484]`; the aux residual (`23 + 483 = 506`)
  → `[revRun 506]`. Rank is preserved (a width-`w` run has exactly `w` pivots) while the
  width profile collapses to the single even width — matching `bitR8`'s `(484, 3542·1771)`
  and `(506, 33744·1771)` per-block entries exactly (checked: `bitR8_deficit` below).

The network `onrNet` places one reversed child per run of the exact `Jain.bitR8` expansion
(`expHist`), so its histogram is bitR8 by construction (`onerun_mom_eq`).

## Why `FormalOK` is not discharged here (the 759/block deficit)

`histRankSum Jain.bitR8 = 529·W - 1771·759` (`bitR8_deficit`). With trivial Bruhat
factors (`E₁ = E₂ = 1`, as here — which discharges `EdgesOK` at EVERY modulus, hence
`q₀ = 0`) every edge matrix is a permutation matrix, and a wire whose formal frame is
assembled from its own edges alone needs its runs' transposition product to be the full
block swap, which forces total width ≥ 529 per role wire (the block swap moves all 1058
points and each run transposition moves 2). Since the whole histogram is 1771·759 *below*
`529·W`, no pure-permutation own-frame witness exists: the last 759 transpositions per
block must come from either (i) nontrivial unipotent `E₁/E₂` Bruhat glue (a wire reaches
`swapMat` through `U₁ P(σ₁) T P(σ₂) U₂` with `|σ₁|+|σ₂| < 529`), or (ii) Jain's
copy-correction gate sharing on the published chunk programs — the platform-intended
route, currently obstructed by the densified-data defect proved in
`Theorems/Thm_pnd_obstruction.lean` (`not_DensifiedSupportOK`). Both routes are open;
this file is the hist/RunsOK/EdgesOK core they would attach to.
-/

namespace IntMul.Kappa.R8.Bit.OnRun

open IntMul.Kappa IntMul.Kappa.R6.Bit IntMul.Kappa.Jain

/-! ## 0. List helpers (ported from the R6/R7 template) -/

theorem filterMap_eq_map_of {α β : Type*} {l : List α} {f : α → Option β} {g : α → β}
    (h : ∀ x ∈ l, f x = some (g x)) : l.filterMap f = l.map g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx : f x = some (g x) := h x (by simp)
    have ih' : xs.filterMap f = xs.map g := ih fun y hy => h y (by simp [hy])
    simp only [List.filterMap_cons, List.map_cons, hx, ih']

theorem flatMap_map' {α β γ : Type*} (l : List α) (f : α → β) (g : β → List γ) :
    (l.map f).flatMap g = l.flatMap (fun x => g (f x)) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.flatMap_cons, ih]

theorem flatMap_singleton_id {α : Type*} (l : List α) :
    l.flatMap (fun x => [x]) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, ih]; rfl

theorem filterMap_map' {α β γ : Type*} (l : List α) (g : α → β) (f : β → Option γ) :
    (l.map g).filterMap f = l.filterMap (fun x => f (g x)) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.filterMap_cons, ih]

theorem flatMap_congr' {α β : Type*} (l : List α) (f g : α → List β)
    (h : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, h x (by simp),
      ih (fun y hy => h y (List.mem_cons.2 (Or.inr hy)))]

theorem redQ_one (N : ℕ) : AModelFac.redQ N 1 = 1 := by
  have hd : Nat.Coprime ((1 : ℚ).den) N := by
    rw [Rat.den_one]; exact Nat.coprime_one_left N
  unfold AModelFac.redQ AModelFac.toGood
  rw [dif_pos hd]
  show AModelFac.redHom N (⟨(1 : ℚ), hd⟩ : AModelFac.goodSub N) = 1
  exact (AModelFac.redHom N).map_one

/-! ## 1. The reversed-child run -/

/-- The reversed child of width `w`: one contiguous run reading the D-chunk from the
opposite bank. -/
def revRun (w : ℕ) : ℕ × ℕ × ℕ := (0, 529 - w, w)

/-- The one-run reversed-child edge (trivial Bruhat factors). -/
def revEdge (w : ℕ) : Edge 529 := ⟨1, [revRun w], 1⟩

theorem runOK_revRun {w : ℕ} (h1 : 0 < w) (h2 : w ≤ 528) : RunOK 529 (revRun w) := by
  show 0 < w ∧ w < 529 ∧ 0 + w ≤ 529 ∧ (529 - w) + w ≤ 529
  omega

theorem revEdge_runs (w : ℕ) : (revEdge w).runs = [revRun w] := rfl

theorem revEdge_EdgeOK (N : ℕ) (w : ℕ) : EdgeOK N (revEdge w) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij
    show (1 : QMat2 529) i j = 0
    exact Matrix.one_apply_ne (ne_of_lt hij)
  · intro i j hij
    show (1 : QMat2 529) i j = 0
    exact Matrix.one_apply_ne (ne_of_lt hij)
  · intro i
    have h : ((1 : QMat2 529) i i) = 1 := by simp
    show IsUnit (AModelFac.redQ N ((1 : QMat2 529) i i))
    rw [h, redQ_one]
    exact isUnit_one
  · intro i
    have h : ((1 : QMat2 529) i i) = 1 := by simp
    show IsUnit (AModelFac.redQ N ((1 : QMat2 529) i i))
    rw [h, redQ_one]
    exact isUnit_one

/-! ## 2. Reversed-child run predicates for the `Ch` families (deliverable (b)) -/

/-- A rank-`r` side residual becomes one contiguous reversed child of width `r`. -/
def RevSideR (r : ℕ) (rs : List (ℕ × ℕ × ℕ)) : Prop := rs = [revRun r]

/-- The data residual (rank `439 + 21 + 24 = 484`) becomes one width-484 reversed child. -/
def RevDataR (rs : List (ℕ × ℕ × ℕ)) : Prop := rs = [revRun 484]

/-- The aux residual (rank `23 + 483 = 506`) becomes one width-506 reversed child. -/
def RevAuxR (rs : List (ℕ × ℕ × ℕ)) : Prop := rs = [revRun 506]

/-- Rank is preserved by the reversed-child recompile: a width-`w` run carries exactly `w`
pivots (`runPairs` length). -/
theorem RevSideR_rank (r : ℕ) (rs : List (ℕ × ℕ × ℕ)) (h : RevSideR r rs) :
    (IntMul.Kappa.R6.Bit.NB.runPairs rs).length = r := by
  subst h
  simp only [IntMul.Kappa.R6.Bit.NB.runPairs, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.length_map, List.length_range, revRun]

/-! ## 3. The onerun network -/

/-- The expansion of a histogram `[(w, n_w)]` into `n_w` copies of each width `w`. -/
def expHist (h : List (ℕ × ℕ)) : List ℕ := h.flatMap fun p => List.replicate p.2 p.1

/-- One instruction per reversed child, on role wire 0. -/
def onrInstr (w : ℕ) : Instr (Fin 104719230 ⊕ Fin 0) (ZMod 2) 529 :=
  Instr.edge (.inl ⟨0, by decide⟩) (revEdge w)

/-- The onerun program: one reversed child per run of the exact `bitR8` expansion. -/
def onrProg : List (Instr (Fin 104719230 ⊕ Fin 0) (ZMod 2) 529) :=
  (expHist Jain.bitR8).map onrInstr

/-- **The onerun net.** `ρ = id`; every child is a reversed run of the exact bitR8 width. -/
def onrNet : QHNet (ZMod 2) 104719230 0 529 := ⟨onrProg, id⟩

theorem bitR8_bounds : ∀ p ∈ Jain.bitR8, 0 < p.1 ∧ p.1 ≤ 528 := by decide

theorem expHist_bound : ∀ w ∈ expHist Jain.bitR8, 0 < w ∧ w ≤ 528 := by
  intro w hw
  obtain ⟨p, hp, hm⟩ := List.mem_flatMap.1 hw
  rw [List.mem_replicate] at hm
  obtain ⟨h1, h2⟩ := bitR8_bounds p hp
  omega

theorem onrNet_edges : onrNet.edges = (expHist Jain.bitR8).map revEdge := by
  show progEdges onrProg = _
  unfold onrProg progEdges
  rw [filterMap_map']
  exact filterMap_eq_map_of (f := fun w => Instr.edgeOf (onrInstr w)) (g := revEdge)
    fun w _ => rfl

theorem onrNet_widths : onrNet.widths = expHist Jain.bitR8 := by
  have h : onrNet.widths = onrNet.edges.flatMap (fun e => e.runs.map fun ρ => ρ.2.2) := rfl
  rw [h, onrNet_edges, flatMap_map']
  have h2 : ∀ w ∈ expHist Jain.bitR8,
      (revEdge w).runs.map (fun ρ => ρ.2.2) = [w] := fun w _ => rfl
  rw [flatMap_congr' _ _ _ h2]
  exact flatMap_singleton_id _

/-! ## 4. Rung 1: `RunsOK` -/

theorem onrNet_RunsOK : onrNet.RunsOK := by
  intro e he ρ hρ
  rw [onrNet_edges] at he
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 he
  rw [revEdge_runs] at hρ
  rcases List.mem_cons.1 hρ with h | h
  · subst h
    exact runOK_revRun (expHist_bound w hw).1 (expHist_bound w hw).2
  · exact absurd h List.not_mem_nil

/-! ## 5. Rung 3 (edges half): `EdgesOK` at every modulus, `q₀ = 0` -/

theorem onrNet_EdgesOK (N : ℕ) : onrNet.EdgesOK N := by
  intro e he
  rw [onrNet_edges] at he
  obtain ⟨w, _, rfl⟩ := List.mem_map.1 he
  exact revEdge_EdgeOK N w

/-! ## 6. Rung 2: the histogram moment equals `Jain.bitR8`'s exactly -/

theorem sum_expHist (g : ℕ → ℝ) (h : List (ℕ × ℕ)) :
    ((expHist h).map g).sum = (h.map fun p => (p.2 : ℝ) * g p.1).sum := by
  have step : ∀ (n a : ℕ), ((List.replicate n a).map g).sum = (n : ℝ) * g a := by
    intro n a
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [List.replicate_succ, List.map_cons, List.sum_cons, ih]
      push_cast
      ring
  induction h with
  | nil => rfl
  | cons p t ih =>
    have e1 : expHist (p :: t) = List.replicate p.2 p.1 ++ expHist t := rfl
    rw [e1, List.map_append, List.sum_append, step, List.map_cons, List.sum_cons, ih]

theorem onrNet_hist : onrNet.hist = (expHist Jain.bitR8).map fun w => (w, 1) := by
  show onrNet.widths.map _ = _
  rw [onrNet_widths]

/-- **The arithmetic core of the keystone**: the onerun net's child-width moment equals
`Jain.bitR8`'s at every exponent. -/
theorem onerun_mom_eq (τ : ℝ) :
    histMoment onrNet.hist 529 τ = histMoment Jain.bitR8 529 τ := by
  rw [onrNet_hist]
  simp only [histMoment, List.map_map]
  have h3 : ((fun p : ℕ × ℕ => (p.2 : ℝ) * ((p.1 : ℝ) / ((529 : ℕ) : ℝ)) ^ τ) ∘
        (fun w : ℕ => (w, 1)))
      = fun w : ℕ => ((w : ℝ) / ((529 : ℕ) : ℝ)) ^ τ := by
    funext w; simp
  rw [h3, sum_expHist]

/-! ## 7. Packaging and the deficit identities -/

/-- Rungs 1–2 plus the `EdgesOK` half of Rung 3 of `oppbank_net` (`1ebc5981`):
everything except `FormalOK`, with `q₀ = 0` (edge checks pass at *every* prime power). -/
theorem onerun_rung12 :
    ∃ (T : ℕ) (C : QHNet (ZMod 2) 104719230 T 529) (q₀ : ℕ),
      C.RunsOK ∧
        (∀ q, q.Prime → q₀ < q → ∀ f, C.EdgesOK (q ^ f)) ∧
          ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
            histMoment C.hist 529 τ = histMoment Jain.bitR8 529 τ :=
  ⟨0, onrNet, 0, onrNet_RunsOK, fun q _ _ f => onrNet_EdgesOK (q ^ f),
    fun τ _ _ => onerun_mom_eq τ⟩

/-- The rank sum of `Jain.bitR8` (the τ = 1 arm of the moment identity). -/
theorem bitR8_rankSum : histRankSum Jain.bitR8 = 55395128481 := by decide

/-- The deficit identity: the whole histogram is `1771 · 759` transpositions below
`529 · W` — the structural reason a pure own-frame witness cannot close `FormalOK`. -/
theorem bitR8_deficit : 529 * 104719230 - histRankSum Jain.bitR8 = 1771 * 759 := by decide

/-- The per-block structure: every one of the `1771` blocks is exactly `759` short. -/
theorem bitR8_deficit_per_block : (529 * 104719230 - histRankSum Jain.bitR8) / 1771 = 759 := by
  rw [bitR8_deficit, Nat.mul_div_cancel_left]
  decide

/-! ## 8. Bridges and design census -/

/-- The platform's frozen one-run oppbank histogram is definitionally the target list
(the platform-side decide lemma `MomPack.oppbankHist_eq_bitR8` says the same). -/
theorem oppbankHist_eq : IntMul.Kappa.R8.Bit.Oppbank.oppbankHist = Jain.bitR8 := rfl

/-- The onerun witness meets the platform's oppbank pack at every exponent. -/
theorem onerun_mom_eq_oppbank (τ : ℝ) :
    histMoment onrNet.hist 529 τ
      = histMoment IntMul.Kappa.R8.Bit.Oppbank.oppbankHist 529 τ := by
  rw [oppbankHist_eq]
  exact onerun_mom_eq τ

/-- Per-block census: `W / 1771 = 59130` roles, and the big-run census (`484`-runs:
`3542`, `506`-runs: `33744`, `507..528`-runs: `21844`) already accounts for every role —
each role wire carries exactly one big reversed child; all small widths `1..22` are
completion/correction filler. -/
theorem bitR8_block_census :
    3542 + 33744 + 21844 = 104719230 / 1771
      ∧ 104719230 / 1771 = 59130 := by decide

/-- Per-block rank ledger: the big runs alone carry `30243086` width; the small-width
pool carries `1035925`; the total is exactly `529·59130 − 759`. -/
theorem bitR8_block_rank :
    3542 * 484 + 33744 * 506 + 11454294 + 1035925 = 529 * 59130 - 759
      ∧ histRankSum Jain.bitR8 / 1771 = 529 * 59130 - 759 := by decide

end IntMul.Kappa.R8.Bit.OnRun
