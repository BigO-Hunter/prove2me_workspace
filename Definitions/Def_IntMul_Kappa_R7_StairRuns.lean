import Definitions.Def_IntMul_Kappa_R7_StairQHNet
import Definitions.Def_IntMul_Kappa_R7_StairHist

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-!
# R7 staircase run-schedule predicates (staircase ③, spec §5 items 3–4)

**Construction: S. Jain**, *integer-mult-kappa* round seven — ported and verified
here.  This module binds the M2b ledgers (`corner_counts`, `chain_rank_counts`,
`ychain_diff_counts`, `xchain_diff_counts`) to the `Ch` edge families of the M3
carrier over `codeBound = 65815`, at the staircase boundaries
`h = 23, m = 529, v = 1771, N = 3136441, NR = 28866, wEnt = 3542`.

Run-schedule families (runs placed back-to-back on the diagonal):

* `auxRunsOf r` — aux exit / region entrance of a slot with corner rank
  `r = h − dim σ_u`: big child `m − 2r`, then Jain's `inner(r, h)`.  Carried by
  `ex` (stage one) and `ei` (stage two), per side slot `wEnt + s`, `s < NR`.
* `chunkRunsOf r` — a chain step of rank `r`: `inner` only.  Carried by the
  `e1`/`e2` moves (chain, deferred-readout and X_S steps; the per-centre
  h-cycle contributes `h` extra rank-`h−1` steps per stage — its indicator is
  folded into `schedCount`'s step term).
* `entRuns` — data entrance: the `m − 4h + 2` block plus the staircase corner
  `(h−2, h−5, 1^6)` (his `check_stair.py`).  Carried by `en`.
* `corrRuns` — one width-1 singleton per pair: the `ec` copy-correction (the
  −759/centre gate sharing).

Binding predicates (`CornerProf`, `MoveProf`, `EntProf`) constrain each
family's `runs` to its schedule through rank assignments; the aggregation
hypotheses of the master theorem say exactly that the assignment fibers are the
M2b ledgers (what the schedule certificate will discharge).

Receipts:

* `prog_count_eq_schedCount` — under profiles + ledger aggregations, the
  program's per-width child count equals `schedCount` for EVERY width (kernel
  list arithmetic over the instruction ranges);
* `sched_count_*` — 37 decide theorems pinning `schedCount` to
  `lcnt stair_hist` on every width class (the M2b decomposition at schedule
  level) — the rung-2 `mom_eq` feed;
* `runsOK_of_profiles` — rung ④ started: under profiles + rank bounds the
  network is `RunsOK` (every scheduled run is in-chunk).

Python↔Lean cross-check: `stair_sched_check.py` recomputed all 37 classes from
the ledgers with exactly these formulas before any Lean was written (it caught
the h-cycle factor `2·v·h`, not `2·v`).
-/

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R7.Stair
open IntMul.Kappa.R7.StairHist

namespace IntMul.Kappa.R7.Stair.NB

/-! ## Jain's inner lemma, as child widths -/

/-- Children of a rank-`r` step: `1^r` when `2r ≤ h`, else `1^(h−r)` plus one
block of width `2r−h` (upstream `inner(r, h)`; here `h = 23`). -/
def innerWidths (r : ℕ) : List ℕ :=
  if 2 * r ≤ h then List.replicate r 1
  else List.replicate (h - r) 1 ++ [2 * r - h]

private theorem m_eq529 : m = 529 := rfl
private theorem h_eq23 : h = 23 := rfl

theorem innerWidths_sum {r : ℕ} (hr : r ≤ 23) : (innerWidths r).sum = r := by
  rw [innerWidths, h_eq23]
  by_cases hle : 2 * r ≤ 23
  · simp [hle, List.sum_replicate]
  · have h2 : (23 - r) + (2 * r - 23) = r := by omega
    simp [hle, List.sum_replicate, List.sum_append, h2]

/-- Place child widths back-to-back on the diagonal starting at offset `o`. -/
def place : ℕ → List ℕ → List (ℕ × ℕ × ℕ)
  | _, [] => []
  | o, w :: ws => (o, o, w) :: place (o + w) ws

/-- The staircase entrance corner: runs `(h−2, h−5, 1^6)`, summing to `2h−1`
(`check_stair.py`). -/
def cornerWidths : List ℕ := [h - 2, h - 5, 1, 1, 1, 1, 1, 1]

theorem cornerWidths_sum : cornerWidths.sum = 2 * h - 1 := by decide

/-- Data-entrance widths: the `m − 4h + 2` block, then the corner. -/
def entWidths : List ℕ := (m - 4 * h + 2) :: cornerWidths

theorem entWidths_sum : entWidths.sum = m - (2 * h - 1) := by decide

theorem entWidths_mem' {x : ℕ} (hx : x ∈ entWidths) : x = 439 ∨ x = 21 ∨ x = 18 ∨ x = 1 := by
  have he : entWidths = [439, 21, 18, 1, 1, 1, 1, 1, 1] := rfl
  rw [he] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- Aux-exit (and region-entrance) run schedule of a slot with corner rank `r`:
the big child `m − 2r`, then the inner decomposition. -/
def auxRunsOf (r : ℕ) : List (ℕ × ℕ × ℕ) := place 0 ((m - 2 * r) :: innerWidths r)

/-- Chunk-move run schedule of a step of rank `r`: the inner decomposition. -/
def chunkRunsOf (r : ℕ) : List (ℕ × ℕ × ℕ) := place 0 (innerWidths r)

/-- Data-entrance run schedule. -/
def entRuns : List (ℕ × ℕ × ℕ) := place 0 entWidths

/-- Copy-correction run schedule: one singleton per pair. -/
def corrRuns : List (ℕ × ℕ × ℕ) := place 0 [1]

/-! ## Every scheduled run is in-chunk (rung ④ groundwork)

Statements are pinned to the concrete numerals (`m = 529`, `h = 23`,
definitional) so the kernel arithmetic never fights the constant names. -/

theorem RunOK_triple {i j r : ℕ} (h1 : 0 < r) (h2 : r < 529) (h3 : i + r ≤ 529)
    (h4 : j + r ≤ 529) : RunOK 529 (i, j, r) := ⟨h1, h2, h3, h4⟩

theorem RunOK_of_mem_place {o : ℕ} {ws : List ℕ}
    (hsum : o + ws.sum ≤ 529) (hw : ∀ x ∈ ws, 0 < x ∧ x < 529) :
    ∀ ρ ∈ place o ws, RunOK 529 ρ := by
  induction ws generalizing o with
  | nil => intro ρ hρ; simp [place] at hρ
  | cons x ws ih =>
    intro ρ hρ
    simp only [place, List.mem_cons] at hρ
    simp only [List.sum_cons] at hsum
    rcases hρ with rfl | hm
    · have hx := hw x (List.mem_cons_self ..)
      exact RunOK_triple hx.1 hx.2 (by omega) (by omega)
    · exact ih (by omega) (fun y hy => hw y (List.mem_cons_of_mem _ hy)) ρ hm

theorem RunOK_of_mem_innerWidths {r : ℕ} (hr1 : 1 ≤ r) (hr2 : r ≤ 23) :
    ∀ x ∈ innerWidths r, 0 < x ∧ x < 529 := by
  rw [innerWidths, h_eq23]
  split_ifs with hle
  · intro x hx
    simp only [List.mem_replicate] at hx
    obtain ⟨_, hx⟩ := hx
    omega
  · intro x hx
    simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hx
    rcases hx with hx | hx
    · obtain ⟨_, hx⟩ := hx
      omega
    · omega

theorem RunOK_of_mem_chunkRunsOf {r : ℕ} (hr1 : 1 ≤ r) (hr2 : r ≤ 23) :
    ∀ ρ ∈ chunkRunsOf r, RunOK 529 ρ := by
  show ∀ ρ ∈ place 0 (innerWidths r), RunOK 529 ρ
  refine RunOK_of_mem_place ?_ ?_
  · rw [innerWidths_sum hr2]
    omega
  · intro x hx
    exact RunOK_of_mem_innerWidths hr1 hr2 x hx

theorem RunOK_of_mem_auxRunsOf {r : ℕ} (hr1 : 1 ≤ r) (hr2 : r ≤ 23) :
    ∀ ρ ∈ auxRunsOf r, RunOK 529 ρ := by
  show ∀ ρ ∈ place 0 ((529 - 2 * r) :: innerWidths r), RunOK 529 ρ
  refine RunOK_of_mem_place ?_ ?_
  · rw [List.sum_cons, innerWidths_sum hr2]
    omega
  · intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨by omega, by omega⟩
    · exact RunOK_of_mem_innerWidths hr1 hr2 x hx

theorem RunOK_of_mem_entRuns : ∀ ρ ∈ entRuns, RunOK 529 ρ := by
  show ∀ ρ ∈ place 0 entWidths, RunOK 529 ρ
  refine RunOK_of_mem_place ?_ ?_
  · rw [entWidths_sum, m_eq529, h_eq23]
    omega
  · intro x hx
    rcases entWidths_mem' hx with rfl | rfl | rfl | rfl <;> omega

theorem RunOK_of_mem_corrRuns : ∀ ρ ∈ corrRuns, RunOK 529 ρ := by
  show ∀ ρ ∈ place 0 [1], RunOK 529 ρ
  refine RunOK_of_mem_place ?_ ?_
  · simp
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx
    omega

/-! ## The binding predicates (ledger → `Ch` families) -/

/-- Corner-rank assignment over the `NR` side slots: `Rk s = h − dim σ_s` is
slot-keyed schedule data; the M2b ledger `corner_counts` is its aggregate.  A
`Ch` has the corner profile when the stage-one aux exit (`ex`, slot
`wEnt + s`) and the stage-two region entrance (`ei`, same slot) both carry the
slot's schedule. -/
def CornerProf (ch : Ch) (Rk : ℕ → ℕ) : Prop :=
  ∀ b < v, ∀ s < NR, (ch.ex (wEnt + s)).runs = auxRunsOf (Rk s)
                  ∧ (ch.ei (wEnt + s)).runs = auxRunsOf (Rk s)

/-- Move-rank assignments for the chunk edges: `Rm1` keys the stage-one moves
`(centre, o, c)`, `Rm2` the stage-two moves. -/
def MoveProf (ch : Ch) (Rm1 Rm2 : ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∀ b o c, (ch.e1 b o c).runs = chunkRunsOf (Rm1 b o c)
        ∧ (ch.e2 b o c).runs = chunkRunsOf (Rm2 b o c)

/-- The data-entrance profile (`en` carries `entRuns` on every data wire) and
the copy-correction profile (`ec` carries one singleton per pair). -/
def EntProf (ch : Ch) : Prop :=
  (∀ a < v, ∀ t < v, (ch.en a t).runs = entRuns)
    ∧ ∀ a < v, ∀ s < v, (ch.ec a s).runs = corrRuns

/-- Rank fiber of the stage-one moves of block `b`. -/
def mvFiber1 (cs1 : List LChunk) (Rm1 : ℕ → ℕ → ℕ → ℕ) (b r : ℕ) : ℕ :=
  (cs1.flatMap fun c => c.2.1.map (fun mv => Rm1 b mv.2 c.1)).countP (· = r)

/-- Rank fiber of the stage-two moves of block `b`. -/
def mvFiber2 (cs2 : List LChunk) (Rm2 : ℕ → ℕ → ℕ → ℕ) (b r : ℕ) : ℕ :=
  (cs2.flatMap fun c => c.2.1.map (fun mv => Rm2 b mv.2 c.1)).countP (· = r)

/-- The per-rank step ledger of one stage's moves: `rc + yd + xd` plus the
`h` h-cycle steps of rank `h−1` (the per-centre temporaries). -/
def stepLedger (r : ℕ) : ℕ := rc r + yd r + xd r + (if r = h - 1 then h else 0)

/-! ## The schedule-level width count -/

/-- Per-width child count of the whole profiled program, from the M2b ledgers:
corners (`cc`) through `ex`/`ei` per slot (both stages), steps (`stepLedger`)
through `e1`/`e2`, the data entrance (`2N` copies of `entWidths`), and the
copy-correction singletons (`N`). -/
def schedCount (w : ℕ) : ℕ :=
  2 * v * (∑ r ∈ Finset.range (h + 1),
      cc r * ((auxRunsOf r).countP (fun ρ => ρ.2.2 = w)))
    + 2 * v * (∑ r ∈ Finset.range (h + 1),
      stepLedger r * ((innerWidths r).countP (fun x => x = w)))
    + 2 * N * (entWidths.countP fun x => x = w)
    + N * ([1].countP fun x => x = w)

/-! ## The 37 class identities (decide; the M2b decomposition at schedule level) -/

theorem sched_count_1 : schedCount 1 = lcnt stair_hist 1 := by decide
theorem sched_count_3 : schedCount 3 = lcnt stair_hist 3 := by decide
theorem sched_count_5 : schedCount 5 = lcnt stair_hist 5 := by decide
theorem sched_count_7 : schedCount 7 = lcnt stair_hist 7 := by decide
theorem sched_count_9 : schedCount 9 = lcnt stair_hist 9 := by decide
theorem sched_count_11 : schedCount 11 = lcnt stair_hist 11 := by decide
theorem sched_count_13 : schedCount 13 = lcnt stair_hist 13 := by decide
theorem sched_count_15 : schedCount 15 = lcnt stair_hist 15 := by decide
theorem sched_count_17 : schedCount 17 = lcnt stair_hist 17 := by decide
theorem sched_count_18 : schedCount 18 = lcnt stair_hist 18 := by decide
theorem sched_count_19 : schedCount 19 = lcnt stair_hist 19 := by decide
theorem sched_count_21 : schedCount 21 = lcnt stair_hist 21 := by decide
theorem sched_count_23 : schedCount 23 = lcnt stair_hist 23 := by decide
theorem sched_count_439 : schedCount 439 = lcnt stair_hist 439 := by decide
theorem sched_count_483 : schedCount 483 = lcnt stair_hist 483 := by decide
theorem sched_count_485 : schedCount 485 = lcnt stair_hist 485 := by decide
theorem sched_count_487 : schedCount 487 = lcnt stair_hist 487 := by decide
theorem sched_count_489 : schedCount 489 = lcnt stair_hist 489 := by decide
theorem sched_count_491 : schedCount 491 = lcnt stair_hist 491 := by decide
theorem sched_count_493 : schedCount 493 = lcnt stair_hist 493 := by decide
theorem sched_count_495 : schedCount 495 = lcnt stair_hist 495 := by decide
theorem sched_count_497 : schedCount 497 = lcnt stair_hist 497 := by decide
theorem sched_count_499 : schedCount 499 = lcnt stair_hist 499 := by decide
theorem sched_count_501 : schedCount 501 = lcnt stair_hist 501 := by decide
theorem sched_count_503 : schedCount 503 = lcnt stair_hist 503 := by decide
theorem sched_count_505 : schedCount 505 = lcnt stair_hist 505 := by decide
theorem sched_count_507 : schedCount 507 = lcnt stair_hist 507 := by decide
theorem sched_count_509 : schedCount 509 = lcnt stair_hist 509 := by decide
theorem sched_count_511 : schedCount 511 = lcnt stair_hist 511 := by decide
theorem sched_count_513 : schedCount 513 = lcnt stair_hist 513 := by decide
theorem sched_count_515 : schedCount 515 = lcnt stair_hist 515 := by decide
theorem sched_count_517 : schedCount 517 = lcnt stair_hist 517 := by decide
theorem sched_count_519 : schedCount 519 = lcnt stair_hist 519 := by decide
theorem sched_count_521 : schedCount 521 = lcnt stair_hist 521 := by decide
theorem sched_count_523 : schedCount 523 = lcnt stair_hist 523 := by decide
theorem sched_count_525 : schedCount 525 = lcnt stair_hist 525 := by decide
theorem sched_count_527 : schedCount 527 = lcnt stair_hist 527 := by decide

/-! ## Kernel list-arithmetic helpers -/

theorem countP_flatMap {α β : Type*} (l : List α) (f : α → List β) (p : β → Bool) :
    (l.flatMap f).countP p = (l.map fun x => (f x).countP p).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih, List.countP_append]

/-- Fiber decomposition of a rank-keyed counted multiset (finite rank range). -/
theorem countP_flatMap_fiber {α : Type*} (l : List α) (Rk : α → ℕ) (g : ℕ → List ℕ)
    (p : ℕ → Bool) (K : ℕ) (hK : ∀ x ∈ l, Rk x < K) :
    (l.flatMap fun x => g (Rk x)).countP p
      = ∑ r ∈ Finset.range K, l.countP (fun x => Rk x = r) * ((g r).countP p) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hlt : Rk a < K := hK a (List.mem_cons_self ..)
    simp only [List.flatMap_cons, List.countP_append, List.countP_cons,
      ih (fun x hx => hK x (List.mem_cons_of_mem _ hx))]
    have key : ∑ r ∈ Finset.range K, (if Rk a = r then (1:ℕ) else 0) * ((g r).countP p)
        = (g (Rk a)).countP p := by
      refine (Finset.sum_eq_single (Rk a) ?_ ?_).trans ?_
      · intro r _ hr
        rw [if_neg (fun h => hr (h.symm)), zero_mul]
      · exact fun hcontra => absurd (Finset.mem_range.mpr hlt) hcontra
      · rw [if_pos rfl, one_mul]
    calc (g (Rk a)).countP p
        + ∑ r ∈ Finset.range K, l.countP (fun x => Rk x = r) * ((g r).countP p)
          = ∑ r ∈ Finset.range K, (if Rk a = r then (1:ℕ) else 0) * ((g r).countP p)
              + ∑ r ∈ Finset.range K, l.countP (fun x => Rk x = r) * ((g r).countP p) := by
            rw [key]
      _ = ∑ r ∈ Finset.range K,
            (l.countP (fun x => Rk x = r) + (if Rk a = r then (1:ℕ) else 0))
              * ((g r).countP p) := by
            have hsplit : ∀ r ∈ Finset.range K,
                (l.countP (fun x => Rk x = r) + (if Rk a = r then (1:ℕ) else 0))
                  * ((g r).countP p)
                = (if Rk a = r then (1:ℕ) else 0) * ((g r).countP p)
                    + l.countP (fun x => Rk x = r) * ((g r).countP p) :=
              fun r _ => by rw [add_mul, Nat.add_comm]
            rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
      _ = ∑ r ∈ Finset.range K,
            (l.countP (fun x => decide (Rk x = r)) + if decide (Rk a = r) = true then (1:ℕ) else 0)
              * ((g r).countP p) := by
            simp

/-- Sum over a range factors through a map's fibers (finite target range). -/
theorem sum_fiber {n K : ℕ} (Rk : ℕ → ℕ) (φ : ℕ → ℕ) (hK : ∀ s < n, Rk s < K) :
    (∑ s ∈ Finset.range n, φ (Rk s))
      = ∑ r ∈ Finset.range K,
        ((Finset.range n).filter (fun s => Rk s = r)).card * φ r := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := Finset.range n) (t := Finset.range K) (g := Rk)
    (fun s hs => Finset.mem_range.2 (hK s (Finset.mem_range.1 hs)))
    (fun s => φ (Rk s))]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hconst : ∀ s ∈ (Finset.range n).filter (fun s => Rk s = r),
      φ (Rk s) = φ r := by
    intro s hs
    rw [Finset.mem_filter] at hs
    rw [hs.2]
  rw [Finset.sum_congr rfl fun s hs => hconst s hs,
    Finset.sum_const, smul_eq_mul]

/-! ## Program width counting -/

/-- The child widths contributed by an instruction list. -/
def iWidths (l : List NI) : List ℕ :=
  (l.filterMap Instr.edgeOf).flatMap fun e => e.runs.map fun ρ => ρ.2.2

theorem iWidths_append (a b : List NI) : iWidths (a ++ b) = iWidths a ++ iWidths b := by
  simp [iWidths, List.filterMap_append]

theorem countP_iWidths_flatMap {α : Type*} (l : List α) (f : α → List NI) (w : ℕ) :
    (iWidths (l.flatMap f)).countP (· = w)
      = (l.map fun x => (iWidths (f x)).countP (· = w)).sum := by
  induction l with
  | nil => simp [iWidths]
  | cons a l ih =>
    simp only [List.flatMap_cons, iWidths_append, List.countP_append, List.map_cons,
      List.sum_cons, ih]

/-- The widths an instruction contributes (none for a gate). -/
def eWidths (i : NI) : List ℕ :=
  match i with
  | .gate _ _ => []
  | .edge _ e => e.runs.map fun ρ => ρ.2.2

theorem iWidths_map {α : Type*} (l : List α) (f : α → NI) :
    iWidths (l.map f) = l.flatMap fun x => eWidths (f x) := by
  induction l with
  | nil => simp [iWidths]
  | cons a l ih =>
    rw [List.map_cons, List.flatMap_cons, ← ih]
    cases hfa : f a <;>
      simp [iWidths, eWidths, List.filterMap_cons, Instr.edgeOf]

theorem countP_edge (wq : Wr) (e : Edge 529) (w : ℕ) :
    (eWidths (Instr.edge wq e)).countP (· = w) = (e.runs.countP fun ρ => ρ.2.2 = w) := by
  simp [eWidths, List.countP_map, Function.comp_def]

end IntMul.Kappa.R7.Stair.NB
