import Theorems.Thm_oneRunNB_scprog
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 200000

/-!
# Generated gate-list certificates for the genuine R8 program

The chunk certificates `hcs1`/`hcs2` follow from the word-level gate bounds of
the hand-written builders `W1F`/`W2F` via `genF_gates` (chunk gates are exactly
the instruction gates).  The only data-dependent facts are the compact decoded
tables (`recs`, `injS`, `retS`, `srcS`, `pts`), each discharged by
`native_decide` on the packed literals — never on the expanded chunk lists.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.OneRunNB

open IntMul.Kappa IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank IntMul.Kappa.R8.Bit.Oppbank.NB
open IntMul.Kappa.R8.Bit.Oppbank.Gen IntMul.Kappa.R8.Bit.Oppbank.GenData

/-! ## Compact data certificates -/

/-- Decoded record bounds: slot indices are within `NR`, basepoints within
`NR + 1`, exception entries are distinct from the pivot, and the first-pair
self-loop condition is excluded (`bp = 0` skips the pair entirely). -/
theorem recs_ok : ∀ r ∈ recs,
    r.2.1 < NR ∧ r.2.2.1 ≤ NR ∧ (∀ o ∈ r.2.2.2, o < NR ∧ o ≠ r.2.1) ∧
      (r.2.2.1 = 0 ∨ r.2.1 ≠ r.2.2.1 - 1) := by
  native_decide

theorem injS_lt : ∀ T < v, ∀ k < 3, injS T k < NR := by
  native_decide

theorem retS_lt : ∀ c < 23, retS c < NR := by
  native_decide

theorem srcS_lt : ∀ t < v, srcS t < NR := by
  native_decide

theorem pts_lt : ∀ T < v, ∀ k < 3, pts T k < 23 := by
  native_decide

/-! ## Arithmetic wire bounds -/

theorem wS_lt_NL' {q : ℕ} (hq : q < NR) : wS q < NL := by
  simp only [wS, wEnt, NR, NL] at hq ⊢; omega

theorem wS_ge_wEnt (q : ℕ) : wEnt ≤ wS q := by
  simp only [wS, wEnt]; omega

theorem wT_lt_NL {c : ℕ} (hc : c < 23) : wT c < NL := by
  simp only [wT, wAuxEnd, NL] at hc ⊢; omega

theorem wT_ge_wEnt (c : ℕ) : wEnt ≤ wT c := by
  simp only [wT, wAuxEnd, wEnt]; omega

theorem wY_lt_NL' {T : ℕ} (hT : T < v) : wY T < NL := by
  simp only [wY, v, NL] at hT ⊢; omega

theorem wY_lt_wEnt {T : ℕ} (hT : T < v) : wY T < wEnt := by
  simp only [wY, v, wEnt] at hT ⊢; omega

theorem wX_lt_wEnt {t : ℕ} (ht : t < v) : wX t < wEnt := by
  simp only [wX, v, wEnt] at ht ⊢; omega

/-! ## Record gate bounds -/

theorem recEl_gates {r : Rec} (hr : r ∈ recs) :
    ∀ p ∈ recEl r, p.1 < NL ∧ p.2 < NL ∧ p.1 ≠ p.2 := by
  obtain ⟨hpiv, hbp, hex, hdisc⟩ := recs_ok r hr
  intro p hp
  by_cases hbp0 : r.2.2.1 = 0
  · rw [show recEl r = r.2.2.2.map fun o => (wS o, wS r.2.1) by
        simp only [recEl, if_pos hbp0, List.nil_append]] at hp
    simp only [List.mem_map] at hp
    obtain ⟨o, ho, rfl⟩ := hp
    obtain ⟨holt, hone⟩ := hex o ho
    refine ⟨wS_lt_NL' holt, wS_lt_NL' hpiv, ?_⟩
    simp only [wS, wEnt] at hone ⊢; omega
  · rw [show recEl r = (wS r.2.1, wS (r.2.2.1 - 1)) ::
        r.2.2.2.map fun o => (wS o, wS r.2.1) by
        simp only [recEl, if_neg hbp0, List.singleton_append]] at hp
    simp only [List.mem_cons, List.mem_singleton, List.mem_map] at hp
    rcases hp with rfl | ⟨o, ho, rfl⟩
    · refine ⟨wS_lt_NL' (by omega), wS_lt_NL' (by omega), fun h => ?_⟩
      have heq : r.2.1 = r.2.2.1 - 1 := by
        simp only [wS, wEnt] at h; omega
      exact (hdisc.resolve_left hbp0) heq
    · obtain ⟨holt, hone⟩ := hex o ho
      refine ⟨wS_lt_NL' holt, wS_lt_NL' hpiv, ?_⟩
      simp only [wS, wEnt] at hone ⊢; omega

theorem blkRecs_subset {a b : ℕ} {r : Rec} (h : r ∈ blkRecs a b) : r ∈ recs := by
  simp only [blkRecs, recs, List.mem_flatMap] at h ⊢
  obtain ⟨g, hg, hg2⟩ := h
  exact ⟨g, List.mem_of_mem_drop (List.mem_of_mem_take hg), hg2⟩

theorem recEl_gates_blk {a b : ℕ} {r : Rec} (hr : r ∈ blkRecs a b) :
    ∀ p ∈ recEl r, p.1 < NL ∧ p.2 < NL ∧ p.1 ≠ p.2 :=
  recEl_gates (blkRecs_subset hr)

/-! ## Builder gate bounds -/

def GW (l : List LInstr) : Prop :=
  ∀ i ∈ l, ∀ p ∈ i.2.2, p.1 < NL ∧ p.2 < NL ∧ p.1 ≠ p.2

theorem mixF_gates (code : ℕ → ℕ) : GW (mixF code) := by
  intro i hi p hp
  simp only [mixF, List.mem_map] at hi
  obtain ⟨r, hr, rfl⟩ := hi
  exact recEl_gates hr p hp

theorem mixI_gates (code : ℕ → ℕ) : GW (mixI code) := by
  intro i hi p hp
  simp only [mixI, List.mem_map] at hi
  obtain ⟨r, hr, rfl⟩ := hi
  have hp' : p ∈ recEl r := by
    simpa [mk] using hp
  exact recEl_gates (by simpa using hr) p hp'

theorem mixFB_gates (a b : ℕ) (code : ℕ → ℕ) : GW (mixFB a b code) := by
  intro i hi p hp
  simp only [mixFB, List.mem_map] at hi
  obtain ⟨r, hr, rfl⟩ := hi
  exact recEl_gates_blk hr p hp

theorem scat_gates (rd code : ℕ → ℕ)
    (hrd : ∀ T < v, ∀ k < 3, rd (pts T k) < NL ∧ wEnt ≤ rd (pts T k)) :
    GW (scat rd code) := by
  intro i hi p hp
  simp only [scat, List.mem_map] at hi
  obtain ⟨T, hT, rfl⟩ := hi
  have hTv : T < v := by simpa using hT
  simp only [mk, scatEl, List.mem_map] at hp
  obtain ⟨k, hk, rfl⟩ := hp
  have hk3 : k < 3 := by
    simp at hk; omega
  obtain ⟨hlt, hge⟩ := hrd T hTv k hk3
  refine ⟨wY_lt_NL' hTv, hlt, ?_⟩
  have hY := wY_lt_wEnt hTv
  simp only [wY, wS, wEnt, wT, wAuxEnd, v, NR, NL] at hY hlt hge ⊢
  omega

theorem scat_rdS_gates : GW (scat rdS fun _ => cLOW) :=
  scat_gates rdS _ (fun T hT k hk =>
    ⟨wS_lt_NL' (retS_lt (pts T k) (pts_lt T hT k hk)), wS_ge_wEnt _⟩)

theorem scat_wT_gates : GW (scat wT fun _ => cLOW) :=
  scat_gates wT _ (fun T hT k hk =>
    ⟨wT_lt_NL (pts_lt T hT k hk), wT_ge_wEnt _⟩)

theorem injo_gates (code : ℕ → ℕ) : GW (injo code) := by
  intro i hi p hp
  simp only [injo, List.mem_map] at hi
  obtain ⟨T, hT, rfl⟩ := hi
  have hTv : T < v := by simpa using hT
  simp only [mk, List.mem_map] at hp
  obtain ⟨k, hk, rfl⟩ := hp
  have hk3 : k < 3 := by
    simp at hk; omega
  refine ⟨wY_lt_NL' hTv, wS_lt_NL' (injS_lt T hTv k hk3), ?_⟩
  have hY := wY_lt_wEnt hTv
  simp only [wY, wS, wEnt, v, NR, NL] at hY ⊢
  omega

theorem copyo_gates (code : ℕ → ℕ) : GW (copyo code) := by
  intro i hi p hp
  simp only [copyo, List.mem_map] at hi
  obtain ⟨t, ht, rfl⟩ := hi
  have htv : t < v := by simpa using ht
  simp only [mk, List.mem_cons, List.mem_singleton] at hp
  rcases hp with rfl | hp
  · refine ⟨wS_lt_NL' (srcS_lt t htv), ?_, ?_⟩
    · have := wX_lt_wEnt htv
      simp only [wX, wS, wEnt, wAuxEnd, NL] at this ⊢; omega
    · have hX := wX_lt_wEnt htv
      simp only [wX, wS, wEnt, v, NR, NL] at hX ⊢
      omega
  · cases hp

theorem tcopy_gates : GW tcopy := by
  intro i hi p hp
  simp only [tcopy, List.mem_map] at hi
  obtain ⟨c, hc, rfl⟩ := hi
  have hc23 : c < 23 := by simpa using hc
  simp only [mk, List.mem_cons, List.mem_singleton] at hp
  rcases hp with rfl | hp
  · refine ⟨wT_lt_NL hc23, wS_lt_NL' (retS_lt c hc23), ?_⟩
    have hret := retS_lt c hc23
    simp only [wT, wAuxEnd, wS, wEnt, NR, NL] at *
    omega
  · cases hp

theorem revI_gates {l : List LInstr} (h : GW l) : GW (revI l) := by
  intro i hi p hp
  simp only [revI, List.mem_map] at hi
  obtain ⟨j, hj, rfl⟩ := hi
  have hj' : j ∈ l := by simpa using hj
  have hp' : p ∈ j.2.2 := by simpa [mk] using hp
  exact h j hj' p hp'

theorem sweepR_gates (a b f : ℕ) : GW (sweepR a b f) := by
  intro i hi p hp
  simp only [sweepR, List.mem_map] at hi
  obtain ⟨q, hq, rfl⟩ := hi
  cases hp

theorem GW_append {l l' : List LInstr} (h : GW l) (h' : GW l') : GW (l ++ l') := by
  intro i hi p hp
  simp only [List.mem_append] at hi
  rcases hi with hi | hi
  · exact h i hi p hp
  · exact h' i hi p hp

/-! ## Word gate bounds -/

theorem scatT_gates : GW scatT := GW_append tcopy_gates scat_wT_gates

macro "gwtriv" : tactic =>
  `(tactic| first
    | exact mixF_gates _
    | exact mixI_gates _
    | exact mixFB_gates _ _ _
    | exact scat_rdS_gates
    | exact scat_wT_gates
    | exact scatT_gates
    | exact injo_gates _
    | exact copyo_gates _
    | exact tcopy_gates
    | exact sweepR_gates _ _ _
    | exact revI_gates (mixF_gates _)
    | exact revI_gates (mixI_gates _)
    | exact revI_gates (mixFB_gates _ _ _)
    | exact revI_gates scat_rdS_gates
    | exact revI_gates scat_wT_gates
    | exact revI_gates scatT_gates
    | exact revI_gates (injo_gates _)
    | exact revI_gates (copyo_gates _)
    | exact revI_gates tcopy_gates
    | exact revI_gates (sweepR_gates _ _ _))

theorem W1F_gates : GW W1F := by
  simp only [W1F]
  repeat' first | gwtriv | (refine GW_append ?_ ?_)

theorem W2F_gates : GW W2F := by
  simp only [W2F]
  repeat' first | gwtriv | (refine GW_append ?_ ?_)

/-! ## genF plumbing (R6 port) -/

theorem foldl_genStepF_acc : ∀ (W : List LInstr) (f : ℕ → ℕ) (acc : List LChunk),
    W.foldl genStepF (f, acc) = ((W.foldl genStepF (f, [])).1, (W.foldl genStepF (f, [])).2 ++ acc)
  | [], f, acc => rfl
  | i :: W, f, acc => by
    simp only [List.foldl_cons, genStepF]
    rw [foldl_genStepF_acc W _ ((i.1, _, i.2.2) :: acc),
      foldl_genStepF_acc W _ [(i.1, _, i.2.2)]]
    all_goals simp

theorem genF_append (f : ℕ → ℕ) (W W' : List LInstr) :
    genF f (W ++ W') =
      ((genF (genF f W).1 W').1, (genF f W).2 ++ (genF (genF f W).1 W').2) := by
  simp only [genF, List.foldl_append]
  rw [foldl_genStepF_acc W' _ (W.foldl genStepF (f, [])).2]
  simp

theorem genF_cons (f : ℕ → ℕ) (i : LInstr) (W : List LInstr) :
    genF f (i :: W) = ((genF (i.2.1.foldl (mvF i.1) (f, [])).1 W).1,
      (i.1, (i.2.1.foldl (mvF i.1) (f, [])).2.reverse, i.2.2) ::
        (genF (i.2.1.foldl (mvF i.1) (f, [])).1 W).2) := by
  have := genF_append f [i] W
  simp only [List.singleton_append] at this
  rw [this]
  simp [genF, genStepF]

theorem genF_nil (f : ℕ → ℕ) : genF f [] = (f, []) := rfl

/-- Gates are kept: the flattened chunk gates are exactly the word gates. -/
theorem genF_gates : ∀ (W : List LInstr) (f : ℕ → ℕ),
    (genF f W).2.flatMap (fun ch => ch.2.2) = W.flatMap (fun i => i.2.2)
  | [], _ => rfl
  | i :: W, f => by
    rw [genF_cons, List.flatMap_cons, List.flatMap_cons, genF_gates W]
    all_goals simp

/-! ## Chunk gate certificates -/

theorem chunk_gates_ok {W : List LInstr} (hW : GW W) (f : ℕ → ℕ) :
    ∀ chk ∈ (genF f W).2, ∀ p ∈ chk.2.2, p.1 < NL ∧ p.2 < NL ∧ p.1 ≠ p.2 := by
  intro chk hchk p hp
  have hmem : p ∈ (genF f W).2.flatMap (fun ch => ch.2.2) :=
    List.mem_flatMap.2 ⟨chk, hchk, hp⟩
  rw [genF_gates] at hmem
  obtain ⟨i, hi, hpi⟩ := List.mem_flatMap.1 hmem
  exact hW i hi p hpi

theorem cs1_eq : NB.cs1 = (genF (codeOf SG1_0) W1F).2 := by unfold NB.cs1; rfl

theorem cs2_eq : NB.cs2 = (genF (codeOf SG2_0) W2F).2 := by unfold NB.cs2; rfl

theorem cs1_gates_ok :
    ∀ c ∈ NB.cs1, ∀ p ∈ c.2.2, p.1 < NL ∧ p.2 < NL ∧ p.1 ≠ p.2 := by
  intro c hc p hp
  rw [cs1_eq] at hc
  exact chunk_gates_ok W1F_gates (codeOf SG1_0) c hc p hp

theorem cs2_gates_ok :
    ∀ c ∈ NB.cs2, ∀ p ∈ c.2.2, p.1 < NL + v ∧ p.2 < NL + v ∧ p.1 ≠ p.2 := by
  intro c hc p hp
  rw [cs2_eq] at hc
  obtain ⟨h1, h2, h3⟩ := chunk_gates_ok W2F_gates (codeOf SG2_0) c hc p hp
  exact ⟨by omega, by omega, h3⟩

end IntMul.Kappa.R8.Bit.Oppbank.OneRunNB
