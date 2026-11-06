import Theorems.Thm_oneRunNB_blocks
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 200000

/-!
# Whole-program scalar semantics for the genuine R8 network

Composition of the two conditional block theorems through a generic
disjoint-image fold driver.  The generated-chunk certificates (`hcs1`, `hcs2`)
and the stage-effect certificates (`hS1`, `hS2`) are explicit hypotheses; the
composition and all wire arithmetic are proved here.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.OneRunNB

open IntMul.Kappa IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank IntMul.Kappa.R8.Bit.Oppbank.NB
open IntMul.Kappa.R8.Bit.Oppbank.Repaired

/-! ## Generic fold machinery -/

section Fold

variable {Wr I α : Type*}

/-- **Parallel composition**: blocks on disjoint wire images. -/
theorem flat_fold (step : (Wr → α) → I → (Wr → α)) (Q : List I → (Wr → α) → Prop)
    (hQ : ∀ p q L, Q (p ++ q) L ↔ Q p L ∧ Q q (p.foldl step L)) (hQ0 : ∀ L, Q [] L)
    (ι : ℕ → ℕ → Wr) (D : ℕ → Prop) (f g : ℕ → ℕ → α) (prog : ℕ → List I) :
    ∀ bs : List ℕ, bs.Nodup →
    (∀ b ∈ bs, ∀ b' ∈ bs, b ≠ b' → ∀ w w', D w → D w' → ι b w ≠ ι b' w') →
    (∀ b ∈ bs, ∀ L : Wr → α, (∀ w, D w → L (ι b w) = f b w) →
      Q (prog b) L ∧ (∀ w, D w → (prog b).foldl step L (ι b w) = g b w) ∧
        ∀ x, (∀ w, D w → ι b w ≠ x) → (prog b).foldl step L x = L x) →
    ∀ L : Wr → α, (∀ b ∈ bs, ∀ w, D w → L (ι b w) = f b w) →
      Q (bs.flatMap prog) L ∧ (∀ b ∈ bs, ∀ w, D w → (bs.flatMap prog).foldl step L (ι b w) = g b w) ∧
        ∀ x, (∀ b ∈ bs, ∀ w, D w → ι b w ≠ x) → (bs.flatMap prog).foldl step L x = L x := by
  intro bs
  induction bs with
  | nil => intro _ _ _ L _; exact ⟨hQ0 L, by simp, fun _ _ => rfl⟩
  | cons b bs ih =>
    intro hbs hdisj hblk L hL
    have hb : b ∉ bs := (List.nodup_cons.1 hbs).1
    obtain ⟨q1, q2, q3⟩ := hblk b List.mem_cons_self L (hL b List.mem_cons_self)
    have hL1 : ∀ b' ∈ bs, ∀ w, D w → (prog b).foldl step L (ι b' w) = f b' w := by
      intro b' hb' w hw
      rw [q3 _ (fun w' hw' e => hdisj b List.mem_cons_self b' (List.mem_cons_of_mem _ hb')
        (fun h => hb (by rw [h]; exact hb')) w' w hw' hw e)]
      exact hL b' (List.mem_cons_of_mem _ hb') w hw
    obtain ⟨r1, r2, r3⟩ := ih (List.nodup_cons.1 hbs).2
      (fun b1 h1 b2 h2 => hdisj b1 (List.mem_cons_of_mem _ h1) b2 (List.mem_cons_of_mem _ h2))
      (fun b' hb' => hblk b' (List.mem_cons_of_mem _ hb')) _ hL1
    rw [List.flatMap_cons, List.foldl_append]
    refine ⟨(hQ _ _ _).2 ⟨q1, r1⟩, ?_, ?_⟩
    · intro b' hb' w hw
      by_cases e : b' = b
      · subst e
        rw [r3 _ (fun b'' hb'' w' hw' e' => hdisj b'' (List.mem_cons_of_mem _ hb'') b' hb'
          (fun h => hb (by rw [← h]; exact hb'')) w' w hw' hw e')]
        exact q2 w hw
      · exact r2 b' ((List.mem_cons.1 hb').resolve_left e) w hw
    · intro x hx
      rw [r3 x (fun b' hb' => hx b' (List.mem_cons_of_mem _ hb')), q3 x (hx b List.mem_cons_self)]

end Fold

/-! ## Local XOR-list facts -/

section XRL

theorem xrL_untouched {M : Type*} [AddCommGroup M] {w : ℕ} :
    ∀ (l : List (ℕ × ℕ)) (u : ℕ → M), (∀ p ∈ l, p.1 ≠ w) → xrL l u w = u w
  | [], _, _ => rfl
  | p :: ls, u, h => by
    have hp : p.1 ≠ w := h p (by simp)
    rw [show xrL (p :: ls) u = xrL ls (Function.update u p.1 (u p.1 + u p.2)) from rfl,
      xrL_untouched _ _ (fun q hq => h q (by simp [hq]))]
    simp only [Function.update]
    rw [dif_neg (Ne.symm hp)]

theorem two_self_zero {N : ℕ} (x : FVN N) : x + x = 0 := by
  have := two_smul (ZMod 2) x
  rw [show (2 : ZMod 2) = 0 from rfl, zero_smul] at this
  exact this.symm

theorem c2a {N : ℕ} (x y : FVN N) : x + (y + x) = y := by
  rw [show x + (y + x) = y + (x + x) by abel, two_self_zero, add_zero]

theorem c2b {N : ℕ} (x y : FVN N) : (y + x) + (x + (y + x)) = x := by
  rw [show (y + x) + (x + (y + x)) = x + ((x + x) + (y + y)) by abel,
    two_self_zero, two_self_zero, add_zero, add_zero]

end XRL

/-! ## Wire mirrors and arithmetic -/

theorem wS_lt_NL {q : ℕ} (hq : q < NR) : wS q < NL := by
  simp only [wS, wEnt, NR, NL] at hq ⊢; omega

theorem wY_lt_NL {s : ℕ} (hs : s < v) : wY s < NL := by
  simp only [wY, v, NL] at hs ⊢; omega

theorem g2_mirror {a w : ℕ} (ha : a < v) (hw1 : v ≤ w) (hw2 : w < wEnt) :
    g2 a w = g1 (w - v) a := by
  have hv : v = 1771 := rfl
  have hE : wEnt = 3542 := rfl
  have hN : N = 3136441 := rfl
  unfold g1 g2
  rw [if_neg (by omega), if_pos (by omega), if_pos ha]

theorem ι2_mirror_x {a t : ℕ} (ha : a < v) (ht : t < v) :
    NB.ι2 a t = NB.ι1 t (wY a) := by
  rw [NB.ι2, NB.ι1, g2_x ht ha]

theorem ι2_mirror_y {a s : ℕ} (ha : a < v) (hs : s < v) :
    NB.ι2 a (wY s) = NB.ι1 s (wX a) := by
  rw [NB.ι2, NB.ι1, g2_y hs ha]

theorem ι2_mirror_t {a w : ℕ} (ha : a < v) (hw1 : v ≤ w) (hw2 : w < wEnt) :
    NB.ι2 a w = NB.ι1 (w - v) a := by
  rw [NB.ι2, NB.ι1, g2_mirror ha hw1 hw2]

theorem ι2_ne_ι1_slot {a w b q : ℕ} (ha : a < v) (hw : w < NL + v) (hb : b < v) (hq : q < NR) :
    NB.ι2 a w ≠ NB.ι1 b (wS q) := by
  have hv : v = 1771 := rfl
  have hN : N = 3136441 := rfl
  have hNR : NR = 27794 := rfl
  have hE : wEnt = 3542 := rfl
  have hA : wAuxEnd = 31336 := rfl
  have hL : NL = 31359 := rfl
  have hW : W = 104719230 := rfl
  have hT : Tmp = 3217907 := rfl
  have hh : Oppbank.h = 23 := rfl
  intro e
  have hg : g2 a w = g1 b (wS q) :=
    gw_inj (g2_lt ha hw) (g1_lt hb (wS_lt_NL hq)) (by rw [← NB.ι2, ← NB.ι1]; exact e)
  unfold g1 wS at hg
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)] at hg
  simp only [Nat.add_sub_cancel_left] at hg
  unfold g2 at hg
  split_ifs at hg <;> simp only [hv, hN, hW, hT, hNR, hE, hA, hL, hh] at * <;> omega

/-! ## Correction-list evaluations -/

theorem xrL_corrIdx_seg {N : ℕ} (u : ℕ → FVN N) (s : ℕ) :
    xrL (corrIdx s) u (wU s) = u (wU s) + u (wY s) ∧
      xrL (corrIdx s) u (wX s) = u (wX s) + (u (wU s) + u (wY s)) ∧
        xrL (corrIdx s) u (wY s) = u (wY s) := by
  have e1 : wX s ≠ wU s := by simp only [wX, wU, NL]; omega
  have e2 : wY s ≠ wU s := by simp only [wY, wU, NL, v]; omega
  have e3 : wY s ≠ wX s := by simp only [wY, wX, v]; omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [corrIdx, xrL, List.foldl_cons, List.foldl_nil, Function.update_self,
      Function.update_of_ne (Ne.symm e1)]
  · simp only [corrIdx, xrL, List.foldl_cons, List.foldl_nil, Function.update_self,
      Function.update_of_ne e1]
  · simp only [corrIdx, xrL, List.foldl_cons, List.foldl_nil,
      Function.update_of_ne e2, Function.update_of_ne e3, Function.update_self]

theorem xrL_corrAll {N : ℕ} :
    ∀ (l : List ℕ), l.Nodup → (∀ s ∈ l, s < v) → ∀ (u : ℕ → FVN N),
      (∀ s ∈ l, xrL (l.flatMap corrIdx) u (wU s) = u (wU s) + u (wY s) ∧
        xrL (l.flatMap corrIdx) u (wX s) = u (wX s) + (u (wU s) + u (wY s))) ∧
      ∀ w, (∀ s ∈ l, w ≠ wU s ∧ w ≠ wX s) → xrL (l.flatMap corrIdx) u w = u w
  | [], _, _, _ => ⟨(fun _ h => nomatch h), (fun w _ => rfl)⟩
  | s₀ :: ls, hn, hall, u => by
    have hs₀ : s₀ < v := hall s₀ (by simp)
    have hnod : ls.Nodup := (List.nodup_cons.1 hn).2
    have hmem : ∀ s ∈ ls, s < v := fun s hs => hall s (by simp [hs])
    have hne : ∀ s ∈ ls, s ≠ s₀ := fun s hs => fun he =>
      (List.nodup_cons.1 hn).1 (by rw [← he]; exact hs)
    have seg1 := (xrL_corrIdx_seg u s₀).1
    have seg2 := (xrL_corrIdx_seg u s₀).2.1
    have seg3 := (xrL_corrIdx_seg u s₀).2.2
    obtain ⟨ih1, ih2⟩ := xrL_corrAll ls hnod hmem (xrL (corrIdx s₀) u)
    have segunt : ∀ x : ℕ, x ≠ wU s₀ → x ≠ wX s₀ → xrL (corrIdx s₀) u x = u x := fun x h1 h2 =>
      xrL_untouched (corrIdx s₀) u (by
        intro p hp
        simp only [corrIdx, List.mem_cons, List.mem_singleton] at hp
        rcases hp with rfl | rfl | h
        · exact h1.symm
        · exact h2.symm
        · cases h)
    refine ⟨fun s hs => ?_, fun w hw => ?_⟩
    · obtain hsmem : s = s₀ ∨ s ∈ ls := List.mem_cons.1 hs
      rw [List.flatMap_cons, xrL_append]
      rcases hsmem with rfl | hsmem
      · refine ⟨?_, ?_⟩
        · rw [ih2 (wU s) (fun s' hs' => ⟨
              fun h => (hne s' hs') (by simp only [wU, NL] at h; omega),
              by have := hmem s' hs'; simp only [wU, wX, NL, v] at this ⊢; omega⟩), seg1]
        · rw [ih2 (wX s) (fun s' hs' => ⟨
              by have h1 := hmem s' hs'; have h2 := hall s hs
                 simp only [wX, wU, NL, v] at h1 h2 ⊢; omega,
              fun h => (hne s' hs') (by simp only [wX, NL] at h; omega)⟩), seg2]
      · obtain ⟨h1, h2⟩ := ih1 s hsmem
        have hns : s ≠ s₀ := hne s hsmem
        have hs₀' : s₀ < 1771 := by simpa [v] using hs₀
        have hs' : s < 1771 := by simpa [v] using hmem s hsmem
        have ku : xrL (corrIdx s₀) u (wU s) = u (wU s) :=
          segunt (wU s) (by simp only [wU, NL]; omega)
            (by simp only [wU, wX, NL, v] at hs₀' ⊢; omega)
        have kv : xrL (corrIdx s₀) u (wX s) = u (wX s) :=
          segunt (wX s) (by simp only [wX, wU, NL, v] at hs' ⊢; omega)
            (by simp only [wX, NL, v] at hs' ⊢; omega)
        have kw : xrL (corrIdx s₀) u (wY s) = u (wY s) :=
          segunt (wY s) (by simp only [wY, wU, NL, v] at hs' ⊢; omega)
            (by simp only [wY, wX, NL, v] at hs' ⊢; omega)
        refine ⟨?_, ?_⟩
        · rw [h1, ku, kw]
        · rw [h2, kv, ku, kw]
    · have ku := segunt w (hw s₀ (by simp)).1 (hw s₀ (by simp)).2
      exact (ih2 w (fun s hs => hw s (by simp [hs]))).trans ku

/-! ## Stage-value facts -/

theorem u2_x {fd : FrameData} {ch : Repaired.Ch} {N : ℕ} {a s : ℕ} (hs : s < v) :
    u2 fd ch N a (wX s) = φ0 fd ch N (NB.ι1 s (wY a)) + φ0 fd ch N (NB.ι1 s (wX a)) := by
  rw [u2, if_pos (show wX s < v from hs)]
  rfl

theorem u2_y {fd : FrameData} {ch : Repaired.Ch} {N : ℕ} {a s : ℕ} (hs : s < v) :
    u2 fd ch N a (wY s) = φ0 fd ch N (NB.ι2 a (wY s)) := by
  rw [u2, if_neg (by simp only [wY, v] at hs ⊢; omega)]

theorem u2_wS {fd : FrameData} {ch : Repaired.Ch} {N : ℕ} {a q : ℕ} (hq : q < NR) :
    u2 fd ch N a (wS q) = φ0 fd ch N (NB.ι2 a (wS q)) := by
  rw [u2, if_neg (by simp only [wS, wEnt, NR, v] at hq ⊢; omega)]

theorem u2_wU_zero {fd : FrameData} {ch : Repaired.Ch} {n : ℕ} {a s : ℕ} (ha : a < v)
    (hs : s < v) : u2 fd ch n a (wU s) = 0 := by
  have hv : v = 1771 := rfl
  have hL : NL = 31359 := rfl
  have hN : N = 3136441 := rfl
  have hW : W = 104719230 := rfl
  have hT : Tmp = 3217907 := rfl
  have hA : wAuxEnd = 31336 := rfl
  have hE : wEnt = 3542 := rfl
  have hh : Oppbank.h = 23 := rfl
  rw [u2, if_neg (by simp only [wU, NL, v] at hs ⊢; omega), NB.ι2]
  have hg : W ≤ g2 a (wU s) := by
    unfold g2 wU
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    omega
  rw [gw_ge hg (g2_lt ha (by simp only [wU, NL, v] at hs ⊢; omega))]
  rfl

/-! ## Whole-program scalar semantics -/

theorem prog_sc_of_gates
    {ch : Repaired.Ch} {N : ℕ} {fd : FrameData}
    (hcs1 : ∀ c ∈ NB.cs1, ∀ p ∈ c.2.2, p.1 < NL ∧ p.2 < NL ∧ p.1 ≠ p.2)
    (hcs2 : ∀ c ∈ NB.cs2, ∀ p ∈ c.2.2, p.1 < NL + v ∧ p.2 < NL + v ∧ p.1 ≠ p.2)
    (hS1 : ∀ b < v,
      (∀ t < v, xrL gateList1 (u1 fd ch N b) (wX t) = u1 fd ch N b (wX t)) ∧
      (∀ q < NR, xrL gateList1 (u1 fd ch N b) (wS q) = u1 fd ch N b (wS q)) ∧
      ∀ t < v, xrL gateList1 (u1 fd ch N b) (wY t) = u1 fd ch N b (wY t) + u1 fd ch N b (wX t))
    (hS2 : ∀ a < v,
      (∀ t < v, xrL gateList2 (u2 fd ch N a) (wX t) = u2 fd ch N a (wX t)) ∧
      (∀ q < NR, xrL gateList2 (u2 fd ch N a) (wS q) = u2 fd ch N a (wS q)) ∧
      (∀ t < v, xrL gateList2 (u2 fd ch N a) (wY t) = u2 fd ch N a (wY t) + u2 fd ch N a (wX t)) ∧
      ∀ s < v, xrL gateList2 (u2 fd ch N a) (wU s) = u2 fd ch N a (wU s)) :
    (∀ a < v, ∀ s < v,
      (prog ch).foldl scalarStepM (φ0 fd ch N) (NB.ι2 a (wY s)) = φ0 fd ch N (NB.ι2 a (wX s)) ∧
      (prog ch).foldl scalarStepM (φ0 fd ch N) (NB.ι2 a (wX s)) = φ0 fd ch N (NB.ι2 a (wY s))) ∧
    (∀ b < v, ∀ q < NR,
      (prog ch).foldl scalarStepM (φ0 fd ch N) (NB.ι1 b (wS q)) = φ0 fd ch N (NB.ι1 b (wS q))) ∧
    ∀ a < v, ∀ q < NR,
      (prog ch).foldl scalarStepM (φ0 fd ch N) (NB.ι2 a (wS q)) = φ0 fd ch N (NB.ι2 a (wS q)) := by
  obtain ⟨-, r2, r3⟩ := flat_fold (scalarStepM (R := ZMod 2) (m := 529)) (fun _ _ => True)
    (fun _ _ _ => by simp) (fun _ => trivial) NB.ι1 (· < NL)
    (u1 fd ch N) (fun b w => xrL gateList1 (u1 fd ch N b) w) (blk1 ch)
    (List.range v) List.nodup_range
    (fun b hb b' hb' hne w w' hw hw' h =>
      hne (ι1_inj (List.mem_range.1 hb) (List.mem_range.1 hb') hw hw' h).1)
    (fun b hb L hL => ⟨trivial, blk1_sc_of_gates hcs1 (List.mem_range.1 hb) L (u1 fd ch N b) hL⟩)
    (φ0 fd ch N) (fun b hb w hw => rfl)
  obtain ⟨v1, hv1⟩ : ∃ v1, v1 = ((List.range v).flatMap (blk1 ch)).foldl scalarStepM
    (φ0 fd ch N) := ⟨_, rfl⟩
  rw [← hv1] at r2 r3
  have v1_pre : ∀ a < v, ∀ w, w < NL + v → v1 (NB.ι2 a w) = u2 fd ch N a w := by
    intro a ha w hw
    by_cases hw1 : w < v
    · rw [show NB.ι2 a w = NB.ι1 w (wY a) from ι2_mirror_x ha hw1,
        r2 w (List.mem_range.2 hw1) (wY a) (by simp only [wY, v, NL] at ha ⊢; omega)]
      obtain ⟨-, -, hS1y⟩ := hS1 w hw1
      rw [hS1y a ha, u2, if_pos hw1]
      rfl
    · by_cases hw2 : w < wEnt
      · rw [show NB.ι2 a w = NB.ι1 (w - v) (wX a) from
          ι2_mirror_t ha (le_of_not_gt hw1) hw2,
          r2 (w - v) (List.mem_range.2 (by simp only [v, wEnt] at hw1 hw2 ⊢; omega))
            (wX a) (by simp only [wX, v, NL] at ha ⊢; omega)]
        obtain ⟨hS1x, -, -⟩ := hS1 (w - v) (by simp only [v, wEnt] at hw1 hw2 ⊢; omega)
        rw [hS1x a ha, u2, if_neg hw1]
        exact congrArg (φ0 fd ch N) (ι2_mirror_t ha (le_of_not_gt hw1) hw2).symm
      · rw [r3 (NB.ι2 a w) (fun b hb w' hw' e => g2_ne_g1 ha (by omega) hw
          (List.mem_range.1 hb) hw'
          (gw_inj (g2_lt ha hw) (g1_lt (List.mem_range.1 hb) hw') e.symm)), u2, if_neg hw1]
  obtain ⟨-, t2, t3⟩ := flat_fold (scalarStepM (R := ZMod 2) (m := 529)) (fun _ _ => True)
    (fun _ _ _ => by simp) (fun _ => trivial) NB.ι2 (· < NL + v)
    (u2 fd ch N) (fun a w => xrL (gateList2 ++ corrIdxAll) (u2 fd ch N a) w) (blk2 ch)
    (List.range v) List.nodup_range
    (fun a ha a' ha' hne w w' hw hw' h =>
      hne (ι2_inj (List.mem_range.1 ha) (List.mem_range.1 ha') hw hw' h).1)
    (fun a ha L hL => ⟨trivial, blk2_sc_of_gates hcs2 (List.mem_range.1 ha) L (u2 fd ch N a) hL⟩)
    v1 (fun a ha w hw => v1_pre a (List.mem_range.1 ha) w hw)
  have hp : prog ch = (List.range v).flatMap (blk1 ch) ++ (List.range v).flatMap (blk2 ch) := rfl
  rw [hp, List.foldl_append, ← hv1]
  have hallv : ∀ s ∈ List.range v, s < v := fun s hs => List.mem_range.1 hs
  refine ⟨fun a ha s hs => ⟨?_, ?_⟩, fun b hb q hq => ?_, fun a ha q hq => ?_⟩
  · obtain ⟨hS2x, hS2q, hS2y, hS2u⟩ := hS2 a ha
    obtain ⟨corr1, corr2⟩ := xrL_corrAll (List.range v) List.nodup_range hallv
      (xrL gateList2 (u2 fd ch N a))
    have corrW : xrL corrIdxAll (xrL gateList2 (u2 fd ch N a)) (wY s) =
        xrL gateList2 (u2 fd ch N a) (wY s) :=
      corr2 (wY s) (fun s' hs' => ⟨
        by simp only [List.mem_range, wY, wU, NL, v] at hs hs' ⊢; omega,
        by simp only [List.mem_range, wY, wX, NL, v] at hs hs' ⊢; omega⟩)
    rw [t2 a (List.mem_range.2 ha) (wY s) (by simp only [wY, v, NL] at hs ⊢; omega),
      xrL_append, corrW, hS2y s hs, u2_y hs, u2_x hs,
      show φ0 fd ch N (NB.ι2 a (wY s)) = φ0 fd ch N (NB.ι1 s (wX a)) from
        congrArg _ (ι2_mirror_y ha hs), c2a]
    exact (congrArg (φ0 fd ch N) (ι2_mirror_x ha hs)).symm
  · obtain ⟨hS2x, hS2q, hS2y, hS2u⟩ := hS2 a ha
    obtain ⟨corr1, corr2⟩ := xrL_corrAll (List.range v) List.nodup_range hallv
      (xrL gateList2 (u2 fd ch N a))
    obtain ⟨corrU, corrX⟩ := corr1 s (List.mem_range.2 hs)
    have corrX' : xrL corrIdxAll (xrL gateList2 (u2 fd ch N a)) (wX s) =
        xrL gateList2 (u2 fd ch N a) (wX s) +
          (xrL gateList2 (u2 fd ch N a) (wU s) + xrL gateList2 (u2 fd ch N a) (wY s)) := corrX
    rw [t2 a (List.mem_range.2 ha) (wX s) (by simp only [wX, v, NL] at hs ⊢; omega),
      xrL_append, corrX', hS2x s hs, hS2u s hs, u2_wU_zero ha hs, hS2y s hs,
      zero_add, c2a, u2_y hs]
  · obtain ⟨-, hS1q, -⟩ := hS1 b hb
    rw [t3 _ (fun a ha w' hw' e => ι2_ne_ι1_slot (List.mem_range.1 ha) hw' hb hq e),
      r2 b (List.mem_range.2 hb) (wS q) (wS_lt_NL hq), hS1q q hq]
    rfl
  · obtain ⟨-, hS2q, -, -⟩ := hS2 a ha
    obtain ⟨corr1, corr2⟩ := xrL_corrAll (List.range v) List.nodup_range hallv
      (xrL gateList2 (u2 fd ch N a))
    have corrW : xrL corrIdxAll (xrL gateList2 (u2 fd ch N a)) (wS q) =
        xrL gateList2 (u2 fd ch N a) (wS q) :=
      corr2 (wS q) (fun s' hs' => ⟨
        by simp only [List.mem_range, wS, wEnt, wU, NL, NR, v] at hq hs' ⊢; omega,
        by simp only [List.mem_range, wS, wEnt, wX, NR, v] at hq hs' ⊢; omega⟩)
    rw [t2 a (List.mem_range.2 ha) (wS q)
        (by simp only [wS, wEnt, NR, wAuxEnd, NL, v] at hq ⊢; omega),
      xrL_append, corrW, hS2q q hq, u2_wS hq]

end IntMul.Kappa.R8.Bit.Oppbank.OneRunNB
