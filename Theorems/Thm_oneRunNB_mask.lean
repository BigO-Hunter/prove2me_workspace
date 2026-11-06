import Theorems.Thm_oneRunNB_certs
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 200000

/-!
# Influence-mask reflection for XOR gate lists

Backward rewriting (Riemann–De Dinechin): an XOR gate list is a GF(2)-linear
circuit; its semantics is determined by the *influence mask* of each wire —
the parity set of basis wires feeding it.  The reflection bridge is proved
once, generically; every concrete gate-list effect then reduces to a decidable
`Nat` equation, discharged by native evaluation of the compact data.  No
structural decomposition of the word is used or needed.

The eager evaluator initializes entry `w` to the identity mask `2 ^ w`
(wound postmortem: a zero-init evaluator silently turns every untouched wire
into an *empty* influence set, producing 100%-false certificates).
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.OneRunNB

open IntMul.Kappa IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank IntMul.Kappa.R8.Bit.Oppbank.NB
open IntMul.Kappa.R8.Bit.Oppbank.Gen IntMul.Kappa.R8.Bit.Oppbank.GenData

/-! ## Parity-mask sums -/

section Mask

variable {M : Type*} [AddCommGroup M]

/-- `Σ_{i < B, i ∈ mask} x i`. -/
def msumB (B : ℕ) (x : ℕ → M) (mask : ℕ) : M :=
  ∑ i ∈ Finset.range B, if mask.testBit i then x i else 0

theorem msumB_xor (h2 : ∀ a : M, a + a = 0) (B : ℕ) (x : ℕ → M) (a b : ℕ) :
    msumB B x (a ^^^ b) = msumB B x a + msumB B x b := by
  rw [msumB, msumB, msumB, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> simp [h2]

theorem msumB_two_pow (B : ℕ) (x : ℕ → M) {T : ℕ} (hT : T < B) :
    msumB B x (2 ^ T) = x T := by
  rw [msumB, Finset.sum_eq_single T]
  · simp
  · intro i _ hi; simp [Nat.testBit_two_pow, Ne.symm hi]
  · intro h; exact absurd (Finset.mem_range.2 hT) h

end Mask

/-! ## Influence maps -/

/-- One gate on influence masks: `inf_d ← inf_d ⊕ inf_s`. -/
def infStep (inf : ℕ → ℕ) (p : ℕ × ℕ) : ℕ → ℕ :=
  fun w => if w = p.1 then inf p.1 ^^^ inf p.2 else inf w

/-- The influence mask of every wire after a gate list (identity start). -/
def infFold (G : List (ℕ × ℕ)) : ℕ → ℕ :=
  G.foldl (fun inf p => infStep inf p) (fun w => 2 ^ w)

/-! ## Eager array evaluator -/

/-- Array read; entry `w` is initialized to the identity mask `2 ^ w`, so the
default only fires out of bounds. -/
def ainf (a : Array Nat) (w : Nat) : Nat := a.getD w 0

/-- Influence fold over an array, entry `w` starting at the identity `2 ^ w`. -/
def infArr (G : List (ℕ × ℕ)) (B : ℕ) : Array Nat :=
  G.foldl (fun a p => a.setIfInBounds p.1 (ainf a p.1 ^^^ ainf a p.2))
    ((Array.range B).map (fun w => 2 ^ w))

theorem ainf_getElem {a : Array Nat} {w : Nat} (hw : w < a.size) : ainf a w = a[w] := by
  simp only [ainf, Array.getD]
  rw [dif_pos hw]
  rfl

theorem ainf_setIfInBounds (a : Array Nat) (i v w : Nat) (hw : w < a.size) :
    ainf (a.setIfInBounds i v) w = if i = w then v else ainf a w := by
  rw [ainf_getElem (by rw [Array.size_setIfInBounds]; exact hw), ainf_getElem hw,
    Array.getElem_setIfInBounds hw]

theorem ainf_idInit (B : ℕ) (w : Nat) (hw : w < B) :
    ainf ((Array.range B).map (fun w => 2 ^ w)) w = 2 ^ w := by
  have h1 : w < (Array.map (fun w => 2 ^ w) (Array.range B)).size := by
    simp only [Array.size_map, Array.size_range]; omega
  have h2 : w < (Array.range B).size := by simp only [Array.size_range]; omega
  rw [ainf_getElem h1, Array.getElem_map _ h1, Array.getElem_range h2]

theorem infArr_eq {B : ℕ} {G : List (ℕ × ℕ)}
    (hg : ∀ p ∈ G, p.1 < B ∧ p.2 < B) {w : ℕ} (hw : w < B) :
    ainf (infArr G B) w = infFold G w := by
  have key : ∀ (G : List (ℕ × ℕ)) (a : Array Nat) (inf : ℕ → ℕ),
      a.size = B → (∀ p ∈ G, p.1 < B ∧ p.2 < B) → (∀ w < B, ainf a w = inf w) →
      ∀ w < B, ainf (G.foldl (fun a p => a.setIfInBounds p.1 (ainf a p.1 ^^^ ainf a p.2)) a) w
        = (G.foldl (fun inf p => infStep inf p) inf) w := by
    intro G
    induction G with
    | nil => intro a inf _ _ h w hw; simpa using h w hw
    | cons p G ih =>
      intro a inf ha hg h w hw
      obtain ⟨hp1, hp2⟩ := hg p (List.mem_cons_self)
      have hgG : ∀ q ∈ G, q.1 < B ∧ q.2 < B := fun q hq => hg q (List.mem_cons_of_mem _ hq)
      rw [List.foldl_cons, List.foldl_cons]
      refine ih _ (infStep inf p) (by rw [Array.size_setIfInBounds]; exact ha) hgG ?_ w hw
      intro w' hw'
      by_cases hwd : w' = p.1
      · subst hwd
        rw [ainf_setIfInBounds _ _ _ _ (by rw [ha]; omega), if_pos rfl,
          h p.1 hp1, h p.2 hp2, infStep, if_pos rfl]
      · rw [ainf_setIfInBounds _ _ _ _ (by rw [ha]; omega), if_neg (Ne.symm hwd),
          h w' hw', infStep, if_neg hwd]
  exact key G _ _ (by simp [Array.size_map, Array.size_range]) hg
    (fun w hw => ainf_idInit B w hw) w hw

/-! ## The reflection bridge -/

section Bridge

variable {M : Type*} [AddCommGroup M]

/-- Paired-fold invariant: the value fold and the mask fold stay in lockstep,
relative to the original carrier `u₀`. -/
theorem pair_fold (h2 : ∀ a : M, a + a = 0) {B : ℕ} :
    ∀ (G : List (ℕ × ℕ)) (u₀ u : ℕ → M) (inf : ℕ → ℕ),
      (∀ p ∈ G, p.1 < B ∧ p.2 < B) → (∀ w < B, u w = msumB B u₀ (inf w)) →
      ∀ w < B, (G.foldl (fun u p => Function.update u p.1 (u p.1 + u p.2)) u) w
        = msumB B u₀ ((G.foldl (fun inf p => infStep inf p) inf) w)
  | [], u₀, u, inf, _, h, w, hw => by
    rw [List.foldl_nil, List.foldl_nil]; exact h w hw
  | p :: G, u₀, u, inf, hg, h, w, hw => by
    obtain ⟨hp1, hp2⟩ := hg p (List.mem_cons_self)
    have hgG : ∀ q ∈ G, q.1 < B ∧ q.2 < B := fun q hq => hg q (List.mem_cons_of_mem _ hq)
    rw [List.foldl_cons, List.foldl_cons]
    refine pair_fold h2 G u₀ (Function.update u p.1 (u p.1 + u p.2)) (infStep inf p) hgG ?_ w hw
    intro w' hw'
    by_cases hwd : w' = p.1
    · subst hwd
      rw [Function.update_self, h p.1 hw', h p.2 hp2, infStep, if_pos rfl, msumB_xor h2]
    · rw [Function.update_of_ne hwd, infStep, if_neg hwd]
      exact h w' hw'

/-- **Reflection bridge**: the gate-list run equals the parity sum over the
influence mask, for every module of characteristic two. -/
theorem xrL_eq_msumB (h2 : ∀ a : M, a + a = 0) {B : ℕ} (G : List (ℕ × ℕ))
    (hg : ∀ p ∈ G, p.1 < B ∧ p.2 < B) (u : ℕ → M) {w : ℕ} (hw : w < B) :
    xrL G u w = msumB B u (infFold G w) :=
  pair_fold h2 G u u (fun w => 2 ^ w) hg
    (fun w hw => (msumB_two_pow B u hw).symm) w hw

end Bridge

/-! ## Gate-list bounds plumbing -/

theorem gateList1_bound {p : ℕ × ℕ} (hp : p ∈ gateList1) : p.1 < NL ∧ p.2 < NL ∧ p.1 ≠ p.2 := by
  have hmem : p ∈ NB.cs1.flatMap (fun c => c.2.2) := hp
  rw [cs1_eq, genF_gates] at hmem
  obtain ⟨i, hi, hpi⟩ := List.mem_flatMap.1 hmem
  exact W1F_gates i hi p hpi

theorem gateList2_bound {p : ℕ × ℕ} (hp : p ∈ gateList2) :
    p.1 < NL + v ∧ p.2 < NL + v ∧ p.1 ≠ p.2 := by
  have hmem : p ∈ NB.cs2.flatMap (fun c => c.2.2) := hp
  rw [cs2_eq, genF_gates] at hmem
  obtain ⟨i, hi, hpi⟩ := List.mem_flatMap.1 hmem
  obtain ⟨h1, h2', h3⟩ := W2F_gates i hi p hpi
  exact ⟨by omega, by omega, h3⟩

theorem gateList1_bound' {p : ℕ × ℕ} (hp : p ∈ gateList1) : p.1 < NL + v ∧ p.2 < NL + v := by
  obtain ⟨h1, h2', -⟩ := gateList1_bound hp
  exact ⟨by omega, by omega⟩

theorem wX_lt' {t : ℕ} (ht : t < v) : wX t < NL + v := by
  simp only [wX, v, NL] at ht ⊢; omega

theorem wY_lt' {t : ℕ} (ht : t < v) : wY t < NL + v := by
  simp only [wY, v, NL] at ht ⊢; omega

theorem wS_lt' {q : ℕ} (hq : q < NR) : wS q < NL + v := by
  simp only [wS, wEnt, NR, NL] at hq ⊢; omega

theorem wU_lt' {s : ℕ} (hs : s < v) : wU s < NL + v := by
  simp only [wU, v, NL] at hs ⊢; omega

end IntMul.Kappa.R8.Bit.Oppbank.OneRunNB
