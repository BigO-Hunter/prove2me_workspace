import Theorems.Thm_oneRunNB_mask
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 200000

/-!
# Influence-mask certificates for the genuine R8 gate lists

Native-evaluation layer.  Claims are UP-TO-TEMPS: masks may carry temporary
wires `wT c` (the `Tg → STg` read path) and nothing else, where `u1`/`u2`
vanish (R6's stage algebra was always `TmpZ`-conditional).  `x`/`u` are
exact.  TCB: `Lean.ofReduceBool`, disclosed by `#print axioms`.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.OneRunNB

open IntMul.Kappa IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank IntMul.Kappa.R8.Bit.Oppbank.NB

/-! ## Temp-vanishing of the value functions -/

theorem u1_wT_zero {fd : FrameData} {ch : Repaired.Ch} {n : ℕ} {b c : ℕ}
    (hb : b < v) (hc : c < 23) : u1 fd ch n b (wT c) = 0 := by
  have hv : v = 1771 := rfl
  have hW : W = 104719230 := rfl
  have hA : wAuxEnd = 31336 := rfl
  have hE : wEnt = 3542 := rfl
  have hh : Oppbank.h = 23 := rfl
  rw [u1, NB.ι1]
  have hg : W ≤ g1 b (wT c) := by
    unfold g1 wT
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    omega
  have hNL : NL = 31359 := rfl
  have hvv : v = 1771 := rfl
  rw [gw_ge hg (g1_lt hb (by
    have hA : wAuxEnd = 31336 := rfl
    have hT : wT c = wAuxEnd + c := rfl
    have hNL : NL = 31359 := rfl
    omega))]
  rfl

theorem u2_wT_zero {fd : FrameData} {ch : Repaired.Ch} {n : ℕ} {a c : ℕ}
    (ha : a < v) (hc : c < 23) : u2 fd ch n a (wT c) = 0 := by
  have hv : v = 1771 := rfl
  have hW : W = 104719230 := rfl
  have hA : wAuxEnd = 31336 := rfl
  have hE : wEnt = 3542 := rfl
  have hh : Oppbank.h = 23 := rfl
  rw [u2, if_neg (by simp only [wT, wAuxEnd, v] at hc ⊢; omega), NB.ι2]
  have hg : W ≤ g2 a (wT c) := by
    unfold g2 wT
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    omega
  have hNL : NL = 31359 := rfl
  have hvv : v = 1771 := rfl
  rw [gw_ge hg (g2_lt ha (by
    have hA : wAuxEnd = 31336 := rfl
    have hT : wT c = wAuxEnd + c := rfl
    have hNL : NL = 31359 := rfl
    have hvv : v = 1771 := rfl
    omega))]
  rfl

theorem u1_temp_zero {fd : FrameData} {ch : Repaired.Ch} {n : ℕ} {b i : ℕ}
    (hb : b < v) (h1 : wAuxEnd ≤ i) (h2 : i < wAuxEnd + 23) :
    u1 fd ch n b i = 0 := by
  have hc : i - wAuxEnd < 23 := by omega
  have hw : wT (i - wAuxEnd) = i := by simp only [wT, Nat.add_sub_cancel' h1]
  rw [← hw]
  exact u1_wT_zero hb hc

theorem u2_temp_zero {fd : FrameData} {ch : Repaired.Ch} {n : ℕ} {a i : ℕ}
    (ha : a < v) (h1 : wAuxEnd ≤ i) (h2 : i < wAuxEnd + 23) :
    u2 fd ch n a i = 0 := by
  have hc : i - wAuxEnd < 23 := by omega
  have hw : wT (i - wAuxEnd) = i := by simp only [wT, Nat.add_sub_cancel' h1]
  rw [← hw]
  exact u2_wT_zero ha hc

/-! ## Bit and mask helpers -/

theorem two_pow_le_of_testBit {m j : ℕ} (h : m.testBit j) : 2 ^ j ≤ m := by
  by_contra hc
  have hlt : m < 2 ^ j := by omega
  have hb := Nat.testBit_lt_two_pow hlt
  rw [h] at hb
  exact absurd hb (by simp)

theorem mod_zero_no_low_bit (d k i : ℕ) (hi : i < k) (h : d % 2 ^ k = 0) :
    d.testBit i = false := by
  have hdvd : 2 ^ (i + 1) ∣ d :=
    Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) (Nat.dvd_of_mod_eq_zero h)
  obtain ⟨q, rfl⟩ := hdvd
  have hpos : 0 < 2 ^ i := Nat.two_pow_pos i
  have key : (2 ^ i * 2) * q / 2 ^ i % 2 = 0 := by
    have hrf : (2 ^ i * 2) * q = 2 ^ i * (2 * q) := by ring
    rw [hrf, Nat.mul_div_cancel_left _ hpos]
    omega
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.pow_succ]
  norm_num
  exact key

theorem msumB_zero_mask {M : Type*} [AddCommGroup M] (B : ℕ) (u : ℕ → M) (d : ℕ)
    (h : ∀ i < B, d.testBit i → u i = 0) : msumB B u d = 0 := by
  rw [msumB]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : d.testBit i
  · rw [if_pos hi]; exact h i (Finset.mem_range.1 ‹i ∈ Finset.range B›) hi
  · rw [if_neg hi]

/-- Bits of a temp-window-confined mask lie in `[wAuxEnd, wAuxEnd + 23)`. -/
theorem diff_bits_window {dm : ℕ} (hlo : dm % 2 ^ wAuxEnd = 0)
    (hhi : dm / 2 ^ wAuxEnd < 2 ^ 23) {i : ℕ} (hi : dm.testBit i) :
    wAuxEnd ≤ i ∧ i < wAuxEnd + 23 := by
  by_cases hw : wAuxEnd ≤ i
  · refine ⟨hw, ?_⟩
    have h3 : (dm >>> wAuxEnd).testBit (i - wAuxEnd) = true := by
      rw [Nat.testBit_shiftRight, Nat.add_sub_cancel' hw]; exact hi
    have hge : 2 ^ (i - wAuxEnd) ≤ dm >>> wAuxEnd := two_pow_le_of_testBit h3
    rw [Nat.shiftRight_eq_div_pow] at hge
    have hlt : 2 ^ (i - wAuxEnd) < 2 ^ 23 := lt_of_le_of_lt hge hhi
    by_contra hbig
    have hp : 23 ≤ i - wAuxEnd := by omega
    have hle : 2 ^ 23 ≤ 2 ^ (i - wAuxEnd) := Nat.pow_le_pow_right hp
    omega
  · exfalso
    have hilt : i < wAuxEnd := by omega
    have := mod_zero_no_low_bit dm wAuxEnd i hilt hlo
    rw [hi] at this
    exact Bool.noConfusion this

/-! ## Native mask certificates (temp-window form) -/

theorem G1_mask_cert :
    ((List.range v).all (fun t =>
      decide (ainf (infArr gateList1 (NL + v)) (wX t) = 2 ^ (wX t)) &&
        decide ((ainf (infArr gateList1 (NL + v)) (wY t) ^^^ 2 ^ (wY t) ^^^ 2 ^ (wX t))
          % 2 ^ wAuxEnd = 0) &&
        decide ((ainf (infArr gateList1 (NL + v)) (wY t) ^^^ 2 ^ (wY t) ^^^ 2 ^ (wX t))
          / 2 ^ wAuxEnd < 2 ^ 23))) = true ∧
    ((List.range NR).all (fun q =>
      decide ((ainf (infArr gateList1 (NL + v)) (wS q) ^^^ 2 ^ (wS q)) % 2 ^ wAuxEnd = 0) &&
        decide ((ainf (infArr gateList1 (NL + v)) (wS q) ^^^ 2 ^ (wS q))
          / 2 ^ wAuxEnd < 2 ^ 23))) = true := by
  native_decide

theorem G2_mask_cert :
    ((List.range v).all (fun t =>
      decide (ainf (infArr gateList2 (NL + v)) (wX t) = 2 ^ (wX t)) &&
        decide ((ainf (infArr gateList2 (NL + v)) (wY t) ^^^ 2 ^ (wY t) ^^^ 2 ^ (wX t))
          % 2 ^ wAuxEnd = 0) &&
        decide ((ainf (infArr gateList2 (NL + v)) (wY t) ^^^ 2 ^ (wY t) ^^^ 2 ^ (wX t))
          / 2 ^ wAuxEnd < 2 ^ 23))) = true ∧
    ((List.range NR).all (fun q =>
      decide ((ainf (infArr gateList2 (NL + v)) (wS q) ^^^ 2 ^ (wS q)) % 2 ^ wAuxEnd = 0) &&
        decide ((ainf (infArr gateList2 (NL + v)) (wS q) ^^^ 2 ^ (wS q))
          / 2 ^ wAuxEnd < 2 ^ 23))) = true ∧
    ((List.range v).all (fun s =>
      decide (ainf (infArr gateList2 (NL + v)) (wU s) = 2 ^ (wU s)))) = true := by
  native_decide

/-! ## v10 window certificates (basket-aware; R2125607354 Tier-0 outcome A)

The masks' data window is X-ONLY: bits of `mask(wI) XOR 2^wI` in `[v, wAuxEnd)`
are zero — below `v` only x-bits (the BASKET: the composed neighbor closure of
the published GREC/TPTS/INJ tables, multi-input by Defs51 construction), above
`wAuxEnd` only temps (< 2^23).  This is the shape the densified R8 word
actually has — NOT the R6-sparse partner-only telescope the earlier hS-forms
assumed (measured: diag2/diag5; all-rows gate: diag6, tmux leanrun-diag6). -/

-- REFUTED by diag6 (all-rows): y/s window fails 1722/1771, 15068 — see R2125607354. Do not compile.
-- theorem G1_window_cert :
    ((List.range v).all (fun t =>
      decide (ainf (infArr gateList1 (NL + v)) (wX t) = 2 ^ (wX t)) &&
        decide (((ainf (infArr gateList1 (NL + v)) (wY t) ^^^ 2 ^ (wY t)) % 2 ^ wAuxEnd)
          / 2 ^ v = 0) &&
        decide ((ainf (infArr gateList1 (NL + v)) (wY t) ^^^ 2 ^ (wY t))
          / 2 ^ wAuxEnd < 2 ^ 23))) = true ∧
    ((List.range NR).all (fun q =>
      decide (((ainf (infArr gateList1 (NL + v)) (wS q) ^^^ 2 ^ (wS q)) % 2 ^ wAuxEnd)
          / 2 ^ v = 0) &&
        decide ((ainf (infArr gateList1 (NL + v)) (wS q) ^^^ 2 ^ (wS q))
          / 2 ^ wAuxEnd < 2 ^ 23))) = true := by
  native_decide

-- REFUTED by diag6 (all-rows): see R2125607354. Do not compile.
-- theorem G2_window_cert :
    ((List.range v).all (fun t =>
      decide (ainf (infArr gateList2 (NL + v)) (wX t) = 2 ^ (wX t)) &&
        decide (((ainf (infArr gateList2 (NL + v)) (wY t) ^^^ 2 ^ (wY t)) % 2 ^ wAuxEnd)
          / 2 ^ v = 0) &&
        decide ((ainf (infArr gateList2 (NL + v)) (wY t) ^^^ 2 ^ (wY t))
          / 2 ^ wAuxEnd < 2 ^ 23))) = true ∧
    ((List.range NR).all (fun q =>
      decide (((ainf (infArr gateList2 (NL + v)) (wS q) ^^^ 2 ^ (wS q)) % 2 ^ wAuxEnd)
          / 2 ^ v = 0) &&
        decide ((ainf (infArr gateList2 (NL + v)) (wS q) ^^^ 2 ^ (wS q))
          / 2 ^ wAuxEnd < 2 ^ 23))) = true ∧
    ((List.range v).all (fun s =>
      decide (ainf (infArr gateList2 (NL + v)) (wU s) = 2 ^ (wU s)))) = true := by
  native_decide

/-! ## Kernel-side mask facts -/

theorem G1_mask_x {t : ℕ} (ht : t < v) : infFold gateList1 (wX t) = 2 ^ (wX t) := by
  have hx := of_decide_eq_true (List.all_eq_true.mp G1_mask_cert.1 t (List.mem_range.2 ht))
  rw [← hx.1, ← infArr_eq gateList1_bound' (wX_lt' ht)]

theorem G1_tempOnly_y {t : ℕ} (ht : t < v) :
    (infFold gateList1 (wY t) ^^^ 2 ^ (wY t) ^^^ 2 ^ (wX t)) % 2 ^ wAuxEnd = 0 ∧
      (infFold gateList1 (wY t) ^^^ 2 ^ (wY t) ^^^ 2 ^ (wX t)) / 2 ^ wAuxEnd < 2 ^ 23 := by
  have hy := of_decide_eq_true (List.all_eq_true.mp G1_mask_cert.1 t (List.mem_range.2 ht))
  constructor
  · rw [← hy.2.1, ← infArr_eq gateList1_bound' (wY_lt' ht)]
  · rw [← hy.2.2.1, ← infArr_eq gateList1_bound' (wY_lt' ht)]

theorem G1_tempOnly_s {q : ℕ} (hq : q < NR) :
    (infFold gateList1 (wS q) ^^^ 2 ^ (wS q)) % 2 ^ wAuxEnd = 0 ∧
      (infFold gateList1 (wS q) ^^^ 2 ^ (wS q)) / 2 ^ wAuxEnd < 2 ^ 23 := by
  have hq' := of_decide_eq_true (List.all_eq_true.mp G1_mask_cert.2 q (List.mem_range.2 hq))
  constructor
  · rw [← hq'.1, ← infArr_eq gateList1_bound' (wS_lt' hq)]
  · rw [← hq'.2, ← infArr_eq gateList1_bound' (wS_lt' hq)]

theorem G2_mask_x {t : ℕ} (ht : t < v) : infFold gateList2 (wX t) = 2 ^ (wX t) := by
  have hx := of_decide_eq_true (List.all_eq_true.mp G2_mask_cert.1 t (List.mem_range.2 ht))
  rw [← hx.1, ← infArr_eq gateList2_bound (wX_lt' ht)]

theorem G2_tempOnly_y {t : ℕ} (ht : t < v) :
    (infFold gateList2 (wY t) ^^^ 2 ^ (wY t) ^^^ 2 ^ (wX t)) % 2 ^ wAuxEnd = 0 ∧
      (infFold gateList2 (wY t) ^^^ 2 ^ (wY t) ^^^ 2 ^ (wX t)) / 2 ^ wAuxEnd < 2 ^ 23 := by
  have hy := of_decide_eq_true (List.all_eq_true.mp G2_mask_cert.1 t (List.mem_range.2 ht))
  constructor
  · rw [← hy.2.1, ← infArr_eq gateList2_bound (wY_lt' ht)]
  · rw [← hy.2.2.1, ← infArr_eq gateList2_bound (wY_lt' ht)]

theorem G2_tempOnly_s {q : ℕ} (hq : q < NR) :
    (infFold gateList2 (wS q) ^^^ 2 ^ (wS q)) % 2 ^ wAuxEnd = 0 ∧
      (infFold gateList2 (wS q) ^^^ 2 ^ (wS q)) / 2 ^ wAuxEnd < 2 ^ 23 := by
  have hq' := of_decide_eq_true (List.all_eq_true.mp G2_mask_cert.2.1 q (List.mem_range.2 hq))
  constructor
  · rw [← hq'.1, ← infArr_eq gateList2_bound (wS_lt' hq)]
  · rw [← hq'.2, ← infArr_eq gateList2_bound (wS_lt' hq)]

theorem G2_mask_u {s : ℕ} (hs : s < v) : infFold gateList2 (wU s) = 2 ^ (wU s) := by
  have hs' := of_decide_eq_true (List.all_eq_true.mp G2_mask_cert.2.2 s (List.mem_range.2 hs))
  rw [← hs', ← infArr_eq gateList2_bound (wU_lt' hs)]

/-! ## From up-to-temps masks to exact claims -/

theorem msum_of_tempOK {M : Type*} [AddCommGroup M] {B d m : ℕ} {u : ℕ → M}
    (hlo : (d ^^^ m) % 2 ^ wAuxEnd = 0) (hhi : (d ^^^ m) / 2 ^ wAuxEnd < 2 ^ 23)
    (hzero : ∀ i, wAuxEnd ≤ i → i < wAuxEnd + 23 → u i = 0)
    (hB : wAuxEnd + 23 ≤ B) : msumB B u d = msumB B u m := by
  have hz : msumB B u (d ^^^ m) = 0 :=
    msumB_zero_mask B u (d ^^^ m) fun i _ hi =>
      hzero i (diff_bits_window hlo hhi hi).1 (diff_bits_window hlo hhi hi).2
  have hx : m ^^^ (d ^^^ m) = d := by
    rw [Nat.xor_comm d m, ← Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  rw [← hx, msumB_xor, hz, add_zero]

/-! ## Stage-effect certificates, discharged -/

theorem hS1 {fd : FrameData} {ch : Repaired.Ch} {N : ℕ} {b : ℕ} (hb : b < v) :
    (∀ t < v, xrL gateList1 (u1 fd ch N b) (wX t) = u1 fd ch N b (wX t)) ∧
    (∀ q < NR, xrL gateList1 (u1 fd ch N b) (wS q) = u1 fd ch N b (wS q)) ∧
    ∀ t < v, xrL gateList1 (u1 fd ch N b) (wY t) =
      u1 fd ch N b (wY t) + u1 fd ch N b (wX t) := by
  have hzt : ∀ i, wAuxEnd ≤ i → i < wAuxEnd + 23 → u1 fd ch N b i = 0 :=
    fun i h1 h2 => u1_temp_zero hb h1 h2
  have hB : wAuxEnd + 23 ≤ NL + v := by simp only [wAuxEnd, NL, v]; omega
  refine ⟨fun t ht => ?_, fun q hq => ?_, fun t ht => ?_⟩
  · rw [xrL_eq_msumB two_self_zero gateList1_bound' (wX_lt' ht), G1_mask_x ht,
      msumB_two_pow _ _ (wX_lt' ht)]
  · rw [xrL_eq_msumB two_self_zero gateList1_bound' (wS_lt' hq),
      msum_of_tempOK (G1_tempOnly_s hq).1 (G1_tempOnly_s hq).2 hzt hB,
      msumB_two_pow _ _ (wS_lt' hq)]
  · rw [xrL_eq_msumB two_self_zero gateList1_bound' (wY_lt' ht),
      msum_of_tempOK (G1_tempOnly_y ht).1 (G1_tempOnly_y ht).2 hzt hB,
      msumB_xor two_self_zero, msumB_two_pow _ _ (wY_lt' ht),
      msumB_two_pow _ _ (wX_lt' ht)]

theorem hS2 {fd : FrameData} {ch : Repaired.Ch} {N : ℕ} {a : ℕ} (ha : a < v) :
    (∀ t < v, xrL gateList2 (u2 fd ch N a) (wX t) = u2 fd ch N a (wX t)) ∧
    (∀ q < NR, xrL gateList2 (u2 fd ch N a) (wS q) = u2 fd ch N a (wS q)) ∧
    (∀ t < v, xrL gateList2 (u2 fd ch N a) (wY t) =
      u2 fd ch N a (wY t) + u2 fd ch N a (wX t)) ∧
    ∀ s < v, xrL gateList2 (u2 fd ch N a) (wU s) = u2 fd ch N a (wU s) := by
  have hzt : ∀ i, wAuxEnd ≤ i → i < wAuxEnd + 23 → u2 fd ch N a i = 0 :=
    fun i h1 h2 => u2_temp_zero ha h1 h2
  have hB : wAuxEnd + 23 ≤ NL + v := by simp only [wAuxEnd, NL, v]; omega
  refine ⟨fun t ht => ?_, fun q hq => ?_, fun t ht => ?_, fun s hs => ?_⟩
  · rw [xrL_eq_msumB two_self_zero gateList2_bound (wX_lt' ht), G2_mask_x ht,
      msumB_two_pow _ _ (wX_lt' ht)]
  · rw [xrL_eq_msumB two_self_zero gateList2_bound (wS_lt' hq),
      msum_of_tempOK (G2_tempOnly_s hq).1 (G2_tempOnly_s hq).2 hzt hB,
      msumB_two_pow _ _ (wS_lt' hq)]
  · rw [xrL_eq_msumB two_self_zero gateList2_bound (wY_lt' ht),
      msum_of_tempOK (G2_tempOnly_y ht).1 (G2_tempOnly_y ht).2 hzt hB,
      msumB_xor two_self_zero, msumB_two_pow _ _ (wY_lt' ht),
      msumB_two_pow _ _ (wX_lt' ht)]
  · rw [xrL_eq_msumB two_self_zero gateList2_bound (wU_lt' hs), G2_mask_u hs,
      msumB_two_pow _ _ (wU_lt' hs)]

end IntMul.Kappa.R8.Bit.Oppbank.OneRunNB
