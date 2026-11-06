import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunNBScalar
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-!
# Wire bounds and injectivity for the genuine R8 program
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.OneRunNB

open IntMul.Kappa IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank IntMul.Kappa.R8.Bit.Oppbank.NB
open IntMul.Kappa.R8.Bit.Oppbank.Repaired

theorem gw_lt {g : ℕ} (h : g < W) : gw g = .inl ⟨g, h⟩ := by rw [gw, dif_pos h]

theorem gw_ge {g : ℕ} (h1 : W ≤ g) (h2 : g < W + Tmp) :
    gw g = .inr ⟨g - W, by omega⟩ := by
  simp only [gw, dif_neg (show ¬ g < W by omega), Sum.inr.injEq, Fin.mk.injEq]
  exact Nat.mod_eq_of_lt (by omega)

theorem gw_inj {g g' : ℕ} (hg : g < W + Tmp) (hg' : g' < W + Tmp)
    (h : gw g = gw g') : g = g' := by
  by_cases h1 : g < W <;> by_cases h2 : g' < W
  · rw [gw_lt h1, gw_lt h2] at h; simpa using h
  · rw [gw_lt h1, gw_ge (by omega) hg'] at h; simp at h
  · rw [gw_ge (by omega) hg, gw_lt h2] at h; simp at h
  · rw [gw_ge (by omega) hg, gw_ge (by omega) hg'] at h
    simp only [Sum.inr.injEq, Fin.mk.injEq] at h; omega

theorem g1_lt {b w : ℕ} (hb : b < v) (hw : w < NL) : g1 b w < W + Tmp := by
  unfold g1; split_ifs <;> norm_num [W, Tmp, N, v, NL, NR, wEnt, wAuxEnd, h] at * <;> omega

theorem g2_lt {a w : ℕ} (ha : a < v) (hw : w < NL + v) : g2 a w < W + Tmp := by
  unfold g2; split_ifs <;> norm_num [W, Tmp, N, v, NL, NR, wEnt, wAuxEnd, h] at * <;> omega

theorem g1_inj {b b' w w' : ℕ} (hb : b < v) (hb' : b' < v) (hw : w < NL) (hw' : w' < NL)
    (h : g1 b w = g1 b' w') : b = b' ∧ w = w' := by
  have hv : v = 1771 := rfl
  have hN : N = 3136441 := rfl
  have hW : W = 104719230 := rfl
  have hT : Tmp = 3217907 := rfl
  have hNR : NR = 27794 := rfl
  have hE : wEnt = 3542 := rfl
  have hA : wAuxEnd = 31336 := rfl
  have hL : NL = 31359 := rfl
  have hh : Oppbank.h = 23 := rfl
  unfold g1 at h; split_ifs at h <;> simp only [hv, hN, hW, hT, hNR, hE, hA, hL, hh] at * <;> omega

theorem g2_inj {a a' w w' : ℕ} (ha : a < v) (ha' : a' < v) (hw : w < NL + v) (hw' : w' < NL + v)
    (h : g2 a w = g2 a' w') : a = a' ∧ w = w' := by
  have hv : v = 1771 := rfl
  have hN : N = 3136441 := rfl
  have hW : W = 104719230 := rfl
  have hT : Tmp = 3217907 := rfl
  have hNR : NR = 27794 := rfl
  have hE : wEnt = 3542 := rfl
  have hA : wAuxEnd = 31336 := rfl
  have hL : NL = 31359 := rfl
  have hh : Oppbank.h = 23 := rfl
  unfold g2 at h; split_ifs at h <;> simp only [hv, hN, hW, hT, hNR, hE, hA, hL, hh] at * <;> omega

theorem ι1_inj {b b' w w' : ℕ} (hb : b < v) (hb' : b' < v) (hw : w < NL) (hw' : w' < NL)
    (h : NB.ι1 b w = NB.ι1 b' w') : b = b' ∧ w = w' :=
  g1_inj hb hb' hw hw' (gw_inj (g1_lt hb hw) (g1_lt hb' hw') h)

theorem ι2_inj {a a' w w' : ℕ} (ha : a < v) (ha' : a' < v) (hw : w < NL + v) (hw' : w' < NL + v)
    (h : NB.ι2 a w = NB.ι2 a' w') : a = a' ∧ w = w' :=
  g2_inj ha ha' hw hw' (gw_inj (g2_lt ha hw) (g2_lt ha' hw') h)

/-- Stage-two `x` wires are the stage-one `Y` images. -/
theorem g2_x {a t : ℕ} (ht : t < v) (ha : a < v) : g2 a t = g1 t (wY a) := by
  rw [show wY a = v + a from rfl]; unfold g1 g2
  rw [if_pos ht, if_neg (by simp only [v, wEnt] at * <;> omega),
    if_pos (by simp only [v, wEnt] at * <;> omega), Nat.add_sub_cancel_left]

/-- Stage-two `Y` wires are the stage-one `X` images. -/
theorem g2_y {a s : ℕ} (hs : s < v) (ha : a < v) : g2 a (wY s) = g1 s (wX a) := by
  rw [show wY s = v + s from rfl, show wX a = a from rfl]; unfold g1 g2
  rw [if_neg (by simp only [v, wEnt] at * <;> omega),
    if_pos (by simp only [v, wEnt] at * <;> omega), if_pos ha, Nat.add_sub_cancel_left]

/-- Stage-two wires beyond the `x,y` banks are not stage-one wires. -/
theorem g2_ne_g1 {a w b w' : ℕ} (ha : a < v) (hw : wEnt ≤ w) (hw2 : w < NL + v) (hb : b < v)
    (hw' : w' < NL) : g2 a w ≠ g1 b w' := by
  have hv : v = 1771 := rfl
  have hN : N = 3136441 := rfl
  have hW : W = 104719230 := rfl
  have hT : Tmp = 3217907 := rfl
  have hNR : NR = 27794 := rfl
  have hE : wEnt = 3542 := rfl
  have hA : wAuxEnd = 31336 := rfl
  have hL : NL = 31359 := rfl
  have hh : Oppbank.h = 23 := rfl
  unfold g1 g2; split_ifs <;> simp only [hv, hN, hW, hT, hNR, hE, hA, hL, hh] at * <;> omega

end IntMul.Kappa.R8.Bit.Oppbank.OneRunNB
