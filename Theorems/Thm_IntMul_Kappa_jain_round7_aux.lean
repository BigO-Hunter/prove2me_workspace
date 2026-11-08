-- Auxiliary decomposition for `IntMul.Kappa.jain_round7_framework` (r7 port attempt).
--
-- Structural relation to round six: round 7 is round 6 with the bit network replaced by
-- Jain's round-seven staircase network (witness 1: `Jain.bitR7`, width 529, `W = 108516254`);
-- the complex network (`Jain.cxR6`), the machine construction and the crude-guard assembly are
-- literally unchanged.  Accordingly this file factors the framework theorem into exactly the
-- pieces the round-six development supplies interfaces for (`Def_IntMul_Kappa_RG_Defs`:
-- `BitNetMomStmtG`, `P14NeedG`, `R6.Prm`), with two lemmas proved outright here and four
-- precisely-stated `sorry` lemmas isolating the subtracted round-six assemblies and the new
-- round-seven network:
--
-- * `r7_normalize`      — the subtracted `R6Norm.r6_normalize` (CrudeAssembly → `Prm`).
-- * `bitNetR7_mom`      — the round-seven staircase bit network (the new content of round 7).
-- * `p14NeedG_cxR6`     — the subtracted `IL3H.p14Need6_all` (round-6 complex network).
-- * `kappa_of_networks_G` — the subtracted `kappaBound_of_machine6`, parametric form.

import Definitions.Def_IntMul_MultitapeModel
import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_KappaJainData
import Definitions.Def_IntMul_Kappa_RG_Defs
import Theorems.Thm_IntMul_Kappa_R6_rG_normalize
import Theorems.Thm_IntMul_Kappa_R6_IL3H_p14NeedG_all

set_option autoImplicit false

namespace IntMul.Kappa.R7Aux

open IntMul.Kappa

/-! ## Small real facts: the moment premises force positive exponents -/

/-- If `τ ≤ 0` then every child width is `≤ m` gives `∑ n_w ≤ ∑ n_w (w/m)^τ`, since each
`(w/m)^τ ≥ 1`. -/
theorem histMoment_ge_counts (h : List (ℕ × ℕ)) (m : ℕ) (τ : ℝ) (hτ : τ ≤ 0)
    (hvalid : ∀ p ∈ h, 0 < p.1 ∧ p.1 ≤ m) :
    ((h.map Prod.snd).sum : ℝ) ≤ histMoment h m τ := by
  have key : ∀ w n : ℕ, 0 < w → w ≤ m → (1 : ℝ) ≤ ((w : ℝ) / m) ^ τ := by
    intro w _ hw0 hwm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast lt_of_lt_of_le hw0 hwm
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by positivity)
      (by rw [div_le_one hm0]; exact_mod_cast hwm) hτ
  induction h with
  | nil => simp [histMoment]
  | cons p t ih =>
    obtain ⟨w, n⟩ := p
    have hv := hvalid (w, n) (by simp)
    have hih := ih (fun q hq => hvalid q (by simp [hq]))
    simp only [histMoment, List.map_cons, List.sum_cons] at hih ⊢
    push_cast at hih ⊢
    have h1 := key w n hv.1 hv.2
    have hterm : (n : ℝ) ≤ (n : ℝ) * ((w : ℝ) / m) ^ τ := by nlinarith
    linarith

/-- The bit moment premise forces `0 < 1 - ab`: at `τ ≤ 0` the single `w = 1` entry of
`Jain.bitR7` already contributes `1690297301 > 108516254`. -/
theorem tau_pos_of_moment {ab : ℝ} (hbit : histMoment Jain.bitR7 529 (1 - ab) < 108516254) :
    0 < 1 - ab := by
  rcases le_or_gt 1 ab with hle | hgt
  · exfalso
    have hge := histMoment_ge_counts Jain.bitR7 529 (1 - ab) (by linarith) (by decide)
    have hsum : (1690297301 : ℝ) ≤ ((Jain.bitR7.map Prod.snd).sum : ℝ) := by
      have h : 1690297301 ≤ (Jain.bitR7.map Prod.snd).sum := by decide
      exact_mod_cast h
    linarith
  · linarith

/-- The complex moment premise forces `0 < 1 - ac`: at `σ ≤ 0` the two entries `w = 1` and
`w = 2` of `Jain.cxR6` already contribute `184811440 + 107199136 = 292010576 > 207387136`. -/
theorem sigma_pos_of_moment {ac : ℝ} (hcx : histMoment Jain.cxR6 576 (1 - ac) < 207387136) :
    0 < 1 - ac := by
  rcases le_or_gt 1 ac with hle | hgt
  · exfalso
    have hge := histMoment_ge_counts Jain.cxR6 576 (1 - ac) (by linarith) (by decide)
    have hsum : (292010576 : ℝ) ≤ ((Jain.cxR6.map Prod.snd).sum : ℝ) := by
      have h : 184811440 + 107199136 ≤ (Jain.cxR6.map Prod.snd).sum := by decide
      exact_mod_cast h
    linarith
  · linarith

/-! ## The four isolated gaps (each a precisely-stated `sorry`) -/

/-- **(A) The subtracted `R6Norm.r6_normalize`.**  The crude-guard assembly at `β = 1/1000`
with positive moment exponents yields a round-six parameter record `P` satisfying `Prm.Ok`,
with `κ` below the minimum cost margin `P.gap`, at the original savings, and with the
crude depth guard transferred to the integral `P.C1`. -/
theorem r7_normalize (ab ac ε x C₁ κ : ℝ) (hab : 0 ≤ ab) (hac : 0 ≤ ac)
    (hτ : 0 < 1 - ab) (hσ : 0 < 1 - ac)
    (hasm : CrudeAssembly ab ac (1 / 1000) ε x C₁ κ 576 (histRankSum Jain.cxR6)) :
    ∃ P : R6.Prm, R6.Prm.Ok P ∧ κ < R6.Prm.gap P ∧ P.τ = 1 - ab ∧ P.σ = 1 - ac ∧
      2 + 576 * Real.log (histRankSum Jain.cxR6) ≤ (P.C1 : ℝ) := by
  exact R6.rG_normalize_sol_aux 576 (histRankSum Jain.cxR6) ab ac ε x C₁ κ
    hτ hσ hab hac hasm

/-- **(B) The round-seven staircase bit network** (witness 1: PR #62 producer, lifted frames,
late copies, deferred readouts, V leaves, staircase entrance corner): an explicit
`QHNet (ZMod 2) 108516254 T 529` with valid runs, `EdgesOK`/`FormalOK` at all large prime
powers, whose child-width moment is dominated by `Jain.bitR7` at every exponent in `(0, 1]`.
This is the new mathematical content of round 7 (round 6 proved the analogous statement at
`W = 148225616` for `Jain.bitR6`). -/
theorem bitNetR7_mom : R6.Bit.BitNetMomStmtG 108516254 529 Jain.bitR7 := by
  sorry

/-- **(C) The subtracted `IL3H.p14Need6_all`.**  The round-six complex network (unchanged from
round 6) in the gate class, with the moment bound and the crude depth guard, produces the
uniform Proposition 14 with a polynomial guard. -/
theorem p14NeedG_cxR6 (P : R6.Prm) (hOK : R6.Prm.Ok P)
    (hm : histMoment Jain.cxR6 576 P.σ < 207387136)
    (hg : 2 + 576 * Real.log (histRankSum Jain.cxR6) ≤ (P.C1 : ℝ)) :
    R6.P14NeedG 207387136 576 Jain.cxR6 P := by
  -- The recovered round-six complex-network theorem, instantiated at the gate class
  -- (Wc = 207387136, mc = 576, hc = Jain.cxR6) with wmax = 552 (largest width in `Jain.cxR6`)
  -- and p₀ = 1024 (inside the window 513..14693).
  have hS : (Jain.cxR6.map Prod.snd).sum = 916054304 := by decide
  have hb : ∀ p ∈ Jain.cxR6, 1 ≤ p.1 ∧ p.1 ≤ 552 := by decide
  have hnum : ∀ e, 1024 ≤ e →
      2 * ((Jain.cxR6.map Prod.snd).sum * (2 * 552 + 1) ^ e) ≤ (2 * 576) ^ e := by
    intro e he
    rw [hS]
    have key : ∀ m : ℕ, 2 * (916054304 * 1105 ^ (1024 + m)) ≤ 1152 ^ (1024 + m) := by
      intro m
      induction m with
      | zero => norm_num
      | succ m ih =>
        have e1 : 1105 ^ (1024 + m + 1) = 1105 ^ (1024 + m) * 1105 := by rw [Nat.pow_succ]
        have e2 : 1152 ^ (1024 + m + 1) = 1152 ^ (1024 + m) * 1152 := by rw [Nat.pow_succ]
        rw [e1, e2, Nat.add_assoc]
        have hshift : 2 * (916054304 * (1105 ^ (1024 + m) * 1105))
            = (2 * (916054304 * 1105 ^ (1024 + m))) * 1105 := by ring
        rw [hshift]
        exact Nat.mul_le_mul ih (by norm_num)
    have hshift : 1024 + (e - 1024) = e := by omega
    have := key (e - 1024)
    rwa [hshift] at this
  have hp0 : ((1024 : ℕ) : ℝ) ≤ 2 + 576 * Real.log (histRankSum Jain.cxR6) := by
    have hH : histRankSum Jain.cxR6 = 119453132304 := by decide
    rw [hH]
    have hge : ((847288609443 : ℕ) : ℝ) ≤ ((119453132304 : ℕ) : ℝ) := by norm_num
    have h25 : Real.log ((3 : ℝ) ^ 25) ≤ Real.log 119453132304 :=
      Real.log_le_log (by norm_num) hge
    have hlog3 : (1 : ℝ) < Real.log 3 := by
      have h := Real.log_lt_log (x := Real.exp 1) (y := (3 : ℝ)) Real.exp_one_lt_three
        (by norm_num)
      rwa [Real.log_exp] at h
    rw [Real.log_pow] at h25
    linarith
  exact p14NeedG_all_sol_aux 207387136 576 552 1024 Jain.cxR6 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb hnum hp0 (by norm_num) P hOK

/-- **(D) The subtracted `kappaBound_of_machine6`, parametric in the bit network.**  From a
bit network whose moment is dominated by the certified histogram, the round-six complex
Proposition 14, and the normalized parameters with `κ` below the minimum cost margin: the
OpenAI/Colkitt construction gives a deterministic multitape multiplier in time
`O(n (lg n)^(1-κ))`. -/
theorem kappa_of_networks_G (P : R6.Prm) (κ : ℝ) (hOK : R6.Prm.Ok P) (hκ : κ < R6.Prm.gap P)
    (hbn : R6.Bit.BitNetMomStmtG 108516254 529 Jain.bitR7)
    (hp14 : R6.P14NeedG 207387136 576 Jain.cxR6 P) :
    KappaBound κ := by
  sorry

end IntMul.Kappa.R7Aux
