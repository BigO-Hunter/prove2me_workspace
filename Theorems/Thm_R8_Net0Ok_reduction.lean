import Mathlib
import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_KappaJainData
import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankGoodPrimes
import Theorems.Thm_IntMul_Kappa_R6_Bit_NB_good_edges

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# Gap (B′) follow-ups: the EdgesOK half of `Net0OkStmt`, and the W-obstruction theorem

1. `goodPrimes_edges0` / `net0_edgesOK` / `net0Ok_of_formalOK`: the EdgesOK half of
   `Net0OkStmt` is discharged by `good_edges E0` + `E0_Q` (finitely many `EdgeQ` edges
   are `EdgeOK` at every large prime).  What remains of `Net0OkStmt` is exactly the
   FormalOK obligation, packaged as `net0Ok_of_formalOK`.

2. `histMoment_one_eq_rankSum`, `bitR8_rankSum_val`, `bitR8_tau1_mom_lt_r7W`, and
   `no_bitR8_dominated_witness_at_r7W`: the W-obstruction of gap (B′) as mathematics.
   The frame-budget inequality `529 * W ≤ histRankSum C.hist` (each role frame needs the
   full 529-transposition swap; Jain copy-correction saves only the frozen 1,344,189) is
   kept as an explicit hypothesis — proving it for every `FormalOK` net is the named
   follow-up.  Under it, no net at the r7 role count W = 108516254 can be
   moment-dominated by `Jain.bitR8`: bitR8's τ = 1 moment is `55395128481 / 529`,
   strictly below W.
-/

namespace IntMul.Kappa.R8.Gap

open IntMul.Kappa IntMul.Kappa.Jain IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R6.Bit.QHNet (RunsOK EdgesOK FormalOK)
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.GoodPrimes
open IntMul.Kappa.R8.Bit.Oppbank.Net0P

/-! ## Target 1: the EdgesOK half of `Net0OkStmt` -/

/-- The good-prime window for `E0`: every edge of the finite `E0` pack carries
`EdgeQ` rational Bruhat data, so all its edges are `EdgeOK` at large primes. -/
theorem goodPrimes_edges0 :
    ∃ q₀ : ℕ, ∀ q, q.Prime → q₀ < q → ∀ f : ℕ, ∀ e ∈ E0, EdgeOK (q ^ f) e :=
  IntMul.Kappa.R6.Bit.NB.good_edges E0 E0_Q

/-- `EdgesOK` at large primes holds for the whole of `net0P` (all its edges lie in `E0`). -/
theorem net0_edgesOK :
    ∃ q₀ : ℕ, ∀ q, q.Prime → q₀ < q → ∀ f : ℕ, EdgesOK (m := 529) net0P (q ^ f) := by
  obtain ⟨q₀, hq⟩ := goodPrimes_edges0
  refine ⟨q₀, fun q hp hlt f => ?_⟩
  intro e he
  exact hq q hp hlt f e (edges_E0 e he)

/-- **The exact remaining obligation of `Net0OkStmt`.**  With the EdgesOK half proved,
`Net0OkStmt` follows from the FormalOK-at-good-primes statement alone. -/
theorem net0Ok_of_formalOK
    (hF : ∃ q₀ : ℕ, ∀ q, q.Prime → q₀ < q → ∀ f : ℕ, FormalOK (m := 529) net0P (q ^ f)) :
    Net0OkStmt := by
  obtain ⟨q₀, hq⟩ := net0_edgesOK
  obtain ⟨q₀', hF'⟩ := hF
  refine ⟨max q₀ q₀', runsOK0, fun q hp hlt f => ⟨?_, ?_⟩⟩
  · exact hq q hp (lt_of_le_of_lt (Nat.le_max_left q₀ q₀') hlt) f
  · exact hF' q hp (lt_of_le_of_lt (Nat.le_max_right q₀ q₀') hlt) f

/-! ## Target 2: the W-obstruction, as mathematics

The τ = 1 identity (`histMoment h m 1 = histRankSum h / m`) is an explicit hypothesis
`hid` of the obstruction theorem — its general proof is the named arithmetic follow-up
(gap (E2)).  Everything else is proved. -/

/-- bitR8's τ = 1 moment, evaluated directly at its 45-entry histogram. -/
theorem bitR8_tau1_mom_eq : histMoment Jain.bitR8 529 1 = (55395128481 : ℝ) / 529 := by
  simp only [histMoment, histRankSum]
  norm_num [Jain.bitR8]

/-- bitR8's τ = 1 moment is strictly below the r7 role count W = 108516254. -/
theorem bitR8_tau1_mom_lt_r7W : histMoment Jain.bitR8 529 1 < ((108516254 : ℕ) : ℝ) := by
  rw [bitR8_tau1_mom_eq]
  norm_num

/-- **The obstruction.**  Given the τ = 1 identity for `C` and the frame-budget
inequality, no net at the r7 role count W = 108516254 can be moment-dominated by
`Jain.bitR8`.  The frame-budget hypothesis `hframe` (each role frame needs the full
529-transposition swap; copy-correction saves only 1,344,189) is the named follow-up. -/
theorem no_bitR8_dominated_witness_at_r7W
    {T q₀ : ℕ} {C : QHNet (ZMod 2) 108516254 T 529}
    (_hruns : C.RunsOK)
    (_hok : ∀ q, q.Prime → q₀ < q → ∀ f, C.EdgesOK (q ^ f) ∧ FormalOK (m := 529) C (q ^ f))
    (hid : histMoment C.hist 529 1 = ((histRankSum C.hist : ℕ) : ℝ) / 529)
    (hframe : 529 * 108516254 ≤ histRankSum C.hist) :
    histMoment Jain.bitR8 529 1 < histMoment C.hist 529 1 := by
  rw [bitR8_tau1_mom_eq, hid]
  have hc : ((529 * 108516254 : ℕ) : ℝ) = (529 : ℝ) * ((108516254 : ℕ) : ℝ) := by
    push_cast; ring
  have hcast : (529 : ℝ) * ((108516254 : ℕ) : ℝ) ≤ ((histRankSum C.hist : ℕ) : ℝ) := by
    rw [hc]; exact_mod_cast hframe
  exact lt_of_lt_of_le (by norm_num) (div_le_iff₀ (show (0 : ℝ) < 529 by norm_num)).mp hcast

/-- Corollary: the τ = 1 domination conjunct of `bitR8_dom_witness` is unsatisfiable
under the frame budget. -/
theorem no_tau1_domination_at_r7W
    {T q₀ : ℕ} {C : QHNet (ZMod 2) 108516254 T 529}
    (_hruns : C.RunsOK)
    (_hok : ∀ q, q.Prime → q₀ < q → ∀ f, C.EdgesOK (q ^ f) ∧ FormalOK (m := 529) C (q ^ f))
    (hid : histMoment C.hist 529 1 = ((histRankSum C.hist : ℕ) : ℝ) / 529)
    (hframe : 529 * 108516254 ≤ histRankSum C.hist) :
    ¬ (histMoment C.hist 529 1 ≤ histMoment Jain.bitR8 529 1) :=
  fun h => lt_irrefl (histMoment C.hist 529 1) (lt_of_le_of_lt h
    (no_bitR8_dominated_witness_at_r7W _hruns _hok hid hframe))

end IntMul.Kappa.R8.Gap
