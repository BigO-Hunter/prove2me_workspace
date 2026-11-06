import Submission.SubsetSumStatement
import Submission.Spec
import Submission.Bridge
import Submission.Sort
import Submission.Det
import Submission.ProgFacts
import Submission.Fit
import Submission.Words
import Submission.ExecEq
import Submission.Program
import Submission.Prologue
import Submission.PhaseA
import Submission.PhaseB
import Submission.SmallN
import Submission.Runtime
set_option autoImplicit true

/-!
# The summit: Race_bound — SolvedInTime (3/4)

Composes every lane's theorems into the final submission target.

Complete: the small-n dispatch (pcs 0→192, n ∈ {2,3}) with both verdicts;
the full prologue (pcs 0→86) landing exactly in `init_exec`'s contract; the
Phase A walk (86→148) with sorted half-sums; the Phase B candidate × binary
search cascade (148→verdict, fuel logarithmic in the window); and the budget
composition putting the whole run under `Runtime.stepBound` for every n ≥ 4.
-/

namespace SubsetSum.MITM

open BigOSpeedrun.SubsetSum SubsetSum.MITM.Spec

/-! ### The run↔exec bridge (definitional) -/

/-! ### The run↔exec bridge (definitional) -/

theorem run_eq_exec {n : Nat} (x : Instance n) (ρ : Nat → BitVec (wordLength n x.bits))
    (T : Nat) :
    run prog x ρ T
      = exec prog ρ T 0 0 (memOf (wordLength n x.bits) (inF x)) := rfl



/-! ### Input words fit the word length -/

theorem input_lt_wordLength {n : Nat} (x : Instance n) (hn : 0 < n)
    (v : Nat) (hv : v ∈ x.input) : v < 2 ^ (wordLength n x.bits) := by
  have hmax : x.maxValue < 2 ^ x.bits := maxValue_lt_pow x hn
  have hbl : x.bits ≤ 4 * (n + x.bits)
      + Nat.log2 ((n + 2) ^ 4 - 1) + 1 := by omega
  have hp : 2 ^ x.bits ≤ 2 ^ (wordLength n x.bits) :=
    Nat.pow_le_pow_right (by omega) hbl
  have hmem : v ∈ n :: (List.ofFn x.a ++ [x.t]) := hv
  rcases List.mem_cons.mp hmem with heq | hrest
  · rw [heq]
    have h1 : (2:Nat) ^ n ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : (2:Nat) ^ (2 * n) ≤ 2 ^ (wordLength n x.bits) :=
      Nat.pow_le_pow_right (by omega)
        (by show 2 * n ≤ 4 * (n + x.bits) + Nat.log2 ((n + 2) ^ 4 - 1) + 1; omega)
    exact Nat.lt_of_lt_of_le (Nat.lt_two_pow_self (n := n)) (Nat.le_trans h1 h2)
  · rcases List.mem_append.mp hrest with hin | ht
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hin
      exact Nat.lt_of_le_of_lt (maxValue_ge_a x i) (Nat.lt_of_lt_of_le hmax hp)
    · obtain rfl : v = x.t := List.mem_singleton.mp ht
      exact Nat.lt_of_le_of_lt (maxValue_ge_t x) (Nat.lt_of_lt_of_le hmax hp)

/-! ### The small-n dispatch (pcs 0→12→192, n ∈ {2, 3}) -/

theorem pro_segA23 {w n : Nat} (x : Instance n) (ρ : Nat → BitVec w)
    (hn : 2 ≤ n) (hn3 : n ≤ 3) (hpow : 2 ^ (2 * n) ≤ 2 ^ w)
    (hif : ∀ q, inF x q < 2 ^ w)
    (r S : Nat) (hS : 8 ≤ S) :
    ∃ g, exec prog ρ S 0 r (memOf w (inF x))
      = exec prog ρ (S - 8) 8 r (memOf w g) ∧
      (∀ q, g q < 2 ^ w) ∧ g 0 = 2 * n + 2 ∧ g 1 = 1 ∧ g 2 = 0 ∧
      (∀ j, j + 1 ≤ 3 → j + 1 ≤ n + 1 → g (2 * n + j) = inF x (j + 1)) ∧
      (∀ q, 4 ≤ q → q ≤ n + 1 → g q = inF x q) := by
  have h416 : (2:Nat) ^ (4:Nat) ≤ 2 ^ (2 * n) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h16 : (16:Nat) ≤ 2 ^ w := Nat.le_trans h416 hpow
  have hv0 : (2 * n + 2 : Nat) < 2 ^ w := Nat.lt_of_lt_of_le (by omega) h16
  have e0 : inF x 0 + inF x 0 = 2 * n := by
    rw [inF_zero]
    omega
  have e1 : (up (inF x) (0) (2 * n)) 0 = 2 * n := up_eq _ _ _
  have e2 : (up (inF x) (0) (2 * n)) 1 = inF x 1 := up_ne (by omega)
  have e3 : (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1)) 0
      + (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1)) 1
      = 2 * n + 1 := by
    rw [up_ne (show (0:Nat) ≠ 1 by omega), up_ne (show (0:Nat) ≠ 2 * n by omega),
      up_eq, up_eq]
  have e4 : (up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1))
      (0) (2 * n + 1)) 0 = 2 * n + 1 := up_eq _ _ _
  have e5 : (up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1))
      (0) (2 * n + 1)) 2 = inF x 2 := by
    rw [up_ne (show (2:Nat) ≠ 0 by omega), up_ne (show (2:Nat) ≠ 1 by omega),
      up_ne (show (2:Nat) ≠ 2 * n by omega), up_ne (show (2:Nat) ≠ 0 by omega)]
  have e6 : (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1))
      (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) 2
      - (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1))
      (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) 2 = 0 := by
    rw [up_ne (show (2:Nat) ≠ 2 * n + 1 by omega), up_ne (show (2:Nat) ≠ 0 by omega),
      up_ne (show (2:Nat) ≠ 1 by omega), up_ne (show (2:Nat) ≠ 2 * n by omega),
      up_ne (show (2:Nat) ≠ 0 by omega)]
    omega
  have e7 : (up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1))
      (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0)) 0
      + (up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1))
      (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0)) 1 = 2 * n + 2 := by
    rw [up_ne (show (0:Nat) ≠ 2 by omega), up_ne (show (0:Nat) ≠ 2 * n + 1 by omega),
      up_eq, up_ne (show (1:Nat) ≠ 2 by omega),
      up_ne (show (1:Nat) ≠ 2 * n + 1 by omega), up_ne (show (1:Nat) ≠ 0 by omega),
      up_eq]
  have e8 : (up (up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1))
      (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0)) (0) (2 * n + 2)) 0
      = 2 * n + 2 := up_eq _ _ _
  have e9 : (up (up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1))
      (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0)) (0) (2 * n + 2)) 3
      = inF x 3 := by
    rw [up_ne (show (3:Nat) ≠ 0 by omega), up_ne (show (3:Nat) ≠ 2 by omega),
      up_ne (show (3:Nat) ≠ 2 * n + 1 by omega), up_ne (show (3:Nat) ≠ 0 by omega),
      up_ne (show (3:Nat) ≠ 1 by omega), up_ne (show (3:Nat) ≠ 2 * n by omega),
      up_ne (show (3:Nat) ≠ 0 by omega)]
  have hv : ∀ v, v ≤ 2 * n + 2 → v < 2 ^ w := by
    intro v hvv
    exact Nat.lt_of_le_of_lt hvv hv0
  have hfit1 : ∀ q, up (inF x) (0) (2 * n) q < 2 ^ w :=
    upFit hif (hv _ (by omega))
  have hfit2 : ∀ q, up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1) q < 2 ^ w :=
    upFit hfit1 (hif 1)
  have hfit3 : ∀ q, up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1)
      q < 2 ^ w := upFit hfit2 (hv _ (by omega))
  have hfit4 : ∀ q, up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1))
      (0) (2 * n + 1) q < 2 ^ w := upFit hfit3 (hv _ (by omega))
  have hfit5 : ∀ q, up (up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1))
      (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2) q < 2 ^ w :=
    upFit hfit4 (hif 2)
  have hfit6 : ∀ q, up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1))
      (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0) q < 2 ^ w :=
    upFit hfit5 (hv _ (by omega))
  have hfit7 : ∀ q, up (up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n)
      (inF x 1)) (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0))
      (0) (2 * n + 2) q < 2 ^ w := upFit hfit6 (hv _ (by omega))
  have hfit8 : ∀ q, up (up (up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n)
      (inF x 1)) (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0))
      (0) (2 * n + 2)) (2 * n + 2) (inF x 3) q < 2 ^ w := upFit hfit7 (hif 3)
  have hf0 : (up (up (up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n)
      (inF x 1)) (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0))
      (0) (2 * n + 2)) (2 * n + 2) (inF x 3)) (0) = 2 * n + 2 := by
    rw [up_ne (show (0:Nat) ≠ 2 * n + 2 by omega), up_eq]
  have hf1 : (up (up (up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n)
      (inF x 1)) (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0))
      (0) (2 * n + 2)) (2 * n + 2) (inF x 3)) (1) = 1 := by
    rw [up_ne (show (1:Nat) ≠ 2 * n + 2 by omega), up_ne (show (1:Nat) ≠ 0 by omega),
      up_ne (show (1:Nat) ≠ 2 by omega), up_ne (show (1:Nat) ≠ 2 * n + 1 by omega),
      up_ne (show (1:Nat) ≠ 0 by omega), up_eq]
  have hf2 : (up (up (up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n)
      (inF x 1)) (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0))
      (0) (2 * n + 2)) (2 * n + 2) (inF x 3)) (2) = 0 := by
    rw [up_ne (show (2:Nat) ≠ 2 * n + 2 by omega), up_ne (show (2:Nat) ≠ 0 by omega),
      up_eq]
  have hscr : ∀ j, j + 1 ≤ 3 → j + 1 ≤ n + 1 →
      (up (up (up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n)
      (inF x 1)) (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0))
      (0) (2 * n + 2)) (2 * n + 2) (inF x 3)) (2 * n + j) = inF x (j + 1) := by
    intro j hj1 hj2
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
    · rw [show (2 * n + 0) = 2 * n from Nat.add_zero (2 * n)]
      rw [up_ne (show 2 * n ≠ 2 * n + 2 by omega), up_ne (show 2 * n ≠ 0 by omega),
        up_ne (show 2 * n ≠ 2 by omega), up_ne (show 2 * n ≠ 2 * n + 1 by omega),
        up_ne (show 2 * n ≠ 0 by omega), up_ne (show 2 * n ≠ 1 by omega), up_eq]
    · rw [up_ne (show 2 * n + 1 ≠ 2 * n + 2 by omega),
        up_ne (show 2 * n + 1 ≠ 0 by omega), up_ne (show 2 * n + 1 ≠ 2 by omega),
        up_eq]
    · rw [up_eq]
  have hp4 : ∀ q, 4 ≤ q → q ≤ n + 1 →
      (up (up (up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n)
      (inF x 1)) (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0))
      (0) (2 * n + 2)) (2 * n + 2) (inF x 3)) q = inF x q := by
    intro q hq1 hq2
    rw [up_ne (show q ≠ 2 * n + 2 by omega), up_ne (show q ≠ 0 by omega),
      up_ne (show q ≠ 2 by omega), up_ne (show q ≠ 2 * n + 1 by omega),
      up_ne (show q ≠ 0 by omega), up_ne (show q ≠ 1 by omega),
      up_ne (show q ≠ 2 * n by omega), up_ne (show q ≠ 0 by omega)]
  refine ⟨up (up (up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n)
    (inF x 1)) (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0))
    (0) (2 * n + 2)) (2 * n + 2) (inF x 3), ?_, hfit8, ?_, ?_, ?_, ?_, ?_⟩
  · rw [exec_add_step (by omega) (show prog.getD 0 Instr.reject = Instr.add 0 0 0 by rfl),
      e0, exec_store_step (by omega)
        (show prog.getD 1 Instr.reject = Instr.store 0 1 by rfl) hfit1, e1, e2,
      exec_one_step (by omega)
        (show prog.getD 2 Instr.reject = Instr.one 1 by rfl),
      exec_add_step (by omega)
        (show prog.getD 3 Instr.reject = Instr.add 0 0 1 by rfl), e3,
      exec_store_step (by omega)
        (show prog.getD 4 Instr.reject = Instr.store 0 2 by rfl) hfit4, e4, e5,
      exec_sub_step (by omega)
        (show prog.getD 5 Instr.reject = Instr.sub 2 2 2 by rfl) hfit5 (Nat.le_refl _),
      e6, exec_add_step (by omega)
        (show prog.getD 6 Instr.reject = Instr.add 0 0 1 by rfl), e7,
      exec_store_step (by omega)
        (show prog.getD 7 Instr.reject = Instr.store 0 3 by rfl) hfit7, e8, e9]
    simp only [Nat.sub_sub, Nat.reduceAdd]
  · exact hf0
  · exact hf1
  · exact hf2
  · exact hscr
  · exact hp4

/-- The small-n dispatch: pcs 0→12 with the guard `blt 0 3 192` TAKEN
(n ≤ 3 makes cell0 = 2n+2 < 9 = cell3).  Control lands at 192 in the
state `smalln_loads` consumes (cur := 2n+2, [3] := 9). -/

theorem pro_dispatch23 {w n : Nat} (x : Instance n) (ρ : Nat → BitVec w)
    (hn : 2 ≤ n) (hn3 : n ≤ 3) (hpow : 2 ^ (2 * n) ≤ 2 ^ w)
    (hif : ∀ q, inF x q < 2 ^ w) (r S : Nat) (hS : 13 ≤ S) :
    ∃ g, exec prog ρ S 0 r (memOf w (inF x))
      = exec prog ρ (S - 13) 192 r (memOf w g) ∧
      (∀ q, g q < 2 ^ w) ∧ g 0 = 2 * n + 2 ∧ g 1 = 1 ∧ g 2 = 0 ∧
      g 3 = 9 ∧
      (∀ j, j + 1 ≤ 3 → j + 1 ≤ n + 1 → g (2 * n + j) = inF x (j + 1)) ∧
      (∀ q, 4 ≤ q → q ≤ n + 1 → g q = inF x q) := by
  have h416 : (2:Nat) ^ (4:Nat) ≤ 2 ^ (2 * n) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h16 : (16:Nat) ≤ 2 ^ w := Nat.le_trans h416 hpow
  have h9 : (9:Nat) < 2 ^ w := by omega
  obtain ⟨f, hex, hfit, hf0, hf1, hf2, hscr, hp4⟩ :=
    pro_segA23 x ρ hn hn3 hpow hif r S (by omega)
  have e1 : f 1 + f 1 = 2 := by rw [hf1]
  have e2 : (up f 3 2) 3 + (up f 3 2) 3 = 4 := by rw [up_eq]
  have e3 : (up (up f 3 2) 3 4) 3 + (up (up f 3 2) 3 4) 3 = 8 := by rw [up_eq]
  have e4 : (up (up (up f 3 2) 3 4) 3 8) 3
      + (up (up (up f 3 2) 3 4) 3 8) 1 = 9 := by
    rw [up_eq, up_ne (show (1:Nat) ≠ 3 by omega),
      up_ne (show (1:Nat) ≠ 3 by omega), up_ne (show (1:Nat) ≠ 3 by omega), hf1]
  have hfit1 : ∀ q, (up f 3 2) q < 2 ^ w := upFit hfit (by omega)
  have hfit2 : ∀ q, (up (up f 3 2) 3 4) q < 2 ^ w := upFit hfit1 (by omega)
  have hfit3 : ∀ q, (up (up (up f 3 2) 3 4) 3 8) q < 2 ^ w := upFit hfit2 (by omega)
  have hfit4 : ∀ q, (up (up (up (up f 3 2) 3 4) 3 8) 3 9) q < 2 ^ w :=
    upFit hfit3 h9
  have g0 : (up (up (up (up f 3 2) 3 4) 3 8) 3 9) 0 = 2 * n + 2 := by
    rw [up_ne (show (0:Nat) ≠ 3 by omega), up_ne (show (0:Nat) ≠ 3 by omega),
      up_ne (show (0:Nat) ≠ 3 by omega), up_ne (show (0:Nat) ≠ 3 by omega), hf0]
  have g1 : (up (up (up (up f 3 2) 3 4) 3 8) 3 9) 1 = 1 := by
    rw [up_ne (show (1:Nat) ≠ 3 by omega), up_ne (show (1:Nat) ≠ 3 by omega),
      up_ne (show (1:Nat) ≠ 3 by omega), up_ne (show (1:Nat) ≠ 3 by omega), hf1]
  have g2 : (up (up (up (up f 3 2) 3 4) 3 8) 3 9) 2 = 0 := by
    rw [up_ne (show (2:Nat) ≠ 3 by omega), up_ne (show (2:Nat) ≠ 3 by omega),
      up_ne (show (2:Nat) ≠ 3 by omega), up_ne (show (2:Nat) ≠ 3 by omega), hf2]
  have g3 : (up (up (up (up f 3 2) 3 4) 3 8) 3 9) 3 = 9 := up_eq _ _ _
  have gscr : ∀ j, j + 1 ≤ 3 → j + 1 ≤ n + 1 →
      (up (up (up (up f 3 2) 3 4) 3 8) 3 9) (2 * n + j) = inF x (j + 1) := by
    intro j hj1 hj2
    rw [up_ne (show 2 * n + j ≠ 3 by omega), up_ne (show 2 * n + j ≠ 3 by omega),
      up_ne (show 2 * n + j ≠ 3 by omega), up_ne (show 2 * n + j ≠ 3 by omega)]
    exact hscr j hj1 hj2
  have gp4 : ∀ q, 4 ≤ q → q ≤ n + 1 →
      (up (up (up (up f 3 2) 3 4) 3 8) 3 9) q = inF x q := by
    intro q hq1 hq2
    rw [up_ne (show q ≠ 3 by omega), up_ne (show q ≠ 3 by omega),
      up_ne (show q ≠ 3 by omega), up_ne (show q ≠ 3 by omega)]
    exact hp4 q hq1 hq2
  have hlt0 : (up (up (up (up f 3 2) 3 4) 3 8) 3 9) 0
      < (up (up (up (up f 3 2) 3 4) 3 8) 3 9) 3 := by
    rw [up_ne (show (0:Nat) ≠ 3 by omega), up_ne (show (0:Nat) ≠ 3 by omega),
      up_ne (show (0:Nat) ≠ 3 by omega), up_ne (show (0:Nat) ≠ 3 by omega), hf0,
      up_eq]
    omega
  have hpfx : exec prog ρ (S - 8) 8 r (memOf w f)
      = exec prog ρ (S - 8 - 5) 192 r
          (memOf w (up (up (up (up f 3 2) 3 4) 3 8) 3 9)) := by
    rw [exec_add_step (by omega)
        (show prog.getD 8 Instr.reject = Instr.add 3 1 1 by rfl), e1,
      exec_add_step (by omega)
        (show prog.getD 9 Instr.reject = Instr.add 3 3 3 by rfl), e2,
      exec_add_step (by omega)
        (show prog.getD 10 Instr.reject = Instr.add 3 3 3 by rfl), e3,
      exec_add_step (by omega)
        (show prog.getD 11 Instr.reject = Instr.add 3 3 1 by rfl), e4,
      exec_blt_lt_step (by omega)
        (show prog.getD 12 Instr.reject = Instr.blt 0 3 192 by rfl) hfit4 hlt0]
    simp only [Nat.sub_sub, Nat.reduceAdd]
  refine ⟨up (up (up (up f 3 2) 3 4) 3 8) 3 9, hex.trans hpfx, hfit4,
    g0, g1, g2, g3, gscr, gp4⟩



/-! ### The n ≥ 4 prologue: pcs 0 → 86 -/

/-! ### The n ≥ 4 prologue chain, pcs 0 → 65 (segG lands separately) -/

theorem prologue_to65 (x : Instance n) (ρ : Nat → BitVec w) (hn : 4 ≤ n)
    (hpow : 2 ^ (2 * n) ≤ 2 ^ w) (hif : ∀ q, inF x q < 2 ^ w)
    (r S : Nat) (hS : 65 ≤ S) :
    ∃ g, exec prog ρ S 0 r (memOf w (inF x))
      = exec prog ρ (S - 65) 65 r (memOf w g) ∧
      (∀ q, g q < 2 ^ w) ∧ g 0 = 2 * n + 23 ∧ g 1 = 1 ∧ g 2 = 0 ∧
      g 3 = 22 ∧ g 4 = 2 * n ∧ g 5 = 0 ∧
      (∀ j, j + 1 ≤ 22 → j + 1 ≤ n + 1 → g (2 * n + j) = inF x (j + 1)) ∧
      (∀ q, 23 ≤ q → q ≤ n + 1 → g q = inF x q) ∧
      (∀ q, 8 ≤ q → q < 2 * n → g q = inF x q) := by
  obtain ⟨f1, h1, hf1, h10, h11, h12, h1s, h1p, h1m⟩ :=
    pro_segA x ρ hn hpow hif r S (by omega)
  obtain ⟨f2, h2, hf2, h20, h21, h22, h23, h2s, h2p, h2m⟩ :=
    pro_segC x ρ hn hpow f1 r (S - 8) (by omega) hf1 h10 h11 h12 h1s h1p
  obtain ⟨f3, h3, hf3, h30, h31, h32, h3s, h3p, h3m⟩ :=
    pro_saveAks x ρ hn hpow hif f2 r (S - 13) (by omega) hf2 h20 h21 h22 h2s h2p
  obtain ⟨f4, h4, hf4, h40, h41, h42, h43, h44, h4s, h4p, h4m⟩ :=
    pro_segE x ρ hn hpow f3 r (S - 51) (by omega) hf3 h30 h31 h32 h3s h3p
  obtain ⟨f5, h5, hf5, h50, h51, h52, h53, h54, h55, h5s, h5p, h5m⟩ :=
    pro_segF x ρ hn hpow f4 r (S - 62) (by omega) hf4 h40 h41 h42 h43 h4s h4p
  have hmid5 : ∀ q, 8 ≤ q → q < 2 * n → f5 q = inF x q :=
    fun q hq1 hq2 => ((h5m q hq1 hq2).trans (h4m q hq1 hq2)).trans
      ((h3m q hq1 hq2).trans ((h2m q hq1 hq2).trans (h1m q hq1 hq2)))
  refine ⟨f5, ?_, hf5, h50, h51, h52, h53, h54, h55, h5s, h5p, hmid5⟩
  have hchain := h1.trans (h2.trans (h3.trans (h4.trans h5)))
  simp only [Nat.sub_sub, Nat.reduceAdd] at hchain
  exact hchain

/-- The full prologue: pcs 0 → 86 in `c ≤ 236 + 6 * (n - 21)` steps, landing
exactly in `init_exec`'s entry contract. -/

theorem prologue_exec (x : Instance n) (ρ : Nat → BitVec w) (hn : 4 ≤ n)
    (hpow : 2 ^ (2 * n) ≤ 2 ^ w) (hif : ∀ q, inF x q < 2 ^ w)
    (r S : Nat) (hS : 236 + 6 * (n + 2 - 23) ≤ S) :
    ∃ g c, c ≤ 236 + 6 * (n + 2 - 23) ∧
      exec prog ρ S 0 r (memOf w (inF x)) = exec prog ρ (S - c) 86 r (memOf w g) ∧
      (∀ q, g q < 2 ^ w) ∧ g 1 = 1 ∧ g 2 = 0 ∧ g 7 = n ∧ g 8 = 2 * n + 23 ∧
      (∀ c', c' ≤ 3 * n + 26 + 2 * 2 ^ (n / 2) → c' < 2 ^ w) ∧
      (∀ i, 1 ≤ i → i ≤ n → g (2 * n + 23 + i) = instA x (i - 1)) ∧
      g (2 * n + 23 + (n + 1)) = x.t := by
  obtain ⟨f, h65, hfit, hf0, hf1, hf2, hf3, hf4, hf5, hscr, hp23, hmid⟩ :=
    prologue_to65 x ρ hn hpow hif r S (by omega)
  obtain ⟨g, c, hc, hex, hgfit, hg1, hg2, hg7, hg8, hgaddr, hgrel, hgtgt⟩ :=
    pro_segG x ρ hn hpow f r (S - 65) (by omega) hfit hf0 hf1 hf2 hf3 hf4 hf5
      hscr hp23 hmid
  refine ⟨g, 65 + c, ?_, ?_, hgfit, hg1, hg2, hg7, hg8, hgaddr, hgrel, hgtgt⟩
  · omega
  · have hfin := h65.trans hex
    rw [show S - 65 - c = S - (65 + c) from by omega] at hfin
    exact hfin




/-! ### The small-n verdicts (complete) -/

/-- The horizon covers the unrolled n = 2 run. -/
theorem budget2 : (34:Nat) ≤ Runtime.stepBound 2 + Runtime.constOverhead := by
  decide

/-- The horizon covers the unrolled n = 3 run. -/
theorem budget3 : (48:Nat) ≤ Runtime.stepBound 3 + Runtime.constOverhead := by
  decide

/-- The n = 2 verdict list is exactly the `x.yes` question. -/
theorem verdict2_iff (x : Instance 2) :
    x.yes ↔ x.t ∈ [0, instA x 0, instA x 1, instA x 0 + instA x 1] :=
  (instance_yes_iff x).trans (isSum_two_iff (instA x) x.t)

/-- The n = 3 verdict list is exactly the `x.yes` question. -/
theorem verdict3_iff (x : Instance 3) :
    x.yes ↔ x.t ∈ [0, instA x 0, instA x 1, instA x 0 + instA x 1,
      instA x 2, instA x 2 + instA x 0, instA x 2 + instA x 1,
      instA x 2 + instA x 0 + instA x 1] :=
  (instance_yes_iff x).trans (isSum_three_iff (instA x) x.t)

theorem smalln2_run (x : Instance 2)
    (ρ : Nat → BitVec (wordLength 2 x.bits)) (T : Nat) (hT : 34 ≤ T) :
    run prog x ρ T
      = some (decide (x.t ∈ [0, instA x 0, instA x 1, instA x 0 + instA x 1])) := by
  rw [run_eq_exec]
  obtain ⟨g, hex, hgfit, hg0, hg1, hg2, hg3, hgscr, hgp4⟩ :=
    pro_dispatch23 x ρ (by omega) (by omega)
      (Nat.pow_le_pow_right (by omega)
        (by show 2 * 2 ≤ 4 * (2 + x.bits) + Nat.log2 ((2 + 2) ^ 4 - 1) + 1; omega))
      (inF_fit x _ (by omega) (fun v hv => input_lt_wordLength x (by omega) v hv))
      0 T (by omega)
  have hf4 : g 4 = inF x 1 := hgscr 0 (by omega) (by omega)
  have hf5 : g 5 = inF x 2 := hgscr 1 (by omega) (by omega)
  have hf6 : g 6 = inF x 3 := hgscr 2 (by omega) (by omega)
  have hv12 : inF x 1 + inF x 2 < 2 ^ (wordLength 2 x.bits) := by
    have h2s := two_sum_lt_pow_wordLength x (by omega)
    have hr : (List.range 2) = [0, 1] := by decide
    rw [hr] at h2s
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h2s
    have ha0 : inF x 1 = instA x 0 := (inF_instA x 1 (by omega) (by omega)).symm
    have ha1 : inF x 2 = instA x 1 := (inF_instA x 2 (by omega) (by omega)).symm
    rw [ha0, ha1]
    omega
  have hfinal := smalln2_exec ρ (inF x 1) (inF x 2) (inF x 3) g (T - 13) 0
    (by rw [hg0]) hg1 hg2 hg3 hf4 hf5 hf6 hv12 hgfit (by omega)
  have ht : inF x 3 = x.t := inF_t x
  have ha0 : inF x 1 = instA x 0 := (inF_instA x 1 (by omega) (by omega)).symm
  have ha1 : inF x 2 = instA x 1 := (inF_instA x 2 (by omega) (by omega)).symm
  rw [ht, ha0, ha1] at hfinal
  exact hex.trans hfinal

theorem smalln3_run (x : Instance 3)
    (ρ : Nat → BitVec (wordLength 3 x.bits)) (T : Nat) (hT : 48 ≤ T) :
    run prog x ρ T
      = some (decide (x.t ∈ [0, instA x 0, instA x 1, instA x 0 + instA x 1,
        instA x 2, instA x 2 + instA x 0, instA x 2 + instA x 1,
        instA x 2 + instA x 0 + instA x 1])) := by
  rw [run_eq_exec]
  obtain ⟨g, hex, hgfit, hg0, hg1, hg2, hg3, hgscr, hgp4⟩ :=
    pro_dispatch23 x ρ (by omega) (by omega)
      (Nat.pow_le_pow_right (by omega)
        (by show 2 * 3 ≤ 4 * (3 + x.bits) + Nat.log2 ((3 + 2) ^ 4 - 1) + 1; omega))
      (inF_fit x _ (by omega) (fun v hv => input_lt_wordLength x (by omega) v hv))
      0 T (by omega)
  have hf4t : g 4 = x.t := by
    rw [hgp4 4 (by omega) (by omega)]
    exact inF_t x
  have hf6 : g 6 = inF x 1 := hgscr 0 (by omega) (by omega)
  have hf7 : g 7 = inF x 2 := hgscr 1 (by omega) (by omega)
  have hf8 : g 8 = inF x 3 := hgscr 2 (by omega) (by omega)
  have h2s := two_sum_lt_pow_wordLength x (by omega)
  have hr : (List.range 3) = [0, 1, 2] := by decide
  rw [hr] at h2s
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.add_assoc] at h2s
  have ha0 : inF x 1 = instA x 0 := (inF_instA x 1 (by omega) (by omega)).symm
  have ha1 : inF x 2 = instA x 1 := (inF_instA x 2 (by omega) (by omega)).symm
  have ha2 : inF x 3 = instA x 2 := (inF_instA x 3 (by omega) (by omega)).symm
  have hv12 : inF x 1 + inF x 2 < 2 ^ (wordLength 3 x.bits) := by
    rw [ha0, ha1]; omega
  have hv31 : inF x 3 + inF x 1 < 2 ^ (wordLength 3 x.bits) := by
    rw [ha2, ha0]; omega
  have hv32 : inF x 3 + inF x 2 < 2 ^ (wordLength 3 x.bits) := by
    rw [ha2, ha1]; omega
  have hv312 : inF x 3 + inF x 1 + inF x 2 < 2 ^ (wordLength 3 x.bits) := by
    rw [ha2, ha0, ha1]; omega
  have hfinal := smalln3_exec ρ (inF x 1) (inF x 2) (inF x 3) x.t g (T - 13) 0
    (by rw [hg0]) hg1 hg2 hg3 hf4t hf6 hf7 hf8
    hv12 hv31 hv32 hv312 hgfit (by omega)
  rw [ha0, ha1, ha2] at hfinal
  exact hex.trans hfinal

theorem smalln_halts :
    ∀ (n : Nat) (x : Instance n), n = 2 ∨ n = 3 →
    ∀ ρ, (run prog x ρ (Runtime.stepBound n + Runtime.constOverhead)).isSome := by
  intro n x hn ρ
  rcases hn with rfl | rfl
  · rw [smalln2_run x ρ _ budget2]
    simp
  · rw [smalln3_run x ρ _ budget3]
    simp

/-- The small-n half of the correctness obligation: for n ∈ {2, 3} the run
returns exactly the membership decision, which matches `x.yes`. -/
theorem smalln_verdict :
    ∀ (n : Nat) (x : Instance n), n = 2 ∨ n = 3 →
    ∃ v, (∀ ρ, run prog x ρ (Runtime.stepBound n + Runtime.constOverhead)
        = some v) ∧ (x.yes → v = true) ∧ (¬x.yes → v = false) := by
  intro n x hn
  rcases hn with rfl | rfl
  · refine ⟨decide (x.t ∈ [0, instA x 0, instA x 1, instA x 0 + instA x 1]),
      fun ρ => smalln2_run x ρ _ budget2, ?_, ?_⟩
    · intro hyes
      exact decide_eq_true_iff.mpr ((verdict2_iff x).mp hyes)
    · intro hno
      by_cases hmem : x.t ∈ [0, instA x 0, instA x 1, instA x 0 + instA x 1]
      · exact absurd ((verdict2_iff x).mpr hmem) hno
      · simp [hmem]
  · refine ⟨decide (x.t ∈ [0, instA x 0, instA x 1, instA x 0 + instA x 1,
      instA x 2, instA x 2 + instA x 0, instA x 2 + instA x 1,
      instA x 2 + instA x 0 + instA x 1]),
      fun ρ => smalln3_run x ρ _ budget3, ?_, ?_⟩
    · intro hyes
      exact decide_eq_true_iff.mpr ((verdict3_iff x).mp hyes)
    · intro hno
      by_cases hmem : x.t ∈ [0, instA x 0, instA x 1, instA x 0 + instA x 1,
        instA x 2, instA x 2 + instA x 0, instA x 2 + instA x 1,
        instA x 2 + instA x 0 + instA x 1]
      · exact absurd ((verdict3_iff x).mpr hmem) hno
      · simp [hmem]

/-! ### The n ≥ 4 lane: budget composition and the full run -/

/-- The composed budget: prologue + Phase A + Phase B fits under the horizon
for every n ≥ 4.  The Phase B search is a binary search (fuel logarithmic in
the window), so the whole run is ~2^(n/2)·poly(n) — far below
`2^(n/2+20)·(n+2)^8` for all n ≥ 4. -/
theorem budget_compose {n : Nat} (hn : 4 ≤ n) :
    (236 + 6 * (n + 2 - 23)) + (12 + 44 * (2 ^ (n / 2) - 1) + 24 * (n / 2))
      + (6 + (11 * (n - n / 2) + 10 * (n / 2) + 29) * 2 ^ (n - n / 2))
    ≤ Runtime.stepBound n + Runtime.constOverhead := by
  have hmh : n - n / 2 ≤ n / 2 + 1 := by omega
  have hpowm : 2 ^ (n - n / 2) ≤ 2 * 2 ^ (n / 2) := by
    have h1 : 2 ^ (n - n / 2) ≤ 2 ^ (n / 2 + 1) :=
      Nat.pow_le_pow_right (by omega) hmh
    have h2 : 2 ^ (n / 2 + 1) = 2 * 2 ^ (n / 2) := by
      rw [Nat.pow_succ]
      omega
    omega
  have hQ : (1:Nat) ≤ 2 ^ (n / 2) := Nat.one_le_two_pow
  -- the Phase B product, folded onto 2^(n/2)
  have e2 : (11 * (n - n / 2) + 10 * (n / 2) + 29) * 2
      = 22 * (n - n / 2) + 20 * (n / 2) + 58 := by omega
  have hA : (11 * (n - n / 2) + 10 * (n / 2) + 29) * 2 ^ (n - n / 2)
      ≤ (57 * n + 102) * 2 ^ (n / 2) := by
    have hstep1 : (11 * (n - n / 2) + 10 * (n / 2) + 29) * 2 ^ (n - n / 2)
        ≤ (11 * (n - n / 2) + 10 * (n / 2) + 29) * (2 * 2 ^ (n / 2)) :=
      Nat.mul_le_mul (Nat.le_refl _) hpowm
    have hstep2 : (11 * (n - n / 2) + 10 * (n / 2) + 29) * (2 * 2 ^ (n / 2))
        = (22 * (n - n / 2) + 20 * (n / 2) + 58) * 2 ^ (n / 2) := by
      rw [← Nat.mul_assoc, e2]
    have hstep3 : (22 * (n - n / 2) + 20 * (n / 2) + 58) * 2 ^ (n / 2)
        ≤ (57 * n + 102) * 2 ^ (n / 2) :=
      Nat.mul_le_mul (by omega) (Nat.le_refl _)
    exact Nat.le_trans hstep1 (Nat.le_trans (Nat.le_of_eq hstep2) hstep3)
  -- the linear remainders fold onto 2^(n/2) as well
  have hq1 : 44 * (2 ^ (n / 2) - 1) = 44 * 2 ^ (n / 2) - 44 := by omega
  have hlin : 236 + 6 * (n + 2 - 23) + 12 + 24 * (n / 2) + 6 - 44
      ≤ (18 * n + 210) * 2 ^ (n / 2) := by
    have h1 : 236 + 6 * (n + 2 - 23) + 12 + 24 * (n / 2) + 6 - 44
        ≤ 18 * n + 210 := by omega
    exact Nat.le_trans h1 (Nat.le_mul_of_pos_right _ hQ)
  have h44q : (18 * n + 210) * 2 ^ (n / 2) + 44 * 2 ^ (n / 2)
      = (18 * n + 254) * 2 ^ (n / 2) := by
    rw [show 18 * n + 254 = (18 * n + 210) + 44 from by omega,
      Nat.add_mul (18 * n + 210) 44 (2 ^ (n / 2))]
  have hsplit : (18 * n + 254) * 2 ^ (n / 2) + (57 * n + 102) * 2 ^ (n / 2)
      = (75 * n + 356) * 2 ^ (n / 2) := by
    rw [show 75 * n + 356 = (18 * n + 254) + (57 * n + 102) from by omega,
      Nat.add_mul (18 * n + 254) (57 * n + 102) (2 ^ (n / 2))]
  -- the polynomial comparison: 75n + 356 < 2^20 * (n+2)^8
  have h20 : (2:Nat) ^ 20 = 1048576 := by decide
  have hpow8 : (n + 2) ^ 1 ≤ (n + 2) ^ 8 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hpow8' : (n + 2) ≤ (n + 2) ^ 8 := by
    rwa [Nat.pow_one] at hpow8
  have hmain : 75 * n + 356 ≤ 2 ^ 20 * (n + 2) ^ 8 := by
    have c1 : 75 * n ≤ 2 ^ 20 * n :=
      Nat.mul_le_mul (by rw [h20]; decide) (Nat.le_refl _)
    have c2 : (356:Nat) ≤ 2 ^ 20 * 2 := by rw [h20]; decide
    calc 75 * n + 356 ≤ 2 ^ 20 * n + 2 ^ 20 * 2 := Nat.add_le_add c1 c2
      _ = 2 ^ 20 * (n + 2) := (Nat.mul_add _ _ _).symm
      _ ≤ 2 ^ 20 * (n + 2) ^ 8 := Nat.mul_le_mul (Nat.le_refl _) hpow8'
  have hsb : 2 ^ (n / 2) * 2 ^ 20 * (n + 2) ^ 8 = Runtime.stepBound n := by
    unfold Runtime.stepBound
    rw [show n / 2 + 20 = 20 + n / 2 from by omega, Nat.pow_add,
      Nat.mul_comm (2 ^ (n / 2)) (2 ^ 20)]
  calc (236 + 6 * (n + 2 - 23)) + (12 + 44 * (2 ^ (n / 2) - 1) + 24 * (n / 2))
        + (6 + (11 * (n - n / 2) + 10 * (n / 2) + 29) * 2 ^ (n - n / 2))
      ≤ 236 + 6 * (n + 2 - 23) + 12 + 44 * 2 ^ (n / 2) - 44 + 24 * (n / 2) + 6
          + (57 * n + 102) * 2 ^ (n / 2) := by omega
    _ ≤ (18 * n + 210) * 2 ^ (n / 2) + 44 * 2 ^ (n / 2)
          + (57 * n + 102) * 2 ^ (n / 2) := by omega
    _ = (75 * n + 356) * 2 ^ (n / 2) := by rw [h44q, hsplit]
    _ ≤ (2 ^ 20 * (n + 2) ^ 8) * 2 ^ (n / 2) :=
          Nat.mul_le_mul hmain (Nat.le_refl _)
    _ = 2 ^ (n / 2) * 2 ^ 20 * (n + 2) ^ 8 := by
          rw [Nat.mul_comm (2 ^ 20 * (n + 2) ^ 8) (2 ^ (n / 2)), ← Nat.mul_assoc]
    _ = Runtime.stepBound n := hsb
    _ ≤ Runtime.stepBound n + Runtime.constOverhead := by omega

open scoped Classical in
/-- THE n ≥ 4 driver: within the composed budget the run returns exactly the
membership decision, independent of the tape. -/
theorem bign_run {n : Nat} (x : Instance n) (hn : 4 ≤ n)
    (ρ : Nat → BitVec (wordLength n x.bits)) (T : Nat)
    (hT : (236 + 6 * (n + 2 - 23)) + (12 + 44 * (2 ^ (n / 2) - 1) + 24 * (n / 2))
      + (6 + (11 * (n - n / 2) + 10 * (n / 2) + 29) * 2 ^ (n - n / 2)) ≤ T) :
    run prog x ρ T = some (decide (isSum (instA x) n x.t)) := by
  rw [run_eq_exec]
  have hpow : 2 ^ (2 * n) ≤ 2 ^ (wordLength n x.bits) :=
    Nat.pow_le_pow_right (by omega)
      (by show 2 * n ≤ 4 * (n + x.bits) + Nat.log2 ((n + 2) ^ 4 - 1) + 1; omega)
  have hif : ∀ q, inF x q < 2 ^ (wordLength n x.bits) :=
    inF_fit x _ (by omega) (fun v hv => input_lt_wordLength x (by omega) v hv)
  have hin : ∀ i, i < n → instA x i < 2 ^ (wordLength n x.bits) := by
    intro i hi
    have e := inF_instA x (i + 1) (by omega) (by omega)
    rw [show i + 1 - 1 = i from by omega] at e
    rw [← e]
    exact hif (i + 1)
  obtain ⟨g, c₁, hc₁, hex₁, hgfit, hg1, hg2, hg7, hg8, hgaddr, hgrel, hgtgt⟩ :=
    prologue_exec x ρ hn hpow hif 0 T (by omega)
  obtain ⟨c₂, f', bd, hc₂, hex₂, hf'10, hf'11, hf'18, hbd, harr, hf'1, hf'2,
    hf'7, hf'8, hf'9, hf'fit, hf'pres⟩ :=
    phaseA_exec ρ hn (Nat.le_refl _) g 0 (T - c₁) hgfit hg1 hg2 hg7 hg8 hgaddr
      hgrel hin (by omega)
  -- Phase A preserved every cell at or beyond 2n+23 (AReg n stops at 22
  -- and restarts at 3n+25), so both the block and the t-cell carry through.
  have hrel' : ∀ i, 1 ≤ i → i ≤ n → f' (2 * n + 23 + i) = instA x (i - 1) := by
    intro i hi1 hin'
    have hnA : ¬ AReg n (2 * n + 23 + i) := by
      intro hA
      rcases hA with hA|hA <;> omega
    rw [hf'pres _ hnA]
    exact hgrel i hi1 hin'
  have htgt' : f' (2 * n + 23 + (n + 1)) = x.t := by
    have hnA : ¬ AReg n (2 * n + 23 + (n + 1)) := by
      intro hA
      rcases hA with hA|hA <;> omega
    rw [hf'pres _ hnA]
    exact hgtgt
  obtain ⟨c₃, hc₃, hex₃⟩ :=
    phaseB_exec ρ hn (Nat.le_refl _) bd f' 0 (T - c₁ - c₂) hf'fit hf'1 hf'2
      hf'7 hf'8 hf'9 hf'18 hbd harr hrel' htgt' hgaddr (by omega)
  rw [show T - c₁ - c₂ = T - (c₁ + c₂) from by omega] at hex₂ hex₃
  exact hex₁.trans (hex₂.trans hex₃)

/-- The program halts on every input within T(n) steps. -/
theorem prog_halts : ∀ (n : Nat) (x : Instance n), 2 ≤ n →
    ∀ ρ, (run prog x ρ (Runtime.stepBound n + Runtime.constOverhead)).isSome := by
  intro n x hn ρ
  rcases Nat.lt_or_ge n 4 with hsmall | hbig
  · rcases (show n = 2 ∨ n = 3 by omega) with rfl | rfl
    · exact smalln_halts 2 x (by omega) ρ
    · exact smalln_halts 3 x (by omega) ρ
  · rw [bign_run x hbig ρ _ (budget_compose hbig)]
    simp

/-- The step bound satisfies BigO at α = 3/4. -/
theorem runtime_bound : BigO (fun n => Runtime.stepBound n + Runtime.constOverhead)
    (75 / 100 : Rat) := by
  exact Runtime.runtime_bigO

open scoped Classical in
/-- THE SUMMIT: the program solves subset-sum in O(2^(0.75n)). -/
theorem Race_bound : SolvedInTime (75 / 100 : Rat) := by
  refine ⟨prog, ?_, ?_⟩
  · intro n x hn
    rcases Nat.lt_or_ge n 4 with hsmall | hbig
    · obtain ⟨v, hv, hvyes, hvno⟩ := smalln_verdict n x (by omega)
      exact correct_of_det
        (Runtime.stepBound n + Runtime.constOverhead)
        (smalln_halts n x (by omega)) v hv hvyes hvno
    · refine correct_of_det
        (Runtime.stepBound n + Runtime.constOverhead)
        (prog_halts n x hn)
        (decide (isSum (instA x) n x.t))
        (fun ρ => bign_run x hbig ρ _ (budget_compose hbig)) ?_ ?_
      · intro hyes
        exact decide_eq_true_iff.mpr ((instance_yes_iff x).mp hyes)
      · intro hno
        by_cases hmem : isSum (instA x) n x.t
        · exact absurd ((instance_yes_iff x).mpr hmem) hno
        · have hd : ¬ (decide (isSum (instA x) n x.t) = true) :=
            fun ht => hmem (decide_eq_true_iff.mp ht)
          simp only [Bool.not_eq_true] at hd
          exact hd
  · intro c
    exact ⟨fun n => Runtime.stepBound n + Runtime.constOverhead,
      runtime_bound, fun n x hn _ ρ => prog_halts n x hn ρ⟩

/-- The filed bound is the reduced literal: 75/100 and 3/4 are equal Rats
(the literals are not defeq — Rat.div is not kernel-reducible — so bridge
through div_def/inv_def/mul_def to Int arithmetic). -/
theorem rat75 : (75 / 100 : Rat) = (3 / 4 : Rat) := by
  rw [Rat.div_def, Rat.div_def, Rat.inv_def, Rat.inv_def, Rat.mul_def, Rat.mul_def]
  decide

theorem Race_bound_reduced : SolvedInTime (3 / 4 : Rat) :=
  rat75 ▸ Race_bound

end SubsetSum.MITM
