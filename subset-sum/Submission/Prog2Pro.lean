import Submission.Prog2Scan
set_option autoImplicit true
set_option maxHeartbeats 2000000

/-!
# The prologue walk re-proven over `prog2` (R2125607749 Lanes 2+3)

`prog2`'s pcs 0–85 are PC-IDENTICAL to `prog`'s, EXCEPT the small-n
dispatch at pc 12 (`blt 0 3 ·` targets LSMALL, which resolves to 244 in
prog2 vs 192 in prog).  This module is the scripted re-proof of
Prologue.lean's `ExecWalk` section + Race.lean's `prologue_to65` /
`prologue_exec` inside `namespace SubsetSum.MITM.P2Pro`, with
`prog` → `prog2` and the single dispatch literal `192` → `244`.
`prologue_exec` here is the 0→86 segment of the prog2 chain.
-/

namespace SubsetSum.MITM.P2Pro

open BigOSpeedrun.SubsetSum SubsetSum.MITM.Spec

/-! ## Layer 3: the exec-level relocation walk (pcs 0 → 86)

Segment map of `prog2` (verified against the resolved list):
`0–5` A (cursor 2n, save a₁ a₂, [1]:=1, [2]:=0) · `6–7` saveAk 3 ·
`8–12` small-n guard (falls through on n ≥ 4; LSMALL = 192) ·
`13–50` saveAk 4..22 (scratch 2n+3..2n+21) · `51–61` E ([3]:=23,
cursor := RELOC = 2n+23) · `62–64` F-setup ([4]:=2n, [5]:=0, [3]:=22) ·
`65–71` LOOP1 (do-while, j = 0..21: block[j+1] := scratch[j]) ·
`72–76` LOOP2-setup ([5]:=22, [4]:=n+2) · `77–82` LOOP2 (do-while,
i = 22..n+1: block[i] := cell i; the i = 22 copy is idempotent) ·
`83–85` post ([7]:=n, [8]:=RELOC).  Phase A entry is pc 86.
-/

section ExecWalk

variable {w n : Nat}

/-- Prologue step budget: fixed 233 steps plus 6 per LOOP2 trip above the
first (LOOP2 runs `max 1 (n+2-22)` trips). -/
def Cpro (n : Nat) : Nat := 233 + 6 * (n + 2 - 22)

/-- Every value the prologue writes fits below `2^(2n)` on `n ≥ 4`. -/
theorem pro_lt_pow (m : Nat) (hm : 4 ≤ m) : 3 * m + 46 < 2 ^ (2 * m) := by
  induction m with
  | zero => omega
  | succ k ih =>
    by_cases hk : 4 ≤ k
    · have h4 : (2 : Nat) ^ (2 * (k + 1)) = 4 * 2 ^ (2 * k) := by
        rw [show 2 * (k + 1) = 2 * k + 2 from by omega,
          Nat.pow_add 2 (2 * k) 2, show (2 : Nat) ^ 2 = 4 from rfl]
        omega
      have hpos : 1 ≤ 2 ^ (2 * k) := Nat.one_le_two_pow
      omega
    · rw [show k + 1 = 4 from by omega]
      decide

/-- The phase-A address ceiling fits below `2^(2n)` (loop2's addresses and
Phase A's array region both live under this bound). -/
theorem pro_addr_lt (m : Nat) (hm : 4 ≤ m) :
    3 * m + 26 + 2 * 2 ^ (m / 2) < 2 ^ (2 * m) := by
  have hbase : 3 * 4 + 26 + 2 * 2 ^ (4 / 2) < 2 ^ (2 * 4) := by decide
  induction m with
  | zero => omega
  | succ k ih =>
    by_cases hk : 4 ≤ k
    · have h1 : (k + 1) / 2 ≤ k / 2 + 1 := by omega
      have h2 : 2 ^ ((k + 1) / 2) ≤ 2 ^ (k / 2 + 1) :=
        Nat.pow_le_pow_right (n := 2) (by omega) h1
      have h3 : (2 : Nat) ^ (k / 2 + 1) = 2 * 2 ^ (k / 2) := by
        rw [Nat.pow_add 2 (k / 2) 1, show (2 : Nat) ^ 1 = 2 from rfl]
        omega
      rw [h3] at h2
      have h4 : (2 : Nat) ^ (2 * (k + 1)) = 4 * 2 ^ (2 * k) := by
        rw [show 2 * (k + 1) = 2 * k + 2 from by omega,
          Nat.pow_add 2 (2 * k) 2, show (2 : Nat) ^ 2 = 4 from rfl]
        omega
      have hpos : 1 ≤ 2 ^ (k / 2) := Nat.one_le_two_pow
      omega
    · rw [show k + 1 = 4 from by omega]
      exact hbase

/-- `2^(2n) ≤ 2^w` under the standing word hypothesis. -/
theorem pro_pow2n (x : Instance n) (hn : 4 ≤ n)
    (hw : wordLength n x.bits ≤ w) : 2 ^ (2 * n) ≤ 2 ^ w := by
  have hbl : 1 ≤ x.bits := by
    have := x.pos ⟨0, by omega⟩
    unfold Instance.bits
    omega
  have h255 : (255 : Nat) ≤ (n + 2) ^ 4 - 1 := by
    have h6 : (6 : Nat) ^ 4 ≤ (n + 2) ^ 4 :=
      Nat.pow_le_pow_left (show 6 ≤ n + 2 by omega) 4
    have h64 : (6 : Nat) ^ 4 = 1296 := by decide
    omega
  have hlogb : 7 ≤ Nat.log2 ((n + 2) ^ 4 - 1) := by
    by_cases hcon : 7 ≤ Nat.log2 ((n + 2) ^ 4 - 1)
    · omega
    · have hlt := log2_lt (show 0 < (n + 2) ^ 4 - 1 by omega)
      have hle : Nat.log2 ((n + 2) ^ 4 - 1) + 1 ≤ 7 := by omega
      have hp7 : (2 : Nat) ^ 7 = 128 := by decide
      have hp2 : (2 : Nat) ^ (Nat.log2 ((n + 2) ^ 4 - 1) + 1) ≤ 2 ^ 7 :=
        Nat.pow_le_pow_right (n := 2) (by omega) hle
      omega
  have hwlb : 4 * n + 12 ≤ wordLength n x.bits := by
    unfold wordLength
    omega
  exact Nat.le_trans
    (Nat.pow_le_pow_right (n := 2) (by omega) (show 2 * n ≤ 4 * n + 12 by omega))
    (Nat.le_trans
      (Nat.pow_le_pow_right (n := 2) (by omega) hwlb)
      (Nat.pow_le_pow_right (n := 2) (by omega) hw))

/-- Any prologue value (all bounded by `3n+46`) fits a word. -/
theorem pro_vfit {v : Nat} (hn : 4 ≤ n) (hpow : 2 ^ (2 * n) ≤ 2 ^ w)
    (hv : v ≤ 3 * n + 46) : v < 2 ^ w :=
  Nat.lt_of_lt_of_le (by have := pro_lt_pow n hn; omega) hpow

/-- Fit is preserved by a cell update (Prologue-local name; PhaseA has its
own `up_fit`). -/
theorem upFit {f : Nat → Nat} {c v w : Nat} (hfit : ∀ q, f q < 2 ^ w)
    (hv : v < 2 ^ w) : ∀ q, (up f c v) q < 2 ^ w := by
  intro q
  by_cases h : q = c <;> simp [h, up, hfit, hv]

/-- One `saveAk k` pair (`[0]++; store 0 k`) at a concrete pc, on any
program; the cursor value is supplied by `hcur` and `cur+1` must fit. -/
theorem saveAkPair {P : List Instr} {ρ : Nat → BitVec w} {f : Nat → Nat}
    (hfit : ∀ q, f q < 2 ^ w) (p k cur S r : Nat) (hk : k ≠ 0)
    (hcur : f 0 = cur) (hf1 : f 1 = 1) (hv : cur + 1 < 2 ^ w) (hS : 2 ≤ S)
    (h1 : P.getD p Instr.reject = Instr.add 0 0 1)
    (h2 : P.getD (p + 1) Instr.reject = Instr.store 0 k) :
    exec P ρ S p r (memOf w f) = exec P ρ (S - 2) (p + 2) r
      (memOf w (up (up f 0 (cur + 1)) (cur + 1) (f k))) := by
  rw [exec_add_step (by omega) h1,
    show f 0 + f 1 = cur + 1 from by rw [hcur, hf1],
    exec_store_step (by omega) h2 (upFit hfit hv)]
  have hst : up (up f 0 (cur + 1)) ((up f 0 (cur + 1)) 0)
      ((up f 0 (cur + 1)) k)
      = up (up f 0 (cur + 1)) (cur + 1) (f k) := by
    rw [up_eq, up_ne hk]
  rw [hst]
  simp only [Nat.sub_sub, Nat.reduceAdd]

/-! ### Segment A + saveAk 3 (pcs 0-7) -/

theorem pro_segA (x : Instance n) (ρ : Nat → BitVec w) (hn : 4 ≤ n)
    (hpow : 2 ^ (2 * n) ≤ 2 ^ w) (hif : ∀ q, inF x q < 2 ^ w)
    (r S : Nat) (hS : 8 ≤ S) :
    ∃ g, exec prog2 ρ S 0 r (memOf w (inF x))
      = exec prog2 ρ (S - 8) 8 r (memOf w g) ∧
      (∀ q, g q < 2 ^ w) ∧ g 0 = 2 * n + 2 ∧ g 1 = 1 ∧ g 2 = 0 ∧
      (∀ j, j + 1 ≤ 3 → j + 1 ≤ n + 1 → g (2 * n + j) = inF x (j + 1)) ∧
      (∀ q, 4 ≤ q → q ≤ n + 1 → g q = inF x q) ∧
      (∀ q, 8 ≤ q → q < 2 * n → g q = inF x q) := by
  have e0 : inF x 0 + inF x 0 = 2 * n := by
    rw [inF_zero]
    omega
  have e1 : (up (inF x) (0) (2 * n)) 0 = 2 * n := up_eq _ _ _
  have e2 : (up (inF x) (0) (2 * n)) 1 = inF x 1 := up_ne (by omega)
  have e3 : (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1)) 0 + (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1)) 1 = 2 * n + 1 := by
    rw [up_ne (show 0 ≠ 1 by omega), up_ne (show 0 ≠ 2 * n by omega), up_eq, up_eq]
  have e4 : (up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1)) (0) (2 * n + 1)) 0 = 2 * n + 1 := up_eq _ _ _
  have e5 : (up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1)) (0) (2 * n + 1)) 2 = inF x 2 := by
    rw [up_ne (show 2 ≠ 0 by omega), up_ne (show 2 ≠ 1 by omega), up_ne (show 2 ≠ 2 * n by omega), up_ne (show 2 ≠ 0 by omega)]
  have e6 : (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) 2 - (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) 2 = 0 := by
    rw [up_ne (show 2 ≠ 2 * n + 1 by omega), up_ne (show 2 ≠ 0 by omega), up_ne (show 2 ≠ 1 by omega), up_ne (show 2 ≠ 2 * n by omega), up_ne (show 2 ≠ 0 by omega)]
    omega
  have e7 : (up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0)) 0 + (up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0)) 1 = 2 * n + 2 := by
    rw [up_ne (show 0 ≠ 2 by omega), up_ne (show 0 ≠ 2 * n + 1 by omega), up_eq, up_ne (show 1 ≠ 2 by omega), up_ne (show 1 ≠ 2 * n + 1 by omega), up_ne (show 1 ≠ 0 by omega), up_eq]
  have e8 : (up (up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0)) (0) (2 * n + 2)) 0 = 2 * n + 2 := up_eq _ _ _
  have e9 : (up (up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0)) (0) (2 * n + 2)) 3 = inF x 3 := by
    rw [up_ne (show 3 ≠ 0 by omega), up_ne (show 3 ≠ 2 by omega), up_ne (show 3 ≠ 2 * n + 1 by omega), up_ne (show 3 ≠ 0 by omega), up_ne (show 3 ≠ 1 by omega), up_ne (show 3 ≠ 2 * n by omega), up_ne (show 3 ≠ 0 by omega)]
  have hfit1 : ∀ q, up (inF x) (0) (2 * n) q < 2 ^ w := upFit hif (pro_vfit hn hpow (by omega))
  have hfit2 : ∀ q, up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1) q < 2 ^ w := upFit hfit1 (hif 1)
  have hfit3 : ∀ q, up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1) q < 2 ^ w := upFit hfit2 (pro_vfit hn hpow (by omega))
  have hfit4 : ∀ q, up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1)) (0) (2 * n + 1) q < 2 ^ w := upFit hfit3 (pro_vfit hn hpow (by omega))
  have hfit5 : ∀ q, up (up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2) q < 2 ^ w := upFit hfit4 (hif 2)
  have hfit6 : ∀ q, up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0) q < 2 ^ w := upFit hfit5 (pro_vfit hn hpow (by omega))
  have hfit7 : ∀ q, up (up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0)) (0) (2 * n + 2) q < 2 ^ w := upFit hfit6 (pro_vfit hn hpow (by omega))
  have hfit8 : ∀ q, up (up (up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0)) (0) (2 * n + 2)) (2 * n + 2) (inF x 3) q < 2 ^ w := upFit hfit7 (hif 3)
  have hf0 : (up (up (up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0)) (0) (2 * n + 2)) (2 * n + 2) (inF x 3)) (0) = 2 * n + 2 := by
    rw [up_ne (show 0 ≠ 2 * n + 2 by omega), up_eq]
  have hf1 : (up (up (up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0)) (0) (2 * n + 2)) (2 * n + 2) (inF x 3)) (1) = 1 := by
    rw [up_ne (show 1 ≠ 2 * n + 2 by omega), up_ne (show 1 ≠ 0 by omega), up_ne (show 1 ≠ 2 by omega), up_ne (show 1 ≠ 2 * n + 1 by omega), up_ne (show 1 ≠ 0 by omega), up_eq]
  have hf2 : (up (up (up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0)) (0) (2 * n + 2)) (2 * n + 2) (inF x 3)) (2) = 0 := by
    rw [up_ne (show 2 ≠ 2 * n + 2 by omega), up_ne (show 2 ≠ 0 by omega), up_eq]
  have hscr : ∀ j, j + 1 ≤ 3 → j + 1 ≤ n + 1 → (up (up (up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0)) (0) (2 * n + 2)) (2 * n + 2) (inF x 3)) (2 * n + j) = inF x (j + 1) := by
    intro j hj1 hj2
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
    · rw [show (2 * n + 0) = 2 * n from Nat.add_zero (2 * n)]
      rw [up_ne (show 2 * n ≠ 2 * n + 2 by omega), up_ne (show 2 * n ≠ 0 by omega), up_ne (show 2 * n ≠ 2 by omega), up_ne (show 2 * n ≠ 2 * n + 1 by omega), up_ne (show 2 * n ≠ 0 by omega), up_ne (show 2 * n ≠ 1 by omega), up_eq]
    · rw [up_ne (show 2 * n + 1 ≠ 2 * n + 2 by omega), up_ne (show 2 * n + 1 ≠ 0 by omega), up_ne (show 2 * n + 1 ≠ 2 by omega), up_eq]
    · rw [up_eq]
  have hp4 : ∀ q, 4 ≤ q → q ≤ n + 1 → (up (up (up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0)) (0) (2 * n + 2)) (2 * n + 2) (inF x 3)) q = inF x q := by
    intro q hq1 hq2
    rw [up_ne (show q ≠ 2 * n + 2 by omega), up_ne (show q ≠ 0 by omega), up_ne (show q ≠ 2 by omega), up_ne (show q ≠ 2 * n + 1 by omega), up_ne (show q ≠ 0 by omega), up_ne (show q ≠ 1 by omega), up_ne (show q ≠ 2 * n by omega), up_ne (show q ≠ 0 by omega)]
  refine ⟨up (up (up (up (up (up (up (up (inF x) (0) (2 * n)) (2 * n) (inF x 1)) (1) (1)) (0) (2 * n + 1)) (2 * n + 1) (inF x 2)) (2) (0)) (0) (2 * n + 2)) (2 * n + 2) (inF x 3), ?_, hfit8, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [exec_add_step (by omega) (show prog2.getD 0 Instr.reject = Instr.add 0 0 0 by rfl), e0, exec_store_step (by omega) (show prog2.getD 1 Instr.reject = Instr.store 0 1 by rfl) hfit1, e1, e2, exec_one_step (by omega) (show prog2.getD 2 Instr.reject = Instr.one 1 by rfl), exec_add_step (by omega) (show prog2.getD 3 Instr.reject = Instr.add 0 0 1 by rfl), e3, exec_store_step (by omega) (show prog2.getD 4 Instr.reject = Instr.store 0 2 by rfl) hfit4, e4, e5, exec_sub_step (by omega) (show prog2.getD 5 Instr.reject = Instr.sub 2 2 2 by rfl) hfit5 (Nat.le_refl _), e6, exec_add_step (by omega) (show prog2.getD 6 Instr.reject = Instr.add 0 0 1 by rfl), e7, exec_store_step (by omega) (show prog2.getD 7 Instr.reject = Instr.store 0 3 by rfl) hfit7, e8, e9]
    simp only [Nat.sub_sub, Nat.reduceAdd]
  · exact hf0
  · exact hf1
  · exact hf2
  · exact hscr
  · exact hp4
  · intro q hq1 hq2
    rw [up_ne (by omega), up_ne (by omega), up_ne (by omega), up_ne (by omega),
      up_ne (by omega), up_ne (by omega), up_ne (by omega), up_ne (by omega)]


/-! ### Segment C: small-n guard (pcs 8–12) -/
theorem pro_segC (x : Instance n) (ρ : Nat → BitVec w) (hn : 4 ≤ n)
    (hpow : 2 ^ (2 * n) ≤ 2 ^ w)
    (f : Nat → Nat) (r S : Nat) (hS : 5 ≤ S)
    (hfit0 : ∀ q, f q < 2 ^ w) (hf0 : f 0 = 2 * n + 2) (hf1 : f 1 = 1)
    (hf2 : f 2 = 0)
    (hscr : ∀ j, j + 1 ≤ 3 → j + 1 ≤ n + 1 → f (2 * n + j) = inF x (j + 1))
    (hp4 : ∀ q, 4 ≤ q → q ≤ n + 1 → f q = inF x q) :
    ∃ g, exec prog2 ρ S 8 r (memOf w f) = exec prog2 ρ (S - 5) 13 r (memOf w g) ∧
      (∀ q, g q < 2 ^ w) ∧ g 0 = 2 * n + 2 ∧ g 1 = 1 ∧ g 2 = 0 ∧ g 3 = 9 ∧
      (∀ j, j + 1 ≤ 3 → j + 1 ≤ n + 1 → g (2 * n + j) = inF x (j + 1)) ∧
      (∀ q, 4 ≤ q → q ≤ n + 1 → g q = inF x q) ∧
      (∀ q, 8 ≤ q → q < 2 * n → g q = f q) := by

  have e1 : (f) 1 + (f) 1 = 2 := by
    rw [hf1]
  have e2 : (up (f) (3) (2)) 3 + (up (f) (3) (2)) 3 = 4 := by
    rw [up_eq]
  have e3 : (up (up (f) (3) (2)) (3) (4)) 3 + (up (up (f) (3) (2)) (3) (4)) 3 = 8 := by
    rw [up_eq]
  have e4 : (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) 3 + (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) 1 = 9 := by
    rw [up_eq, up_ne (show 1 ≠ 3 by omega), up_ne (show 1 ≠ 3 by omega), up_ne (show 1 ≠ 3 by omega), hf1]
  have hge : ¬ (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (9)) 0 < (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (9)) 3 := by
    rw [up_ne (show 0 ≠ 3 by omega), up_ne (show 0 ≠ 3 by omega), up_ne (show 0 ≠ 3 by omega), up_ne (show 0 ≠ 3 by omega), hf0, up_eq]
    omega
  have hfitC1 : ∀ q, up (f) (3) (2) q < 2 ^ w := upFit hfit0 (pro_vfit hn hpow (by omega))
  have hfitC2 : ∀ q, up (up (f) (3) (2)) (3) (4) q < 2 ^ w := upFit hfitC1 (pro_vfit hn hpow (by omega))
  have hfitC3 : ∀ q, up (up (up (f) (3) (2)) (3) (4)) (3) (8) q < 2 ^ w := upFit hfitC2 (pro_vfit hn hpow (by omega))
  have hfitC4 : ∀ q, up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (9) q < 2 ^ w := upFit hfitC3 (pro_vfit hn hpow (by omega))
  have gf0 : (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (9)) (0) = 2 * n + 2 := by
    rw [up_ne (show 0 ≠ 3 by omega), up_ne (show 0 ≠ 3 by omega), up_ne (show 0 ≠ 3 by omega), up_ne (show 0 ≠ 3 by omega), hf0]
  have gf1 : (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (9)) (1) = 1 := by
    rw [up_ne (show 1 ≠ 3 by omega), up_ne (show 1 ≠ 3 by omega), up_ne (show 1 ≠ 3 by omega), up_ne (show 1 ≠ 3 by omega), hf1]
  have gf2 : (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (9)) (2) = 0 := by
    rw [up_ne (show 2 ≠ 3 by omega), up_ne (show 2 ≠ 3 by omega), up_ne (show 2 ≠ 3 by omega), up_ne (show 2 ≠ 3 by omega), hf2]
  have gf3 : (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (9)) (3) = 9 := by
    rw [up_eq]
  have gscr : ∀ j, j + 1 ≤ 3 → j + 1 ≤ n + 1 → (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (9)) (2 * n + j) = inF x (j + 1) := by
    intro j hj1 hj2
    rw [up_ne (show 2 * n + j ≠ 3 by omega), up_ne (show 2 * n + j ≠ 3 by omega), up_ne (show 2 * n + j ≠ 3 by omega), up_ne (show 2 * n + j ≠ 3 by omega)]
    exact hscr j hj1 hj2
  have gp4 : ∀ q, 4 ≤ q → q ≤ n + 1 → (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (9)) q = inF x q := by
    intro q hq1 hq2
    rw [up_ne (show q ≠ 3 by omega), up_ne (show q ≠ 3 by omega), up_ne (show q ≠ 3 by omega), up_ne (show q ≠ 3 by omega)]
    exact hp4 q hq1 hq2
  refine ⟨up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (9), ?_, hfitC4, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [exec_add_step (by omega) (show prog2.getD 8 Instr.reject = Instr.add 3 1 1 by rfl), e1, exec_add_step (by omega) (show prog2.getD 9 Instr.reject = Instr.add 3 3 3 by rfl), e2, exec_add_step (by omega) (show prog2.getD 10 Instr.reject = Instr.add 3 3 3 by rfl), e3, exec_add_step (by omega) (show prog2.getD 11 Instr.reject = Instr.add 3 3 1 by rfl), e4, exec_blt_ge_step (by omega) (show prog2.getD 12 Instr.reject = Instr.blt 0 3 244 by rfl) hfitC4 hge]
    simp only [Nat.sub_sub, Nat.reduceAdd]
  · exact gf0
  · exact gf1
  · exact gf2
  · exact gf3
  · exact gscr
  · exact gp4
  · intro q hq1 hq2
    rw [up_ne (by omega), up_ne (by omega),
      up_ne (by omega), up_ne (by omega)]


/-! ### Segment E: rebuild [3]=23, cursor := RELOC (pcs 51–61) -/
theorem pro_segE (x : Instance n) (ρ : Nat → BitVec w) (hn : 4 ≤ n)
    (hpow : 2 ^ (2 * n) ≤ 2 ^ w)
    (f : Nat → Nat) (r S : Nat) (hS : 11 ≤ S)
    (hfit0 : ∀ q, f q < 2 ^ w) (hf0 : f 0 = 2 * n + 21) (hf1 : f 1 = 1)
    (hf2 : f 2 = 0)
    (hscr : ∀ j, j + 1 ≤ 22 → j + 1 ≤ n + 1 → f (2 * n + j) = inF x (j + 1))
    (hp4 : ∀ q, 4 ≤ q → q ≤ n + 1 → f q = inF x q) :
    ∃ g, exec prog2 ρ S 51 r (memOf w f) = exec prog2 ρ (S - 11) 62 r (memOf w g) ∧
      (∀ q, g q < 2 ^ w) ∧ g 0 = 2 * n + 23 ∧ g 1 = 1 ∧ g 2 = 0 ∧
      g 3 = 23 ∧ g 4 = 7 ∧
      (∀ j, j + 1 ≤ 22 → j + 1 ≤ n + 1 → g (2 * n + j) = inF x (j + 1)) ∧
      (∀ q, 23 ≤ q → q ≤ n + 1 → g q = inF x q) ∧
      (∀ q, 8 ≤ q → q < 2 * n → g q = f q) := by

  have e1 : (f) 1 + (f) 1 = 2 := by
    rw [hf1]
  have e2 : (up (f) (3) (2)) 3 + (up (f) (3) (2)) 3 = 4 := by
    rw [up_eq]
  have e3 : (up (up (f) (3) (2)) (3) (4)) 3 + (up (up (f) (3) (2)) (3) (4)) 3 = 8 := by
    rw [up_eq]
  have e4 : (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) 3 + (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) 3 = 16 := by
    rw [up_eq]
  have e5 : (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (16)) 1 + (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (16)) 1 = 2 := by
    rw [up_ne (show 1 ≠ 3 by omega), up_ne (show 1 ≠ 3 by omega), up_ne (show 1 ≠ 3 by omega), up_ne (show 1 ≠ 3 by omega), hf1]
  have e6 : (up (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (16)) (4) (2)) 4 + (up (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (16)) (4) (2)) 4 = 4 := by
    rw [up_eq]
  have e7 : (up (up (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (16)) (4) (2)) (4) (4)) 4 + (up (up (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (16)) (4) (2)) (4) (4)) 4 = 8 := by
    rw [up_eq]
  have e8 : (up (up (up (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (16)) (4) (2)) (4) (4)) (4) (8)) 4 - (up (up (up (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (16)) (4) (2)) (4) (4)) (4) (8)) 1 = 7 := by
    rw [up_eq, up_ne (show 1 ≠ 4 by omega), up_ne (show 1 ≠ 4 by omega), up_ne (show 1 ≠ 4 by omega), up_ne (show 1 ≠ 3 by omega), up_ne (show 1 ≠ 3 by omega), up_ne (show 1 ≠ 3 by omega), up_ne (show 1 ≠ 3 by omega), hf1]
  have hle8 : (up (up (up (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (16)) (4) (2)) (4) (4)) (4) (8)) 1 ≤ (up (up (up (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (16)) (4) (2)) (4) (4)) (4) (8)) 4 := by
    rw [up_ne (show 1 ≠ 4 by omega), up_ne (show 1 ≠ 4 by omega), up_ne (show 1 ≠ 4 by omega), up_ne (show 1 ≠ 3 by omega), up_ne (show 1 ≠ 3 by omega), up_ne (show 1 ≠ 3 by omega), up_ne (show 1 ≠ 3 by omega), up_eq, hf1]
    omega
  have e9 : (up (up (up (up (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (16)) (4) (2)) (4) (4)) (4) (8)) (4) (7)) 3 + (up (up (up (up (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (16)) (4) (2)) (4) (4)) (4) (8)) (4) (7)) 4 = 23 := by
    rw [up_ne (show 3 ≠ 4 by omega), up_ne (show 3 ≠ 4 by omega), up_ne (show 3 ≠ 4 by omega), up_ne (show 3 ≠ 4 by omega), up_eq, up_eq]
  have e10 : (up (up (up (up (up (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (16)) (4) (2)) (4) (4)) (4) (8)) (4) (7)) (3) (23)) 0 + (up (up (up (up (up (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (16)) (4) (2)) (4) (4)) (4) (8)) (4) (7)) (3) (23)) 1 = 2 * n + 22 := by
    rw [up_ne (show 0 ≠ 3 by omega), up_ne (show 0 ≠ 4 by omega), up_ne (show 0 ≠ 4 by omega), up_ne (show 0 ≠ 4 by omega), up_ne (show 0 ≠ 4 by omega), up_ne (show 0 ≠ 3 by omega), up_ne (show 0 ≠ 3 by omega), up_ne (show 0 ≠ 3 by omega), up_ne (show 0 ≠ 3 by omega), up_ne (show 1 ≠ 3 by omega), up_ne (show 1 ≠ 4 by omega), up_ne (show 1 ≠ 4 by omega), up_ne (show 1 ≠ 4 by omega), up_ne (show 1 ≠ 4 by omega), up_ne (show 1 ≠ 3 by omega), up_ne (show 1 ≠ 3 by omega), up_ne (show 1 ≠ 3 by omega), up_ne (show 1 ≠ 3 by omega), hf0, hf1]
  have e11 : (up (up (up (up (up (up (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (16)) (4) (2)) (4) (4)) (4) (8)) (4) (7)) (3) (23)) (0) (2 * n + 22)) 0 + (up (up (up (up (up (up (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (16)) (4) (2)) (4) (4)) (4) (8)) (4) (7)) (3) (23)) (0) (2 * n + 22)) 1 = 2 * n + 23 := by
    rw [up_eq, up_ne (show 1 ≠ 0 by omega), up_ne (show 1 ≠ 3 by omega), up_ne (show 1 ≠ 4 by omega), up_ne (show 1 ≠ 4 by omega), up_ne (show 1 ≠ 4 by omega), up_ne (show 1 ≠ 4 by omega), up_ne (show 1 ≠ 3 by omega), up_ne (show 1 ≠ 3 by omega), up_ne (show 1 ≠ 3 by omega), up_ne (show 1 ≠ 3 by omega), hf1]
  have hfitE1 : ∀ q, up (f) (3) (2) q < 2 ^ w := upFit hfit0 (pro_vfit hn hpow (by omega))
  have hfitE2 : ∀ q, up (up (f) (3) (2)) (3) (4) q < 2 ^ w := upFit hfitE1 (pro_vfit hn hpow (by omega))
  have hfitE3 : ∀ q, up (up (up (f) (3) (2)) (3) (4)) (3) (8) q < 2 ^ w := upFit hfitE2 (pro_vfit hn hpow (by omega))
  have hfitE4 : ∀ q, up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (16) q < 2 ^ w := upFit hfitE3 (pro_vfit hn hpow (by omega))
  have hfitE5 : ∀ q, up (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (16)) (4) (2) q < 2 ^ w := upFit hfitE4 (pro_vfit hn hpow (by omega))
  have hfitE6 : ∀ q, up (up (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (16)) (4) (2)) (4) (4) q < 2 ^ w := upFit hfitE5 (pro_vfit hn hpow (by omega))
  have hfitE7 : ∀ q, up (up (up (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (16)) (4) (2)) (4) (4)) (4) (8) q < 2 ^ w := upFit hfitE6 (pro_vfit hn hpow (by omega))
  have hfitE8 : ∀ q, up (up (up (up (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (16)) (4) (2)) (4) (4)) (4) (8)) (4) (7) q < 2 ^ w := upFit hfitE7 (pro_vfit hn hpow (by omega))
  have hfitE9 : ∀ q, up (up (up (up (up (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (16)) (4) (2)) (4) (4)) (4) (8)) (4) (7)) (3) (23) q < 2 ^ w := upFit hfitE8 (pro_vfit hn hpow (by omega))
  have hfitE10 : ∀ q, up (up (up (up (up (up (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (16)) (4) (2)) (4) (4)) (4) (8)) (4) (7)) (3) (23)) (0) (2 * n + 22) q < 2 ^ w := upFit hfitE9 (pro_vfit hn hpow (by omega))
  have hfitE11 : ∀ q, up (up (up (up (up (up (up (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (16)) (4) (2)) (4) (4)) (4) (8)) (4) (7)) (3) (23)) (0) (2 * n + 22)) (0) (2 * n + 23) q < 2 ^ w := upFit hfitE10 (pro_vfit hn hpow (by omega))
  have gf0 : (up (up (up (up (up (up (up (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (16)) (4) (2)) (4) (4)) (4) (8)) (4) (7)) (3) (23)) (0) (2 * n + 22)) (0) (2 * n + 23)) (0) = 2 * n + 23 := by
    rw [up_eq]
  have gf1 : (up (up (up (up (up (up (up (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (16)) (4) (2)) (4) (4)) (4) (8)) (4) (7)) (3) (23)) (0) (2 * n + 22)) (0) (2 * n + 23)) (1) = 1 := by
    rw [up_ne (show 1 ≠ 0 by omega), up_ne (show 1 ≠ 0 by omega), up_ne (show 1 ≠ 3 by omega), up_ne (show 1 ≠ 4 by omega), up_ne (show 1 ≠ 4 by omega), up_ne (show 1 ≠ 4 by omega), up_ne (show 1 ≠ 4 by omega), up_ne (show 1 ≠ 3 by omega), up_ne (show 1 ≠ 3 by omega), up_ne (show 1 ≠ 3 by omega), up_ne (show 1 ≠ 3 by omega), hf1]
  have gf2 : (up (up (up (up (up (up (up (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (16)) (4) (2)) (4) (4)) (4) (8)) (4) (7)) (3) (23)) (0) (2 * n + 22)) (0) (2 * n + 23)) (2) = 0 := by
    rw [up_ne (show 2 ≠ 0 by omega), up_ne (show 2 ≠ 0 by omega), up_ne (show 2 ≠ 3 by omega), up_ne (show 2 ≠ 4 by omega), up_ne (show 2 ≠ 4 by omega), up_ne (show 2 ≠ 4 by omega), up_ne (show 2 ≠ 4 by omega), up_ne (show 2 ≠ 3 by omega), up_ne (show 2 ≠ 3 by omega), up_ne (show 2 ≠ 3 by omega), up_ne (show 2 ≠ 3 by omega), hf2]
  have gf3 : (up (up (up (up (up (up (up (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (16)) (4) (2)) (4) (4)) (4) (8)) (4) (7)) (3) (23)) (0) (2 * n + 22)) (0) (2 * n + 23)) (3) = 23 := by
    rw [up_ne (show 3 ≠ 0 by omega), up_ne (show 3 ≠ 0 by omega), up_eq]
  have gf4 : (up (up (up (up (up (up (up (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (16)) (4) (2)) (4) (4)) (4) (8)) (4) (7)) (3) (23)) (0) (2 * n + 22)) (0) (2 * n + 23)) (4) = 7 := by
    rw [up_ne (show 4 ≠ 0 by omega), up_ne (show 4 ≠ 0 by omega), up_ne (show 4 ≠ 3 by omega), up_eq]
  have gscr : ∀ j, j + 1 ≤ 22 → j + 1 ≤ n + 1 → (up (up (up (up (up (up (up (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (16)) (4) (2)) (4) (4)) (4) (8)) (4) (7)) (3) (23)) (0) (2 * n + 22)) (0) (2 * n + 23)) (2 * n + j) = inF x (j + 1) := by
    intro j hj1 hj2
    rw [up_ne (show 2 * n + j ≠ 0 by omega), up_ne (show 2 * n + j ≠ 0 by omega), up_ne (show 2 * n + j ≠ 3 by omega), up_ne (show 2 * n + j ≠ 4 by omega), up_ne (show 2 * n + j ≠ 4 by omega), up_ne (show 2 * n + j ≠ 4 by omega), up_ne (show 2 * n + j ≠ 4 by omega), up_ne (show 2 * n + j ≠ 3 by omega), up_ne (show 2 * n + j ≠ 3 by omega), up_ne (show 2 * n + j ≠ 3 by omega), up_ne (show 2 * n + j ≠ 3 by omega)]
    exact hscr j hj1 hj2
  have gp23 : ∀ q, 23 ≤ q → q ≤ n + 1 → (up (up (up (up (up (up (up (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (16)) (4) (2)) (4) (4)) (4) (8)) (4) (7)) (3) (23)) (0) (2 * n + 22)) (0) (2 * n + 23)) q = inF x q := by
    intro q hq1 hq2
    rw [up_ne (show q ≠ 0 by omega), up_ne (show q ≠ 0 by omega), up_ne (show q ≠ 3 by omega), up_ne (show q ≠ 4 by omega), up_ne (show q ≠ 4 by omega), up_ne (show q ≠ 4 by omega), up_ne (show q ≠ 4 by omega), up_ne (show q ≠ 3 by omega), up_ne (show q ≠ 3 by omega), up_ne (show q ≠ 3 by omega), up_ne (show q ≠ 3 by omega)]
    exact hp4 q (by omega) hq2
  refine ⟨up (up (up (up (up (up (up (up (up (up (up (f) (3) (2)) (3) (4)) (3) (8)) (3) (16)) (4) (2)) (4) (4)) (4) (8)) (4) (7)) (3) (23)) (0) (2 * n + 22)) (0) (2 * n + 23), ?_, hfitE11, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [exec_add_step (by omega) (show prog2.getD 51 Instr.reject = Instr.add 3 1 1 by rfl), e1, exec_add_step (by omega) (show prog2.getD 52 Instr.reject = Instr.add 3 3 3 by rfl), e2, exec_add_step (by omega) (show prog2.getD 53 Instr.reject = Instr.add 3 3 3 by rfl), e3, exec_add_step (by omega) (show prog2.getD 54 Instr.reject = Instr.add 3 3 3 by rfl), e4, exec_add_step (by omega) (show prog2.getD 55 Instr.reject = Instr.add 4 1 1 by rfl), e5, exec_add_step (by omega) (show prog2.getD 56 Instr.reject = Instr.add 4 4 4 by rfl), e6, exec_add_step (by omega) (show prog2.getD 57 Instr.reject = Instr.add 4 4 4 by rfl), e7, exec_sub_step (by omega) (show prog2.getD 58 Instr.reject = Instr.sub 4 4 1 by rfl) hfitE7 hle8, e8, exec_add_step (by omega) (show prog2.getD 59 Instr.reject = Instr.add 3 3 4 by rfl), e9, exec_add_step (by omega) (show prog2.getD 60 Instr.reject = Instr.add 0 0 1 by rfl), e10, exec_add_step (by omega) (show prog2.getD 61 Instr.reject = Instr.add 0 0 1 by rfl), e11]
    simp only [Nat.sub_sub, Nat.reduceAdd]
  · exact gf0
  · exact gf1
  · exact gf2
  · exact gf3
  · exact gf4
  · exact gscr
  · exact gp23
  · intro q hq1 hq2
    rw [up_ne (by omega), up_ne (by omega), up_ne (by omega),
      up_ne (by omega), up_ne (by omega), up_ne (by omega),
      up_ne (by omega), up_ne (by omega), up_ne (by omega),
      up_ne (by omega), up_ne (by omega)]


/-! ### Segment F setup: LOOP1 registers (pcs 62–64) -/
theorem pro_segF (x : Instance n) (ρ : Nat → BitVec w) (hn : 4 ≤ n)
    (hpow : 2 ^ (2 * n) ≤ 2 ^ w)
    (f : Nat → Nat) (r S : Nat) (hS : 3 ≤ S)
    (hfit0 : ∀ q, f q < 2 ^ w) (hf0 : f 0 = 2 * n + 23) (hf1 : f 1 = 1)
    (hf2 : f 2 = 0) (hf3 : f 3 = 23)
    (hscr : ∀ j, j + 1 ≤ 22 → j + 1 ≤ n + 1 → f (2 * n + j) = inF x (j + 1))
    (hp23 : ∀ q, 23 ≤ q → q ≤ n + 1 → f q = inF x q) :
    ∃ g, exec prog2 ρ S 62 r (memOf w f) = exec prog2 ρ (S - 3) 65 r (memOf w g) ∧
      (∀ q, g q < 2 ^ w) ∧ g 0 = 2 * n + 23 ∧ g 1 = 1 ∧ g 2 = 0 ∧
      g 3 = 22 ∧ g 4 = 2 * n ∧ g 5 = 0 ∧
      (∀ j, j + 1 ≤ 22 → j + 1 ≤ n + 1 → g (2 * n + j) = inF x (j + 1)) ∧
      (∀ q, 23 ≤ q → q ≤ n + 1 → g q = inF x q) ∧
      (∀ q, 8 ≤ q → q < 2 * n → g q = f q) := by

  have e1 : (f) 0 - (f) 3 = 2 * n := by
    rw [hf0, hf3]
    omega
  have hle1 : (f) 3 ≤ (f) 0 := by
    rw [hf0, hf3]
    omega
  have e2 : (up (f) (4) (2 * n)) 5 - (up (f) (4) (2 * n)) 5 = 0 := by
    rw [up_ne (show 5 ≠ 4 by omega), Nat.sub_self]
  have hle2 : (up (f) (4) (2 * n)) 5 ≤ (up (f) (4) (2 * n)) 5 := by
    rw [up_ne (show 5 ≠ 4 by omega)]
    omega
  have e3 : (up (up (f) (4) (2 * n)) (5) (0)) 3 - (up (up (f) (4) (2 * n)) (5) (0)) 1 = 22 := by
    rw [up_ne (show 3 ≠ 5 by omega), up_ne (show 3 ≠ 4 by omega), up_ne (show 1 ≠ 5 by omega), up_ne (show 1 ≠ 4 by omega), hf3, hf1]
  have hle3 : (up (up (f) (4) (2 * n)) (5) (0)) 1 ≤ (up (up (f) (4) (2 * n)) (5) (0)) 3 := by
    rw [up_ne (show 1 ≠ 5 by omega), up_ne (show 1 ≠ 4 by omega), up_ne (show 3 ≠ 5 by omega), up_ne (show 3 ≠ 4 by omega), hf1, hf3]
    omega
  have hfitF1 : ∀ q, up (f) (4) (2 * n) q < 2 ^ w := upFit hfit0 (pro_vfit hn hpow (by omega))
  have hfitF2 : ∀ q, up (up (f) (4) (2 * n)) (5) (0) q < 2 ^ w := upFit hfitF1 (pro_vfit hn hpow (by omega))
  have hfitF3 : ∀ q, up (up (up (f) (4) (2 * n)) (5) (0)) (3) (22) q < 2 ^ w := upFit hfitF2 (pro_vfit hn hpow (by omega))
  have gf0 : (up (up (up (f) (4) (2 * n)) (5) (0)) (3) (22)) (0) = 2 * n + 23 := by
    rw [up_ne (show 0 ≠ 3 by omega), up_ne (show 0 ≠ 5 by omega), up_ne (show 0 ≠ 4 by omega), hf0]
  have gf1 : (up (up (up (f) (4) (2 * n)) (5) (0)) (3) (22)) (1) = 1 := by
    rw [up_ne (show 1 ≠ 3 by omega), up_ne (show 1 ≠ 5 by omega), up_ne (show 1 ≠ 4 by omega), hf1]
  have gf2 : (up (up (up (f) (4) (2 * n)) (5) (0)) (3) (22)) (2) = 0 := by
    rw [up_ne (show 2 ≠ 3 by omega), up_ne (show 2 ≠ 5 by omega), up_ne (show 2 ≠ 4 by omega), hf2]
  have gf3 : (up (up (up (f) (4) (2 * n)) (5) (0)) (3) (22)) (3) = 22 := by
    rw [up_eq]
  have gf4 : (up (up (up (f) (4) (2 * n)) (5) (0)) (3) (22)) (4) = 2 * n := by
    rw [up_ne (show 4 ≠ 3 by omega), up_ne (show 4 ≠ 5 by omega), up_eq]
  have gf5 : (up (up (up (f) (4) (2 * n)) (5) (0)) (3) (22)) (5) = 0 := by
    rw [up_ne (show 5 ≠ 3 by omega), up_eq]
  have gscr : ∀ j, j + 1 ≤ 22 → j + 1 ≤ n + 1 → (up (up (up (f) (4) (2 * n)) (5) (0)) (3) (22)) (2 * n + j) = inF x (j + 1) := by
    intro j hj1 hj2
    rw [up_ne (show 2 * n + j ≠ 3 by omega), up_ne (show 2 * n + j ≠ 5 by omega), up_ne (show 2 * n + j ≠ 4 by omega)]
    exact hscr j hj1 hj2
  have gp23 : ∀ q, 23 ≤ q → q ≤ n + 1 → (up (up (up (f) (4) (2 * n)) (5) (0)) (3) (22)) q = inF x q := by
    intro q hq1 hq2
    rw [up_ne (show q ≠ 3 by omega), up_ne (show q ≠ 5 by omega), up_ne (show q ≠ 4 by omega)]
    exact hp23 q hq1 hq2
  refine ⟨up (up (up (f) (4) (2 * n)) (5) (0)) (3) (22), ?_, hfitF3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [exec_sub_step (by omega) (show prog2.getD 62 Instr.reject = Instr.sub 4 0 3 by rfl) hfit0 hle1, e1, exec_sub_step (by omega) (show prog2.getD 63 Instr.reject = Instr.sub 5 5 5 by rfl) hfitF1 hle2, e2, exec_sub_step (by omega) (show prog2.getD 64 Instr.reject = Instr.sub 3 3 1 by rfl) hfitF2 hle3, e3]
    simp only [Nat.sub_sub, Nat.reduceAdd]
  · exact gf0
  · exact gf1
  · exact gf2
  · exact gf3
  · exact gf4
  · exact gf5
  · exact gscr
  · exact gp23
  · intro q hq1 hq2
    rw [up_ne (by omega), up_ne (by omega), up_ne (by omega)]


/-! ### The saveAk chain: a₄..a₂₂ to scratch (pcs 13-50) -/


/-! ### saveAks rounds, abstracted (R2125607414 build-unblock) -/

/-- One relocation pair of the sweep (for `m = 2..20`, pcs `2m+9`/`2m+10`):
bump the cursor in cell 0, then store cell `m+2` to `mem[2n+m+1]`.  Stated
over an abstract state so the write chain never appears nested: each round's
witness is two `up`s with flat values, and the caller chains rounds through
`obtain` and `.trans`, keeping every term linear. -/
theorem saveAks_pair (x : Instance n) (ρ : Nat → BitVec w) (hn : 4 ≤ n)
    (hpow : 2 ^ (2 * n) ≤ 2 ^ w) (hif : ∀ q, inF x q < 2 ^ w)
    (f : Nat → Nat) (r S m : Nat) (hS : 2 ≤ S) (hm : 2 ≤ m) (hm' : m ≤ 20)
    (hadd : prog2.getD (2 * m + 9) Instr.reject = Instr.add 0 0 1)
    (hst : prog2.getD (2 * m + 10) Instr.reject = Instr.store 0 (m + 2))
    (hfit : ∀ q, f q < 2 ^ w)
    (hf0 : f 0 = 2 * n + m) (hf1 : f 1 = 1) (hf2 : f 2 = 0)
    (hscr : ∀ j, j + 1 ≤ m + 1 → j + 1 ≤ n + 1 → f (2 * n + j) = inF x (j + 1))
    (hp4 : ∀ q, 4 ≤ q → q ≤ n + 1 → f q = inF x q) :
    ∃ g, exec prog2 ρ S (2 * m + 9) r (memOf w f)
      = exec prog2 ρ (S - 2) (2 * m + 11) r (memOf w g) ∧
      (∀ q, g q < 2 ^ w) ∧ g 0 = 2 * n + m + 1 ∧ g 1 = 1 ∧ g 2 = 0 ∧
      (∀ j, j + 1 ≤ m + 2 → j + 1 ≤ n + 1 → g (2 * n + j) = inF x (j + 1)) ∧
      (∀ q, 4 ≤ q → q ≤ n + 1 → g q = inF x q) ∧
      (∀ q, 8 ≤ q → q < 2 * n → g q = f q) := by
  have esum : f 0 + f 1 = 2 * n + m + 1 := by omega
  have ec0 : (up f 0 (2 * n + m + 1)) 0 = 2 * n + m + 1 := up_eq _ _ _
  have ecv : (up f 0 (2 * n + m + 1)) (m + 2) = f (m + 2) := by
    rw [up_ne (by omega)]
  have hvv : f (m + 2) < 2 ^ w := by
    by_cases hkn : m + 2 ≤ n + 1
    · rw [hp4 (m + 2) (by omega) hkn]; exact hif (m + 2)
    · exact hfit (m + 2)
  have f1fit : ∀ q, up f 0 (2 * n + m + 1) q < 2 ^ w :=
    upFit hfit (pro_vfit hn hpow (by omega))
  have gfit : ∀ q, up (up f 0 (2 * n + m + 1)) (2 * n + m + 1) (f (m + 2)) q
      < 2 ^ w := upFit f1fit hvv
  have g0 : (up (up f 0 (2 * n + m + 1)) (2 * n + m + 1) (f (m + 2))) 0
      = 2 * n + m + 1 := by
    rw [up_ne (by omega), ec0]
  have g1 : (up (up f 0 (2 * n + m + 1)) (2 * n + m + 1) (f (m + 2))) 1
      = 1 := by
    rw [up_ne (by omega), up_ne (by omega), hf1]
  have g2 : (up (up f 0 (2 * n + m + 1)) (2 * n + m + 1) (f (m + 2))) 2
      = 0 := by
    rw [up_ne (by omega), up_ne (by omega), hf2]
  have gscr : ∀ j, j + 1 ≤ m + 2 → j + 1 ≤ n + 1 →
      (up (up f 0 (2 * n + m + 1)) (2 * n + m + 1) (f (m + 2)))
        (2 * n + j) = inF x (j + 1) := by
    intro j hj1 hj2
    by_cases hjm : j = m + 1
    · rw [hjm, (by omega : 2 * n + (m + 1) = 2 * n + m + 1), up_eq,
        (by omega : m + 1 + 1 = m + 2)]
      exact hp4 (m + 2) (by omega) (by omega)
    · rw [up_ne (by omega), up_ne (by omega)]
      exact hscr j (by omega) hj2
  have gp4 : ∀ q, 4 ≤ q → q ≤ n + 1 →
      (up (up f 0 (2 * n + m + 1)) (2 * n + m + 1) (f (m + 2))) q
        = inF x q := by
    intro q hq1 hq2
    rw [up_ne (by omega), up_ne (by omega)]
    exact hp4 q hq1 hq2
  have gmid : ∀ q, 8 ≤ q → q < 2 * n →
      (up (up f 0 (2 * n + m + 1)) (2 * n + m + 1) (f (m + 2))) q = f q := by
    intro q hq1 hq2
    rw [up_ne (by omega), up_ne (by omega)]
  refine ⟨up (up f 0 (2 * n + m + 1)) (2 * n + m + 1) (f (m + 2)),
    ?_, gfit, g0, g1, g2, gscr, gp4, gmid⟩
  rw [exec_add_step (by omega) hadd, esum,
    exec_store_step (by omega) hst f1fit, ec0, ecv]
  simp only [Nat.sub_sub, Nat.reduceAdd]

/-- The 19-round relocation sweep (pcs 13-50) via `saveAks_pair` chains:
every intermediate state stays abstract, so no nested `up` term is ever
written.  Replaces the inlined 388-line proof whose nested-state `have`s
exploded elaboration to ~137 GB (R2125607414 build unblock). -/
theorem pro_saveAks (x : Instance n) (ρ : Nat → BitVec w) (hn : 4 ≤ n)
    (hpow : 2 ^ (2 * n) ≤ 2 ^ w) (hif : ∀ q, inF x q < 2 ^ w)
    (f : Nat → Nat) (r S : Nat) (hS : 38 ≤ S)
    (hfit0 : ∀ q, f q < 2 ^ w) (hf0 : f 0 = 2 * n + 2) (hf1 : f 1 = 1)
    (hf2 : f 2 = 0)
    (hscr : ∀ j, j + 1 ≤ 3 → j + 1 ≤ n + 1 → f (2 * n + j) = inF x (j + 1))
    (hp4 : ∀ q, 4 ≤ q → q ≤ n + 1 → f q = inF x q) :
    ∃ g, exec prog2 ρ S 13 r (memOf w f) = exec prog2 ρ (S - 38) 51 r (memOf w g) ∧
      (∀ q, g q < 2 ^ w) ∧ g 0 = 2 * n + 21 ∧ g 1 = 1 ∧ g 2 = 0 ∧
      (∀ j, j + 1 ≤ 22 → j + 1 ≤ n + 1 → g (2 * n + j) = inF x (j + 1)) ∧
      (∀ q, 4 ≤ q → q ≤ n + 1 → g q = inF x q) ∧
      (∀ q, 8 ≤ q → q < 2 * n → g q = f q) := by
  obtain ⟨f2, hex2, hfit2, hf02, hf12, hf22, hscr2, hp42, hmid2⟩ :=
    saveAks_pair x ρ hn hpow hif f r S 2 (by omega) (by omega) (by omega)
      (by rfl) (by rfl) hfit0 (by omega) hf1 hf2 hscr hp4
  obtain ⟨f3, hex3, hfit3, hf03, hf13, hf23, hscr3, hp43, hmid3⟩ :=
    saveAks_pair x ρ hn hpow hif f2 r (S - 2) 3 (by omega) (by omega) (by omega)
      (by rfl) (by rfl) hfit2 (by omega) hf12 hf22 hscr2 hp42
  obtain ⟨f4, hex4, hfit4, hf04, hf14, hf24, hscr4, hp44, hmid4⟩ :=
    saveAks_pair x ρ hn hpow hif f3 r (S - 4) 4 (by omega) (by omega) (by omega)
      (by rfl) (by rfl) hfit3 (by omega) hf13 hf23 hscr3 hp43
  obtain ⟨f5, hex5, hfit5, hf05, hf15, hf25, hscr5, hp45, hmid5⟩ :=
    saveAks_pair x ρ hn hpow hif f4 r (S - 6) 5 (by omega) (by omega) (by omega)
      (by rfl) (by rfl) hfit4 (by omega) hf14 hf24 hscr4 hp44
  obtain ⟨f6, hex6, hfit6, hf06, hf16, hf26, hscr6, hp46, hmid6⟩ :=
    saveAks_pair x ρ hn hpow hif f5 r (S - 8) 6 (by omega) (by omega) (by omega)
      (by rfl) (by rfl) hfit5 (by omega) hf15 hf25 hscr5 hp45
  obtain ⟨f7, hex7, hfit7, hf07, hf17, hf27, hscr7, hp47, hmid7⟩ :=
    saveAks_pair x ρ hn hpow hif f6 r (S - 10) 7 (by omega) (by omega) (by omega)
      (by rfl) (by rfl) hfit6 (by omega) hf16 hf26 hscr6 hp46
  obtain ⟨f8, hex8, hfit8, hf08, hf18, hf28, hscr8, hp48, hmid8⟩ :=
    saveAks_pair x ρ hn hpow hif f7 r (S - 12) 8 (by omega) (by omega) (by omega)
      (by rfl) (by rfl) hfit7 (by omega) hf17 hf27 hscr7 hp47
  obtain ⟨f9, hex9, hfit9, hf09, hf19, hf29, hscr9, hp49, hmid9⟩ :=
    saveAks_pair x ρ hn hpow hif f8 r (S - 14) 9 (by omega) (by omega) (by omega)
      (by rfl) (by rfl) hfit8 (by omega) hf18 hf28 hscr8 hp48
  obtain ⟨f10, hex10, hfit10, hf010, hf110, hf210, hscr10, hp410, hmid10⟩ :=
    saveAks_pair x ρ hn hpow hif f9 r (S - 16) 10 (by omega) (by omega) (by omega)
      (by rfl) (by rfl) hfit9 (by omega) hf19 hf29 hscr9 hp49
  obtain ⟨f11, hex11, hfit11, hf011, hf111, hf211, hscr11, hp411, hmid11⟩ :=
    saveAks_pair x ρ hn hpow hif f10 r (S - 18) 11 (by omega) (by omega) (by omega)
      (by rfl) (by rfl) hfit10 (by omega) hf110 hf210 hscr10 hp410
  obtain ⟨f12, hex12, hfit12, hf012, hf112, hf212, hscr12, hp412, hmid12⟩ :=
    saveAks_pair x ρ hn hpow hif f11 r (S - 20) 12 (by omega) (by omega) (by omega)
      (by rfl) (by rfl) hfit11 (by omega) hf111 hf211 hscr11 hp411
  obtain ⟨f13, hex13, hfit13, hf013, hf113, hf213, hscr13, hp413, hmid13⟩ :=
    saveAks_pair x ρ hn hpow hif f12 r (S - 22) 13 (by omega) (by omega) (by omega)
      (by rfl) (by rfl) hfit12 (by omega) hf112 hf212 hscr12 hp412
  obtain ⟨f14, hex14, hfit14, hf014, hf114, hf214, hscr14, hp414, hmid14⟩ :=
    saveAks_pair x ρ hn hpow hif f13 r (S - 24) 14 (by omega) (by omega) (by omega)
      (by rfl) (by rfl) hfit13 (by omega) hf113 hf213 hscr13 hp413
  obtain ⟨f15, hex15, hfit15, hf015, hf115, hf215, hscr15, hp415, hmid15⟩ :=
    saveAks_pair x ρ hn hpow hif f14 r (S - 26) 15 (by omega) (by omega) (by omega)
      (by rfl) (by rfl) hfit14 (by omega) hf114 hf214 hscr14 hp414
  obtain ⟨f16, hex16, hfit16, hf016, hf116, hf216, hscr16, hp416, hmid16⟩ :=
    saveAks_pair x ρ hn hpow hif f15 r (S - 28) 16 (by omega) (by omega) (by omega)
      (by rfl) (by rfl) hfit15 (by omega) hf115 hf215 hscr15 hp415
  obtain ⟨f17, hex17, hfit17, hf017, hf117, hf217, hscr17, hp417, hmid17⟩ :=
    saveAks_pair x ρ hn hpow hif f16 r (S - 30) 17 (by omega) (by omega) (by omega)
      (by rfl) (by rfl) hfit16 (by omega) hf116 hf216 hscr16 hp416
  obtain ⟨f18, hex18, hfit18, hf018, hf118, hf218, hscr18, hp418, hmid18⟩ :=
    saveAks_pair x ρ hn hpow hif f17 r (S - 32) 18 (by omega) (by omega) (by omega)
      (by rfl) (by rfl) hfit17 (by omega) hf117 hf217 hscr17 hp417
  obtain ⟨f19, hex19, hfit19, hf019, hf119, hf219, hscr19, hp419, hmid19⟩ :=
    saveAks_pair x ρ hn hpow hif f18 r (S - 34) 19 (by omega) (by omega) (by omega)
      (by rfl) (by rfl) hfit18 (by omega) hf118 hf218 hscr18 hp418
  obtain ⟨f20, hex20, hfit20, hf020, hf120, hf220, hscr20, hp420, hmid20⟩ :=
    saveAks_pair x ρ hn hpow hif f19 r (S - 36) 20 (by omega) (by omega) (by omega)
      (by rfl) (by rfl) hfit19 (by omega) hf119 hf219 hscr19 hp419
  have hchain : exec prog2 ρ S 13 r (memOf w f)
      = exec prog2 ρ (S - 36 - 2) (2 * 20 + 11) r (memOf w f20) := hex2.trans (hex3.trans (hex4.trans (hex5.trans (hex6.trans (hex7.trans (hex8.trans (hex9.trans (hex10.trans (hex11.trans (hex12.trans (hex13.trans (hex14.trans (hex15.trans (hex16.trans (hex17.trans (hex18.trans (hex19.trans (hex20))))))))))))))))))
  simp only [Nat.sub_sub, Nat.reduceAdd] at hchain
  refine ⟨f20, hchain, hfit20, (by omega : f20 0 = 2 * n + 21), hf120, hf220,
    ?_, hp420,
    (fun q hq1 hq2 => ((fun q hq1 hq2 => ((fun q hq1 hq2 => ((fun q hq1 hq2 => ((fun q hq1 hq2 => ((fun q hq1 hq2 => ((fun q hq1 hq2 => ((fun q hq1 hq2 => ((fun q hq1 hq2 => ((fun q hq1 hq2 => ((fun q hq1 hq2 => ((fun q hq1 hq2 => ((fun q hq1 hq2 => ((fun q hq1 hq2 => ((fun q hq1 hq2 => ((fun q hq1 hq2 => ((fun q hq1 hq2 => ((fun q hq1 hq2 => (hmid20 q hq1 hq2).trans (hmid19 q hq1 hq2)) q hq1 hq2).trans (hmid18 q hq1 hq2)) q hq1 hq2).trans (hmid17 q hq1 hq2)) q hq1 hq2).trans (hmid16 q hq1 hq2)) q hq1 hq2).trans (hmid15 q hq1 hq2)) q hq1 hq2).trans (hmid14 q hq1 hq2)) q hq1 hq2).trans (hmid13 q hq1 hq2)) q hq1 hq2).trans (hmid12 q hq1 hq2)) q hq1 hq2).trans (hmid11 q hq1 hq2)) q hq1 hq2).trans (hmid10 q hq1 hq2)) q hq1 hq2).trans (hmid9 q hq1 hq2)) q hq1 hq2).trans (hmid8 q hq1 hq2)) q hq1 hq2).trans (hmid7 q hq1 hq2)) q hq1 hq2).trans (hmid6 q hq1 hq2)) q hq1 hq2).trans (hmid5 q hq1 hq2)) q hq1 hq2).trans (hmid4 q hq1 hq2)) q hq1 hq2).trans (hmid3 q hq1 hq2)) q hq1 hq2).trans (hmid2 q hq1 hq2))⟩
  exact fun j hj1 hj2 => hscr20 j (by omega) hj2
/-! ### Segment G: LOOP1 + LOOP2 + post (pcs 65-85, Phase A entry at 86) -/

/-- One LOOP1 trip (pcs 65-70, six steps, stops at the `blt` at 71):
`block[j+1] := scratch[j]`, counter `j → j+1`.  Stated over an abstract
state `f` so the walk below never nests `up`-chains. -/
theorem loop1_body (x : Instance n) (ρ : Nat → BitVec w) (hn : 4 ≤ n)
    (hpow : 2 ^ (2 * n) ≤ 2 ^ w)
    (f : Nat → Nat) (j r S : Nat) (hj : j ≤ 21) (hS : 6 ≤ S)
    (hfit : ∀ q, f q < 2 ^ w) (hf0 : f 0 = 2 * n + 23) (hf1 : f 1 = 1)
    (hf2 : f 2 = 0) (hf3 : f 3 = 22) (hf4 : f 4 = 2 * n) (hf5 : f 5 = j)
    (hcop : ∀ i', 1 ≤ i' → i' ≤ j → i' ≤ n + 1 → f (2 * n + 23 + i') = inF x i')
    (hscr : ∀ j', j' + 1 ≤ 22 → j' + 1 ≤ n + 1 → f (2 * n + j') = inF x (j' + 1))
    (hsrc : ∀ q, 23 ≤ q → q ≤ n + 1 → f q = inF x q)
    (hmid : ∀ q, 8 ≤ q → q < 2 * n → f q = inF x q) :
    ∃ g, exec prog2 ρ S 65 r (memOf w f) = exec prog2 ρ (S - 6) 71 r (memOf w g) ∧
      (∀ q, g q < 2 ^ w) ∧ g 0 = 2 * n + 23 ∧ g 1 = 1 ∧ g 2 = 0 ∧
      g 3 = 22 ∧ g 4 = 2 * n ∧ g 5 = j + 1 ∧
      (∀ i', 1 ≤ i' → i' ≤ j + 1 → i' ≤ n + 1 → g (2 * n + 23 + i') = inF x i') ∧
      (∀ j', j' + 1 ≤ 22 → j' + 1 ≤ n + 1 → g (2 * n + j') = inF x (j' + 1)) ∧
      (∀ q, 23 ≤ q → q ≤ n + 1 → g q = inF x q) ∧
      (∀ q, 8 ≤ q → q < 2 * n → g q = inF x q) := by
  have e65 : f 4 + f 5 = 2 * n + j := by rw [hf4, hf5]
  have fitA : ∀ q, (up f 6 (2 * n + j)) q < 2 ^ w :=
    upFit hfit (pro_vfit hn hpow (by omega))
  have e66 : (up f 6 (2 * n + j)) ((up f 6 (2 * n + j)) 6) = f (2 * n + j) := by
    rw [up_eq, up_ne (show 2 * n + j ≠ 6 by omega)]
  have fitB : ∀ q, (up (up f 6 (2 * n + j)) 7 (f (2 * n + j))) q < 2 ^ w :=
    upFit fitA (hfit (2 * n + j))
  have e67 : (up (up f 6 (2 * n + j)) 7 (f (2 * n + j))) 0
      + (up (up f 6 (2 * n + j)) 7 (f (2 * n + j))) 5 = 2 * n + 23 + j := by
    rw [up_ne (show (0:Nat) ≠ 7 by omega), up_ne (show (0:Nat) ≠ 6 by omega), hf0,
      up_ne (show (5:Nat) ≠ 7 by omega), up_ne (show (5:Nat) ≠ 6 by omega), hf5]
  have fitC : ∀ q, (up (up (up f 6 (2 * n + j)) 7 (f (2 * n + j))) 6 (2 * n + 23 + j)) q
      < 2 ^ w := upFit fitB (pro_vfit hn hpow (by omega))
  have e68 : (up (up (up f 6 (2 * n + j)) 7 (f (2 * n + j))) 6 (2 * n + 23 + j)) 6
      + (up (up (up f 6 (2 * n + j)) 7 (f (2 * n + j))) 6 (2 * n + 23 + j)) 1
      = 2 * n + 24 + j := by
    rw [up_eq, up_ne (show (1:Nat) ≠ 6 by omega), up_ne (show (1:Nat) ≠ 7 by omega),
      up_ne (show (1:Nat) ≠ 6 by omega), hf1]
    omega
  have fitD : ∀ q,
      (up (up (up (up f 6 (2 * n + j)) 7 (f (2 * n + j))) 6 (2 * n + 23 + j))
        6 (2 * n + 24 + j)) q < 2 ^ w := upFit fitC (pro_vfit hn hpow (by omega))
  have e69a : (up (up (up (up f 6 (2 * n + j)) 7 (f (2 * n + j))) 6 (2 * n + 23 + j))
      6 (2 * n + 24 + j)) 6 = 2 * n + 24 + j := up_eq _ _ _
  have e69b : (up (up (up (up f 6 (2 * n + j)) 7 (f (2 * n + j))) 6 (2 * n + 23 + j))
      6 (2 * n + 24 + j)) 7 = f (2 * n + j) := by
    rw [up_ne (show (7:Nat) ≠ 6 by omega), up_ne (show (7:Nat) ≠ 6 by omega), up_eq]
  have fitE : ∀ q,
      (up (up (up (up (up f 6 (2 * n + j)) 7 (f (2 * n + j))) 6 (2 * n + 23 + j))
        6 (2 * n + 24 + j)) (2 * n + 24 + j) (f (2 * n + j))) q < 2 ^ w :=
    upFit fitD (hfit (2 * n + j))
  have e70 : (up (up (up (up (up f 6 (2 * n + j)) 7 (f (2 * n + j))) 6 (2 * n + 23 + j))
        6 (2 * n + 24 + j)) (2 * n + 24 + j) (f (2 * n + j))) 5
      + (up (up (up (up (up f 6 (2 * n + j)) 7 (f (2 * n + j))) 6 (2 * n + 23 + j))
        6 (2 * n + 24 + j)) (2 * n + 24 + j) (f (2 * n + j))) 1 = j + 1 := by
    rw [up_ne (show (5:Nat) ≠ 2 * n + 24 + j by omega),
      up_ne (show (5:Nat) ≠ 6 by omega), up_ne (show (5:Nat) ≠ 6 by omega),
      up_ne (show (5:Nat) ≠ 7 by omega), up_ne (show (5:Nat) ≠ 6 by omega), hf5,
      up_ne (show (1:Nat) ≠ 2 * n + 24 + j by omega),
      up_ne (show (1:Nat) ≠ 6 by omega), up_ne (show (1:Nat) ≠ 6 by omega),
      up_ne (show (1:Nat) ≠ 7 by omega), up_ne (show (1:Nat) ≠ 6 by omega), hf1]
  have fitG : ∀ q,
      (up (up (up (up (up (up f 6 (2 * n + j)) 7 (f (2 * n + j))) 6 (2 * n + 23 + j))
        6 (2 * n + 24 + j)) (2 * n + 24 + j) (f (2 * n + j))) 5 (j + 1)) q < 2 ^ w :=
    upFit fitE (pro_vfit hn hpow (by omega))
  have g0 : (up (up (up (up (up (up f 6 (2 * n + j)) 7 (f (2 * n + j))) 6 (2 * n + 23 + j))
        6 (2 * n + 24 + j)) (2 * n + 24 + j) (f (2 * n + j))) 5 (j + 1)) 0
      = 2 * n + 23 := by
    rw [up_ne (show (0:Nat) ≠ 5 by omega),
      up_ne (show (0:Nat) ≠ 2 * n + 24 + j by omega),
      up_ne (show (0:Nat) ≠ 6 by omega), up_ne (show (0:Nat) ≠ 6 by omega),
      up_ne (show (0:Nat) ≠ 7 by omega), up_ne (show (0:Nat) ≠ 6 by omega), hf0]
  have g1 : (up (up (up (up (up (up f 6 (2 * n + j)) 7 (f (2 * n + j))) 6 (2 * n + 23 + j))
        6 (2 * n + 24 + j)) (2 * n + 24 + j) (f (2 * n + j))) 5 (j + 1)) 1 = 1 := by
    rw [up_ne (show (1:Nat) ≠ 5 by omega),
      up_ne (show (1:Nat) ≠ 2 * n + 24 + j by omega),
      up_ne (show (1:Nat) ≠ 6 by omega), up_ne (show (1:Nat) ≠ 6 by omega),
      up_ne (show (1:Nat) ≠ 7 by omega), up_ne (show (1:Nat) ≠ 6 by omega), hf1]
  have g2 : (up (up (up (up (up (up f 6 (2 * n + j)) 7 (f (2 * n + j))) 6 (2 * n + 23 + j))
        6 (2 * n + 24 + j)) (2 * n + 24 + j) (f (2 * n + j))) 5 (j + 1)) 2 = 0 := by
    rw [up_ne (show (2:Nat) ≠ 5 by omega),
      up_ne (show (2:Nat) ≠ 2 * n + 24 + j by omega),
      up_ne (show (2:Nat) ≠ 6 by omega), up_ne (show (2:Nat) ≠ 6 by omega),
      up_ne (show (2:Nat) ≠ 7 by omega), up_ne (show (2:Nat) ≠ 6 by omega), hf2]
  have g3 : (up (up (up (up (up (up f 6 (2 * n + j)) 7 (f (2 * n + j))) 6 (2 * n + 23 + j))
        6 (2 * n + 24 + j)) (2 * n + 24 + j) (f (2 * n + j))) 5 (j + 1)) 3 = 22 := by
    rw [up_ne (show (3:Nat) ≠ 5 by omega),
      up_ne (show (3:Nat) ≠ 2 * n + 24 + j by omega),
      up_ne (show (3:Nat) ≠ 6 by omega), up_ne (show (3:Nat) ≠ 6 by omega),
      up_ne (show (3:Nat) ≠ 7 by omega), up_ne (show (3:Nat) ≠ 6 by omega), hf3]
  have g4 : (up (up (up (up (up (up f 6 (2 * n + j)) 7 (f (2 * n + j))) 6 (2 * n + 23 + j))
        6 (2 * n + 24 + j)) (2 * n + 24 + j) (f (2 * n + j))) 5 (j + 1)) 4 = 2 * n := by
    rw [up_ne (show (4:Nat) ≠ 5 by omega),
      up_ne (show (4:Nat) ≠ 2 * n + 24 + j by omega),
      up_ne (show (4:Nat) ≠ 6 by omega), up_ne (show (4:Nat) ≠ 6 by omega),
      up_ne (show (4:Nat) ≠ 7 by omega), up_ne (show (4:Nat) ≠ 6 by omega), hf4]
  have g5 : (up (up (up (up (up (up f 6 (2 * n + j)) 7 (f (2 * n + j))) 6 (2 * n + 23 + j))
        6 (2 * n + 24 + j)) (2 * n + 24 + j) (f (2 * n + j))) 5 (j + 1)) 5 = j + 1 :=
    up_eq _ _ _
  have gcop : ∀ i', 1 ≤ i' → i' ≤ j + 1 → i' ≤ n + 1 →
      (up (up (up (up (up (up f 6 (2 * n + j)) 7 (f (2 * n + j))) 6 (2 * n + 23 + j))
        6 (2 * n + 24 + j)) (2 * n + 24 + j) (f (2 * n + j))) 5 (j + 1)) (2 * n + 23 + i')
        = inF x i' := by
    intro i' h1 h2 h3
    by_cases hij : i' = j + 1
    · rw [hij, show 2 * n + 23 + (j + 1) = 2 * n + 24 + j from by omega,
        up_ne (show 2 * n + 24 + j ≠ 5 by omega), up_eq]
      exact hscr j (by omega) (by omega)
    · rw [up_ne (show 2 * n + 23 + i' ≠ 5 by omega),
        up_ne (show 2 * n + 23 + i' ≠ 2 * n + 24 + j by omega),
        up_ne (show 2 * n + 23 + i' ≠ 6 by omega),
        up_ne (show 2 * n + 23 + i' ≠ 6 by omega),
        up_ne (show 2 * n + 23 + i' ≠ 7 by omega),
        up_ne (show 2 * n + 23 + i' ≠ 6 by omega)]
      exact hcop i' h1 (by omega) h3
  have gscr : ∀ j', j' + 1 ≤ 22 → j' + 1 ≤ n + 1 →
      (up (up (up (up (up (up f 6 (2 * n + j)) 7 (f (2 * n + j))) 6 (2 * n + 23 + j))
        6 (2 * n + 24 + j)) (2 * n + 24 + j) (f (2 * n + j))) 5 (j + 1)) (2 * n + j')
        = inF x (j' + 1) := by
    intro j' h1 h2
    rw [up_ne (show 2 * n + j' ≠ 5 by omega),
      up_ne (show 2 * n + j' ≠ 2 * n + 24 + j by omega),
      up_ne (show 2 * n + j' ≠ 6 by omega), up_ne (show 2 * n + j' ≠ 6 by omega),
      up_ne (show 2 * n + j' ≠ 7 by omega), up_ne (show 2 * n + j' ≠ 6 by omega)]
    exact hscr j' h1 h2
  have gsrc : ∀ q, 23 ≤ q → q ≤ n + 1 →
      (up (up (up (up (up (up f 6 (2 * n + j)) 7 (f (2 * n + j))) 6 (2 * n + 23 + j))
        6 (2 * n + 24 + j)) (2 * n + 24 + j) (f (2 * n + j))) 5 (j + 1)) q = inF x q := by
    intro q h1 h2
    rw [up_ne (show q ≠ 5 by omega),
      up_ne (show q ≠ 2 * n + 24 + j by omega),
      up_ne (show q ≠ 6 by omega), up_ne (show q ≠ 6 by omega),
      up_ne (show q ≠ 7 by omega), up_ne (show q ≠ 6 by omega)]
    exact hsrc q h1 h2
  have gmid : ∀ q, 8 ≤ q → q < 2 * n →
      (up (up (up (up (up (up f 6 (2 * n + j)) 7 (f (2 * n + j))) 6 (2 * n + 23 + j))
        6 (2 * n + 24 + j)) (2 * n + 24 + j) (f (2 * n + j))) 5 (j + 1)) q = inF x q := by
    intro q h1 h2
    rw [up_ne (show q ≠ 5 by omega),
      up_ne (show q ≠ 2 * n + 24 + j by omega),
      up_ne (show q ≠ 6 by omega), up_ne (show q ≠ 6 by omega),
      up_ne (show q ≠ 7 by omega), up_ne (show q ≠ 6 by omega)]
    exact hmid q h1 h2
  refine ⟨up (up (up (up (up (up f 6 (2 * n + j)) 7 (f (2 * n + j))) 6 (2 * n + 23 + j))
    6 (2 * n + 24 + j)) (2 * n + 24 + j) (f (2 * n + j))) 5 (j + 1),
    ?_, fitG, g0, g1, g2, g3, g4, g5, gcop, gscr, gsrc, gmid⟩
  rw [exec_add_step (by omega) (show prog2.getD 65 Instr.reject = Instr.add 6 4 5 by rfl),
    e65,
    exec_load_step (by omega) (show prog2.getD 66 Instr.reject = Instr.load 7 6 by rfl) fitA,
    e66,
    exec_add_step (by omega) (show prog2.getD 67 Instr.reject = Instr.add 6 0 5 by rfl),
    e67,
    exec_add_step (by omega) (show prog2.getD 68 Instr.reject = Instr.add 6 6 1 by rfl),
    e68,
    exec_store_step (by omega) (show prog2.getD 69 Instr.reject = Instr.store 6 7 by rfl) fitD,
    e69a, e69b,
    exec_add_step (by omega) (show prog2.getD 70 Instr.reject = Instr.add 5 5 1 by rfl),
    e70]
  simp only [Nat.sub_sub, Nat.reduceAdd]


/-- LOOP2 setup (pcs 72-76): counter `[5] := 22`, bound `[4] := n+2`
via `(2n+23-22)/2 + 2`. -/
theorem loop2_setup (x : Instance n) (ρ : Nat → BitVec w) (hn : 4 ≤ n)
    (hpow : 2 ^ (2 * n) ≤ 2 ^ w)
    (f : Nat → Nat) (r S : Nat) (hS : 5 ≤ S)
    (hfit : ∀ q, f q < 2 ^ w) (hf0 : f 0 = 2 * n + 23) (hf1 : f 1 = 1)
    (hf2 : f 2 = 0) (hf3 : f 3 = 22) (hf5 : f 5 = 22)
    (hcop : ∀ i', 1 ≤ i' → i' ≤ 22 → i' ≤ n + 1 → f (2 * n + 23 + i') = inF x i')
    (hsrc : ∀ q, 23 ≤ q → q ≤ n + 1 → f q = inF x q)
    (hmid : ∀ q, 8 ≤ q → q < 2 * n → f q = inF x q) :
    ∃ g, exec prog2 ρ S 72 r (memOf w f) = exec prog2 ρ (S - 5) 77 r (memOf w g) ∧
      (∀ q, g q < 2 ^ w) ∧ g 0 = 2 * n + 23 ∧ g 1 = 1 ∧ g 2 = 0 ∧
      g 4 = n + 2 ∧ g 5 = 22 ∧
      (∀ i', 1 ≤ i' → i' ≤ 22 → i' ≤ n + 1 → g (2 * n + 23 + i') = inF x i') ∧
      (∀ q, 23 ≤ q → q ≤ n + 1 → g q = inF x q) ∧
      (∀ q, 8 ≤ q → q < 2 * n → g q = inF x q) := by
  have e72 : f 3 + f 2 = 22 := by rw [hf3, hf2]
  have fitA : ∀ q, (up f 5 22) q < 2 ^ w :=
    upFit hfit (pro_vfit hn hpow (by omega))
  have e73a : (up f 5 22) 0 = 2 * n + 23 := by rw [up_ne (show (0:Nat) ≠ 5 by omega), hf0]
  have e73b : (up f 5 22) 3 = 22 := by rw [up_ne (show (3:Nat) ≠ 5 by omega), hf3]
  have hle73 : (up f 5 22) 3 ≤ (up f 5 22) 0 := by rw [e73b, e73a]; omega
  have e73 : (up f 5 22) 0 - (up f 5 22) 3 = 2 * n + 1 := by rw [e73a, e73b]; omega
  have fitB : ∀ q, (up (up f 5 22) 4 (2 * n + 1)) q < 2 ^ w :=
    upFit fitA (pro_vfit hn hpow (by omega))
  have e74a : (up (up f 5 22) 4 (2 * n + 1)) 4 = 2 * n + 1 := up_eq _ _ _
  have e74b : (up (up f 5 22) 4 (2 * n + 1)) 1 = 1 := by
    rw [up_ne (show (1:Nat) ≠ 4 by omega), up_ne (show (1:Nat) ≠ 5 by omega), hf1]
  have e74 : (up (up f 5 22) 4 (2 * n + 1)) 4
      / 2 ^ (up (up f 5 22) 4 (2 * n + 1)) 1 = n := by
    rw [e74a, e74b, Nat.pow_one]; omega
  have fitC : ∀ q, (up (up (up f 5 22) 4 (2 * n + 1)) 4 n) q < 2 ^ w :=
    upFit fitB (pro_vfit hn hpow (by omega))
  have e75a : (up (up (up f 5 22) 4 (2 * n + 1)) 4 n) 4 = n := up_eq _ _ _
  have e75b : (up (up (up f 5 22) 4 (2 * n + 1)) 4 n) 1 = 1 := by
    rw [up_ne (show (1:Nat) ≠ 4 by omega), up_ne (show (1:Nat) ≠ 4 by omega),
      up_ne (show (1:Nat) ≠ 5 by omega), hf1]
  have e75 : (up (up (up f 5 22) 4 (2 * n + 1)) 4 n) 4
      + (up (up (up f 5 22) 4 (2 * n + 1)) 4 n) 1 = n + 1 := by rw [e75a, e75b]
  have fitD : ∀ q, (up (up (up (up f 5 22) 4 (2 * n + 1)) 4 n) 4 (n + 1)) q < 2 ^ w :=
    upFit fitC (pro_vfit hn hpow (by omega))
  have e76a : (up (up (up (up f 5 22) 4 (2 * n + 1)) 4 n) 4 (n + 1)) 4 = n + 1 :=
    up_eq _ _ _
  have e76b : (up (up (up (up f 5 22) 4 (2 * n + 1)) 4 n) 4 (n + 1)) 1 = 1 := by
    rw [up_ne (show (1:Nat) ≠ 4 by omega), up_ne (show (1:Nat) ≠ 4 by omega),
      up_ne (show (1:Nat) ≠ 4 by omega), up_ne (show (1:Nat) ≠ 5 by omega), hf1]
  have e76 : (up (up (up (up f 5 22) 4 (2 * n + 1)) 4 n) 4 (n + 1)) 4
      + (up (up (up (up f 5 22) 4 (2 * n + 1)) 4 n) 4 (n + 1)) 1 = n + 2 := by
    rw [e76a, e76b]
  have fitE : ∀ q,
      (up (up (up (up (up f 5 22) 4 (2 * n + 1)) 4 n) 4 (n + 1)) 4 (n + 2)) q
      < 2 ^ w := upFit fitD (pro_vfit hn hpow (by omega))
  have g0 : (up (up (up (up (up f 5 22) 4 (2 * n + 1)) 4 n) 4 (n + 1)) 4 (n + 2)) 0
      = 2 * n + 23 := by
    rw [up_ne (show (0:Nat) ≠ 4 by omega), up_ne (show (0:Nat) ≠ 4 by omega),
      up_ne (show (0:Nat) ≠ 4 by omega), up_ne (show (0:Nat) ≠ 4 by omega),
      up_ne (show (0:Nat) ≠ 5 by omega), hf0]
  have g1 : (up (up (up (up (up f 5 22) 4 (2 * n + 1)) 4 n) 4 (n + 1)) 4 (n + 2)) 1
      = 1 := by
    rw [up_ne (show (1:Nat) ≠ 4 by omega), up_ne (show (1:Nat) ≠ 4 by omega),
      up_ne (show (1:Nat) ≠ 4 by omega), up_ne (show (1:Nat) ≠ 4 by omega),
      up_ne (show (1:Nat) ≠ 5 by omega), hf1]
  have g2 : (up (up (up (up (up f 5 22) 4 (2 * n + 1)) 4 n) 4 (n + 1)) 4 (n + 2)) 2
      = 0 := by
    rw [up_ne (show (2:Nat) ≠ 4 by omega), up_ne (show (2:Nat) ≠ 4 by omega),
      up_ne (show (2:Nat) ≠ 4 by omega), up_ne (show (2:Nat) ≠ 4 by omega),
      up_ne (show (2:Nat) ≠ 5 by omega), hf2]
  have g4 : (up (up (up (up (up f 5 22) 4 (2 * n + 1)) 4 n) 4 (n + 1)) 4 (n + 2)) 4
      = n + 2 := up_eq _ _ _
  have g5 : (up (up (up (up (up f 5 22) 4 (2 * n + 1)) 4 n) 4 (n + 1)) 4 (n + 2)) 5
      = 22 := by
    rw [up_ne (show (5:Nat) ≠ 4 by omega), up_ne (show (5:Nat) ≠ 4 by omega),
      up_ne (show (5:Nat) ≠ 4 by omega), up_ne (show (5:Nat) ≠ 4 by omega), up_eq]
  have gcop : ∀ i', 1 ≤ i' → i' ≤ 22 → i' ≤ n + 1 →
      (up (up (up (up (up f 5 22) 4 (2 * n + 1)) 4 n) 4 (n + 1)) 4 (n + 2))
        (2 * n + 23 + i') = inF x i' := by
    intro i' h1 h2 h3
    rw [up_ne (show 2 * n + 23 + i' ≠ 4 by omega),
      up_ne (show 2 * n + 23 + i' ≠ 4 by omega),
      up_ne (show 2 * n + 23 + i' ≠ 4 by omega),
      up_ne (show 2 * n + 23 + i' ≠ 4 by omega),
      up_ne (show 2 * n + 23 + i' ≠ 5 by omega)]
    exact hcop i' h1 h2 h3
  have gsrc : ∀ q, 23 ≤ q → q ≤ n + 1 →
      (up (up (up (up (up f 5 22) 4 (2 * n + 1)) 4 n) 4 (n + 1)) 4 (n + 2)) q
      = inF x q := by
    intro q h1 h2
    rw [up_ne (show q ≠ 4 by omega), up_ne (show q ≠ 4 by omega),
      up_ne (show q ≠ 4 by omega), up_ne (show q ≠ 4 by omega),
      up_ne (show q ≠ 5 by omega)]
    exact hsrc q h1 h2
  have gmid : ∀ q, 8 ≤ q → q < 2 * n →
      (up (up (up (up (up f 5 22) 4 (2 * n + 1)) 4 n) 4 (n + 1)) 4 (n + 2)) q
      = inF x q := by
    intro q h1 h2
    rw [up_ne (show q ≠ 4 by omega), up_ne (show q ≠ 4 by omega),
      up_ne (show q ≠ 4 by omega), up_ne (show q ≠ 4 by omega),
      up_ne (show q ≠ 5 by omega)]
    exact hmid q h1 h2
  refine ⟨up (up (up (up (up f 5 22) 4 (2 * n + 1)) 4 n) 4 (n + 1)) 4 (n + 2),
    ?_, fitE, g0, g1, g2, g4, g5, gcop, gsrc, gmid⟩
  rw [exec_add_step (by omega) (show prog2.getD 72 Instr.reject = Instr.add 5 3 2 by rfl),
    e72,
    exec_sub_step (by omega) (show prog2.getD 73 Instr.reject = Instr.sub 4 0 3 by rfl)
      fitA hle73, e73,
    exec_shr_step (by omega) (show prog2.getD 74 Instr.reject = Instr.shr 4 4 1 by rfl)
      fitB, e74,
    exec_add_step (by omega) (show prog2.getD 75 Instr.reject = Instr.add 4 4 1 by rfl),
    e75,
    exec_add_step (by omega) (show prog2.getD 76 Instr.reject = Instr.add 4 4 1 by rfl),
    e76]
  simp only [Nat.sub_sub, Nat.reduceAdd]


/-- One LOOP2 trip (pcs 77-81, five steps, stops at the `blt` at 82):
`block[i] := cell i`, counter `i → i+1`.  `i = 22` is the do-while's first
(idempotent) trip; `i ≥ 23` are the while trips. -/
theorem loop2_body (x : Instance n) (ρ : Nat → BitVec w) (hn : 4 ≤ n)
    (hpow : 2 ^ (2 * n) ≤ 2 ^ w)
    (f : Nat → Nat) (i r S : Nat) (hi : 22 ≤ i) (hile : i = 22 ∨ i ≤ n + 2)
    (hS : 5 ≤ S)
    (hfit : ∀ q, f q < 2 ^ w) (hf0 : f 0 = 2 * n + 23) (hf1 : f 1 = 1)
    (hf2 : f 2 = 0) (hf4 : f 4 = n + 2) (hf5 : f 5 = i)
    (hisrc : i ≤ n + 1 → f i = inF x i)
    (hblk : ∀ i', 1 ≤ i' → i' < i → i' ≤ n + 1 → f (2 * n + 23 + i') = inF x i')
    (hcop : ∀ i', 1 ≤ i' → i' ≤ 22 → i' ≤ n + 1 → f (2 * n + 23 + i') = inF x i')
    (hsrc : ∀ q, 23 ≤ q → q ≤ n + 1 → f q = inF x q) :
    ∃ g, exec prog2 ρ S 77 r (memOf w f) = exec prog2 ρ (S - 5) 82 r (memOf w g) ∧
      (∀ q, g q < 2 ^ w) ∧ g 0 = 2 * n + 23 ∧ g 1 = 1 ∧ g 2 = 0 ∧
      g 4 = n + 2 ∧ g 5 = i + 1 ∧
      (∀ i', 1 ≤ i' → i' < i + 1 → i' ≤ n + 1 → g (2 * n + 23 + i') = inF x i') ∧
      (∀ i', 1 ≤ i' → i' ≤ 22 → i' ≤ n + 1 → g (2 * n + 23 + i') = inF x i') ∧
      (∀ q, 23 ≤ q → q ≤ n + 1 → g q = inF x q) := by
  have e77 : f 5 + f 2 = i := by rw [hf5, hf2, Nat.add_zero]
  have fitA : ∀ q, (up f 20 i) q < 2 ^ w :=
    upFit hfit (pro_vfit hn hpow (by omega))
  have e78 : (up f 20 i) ((up f 20 i) 20) = f i := by
    rw [up_eq, up_ne (show i ≠ 20 by omega)]
  have fitB : ∀ q, (up (up f 20 i) 6 (f i)) q < 2 ^ w := upFit fitA (hfit i)
  have e79 : (up (up f 20 i) 6 (f i)) 0 + (up (up f 20 i) 6 (f i)) 5
      = 2 * n + 23 + i := by
    rw [up_ne (show (0:Nat) ≠ 6 by omega), up_ne (show (0:Nat) ≠ 20 by omega), hf0,
      up_ne (show (5:Nat) ≠ 6 by omega), up_ne (show (5:Nat) ≠ 20 by omega), hf5]
  have fitC : ∀ q, (up (up (up f 20 i) 6 (f i)) 21 (2 * n + 23 + i)) q < 2 ^ w :=
    upFit fitB (pro_vfit hn hpow (by omega))
  have e80a : (up (up (up f 20 i) 6 (f i)) 21 (2 * n + 23 + i)) 21 = 2 * n + 23 + i :=
    up_eq _ _ _
  have e80b : (up (up (up f 20 i) 6 (f i)) 21 (2 * n + 23 + i)) 6 = f i := by
    rw [up_ne (show (6:Nat) ≠ 21 by omega), up_eq]
  have fitD : ∀ q,
      (up (up (up (up f 20 i) 6 (f i)) 21 (2 * n + 23 + i)) (2 * n + 23 + i) (f i)) q
      < 2 ^ w := upFit fitC (hfit i)
  have e81 : (up (up (up (up f 20 i) 6 (f i)) 21 (2 * n + 23 + i)) (2 * n + 23 + i) (f i)) 5
      + (up (up (up (up f 20 i) 6 (f i)) 21 (2 * n + 23 + i)) (2 * n + 23 + i) (f i)) 1
      = i + 1 := by
    rw [up_ne (show (5:Nat) ≠ 2 * n + 23 + i by omega),
      up_ne (show (5:Nat) ≠ 21 by omega), up_ne (show (5:Nat) ≠ 6 by omega),
      up_ne (show (5:Nat) ≠ 20 by omega), hf5,
      up_ne (show (1:Nat) ≠ 2 * n + 23 + i by omega),
      up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (1:Nat) ≠ 6 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega), hf1]
  have fitE : ∀ q,
      (up (up (up (up (up f 20 i) 6 (f i)) 21 (2 * n + 23 + i)) (2 * n + 23 + i) (f i))
        5 (i + 1)) q < 2 ^ w := upFit fitD (pro_vfit hn hpow (by omega))
  have g0 : (up (up (up (up (up f 20 i) 6 (f i)) 21 (2 * n + 23 + i)) (2 * n + 23 + i)
      (f i)) 5 (i + 1)) 0 = 2 * n + 23 := by
    rw [up_ne (show (0:Nat) ≠ 5 by omega),
      up_ne (show (0:Nat) ≠ 2 * n + 23 + i by omega),
      up_ne (show (0:Nat) ≠ 21 by omega), up_ne (show (0:Nat) ≠ 6 by omega),
      up_ne (show (0:Nat) ≠ 20 by omega), hf0]
  have g1 : (up (up (up (up (up f 20 i) 6 (f i)) 21 (2 * n + 23 + i)) (2 * n + 23 + i)
      (f i)) 5 (i + 1)) 1 = 1 := by
    rw [up_ne (show (1:Nat) ≠ 5 by omega),
      up_ne (show (1:Nat) ≠ 2 * n + 23 + i by omega),
      up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (1:Nat) ≠ 6 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega), hf1]
  have g2 : (up (up (up (up (up f 20 i) 6 (f i)) 21 (2 * n + 23 + i)) (2 * n + 23 + i)
      (f i)) 5 (i + 1)) 2 = 0 := by
    rw [up_ne (show (2:Nat) ≠ 5 by omega),
      up_ne (show (2:Nat) ≠ 2 * n + 23 + i by omega),
      up_ne (show (2:Nat) ≠ 21 by omega), up_ne (show (2:Nat) ≠ 6 by omega),
      up_ne (show (2:Nat) ≠ 20 by omega), hf2]
  have g4 : (up (up (up (up (up f 20 i) 6 (f i)) 21 (2 * n + 23 + i)) (2 * n + 23 + i)
      (f i)) 5 (i + 1)) 4 = n + 2 := by
    rw [up_ne (show (4:Nat) ≠ 5 by omega),
      up_ne (show (4:Nat) ≠ 2 * n + 23 + i by omega),
      up_ne (show (4:Nat) ≠ 21 by omega), up_ne (show (4:Nat) ≠ 6 by omega),
      up_ne (show (4:Nat) ≠ 20 by omega), hf4]
  have g5 : (up (up (up (up (up f 20 i) 6 (f i)) 21 (2 * n + 23 + i)) (2 * n + 23 + i)
      (f i)) 5 (i + 1)) 5 = i + 1 := up_eq _ _ _
  have gall : ∀ i', 1 ≤ i' → i' < i + 1 → i' ≤ n + 1 →
      (up (up (up (up (up f 20 i) 6 (f i)) 21 (2 * n + 23 + i)) (2 * n + 23 + i)
        (f i)) 5 (i + 1)) (2 * n + 23 + i') = inF x i' := by
    intro i' h1 h2 h3
    by_cases hie : i' = i
    · rw [hie, up_ne (show 2 * n + 23 + i ≠ 5 by omega), up_eq]
      exact hisrc (by rw [← hie]; exact h3)
    · rw [up_ne (show 2 * n + 23 + i' ≠ 5 by omega),
        up_ne (show 2 * n + 23 + i' ≠ 2 * n + 23 + i by omega),
        up_ne (show 2 * n + 23 + i' ≠ 21 by omega),
        up_ne (show 2 * n + 23 + i' ≠ 6 by omega),
        up_ne (show 2 * n + 23 + i' ≠ 20 by omega)]
      exact hblk i' h1 (by omega) h3
  have gcop : ∀ i', 1 ≤ i' → i' ≤ 22 → i' ≤ n + 1 →
      (up (up (up (up (up f 20 i) 6 (f i)) 21 (2 * n + 23 + i)) (2 * n + 23 + i)
        (f i)) 5 (i + 1)) (2 * n + 23 + i') = inF x i' := by
    intro i' h1 h2 h3
    by_cases hie : i' = i
    · rw [hie, up_ne (show 2 * n + 23 + i ≠ 5 by omega), up_eq]
      exact hisrc (by rw [← hie]; exact h3)
    · rw [up_ne (show 2 * n + 23 + i' ≠ 5 by omega),
        up_ne (show 2 * n + 23 + i' ≠ 2 * n + 23 + i by omega),
        up_ne (show 2 * n + 23 + i' ≠ 21 by omega),
        up_ne (show 2 * n + 23 + i' ≠ 6 by omega),
        up_ne (show 2 * n + 23 + i' ≠ 20 by omega)]
      exact hcop i' h1 h2 h3
  have gsrc : ∀ q, 23 ≤ q → q ≤ n + 1 →
      (up (up (up (up (up f 20 i) 6 (f i)) 21 (2 * n + 23 + i)) (2 * n + 23 + i)
        (f i)) 5 (i + 1)) q = inF x q := by
    intro q h1 h2
    rw [up_ne (show q ≠ 5 by omega),
      up_ne (show q ≠ 2 * n + 23 + i by omega),
      up_ne (show q ≠ 21 by omega), up_ne (show q ≠ 6 by omega),
      up_ne (show q ≠ 20 by omega)]
    exact hsrc q h1 h2
  refine ⟨up (up (up (up (up f 20 i) 6 (f i)) 21 (2 * n + 23 + i)) (2 * n + 23 + i)
    (f i)) 5 (i + 1), ?_, fitE, g0, g1, g2, g4, g5, gall, gcop, gsrc⟩
  rw [exec_add_step (by omega) (show prog2.getD 77 Instr.reject = Instr.add 20 5 2 by rfl),
    e77,
    exec_load_step (by omega) (show prog2.getD 78 Instr.reject = Instr.load 6 20 by rfl)
      fitA, e78,
    exec_add_step (by omega) (show prog2.getD 79 Instr.reject = Instr.add 21 0 5 by rfl),
    e79,
    exec_store_step (by omega) (show prog2.getD 80 Instr.reject = Instr.store 21 6 by rfl)
      fitC, e80a, e80b,
    exec_add_step (by omega) (show prog2.getD 81 Instr.reject = Instr.add 5 5 1 by rfl),
    e81]
  simp only [Nat.sub_sub, Nat.reduceAdd]


/-- LOOP1 in full: 22 trips from counter `j` (with `k = 22 - j` trips
left), landing at pc 72 with `block[1..22] = inF 1..22` (gated `i ≤ n+1`),
scratch/source/mid regions intact. -/
theorem loop1_walk (x : Instance n) (ρ : Nat → BitVec w) (hn : 4 ≤ n)
    (hpow : 2 ^ (2 * n) ≤ 2 ^ w) :
    ∀ (k j S : Nat) (f : Nat → Nat) (r : Nat), j + k = 22 → 1 ≤ k → 7 * k ≤ S →
      (∀ q, f q < 2 ^ w) → f 0 = 2 * n + 23 → f 1 = 1 → f 2 = 0 →
      f 3 = 22 → f 4 = 2 * n → f 5 = j →
      (∀ i', 1 ≤ i' → i' ≤ j → i' ≤ n + 1 → f (2 * n + 23 + i') = inF x i') →
      (∀ j', j' + 1 ≤ 22 → j' + 1 ≤ n + 1 → f (2 * n + j') = inF x (j' + 1)) →
      (∀ q, 23 ≤ q → q ≤ n + 1 → f q = inF x q) →
      (∀ q, 8 ≤ q → q < 2 * n → f q = inF x q) →
      ∃ g, exec prog2 ρ S 65 r (memOf w f) = exec prog2 ρ (S - 7 * k) 72 r (memOf w g) ∧
        (∀ q, g q < 2 ^ w) ∧ g 0 = 2 * n + 23 ∧ g 1 = 1 ∧ g 2 = 0 ∧
        g 3 = 22 ∧ g 5 = 22 ∧
        (∀ i', 1 ≤ i' → i' ≤ 22 → i' ≤ n + 1 → g (2 * n + 23 + i') = inF x i') ∧
        (∀ q, 23 ≤ q → q ≤ n + 1 → g q = inF x q) ∧
        (∀ q, 8 ≤ q → q < 2 * n → g q = inF x q) := by
  intro k
  induction k with
  | zero => intro j S f r _hk1 _; omega
  | succ k ih =>
    intro j S f r hjk hk hS hfit hf0 hf1 hf2 hf3 hf4 hf5 hcop hscr hsrc hmid
    obtain ⟨g, hex, gfit, gf0, gf1, gf2, gf3, gf4, gf5, gcop, gscr, gsrc, gmid⟩ :=
      loop1_body x ρ hn hpow f j r S (by omega) (by omega) hfit hf0 hf1 hf2 hf3
        hf4 hf5 hcop hscr hsrc hmid
    by_cases hk0 : k = 0
    · subst hk0
      refine ⟨g, ?_, gfit, gf0, gf1, gf2, gf3, by rw [gf5]; omega,
        fun i' h1 h2 h3 => gcop i' h1 (by omega) h3, gsrc, gmid⟩
      rw [hex,
        exec_blt_ge_step (by omega)
          (show prog2.getD 71 Instr.reject = Instr.blt 5 3 65 by rfl) gfit
          (by rw [gf5, gf3]; omega)]
      simp only [Nat.sub_sub, Nat.reduceAdd, Nat.mul_one, Nat.zero_add]
    · have hlt : g 5 < g 3 := by rw [gf5, gf3]; omega
      obtain ⟨g2, hex2, g2fit, g2f0, g2f1, g2f2, g2f3, g2f5, g2cop, g2src, g2mid⟩ :=
        ih (j + 1) (S - 7) g r (by omega) (by omega) (by omega) gfit gf0 gf1 gf2
          gf3 gf4 gf5 gcop gscr gsrc gmid
      refine ⟨g2, ?_, g2fit, g2f0, g2f1, g2f2, g2f3, g2f5, g2cop, g2src, g2mid⟩
      rw [hex,
        exec_blt_lt_step (by omega)
          (show prog2.getD 71 Instr.reject = Instr.blt 5 3 65 by rfl) gfit hlt,
        show S - 6 - 1 = S - 7 from by omega,
        hex2, show S - 7 - 7 * k = S - 7 * (k + 1) from by omega]



/-- LOOP2 while-part: from pc 77 with counter `i` (23 ≤ i, `i + m = n+2`),
`m` trips land at pc 83 with `block[1..n+1] = inF 1..n+1`. -/
theorem loop2_walk (x : Instance n) (ρ : Nat → BitVec w) (hn : 4 ≤ n)
    (hpow : 2 ^ (2 * n) ≤ 2 ^ w) :
    ∀ (m i S : Nat) (f : Nat → Nat) (r : Nat), i + m = n + 2 → 23 ≤ i → 1 ≤ m →
      6 * m ≤ S →
      (∀ q, f q < 2 ^ w) → f 0 = 2 * n + 23 → f 1 = 1 → f 2 = 0 →
      f 4 = n + 2 → f 5 = i →
      (∀ i', 1 ≤ i' → i' < i → i' ≤ n + 1 → f (2 * n + 23 + i') = inF x i') →
      (∀ i', 1 ≤ i' → i' ≤ 22 → i' ≤ n + 1 → f (2 * n + 23 + i') = inF x i') →
      (∀ q, 23 ≤ q → q ≤ n + 1 → f q = inF x q) →
      ∃ g c, c ≤ 6 * m ∧
        exec prog2 ρ S 77 r (memOf w f) = exec prog2 ρ (S - c) 83 r (memOf w g) ∧
        (∀ q, g q < 2 ^ w) ∧ g 0 = 2 * n + 23 ∧ g 1 = 1 ∧ g 2 = 0 ∧
        g 4 = n + 2 ∧
        (∀ i', 1 ≤ i' → i' ≤ n + 1 → g (2 * n + 23 + i') = inF x i') := by
  intro m
  induction m with
  | zero => intro i S f r _ _ hm1 _; omega
  | succ m ih =>
    intro i S f r him h23 hm1 hS hfit hf0 hf1 hf2 hf4 hf5 hblk hcop hsrc
    obtain ⟨g, hex, gfit, gf0, gf1, gf2, gf4, gf5, gall, gcop, gsrc⟩ :=
      loop2_body x ρ hn hpow f i r S (by omega) (Or.inr (by omega)) (by omega)
        hfit hf0 hf1 hf2 hf4 hf5 (fun h => hsrc i (by omega) h) hblk hcop hsrc
    by_cases hm0 : m = 0
    · subst hm0
      have hge : ¬ g 5 < g 4 := by rw [gf5, gf4]; omega
      refine ⟨g, 6, by omega, ?_, gfit, gf0, gf1, gf2, gf4,
        fun i' h1 h3 => gall i' h1 (by omega) h3⟩
      rw [hex,
        exec_blt_ge_step (by omega)
          (show prog2.getD 82 Instr.reject = Instr.blt 5 4 77 by rfl) gfit hge]
      simp only [Nat.sub_sub, Nat.reduceAdd, Nat.mul_one, Nat.zero_add]
    · have hlt : g 5 < g 4 := by rw [gf5, gf4]; omega
      obtain ⟨g2, c2, hc2, hex2, g2fit, g2f0, g2f1, g2f2, g2f4, g2all⟩ :=
        ih (i + 1) (S - 6) g r (by omega) (by omega) (by omega) (by omega)
          gfit gf0 gf1 gf2 gf4 gf5 gall gcop gsrc
      refine ⟨g2, 6 + c2, by omega, ?_, g2fit, g2f0, g2f1, g2f2, g2f4, g2all⟩
      rw [hex,
        exec_blt_lt_step (by omega)
          (show prog2.getD 82 Instr.reject = Instr.blt 5 4 77 by rfl) gfit hlt,
        show S - 5 - 1 = S - 6 from by omega,
        hex2, show S - 6 - c2 = S - (6 + c2) from by omega]

/-- Post-loop tail (pcs 83-85): `[7] := n`, `[8] := RELOC = 2n+23`;
Phase A entry (pc 86) bundle. -/
theorem segG_tail (x : Instance n) (ρ : Nat → BitVec w) (hn : 4 ≤ n)
    (hpow : 2 ^ (2 * n) ≤ 2 ^ w)
    (f : Nat → Nat) (r S : Nat) (hS : 3 ≤ S)
    (hfit : ∀ q, f q < 2 ^ w) (hf0 : f 0 = 2 * n + 23) (hf1 : f 1 = 1)
    (hf2 : f 2 = 0) (hf4 : f 4 = n + 2)
    (hblk : ∀ i', 1 ≤ i' → i' ≤ n + 1 → f (2 * n + 23 + i') = inF x i') :
    ∃ g, exec prog2 ρ S 83 r (memOf w f) = exec prog2 ρ (S - 3) 86 r (memOf w g) ∧
      (∀ q, g q < 2 ^ w) ∧ g 0 = 2 * n + 23 ∧ g 1 = 1 ∧ g 2 = 0 ∧
      g 7 = n ∧ g 8 = 2 * n + 23 ∧
      (∀ i', 1 ≤ i' → i' ≤ n + 1 → g (2 * n + 23 + i') = inF x i') := by
  have e83a : f 4 - f 1 = n + 1 := by rw [hf4, hf1]; omega
  have hle83 : f 1 ≤ f 4 := by rw [hf4, hf1]; omega
  have fitA : ∀ q, (up f 7 (n + 1)) q < 2 ^ w :=
    upFit hfit (pro_vfit hn hpow (by omega))
  have e84a : (up f 7 (n + 1)) 7 - (up f 7 (n + 1)) 1 = n := by
    rw [up_eq, up_ne (show (1:Nat) ≠ 7 by omega), hf1]
    omega
  have hle84 : (up f 7 (n + 1)) 1 ≤ (up f 7 (n + 1)) 7 := by
    rw [up_ne (show (1:Nat) ≠ 7 by omega), up_eq, hf1]
    omega
  have fitB : ∀ q, (up (up f 7 (n + 1)) 7 n) q < 2 ^ w :=
    upFit fitA (pro_vfit hn hpow (by omega))
  have e85 : (up (up f 7 (n + 1)) 7 n) 0 + (up (up f 7 (n + 1)) 7 n) 2
      = 2 * n + 23 := by
    rw [up_ne (show (0:Nat) ≠ 7 by omega), up_ne (show (0:Nat) ≠ 7 by omega), hf0,
      up_ne (show (2:Nat) ≠ 7 by omega), up_ne (show (2:Nat) ≠ 7 by omega), hf2]
  have fitC : ∀ q, (up (up (up f 7 (n + 1)) 7 n) 8 (2 * n + 23)) q < 2 ^ w :=
    upFit fitB (pro_vfit hn hpow (by omega))
  have g0 : (up (up (up f 7 (n + 1)) 7 n) 8 (2 * n + 23)) 0 = 2 * n + 23 := by
    rw [up_ne (show (0:Nat) ≠ 8 by omega), up_ne (show (0:Nat) ≠ 7 by omega),
      up_ne (show (0:Nat) ≠ 7 by omega), hf0]
  have g1 : (up (up (up f 7 (n + 1)) 7 n) 8 (2 * n + 23)) 1 = 1 := by
    rw [up_ne (show (1:Nat) ≠ 8 by omega), up_ne (show (1:Nat) ≠ 7 by omega),
      up_ne (show (1:Nat) ≠ 7 by omega), hf1]
  have g2 : (up (up (up f 7 (n + 1)) 7 n) 8 (2 * n + 23)) 2 = 0 := by
    rw [up_ne (show (2:Nat) ≠ 8 by omega), up_ne (show (2:Nat) ≠ 7 by omega),
      up_ne (show (2:Nat) ≠ 7 by omega), hf2]
  have g7 : (up (up (up f 7 (n + 1)) 7 n) 8 (2 * n + 23)) 7 = n := by
    rw [up_ne (show (7:Nat) ≠ 8 by omega), up_eq]
  have g8 : (up (up (up f 7 (n + 1)) 7 n) 8 (2 * n + 23)) 8 = 2 * n + 23 :=
    up_eq _ _ _
  have gblk : ∀ i', 1 ≤ i' → i' ≤ n + 1 →
      (up (up (up f 7 (n + 1)) 7 n) 8 (2 * n + 23)) (2 * n + 23 + i') = inF x i' := by
    intro i' h1 h2
    rw [up_ne (show 2 * n + 23 + i' ≠ 8 by omega),
      up_ne (show 2 * n + 23 + i' ≠ 7 by omega),
      up_ne (show 2 * n + 23 + i' ≠ 7 by omega)]
    exact hblk i' h1 h2
  refine ⟨up (up (up f 7 (n + 1)) 7 n) 8 (2 * n + 23), ?_, fitC, g0, g1, g2, g7, g8,
    gblk⟩
  rw [exec_sub_step (by omega) (show prog2.getD 83 Instr.reject = Instr.sub 7 4 1 by rfl)
      hfit hle83, e83a,
    exec_sub_step (by omega) (show prog2.getD 84 Instr.reject = Instr.sub 7 7 1 by rfl)
      fitA hle84, e84a,
    exec_add_step (by omega) (show prog2.getD 85 Instr.reject = Instr.add 8 0 2 by rfl),
    e85]
  simp only [Nat.sub_sub, Nat.reduceAdd]

/-- **Segment G** (pcs 65-85): LOOP1 (22 copy trips), LOOP2 setup, LOOP2
(peel `i = 22`, then `i = 23..n+1`), post tail — landing at the Phase A
entry (pc 86) with `[1]=1 [2]=0 [7]=n [8]=2n+23`, every address under
`3n+26+2·2^(n/2)` fitting, and the input block faithful at
`mem[2n+23+i] = instA x (i-1)` for `i = 1..n`.  Entry = pro_segF's output
plus `hmid` (untouched mid region; machine-true, see the seg G rider). -/
theorem pro_segG (x : Instance n) (ρ : Nat → BitVec w) (hn : 4 ≤ n)
    (hpow : 2 ^ (2 * n) ≤ 2 ^ w)
    (f : Nat → Nat) (r S : Nat) (hS : 171 + 6 * (n + 2 - 23) ≤ S)
    (hfit0 : ∀ q, f q < 2 ^ w) (hf0 : f 0 = 2 * n + 23) (hf1 : f 1 = 1)
    (hf2 : f 2 = 0) (hf3 : f 3 = 22) (hf4 : f 4 = 2 * n) (hf5 : f 5 = 0)
    (hscr : ∀ j, j + 1 ≤ 22 → j + 1 ≤ n + 1 → f (2 * n + j) = inF x (j + 1))
    (hp23 : ∀ q, 23 ≤ q → q ≤ n + 1 → f q = inF x q)
    (hmid : ∀ q, 8 ≤ q → q < 2 * n → f q = inF x q) :
    ∃ g c, c ≤ 171 + 6 * (n + 2 - 23) ∧
      exec prog2 ρ S 65 r (memOf w f) = exec prog2 ρ (S - c) 86 r (memOf w g) ∧
      (∀ q, g q < 2 ^ w) ∧ g 1 = 1 ∧ g 2 = 0 ∧ g 7 = n ∧ g 8 = 2 * n + 23 ∧
      (∀ c', c' ≤ 3 * n + 26 + 2 * 2 ^ (n / 2) → c' < 2 ^ w) ∧
      (∀ i, 1 ≤ i → i ≤ n → g (2 * n + 23 + i) = instA x (i - 1)) ∧
      g (2 * n + 23 + (n + 1)) = x.t := by
  have haddr : ∀ c', c' ≤ 3 * n + 26 + 2 * 2 ^ (n / 2) → c' < 2 ^ w :=
    fun c' hc' => Nat.lt_of_lt_of_le (by have := pro_addr_lt n hn; omega) hpow
  -- LOOP1: 22 trips, pcs 65→72
  obtain ⟨f1, hex1, f1fit, f1_0, f1_1, f1_2, f1_3, f1_5, f1cop, f1src, f1mid⟩ :=
    loop1_walk x ρ hn hpow 22 0 S f r (by omega) (by omega) (by omega) hfit0
      hf0 hf1 hf2 hf3 hf4 hf5
      (fun i' h1 h2 _ => absurd h1 (by omega)) hscr hp23 hmid
  have hex1' : exec prog2 ρ S 65 r (memOf w f)
      = exec prog2 ρ (S - 154) 72 r (memOf w f1) := by
    rw [hex1, show S - 7 * 22 = S - 154 from by omega]
  -- LOOP2 setup: pcs 72→77
  obtain ⟨f2, hex2, f2fit, f2_0, f2_1, f2_2, f2_4, f2_5, f2cop, f2src, f2mid⟩ :=
    loop2_setup x ρ hn hpow f1 r (S - 154) (by omega) f1fit f1_0 f1_1 f1_2
      f1_3 f1_5 f1cop f1src f1mid
  have hex2' : exec prog2 ρ (S - 154) 72 r (memOf w f1)
      = exec prog2 ρ (S - 159) 77 r (memOf w f2) := by
    rw [hex2, show S - 154 - 5 = S - 159 from by omega]
  -- LOOP2 peel trip (i = 22): pcs 77→82
  obtain ⟨f3, hex3, f3fit, f3_0, f3_1, f3_2, f3_4, f3_5, f3all, f3cop, f3src⟩ :=
    loop2_body x ρ hn hpow f2 22 r (S - 159) (by omega) (Or.inl rfl) (by omega)
      f2fit f2_0 f2_1 f2_2 f2_4 f2_5
      (fun h => by rw [f2mid 22 (by omega) (by omega)])
      (fun i' h1 h2 h3 => f2cop i' h1 (by omega) h3) f2cop f2src
  have hex3' : exec prog2 ρ (S - 159) 77 r (memOf w f2)
      = exec prog2 ρ (S - 164) 82 r (memOf w f3) := by
    rw [hex3, show S - 159 - 5 = S - 164 from by omega]
  by_cases hn22 : 23 < n + 2
  · -- n ≥ 22: blt back to 77, counter 23; while-walk, then tail
    have hblt : f3 5 < f3 4 := by rw [f3_5, f3_4]; omega
    obtain ⟨f4, c4, hc4, hex4, f4fit, f4_0, f4_1, f4_2, f4_4, f4all⟩ :=
      loop2_walk x ρ hn hpow (n + 2 - 23) 23 (S - 165) f3 r (by omega) (by omega)
        (by omega) (by omega) f3fit f3_0 f3_1 f3_2 f3_4 (by omega) f3all f3cop
        f3src
    obtain ⟨g, hext, gfit, g_0, g_1, g_2, g_7, g_8, gall⟩ :=
      segG_tail x ρ hn hpow f4 r ((S - 165) - c4) (by omega) f4fit f4_0 f4_1
        f4_2 f4_4 f4all
    refine ⟨g, 168 + c4, by omega, ?_, gfit, g_1, g_2, g_7, g_8, haddr, ?_, ?_⟩
    · rw [hex1', hex2', hex3',
        exec_blt_lt_step (by omega)
          (show prog2.getD 82 Instr.reject = Instr.blt 5 4 77 by rfl) f3fit hblt,
        show S - 164 - 1 = S - 165 from by omega, hex4, hext,
        show S - 165 - c4 - 3 = S - (168 + c4) from by omega]
    · intro i h1 h2
      rw [gall i h1 (by omega), inF_instA x i h1 h2]
    · rw [gall (n + 1) (by omega) (by omega), inF_t x]
  · -- n ≤ 21: blt falls through to 83; tail
    have hge : ¬ f3 5 < f3 4 := by rw [f3_5, f3_4]; omega
    obtain ⟨g, hext, gfit, g_0, g_1, g_2, g_7, g_8, gall⟩ :=
      segG_tail x ρ hn hpow f3 r (S - 165) (by omega) f3fit f3_0 f3_1 f3_2
        f3_4 (fun i' h1 h3 => f3all i' h1 (by omega) h3)
    refine ⟨g, 168, by omega, ?_, gfit, g_1, g_2, g_7, g_8, haddr, ?_, ?_⟩
    · rw [hex1', hex2', hex3',
        exec_blt_ge_step (by omega)
          (show prog2.getD 82 Instr.reject = Instr.blt 5 4 77 by rfl) f3fit hge,
        show S - 164 - 1 = S - 165 from by omega, hext,
        show S - 165 - 3 = S - 168 from by omega]
    · intro i h1 h2
      rw [gall i h1 (by omega), inF_instA x i h1 h2]
    · rw [gall (n + 1) (by omega) (by omega), inF_t x]

end ExecWalk

theorem prologue_to65 (x : Instance n) (ρ : Nat → BitVec w) (hn : 4 ≤ n)
    (hpow : 2 ^ (2 * n) ≤ 2 ^ w) (hif : ∀ q, inF x q < 2 ^ w)
    (r S : Nat) (hS : 65 ≤ S) :
    ∃ g, exec prog2 ρ S 0 r (memOf w (inF x))
      = exec prog2 ρ (S - 65) 65 r (memOf w g) ∧
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
      exec prog2 ρ S 0 r (memOf w (inF x)) = exec prog2 ρ (S - c) 86 r (memOf w g) ∧
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

end SubsetSum.MITM.P2Pro
