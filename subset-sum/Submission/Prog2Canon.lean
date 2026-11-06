import Submission.Prog2Layout
set_option autoImplicit true

/-!
# canon: pcs 148 → 161 (R2125607749 Lane 2)

`canon` canonicalizes `S₁` into `ARR1 = 3n+25` and records the base in
cell 22 (scanB's fixed `S₁` base).  Entry: `phaseA_exec`'s output contract
(the sorted first-half sums at `bd ∈ {ARR1, ARR2}`, `[11] = 2^h`).  The
`blt` at 152 dispatches: `bd = ARR1` falls through in 6 steps; `bd = ARR2`
runs the 6-instruction copy loop `H = 2^h` times (budget `6·2^h + 6`).
Output: `arrL f2 (3n+25) (2^(n/2)) = halfSums (instA x) (n/2)` —
UNCONDITIONALLY (the bd-disjunction is dead downstream), `[22] = 3n+25`,
all prologue-preserved registers and the relocated array intact.
-/

namespace SubsetSum.MITM

open BigOSpeedrun.SubsetSum SubsetSum.MITM.Spec

/-- canon's write region: registers 12/15/21 plus the ARR1 strip. -/
def CanReg (A1 H : Nat) (c : Nat) : Prop :=
  c = 12 ∨ c = 15 ∨ c = 21 ∨ (A1 ≤ c ∧ c < A1 + H)

/-- The copy loop (pc 155 → 161): `H − i` trips of 6 instructions,
copying `bd[i..H)` down to `A1[i..H)`.  Do-while: entered with `i < H`. -/
theorem canLoop_exec {w : Nat} (ρ : Nat → BitVec w) :
    ∀ (N H bd A1 : Nat) (sl : List Nat) (f : Nat → Nat) (i S r : Nat),
    sl.length = H →
    i < H → H - i ≤ N →
    f 12 = i → f 11 = H → f 18 = bd → f 20 = A1 → f 1 = 1 → f 2 = 0 →
    (∀ q, q < H → f (bd + q) = sl.getD q 0) →
    (∀ q, q < i → f (A1 + q) = sl.getD q 0) →
    (∀ q, f q < 2 ^ w) → A1 + H < 2 ^ w → bd + H < 2 ^ w →
    33 ≤ A1 → 33 ≤ bd → A1 + H ≤ bd →
    6 * (H - i) ≤ S →
    ∃ c f', c ≤ 6 * (H - i) ∧
      exec prog2 ρ S 155 r (memOf w f) = exec prog2 ρ (S - c) 161 r (memOf w f') ∧
      (∀ q, q < H → f' (A1 + q) = sl.getD q 0) ∧
      (∀ q, q < H → f' (bd + q) = sl.getD q 0) ∧
      f' 11 = H ∧ f' 18 = bd ∧ f' 20 = A1 ∧ f' 1 = 1 ∧ f' 2 = 0 ∧
      (∀ q, f' q < 2 ^ w) ∧ Pres (CanReg A1 H) f f' := by
  intro N
  induction N with
  | zero =>
    intro H bd A1 sl f i S r hsL hiH hN hf12 hf11 hf18 hf20 h1 h2 hsrc hcopy
      hfit hA1 hbd hA33 hb33 hdisj hS
    omega
  | succ N ih =>
    intro H bd A1 sl f i S r hsL hiH hN hf12 hf11 hf18 hf20 h1 h2 hsrc hcopy
      hfit hA1 hbd hA33 hb33 hdisj hS
    -- one body trip: 155..160
    have hbi : bd + i < 2 ^ w := by have := hbd; omega
    have hAi : A1 + i < 2 ^ w := by have := hA1; omega
    have hvi : sl.getD i 0 < 2 ^ w := by
      have e := hsrc i hiH
      rw [← e]
      exact hfit _
    have hi1 : i + 1 < 2 ^ w := by have := hfit 12; rw [hf12] at this; omega
    have f1f : ∀ q, (up f 21 (bd + i)) q < 2 ^ w := up_fit hfit hbi
    have f2f : ∀ q, (up (up f 21 (bd + i)) 15 (sl.getD i 0)) q < 2 ^ w :=
      up_fit f1f hvi
    have f3f : ∀ q, (up (up (up f 21 (bd + i)) 15 (sl.getD i 0)) 21 (A1 + i)) q < 2 ^ w :=
      up_fit f2f hAi
    have f4f : ∀ q, (up (up (up (up f 21 (bd + i)) 15 (sl.getD i 0)) 21 (A1 + i)) (A1 + i) (sl.getD i 0)) q < 2 ^ w :=
      up_fit f3f hvi
    have f5f : ∀ q, (up (up (up (up (up f 21 (bd + i)) 15 (sl.getD i 0)) 21 (A1 + i)) (A1 + i) (sl.getD i 0)) 12 (i + 1)) q < 2 ^ w :=
      up_fit f4f hi1
    -- register/address equations along the chain
    have e21a : (up f 21 (bd + i)) 21 = bd + i := up_eq _ _ _
    have e15 : f 15 = f 15 := rfl
    have eA1i : (up (up (up f 21 (bd + i)) 15 (sl.getD i 0)) 21 (A1 + i)) 21 = A1 + i := up_eq _ _ _
    have e12 : (up (up (up (up f 21 (bd + i)) 15 (sl.getD i 0)) 21 (A1 + i)) (A1 + i) (sl.getD i 0)) 12 = i := by
      rw [up_ne (show (12:Nat) ≠ A1 + i by omega),
        up_ne (show (12:Nat) ≠ 21 by omega),
        up_ne (show (12:Nat) ≠ 15 by omega),
        up_ne (show (12:Nat) ≠ 21 by omega), hf12]
    have e1 : (up (up (up (up f 21 (bd + i)) 15 (sl.getD i 0)) 21 (A1 + i)) (A1 + i) (sl.getD i 0)) 1 = 1 := by
      rw [up_ne (show (1:Nat) ≠ A1 + i by omega),
        up_ne (show (1:Nat) ≠ 21 by omega),
        up_ne (show (1:Nat) ≠ 15 by omega),
        up_ne (show (1:Nat) ≠ 21 by omega), h1]
    -- the shared 6-step body (155..160 lands on the blt decision)
    have hsteps : exec prog2 ρ S 155 r (memOf w f)
        = exec prog2 ρ (S - 5) 160 r
            (memOf w (up (up (up (up (up f 21 (bd + i)) 15 (sl.getD i 0)) 21 (A1 + i)) (A1 + i) (sl.getD i 0)) 12 (i + 1))) := by
      rw [exec_add_step (by omega)
            (show prog2.getD 155 Instr.reject = Instr.add 21 18 12 by rfl),
          show f 18 + f 12 = bd + i from by rw [hf18, hf12],
        exec_load_step (by omega)
            (show prog2.getD 156 Instr.reject = Instr.load 15 21 by rfl) f1f,
          up_eq, up_ne (show bd + i ≠ 21 by omega), hsrc i hiH,
        exec_add_step (by omega)
            (show prog2.getD 157 Instr.reject = Instr.add 21 20 12 by rfl),
          show (up (up f 21 (bd + i)) 15 (sl.getD i 0)) 20
              + (up (up f 21 (bd + i)) 15 (sl.getD i 0)) 12 = A1 + i from by
            rw [up_ne (show (20:Nat) ≠ 15 by omega),
              up_ne (show (20:Nat) ≠ 21 by omega), hf20,
              up_ne (show (12:Nat) ≠ 15 by omega),
              up_ne (show (12:Nat) ≠ 21 by omega), hf12],
        exec_store_step (by omega)
            (show prog2.getD 158 Instr.reject = Instr.store 21 15 by rfl) f3f,
          up_eq, up_ne (show (15:Nat) ≠ 21 by omega), up_eq,
        exec_add_step (by omega)
            (show prog2.getD 159 Instr.reject = Instr.add 12 12 1 by rfl),
          show (up (up (up (up f 21 (bd + i)) 15 (sl.getD i 0)) 21 (A1 + i)) (A1 + i) (sl.getD i 0)) 12
              + (up (up (up (up f 21 (bd + i)) 15 (sl.getD i 0)) 21 (A1 + i)) (A1 + i) (sl.getD i 0)) 1
              = i + 1 from by
            rw [e12, e1]]
      simp only [Nat.sub_sub, Nat.reduceAdd]
    -- facts about the post-body state
    have g12 : (up (up (up (up (up f 21 (bd + i)) 15 (sl.getD i 0)) 21 (A1 + i)) (A1 + i) (sl.getD i 0)) 12 (i + 1)) 12 = i + 1 := up_eq _ _ _
    have g11 : (up (up (up (up (up f 21 (bd + i)) 15 (sl.getD i 0)) 21 (A1 + i)) (A1 + i) (sl.getD i 0)) 12 (i + 1)) 11 = H := by
      rw [up_ne (show (11:Nat) ≠ 12 by omega),
        up_ne (show (11:Nat) ≠ A1 + i by omega),
        up_ne (show (11:Nat) ≠ 21 by omega),
        up_ne (show (11:Nat) ≠ 15 by omega),
        up_ne (show (11:Nat) ≠ 21 by omega), hf11]
    have g18 : (up (up (up (up (up f 21 (bd + i)) 15 (sl.getD i 0)) 21 (A1 + i)) (A1 + i) (sl.getD i 0)) 12 (i + 1)) 18 = bd := by
      rw [up_ne (show (18:Nat) ≠ 12 by omega),
        up_ne (show (18:Nat) ≠ A1 + i by omega),
        up_ne (show (18:Nat) ≠ 21 by omega),
        up_ne (show (18:Nat) ≠ 15 by omega),
        up_ne (show (18:Nat) ≠ 21 by omega), hf18]
    have g20 : (up (up (up (up (up f 21 (bd + i)) 15 (sl.getD i 0)) 21 (A1 + i)) (A1 + i) (sl.getD i 0)) 12 (i + 1)) 20 = A1 := by
      rw [up_ne (show (20:Nat) ≠ 12 by omega),
        up_ne (show (20:Nat) ≠ A1 + i by omega),
        up_ne (show (20:Nat) ≠ 21 by omega),
        up_ne (show (20:Nat) ≠ 15 by omega),
        up_ne (show (20:Nat) ≠ 21 by omega), hf20]
    have g1 : (up (up (up (up (up f 21 (bd + i)) 15 (sl.getD i 0)) 21 (A1 + i)) (A1 + i) (sl.getD i 0)) 12 (i + 1)) 1 = 1 := by
      rw [up_ne (show (1:Nat) ≠ 12 by omega),
        up_ne (show (1:Nat) ≠ A1 + i by omega),
        up_ne (show (1:Nat) ≠ 21 by omega),
        up_ne (show (1:Nat) ≠ 15 by omega),
        up_ne (show (1:Nat) ≠ 21 by omega), h1]
    have g2 : (up (up (up (up (up f 21 (bd + i)) 15 (sl.getD i 0)) 21 (A1 + i)) (A1 + i) (sl.getD i 0)) 12 (i + 1)) 2 = 0 := by
      rw [up_ne (show (2:Nat) ≠ 12 by omega),
        up_ne (show (2:Nat) ≠ A1 + i by omega),
        up_ne (show (2:Nat) ≠ 21 by omega),
        up_ne (show (2:Nat) ≠ 15 by omega),
        up_ne (show (2:Nat) ≠ 21 by omega), h2]
    have gsrc : ∀ q, q < H →
        (up (up (up (up (up f 21 (bd + i)) 15 (sl.getD i 0)) 21 (A1 + i)) (A1 + i) (sl.getD i 0)) 12 (i + 1)) (bd + q) = sl.getD q 0 := by
      intro q hq
      rw [up_ne (show bd + q ≠ 12 by omega),
        up_ne (show bd + q ≠ A1 + i by omega),
        up_ne (show bd + q ≠ 21 by omega),
        up_ne (show bd + q ≠ 15 by omega),
        up_ne (show bd + q ≠ 21 by omega),
        hsrc q hq]
    have gcopy : ∀ q, q < i + 1 →
        (up (up (up (up (up f 21 (bd + i)) 15 (sl.getD i 0)) 21 (A1 + i)) (A1 + i) (sl.getD i 0)) 12 (i + 1)) (A1 + q) = sl.getD q 0 := by
      intro q hq
      by_cases hqi : q < i
      · rw [up_ne (show A1 + q ≠ 12 by omega),
          up_ne (show A1 + q ≠ A1 + i by omega),
          up_ne (show A1 + q ≠ 21 by omega),
          up_ne (show A1 + q ≠ 15 by omega),
          up_ne (show A1 + q ≠ 21 by omega),
          hcopy q hqi]
      · have hqe : q = i := by omega
        rw [hqe, up_ne (show A1 + i ≠ 12 by omega), up_eq]
    have hbody : ∀ g,
        g = (up (up (up (up (up f 21 (bd + i)) 15 (sl.getD i 0)) 21 (A1 + i)) (A1 + i) (sl.getD i 0)) 12 (i + 1)) →
        Pres (CanReg A1 H) f g := by
      intro g hg
      subst hg
      exact pres_trans (pres_up (Or.inr (Or.inr (Or.inl rfl))))
        (pres_trans (pres_up (Or.inr (Or.inl rfl)))
        (pres_trans (pres_up (Or.inr (Or.inr (Or.inl rfl))))
        (pres_trans (pres_up (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))
        (pres_up (Or.inl rfl)))))
    by_cases hnext : i + 1 < H
    · have hlt : (up (up (up (up (up f 21 (bd + i)) 15 (sl.getD i 0)) 21 (A1 + i)) (A1 + i) (sl.getD i 0)) 12 (i + 1)) 12
          < (up (up (up (up (up f 21 (bd + i)) 15 (sl.getD i 0)) 21 (A1 + i)) (A1 + i) (sl.getD i 0)) 12 (i + 1)) 11 := by
        rw [g12, g11]
        exact hnext
      rw [hsteps, exec_blt_lt_step (by omega)
        (show prog2.getD 160 Instr.reject = Instr.blt 12 11 155 by rfl) f5f hlt]
      obtain ⟨c2, f2, hc2, hex2, hA2, hB2, h112, h182, h202, h12, h22, hfit2, hpres2⟩ :=
        ih H bd A1 sl
          (up (up (up (up (up f 21 (bd + i)) 15 (sl.getD i 0)) 21 (A1 + i)) (A1 + i) (sl.getD i 0)) 12 (i + 1))
          (i + 1) (S - 6) r hsL hnext (by omega)
          g12 g11 g18 g20 g1 g2 gsrc gcopy f5f hA1 hbd hA33 hb33 hdisj (by omega)
      refine ⟨6 + c2, f2, by omega, ?_, hA2, hB2, h112, h182, h202, h12, h22, hfit2, ?_⟩
      · have hS5 : S - 5 - 1 = S - 6 := by omega
        have hS6 : S - 6 - c2 = S - (6 + c2) := by omega
        rw [hS5, hex2, hS6]
      · exact pres_trans (hbody _ rfl) hpres2
    · have hge : ¬ ((up (up (up (up (up f 21 (bd + i)) 15 (sl.getD i 0)) 21 (A1 + i)) (A1 + i) (sl.getD i 0)) 12 (i + 1)) 12
          < (up (up (up (up (up f 21 (bd + i)) 15 (sl.getD i 0)) 21 (A1 + i)) (A1 + i) (sl.getD i 0)) 12 (i + 1)) 11) := by
        rw [g12, g11]
        omega
      have hiH : i + 1 = H := by omega
      refine ⟨6, (up (up (up (up (up f 21 (bd + i)) 15 (sl.getD i 0)) 21 (A1 + i)) (A1 + i) (sl.getD i 0)) 12 (i + 1)),
        by omega, ?_, ?_, gsrc, g11, g18, g20, g1, g2, f5f, hbody _ rfl⟩
      · rw [hsteps, exec_blt_ge_step (by omega)
          (show prog2.getD 160 Instr.reject = Instr.blt 12 11 155 by rfl) f5f hge]
        simp only [Nat.sub_sub, Nat.reduceAdd]
      · intro q hq
        exact gcopy q (by omega)

/-- The canon segment (pcs 148 → 161), consuming `phaseA_exec`'s output
contract and killing the `bd`-disjunction. -/
theorem canon_exec {w n : Nat} (ρ : Nat → BitVec w) {x : Instance n}
    (hn : 4 ≤ n)
    (f1 : Nat → Nat) (bd r S : Nat)
    (hfit : ∀ q, f1 q < 2 ^ w)
    (h1 : f1 1 = 1) (h2 : f1 2 = 0) (h7 : f1 7 = n) (h8 : f1 8 = 2 * n + 23)
    (h9 : f1 9 = n / 2) (h11 : f1 11 = 2 ^ (n / 2))
    (h18 : f1 18 = bd)
    (hbd : bd = 3 * n + 25 ∨ bd = 3 * n + 25 + 2 ^ (n / 2) + 1)
    (harr : arrL f1 bd (2 ^ (n / 2)) = halfSums (instA x) (n / 2))
    (hrel : ∀ i, 1 ≤ i → i ≤ n → f1 (2 * n + 23 + i) = instA x (i - 1))
    (hft : f1 (2 * n + 23 + (n + 1)) = x.t)
    (haddr : ∀ c, c ≤ 3 * n + 27 + 2 ^ (n / 2) + 2 * 2 ^ (n - n / 2) → c < 2 ^ w)
    (hS : 6 * 2 ^ (n / 2) + 6 ≤ S) :
    ∃ c f2, c ≤ 6 * 2 ^ (n / 2) + 6 ∧
      exec prog2 ρ S 148 r (memOf w f1) = exec prog2 ρ (S - c) 161 r (memOf w f2) ∧
      f2 22 = 3 * n + 25 ∧ f2 11 = 2 ^ (n / 2) ∧ f2 9 = n / 2 ∧
      f2 7 = n ∧ f2 8 = 2 * n + 23 ∧ f2 1 = 1 ∧ f2 2 = 0 ∧
      arrL f2 (3 * n + 25) (2 ^ (n / 2)) = halfSums (instA x) (n / 2) ∧
      (∀ i, 1 ≤ i → i ≤ n → f2 (2 * n + 23 + i) = instA x (i - 1)) ∧
      f2 (2 * n + 23 + (n + 1)) = x.t ∧
      (∀ q, f2 q < 2 ^ w) := by
  have h2p : 3 * n + 23 < 2 ^ w := haddr _ (by omega)
  have h2p' : 3 * n + 24 < 2 ^ w := haddr _ (by omega)
  have h2p'' : 3 * n + 25 < 2 ^ w := haddr _ (by omega)
  have e148 : f1 8 + f1 7 = 3 * n + 23 := by rw [h8, h7]; omega
  have g1f : ∀ q, (up f1 20 (3 * n + 23)) q < 2 ^ w := up_fit hfit h2p
  have e149 : (up f1 20 (3 * n + 23)) 20 + (up f1 20 (3 * n + 23)) 1 = 3 * n + 24 := by
    rw [up_eq, up_ne (show (1:Nat) ≠ 20 by omega), h1]
  have g2f : ∀ q, (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) q < 2 ^ w := up_fit g1f h2p'
  have e150 : (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20
      + (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 1 = 3 * n + 25 := by
    rw [up_eq, up_ne (show (1:Nat) ≠ 20 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega), h1]
  have g3f : ∀ q, (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) q < 2 ^ w :=
    up_fit g2f h2p''
  have e151 : (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) 20
      + (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) 2 = 3 * n + 25 := by
    rw [up_eq, up_ne (show (2:Nat) ≠ 20 by omega),
      up_ne (show (2:Nat) ≠ 20 by omega),
      up_ne (show (2:Nat) ≠ 20 by omega), h2, Nat.add_zero]
  have g4f : ∀ q, (up (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) 22 (3 * n + 25)) q < 2 ^ w :=
    up_fit g3f h2p''
  -- the shared 4-step prefix 148..151, then the blt at 152
  have hpre : exec prog2 ρ S 148 r (memOf w f1)
      = exec prog2 ρ (S - 4) 152 r
          (memOf w (up (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) 22 (3 * n + 25))) := by
    rw [exec_add_step (by omega)
          (show prog2.getD 148 Instr.reject = Instr.add 20 8 7 by rfl), e148,
        exec_add_step (by omega)
          (show prog2.getD 149 Instr.reject = Instr.add 20 20 1 by rfl), e149,
        exec_add_step (by omega)
          (show prog2.getD 150 Instr.reject = Instr.add 20 20 1 by rfl), e150,
        exec_add_step (by omega)
          (show prog2.getD 151 Instr.reject = Instr.add 22 20 2 by rfl), e151]
    simp only [Nat.sub_sub, Nat.reduceAdd]
  have g20 : (up (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) 22 (3 * n + 25)) 20 = 3 * n + 25 := by
    rw [up_ne (show (20:Nat) ≠ 22 by omega), up_eq]
  have g18 : (up (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) 22 (3 * n + 25)) 18 = bd := by
    rw [up_ne (show (18:Nat) ≠ 22 by omega),
      up_ne (show (18:Nat) ≠ 20 by omega),
      up_ne (show (18:Nat) ≠ 20 by omega),
      up_ne (show (18:Nat) ≠ 20 by omega), h18]
  have g2 : (up (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) 22 (3 * n + 25)) 2 = 0 := by
    rw [up_ne (show (2:Nat) ≠ 22 by omega),
      up_ne (show (2:Nat) ≠ 20 by omega),
      up_ne (show (2:Nat) ≠ 20 by omega),
      up_ne (show (2:Nat) ≠ 20 by omega), h2]
  have g1 : (up (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) 22 (3 * n + 25)) 1 = 1 := by
    rw [up_ne (show (1:Nat) ≠ 22 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega), h1]
  have g22 : (up (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) 22 (3 * n + 25)) 22 = 3 * n + 25 :=
    up_eq _ _ _
  have g11 : (up (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) 22 (3 * n + 25)) 11 = 2 ^ (n / 2) := by
    rw [up_ne (show (11:Nat) ≠ 22 by omega),
      up_ne (show (11:Nat) ≠ 20 by omega),
      up_ne (show (11:Nat) ≠ 20 by omega),
      up_ne (show (11:Nat) ≠ 20 by omega), h11]
  have g9 : (up (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) 22 (3 * n + 25)) 9 = n / 2 := by
    rw [up_ne (show (9:Nat) ≠ 22 by omega),
      up_ne (show (9:Nat) ≠ 20 by omega),
      up_ne (show (9:Nat) ≠ 20 by omega),
      up_ne (show (9:Nat) ≠ 20 by omega), h9]
  have g7 : (up (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) 22 (3 * n + 25)) 7 = n := by
    rw [up_ne (show (7:Nat) ≠ 22 by omega),
      up_ne (show (7:Nat) ≠ 20 by omega),
      up_ne (show (7:Nat) ≠ 20 by omega),
      up_ne (show (7:Nat) ≠ 20 by omega), h7]
  have g8 : (up (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) 22 (3 * n + 25)) 8 = 2 * n + 23 := by
    rw [up_ne (show (8:Nat) ≠ 22 by omega),
      up_ne (show (8:Nat) ≠ 20 by omega),
      up_ne (show (8:Nat) ≠ 20 by omega),
      up_ne (show (8:Nat) ≠ 20 by omega), h8]
  -- cells the g4 prefix never touches: the relocated array and t
  have gmid : ∀ i, (up (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) 22 (3 * n + 25)) (2 * n + 23 + i)
      = f1 (2 * n + 23 + i) := by
    intro i
    rw [up_ne (show 2 * n + 23 + i ≠ 22 by omega),
      up_ne (show 2 * n + 23 + i ≠ 20 by omega),
      up_ne (show 2 * n + 23 + i ≠ 20 by omega),
      up_ne (show 2 * n + 23 + i ≠ 20 by omega)]
  rcases hbd with hbdA | hbdB
  · -- Case A: bd = ARR1 — no copy, 6 steps through the jmp at 153
    have hge : ¬ ((up (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) 22 (3 * n + 25)) 20
        < (up (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) 22 (3 * n + 25)) 18) := by
      rw [g20, g18, hbdA]
      omega
    have hlt2 : (up (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) 22 (3 * n + 25)) 2
        < (up (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) 22 (3 * n + 25)) 1 := by
      rw [g2, g1]; omega
    refine ⟨6, (up (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) 22 (3 * n + 25)),
      by omega, ?_, g22, g11, g9, g7, g8, g1, g2, ?_, ?_, ?_, g4f⟩
    · rw [hpre,
        exec_blt_ge_step (by omega)
          (show prog2.getD 152 Instr.reject = Instr.blt 20 18 154 by rfl) g4f hge,
        exec_blt_lt_step (by omega)
          (show prog2.getD 153 Instr.reject = Instr.blt 2 1 161 by rfl) g4f hlt2]
      simp only [Nat.sub_sub, Nat.reduceAdd]
    · -- arrL: g4 agrees with f1 on the ARR1 strip, and bd = ARR1
      have hcong : arrL (up (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) 22 (3 * n + 25))
          (3 * n + 25) (2 ^ (n / 2)) = arrL f1 (3 * n + 25) (2 ^ (n / 2)) := by
        rw [arrL_up_out (fun q _ => show (22:Nat) ≠ 3 * n + 25 + q by omega),
          arrL_up_out (fun q _ => show (20:Nat) ≠ 3 * n + 25 + q by omega),
          arrL_up_out (fun q _ => show (20:Nat) ≠ 3 * n + 25 + q by omega),
          arrL_up_out (fun q _ => show (20:Nat) ≠ 3 * n + 25 + q by omega)]
      rw [hcong, ← hbdA]
      exact harr
    · intro i hi1 hin
      rw [gmid i, hrel i hi1 hin]
    · rw [gmid (n + 1), hft]
  · -- Case B: bd = ARR2 — copy loop, 6·H + 6 steps
    have hlt : (up (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) 22 (3 * n + 25)) 20
        < (up (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) 22 (3 * n + 25)) 18 := by
      rw [g20, g18, hbdB]
      have hpos : 0 < 2 ^ (n / 2) := by
        have h : (1:Nat) ≤ 2 ^ (n / 2) := Nat.one_le_two_pow
        omega
      omega
    rw [hpre, exec_blt_lt_step (by omega)
      (show prog2.getD 152 Instr.reject = Instr.blt 20 18 154 by rfl) g4f hlt]
    -- pc 154: i := 0
    let g5 : Nat → Nat := up (up (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) 22 (3 * n + 25)) 12 0
    have hsub : exec prog2 ρ (S - 4 - 1) 154 r
        (memOf w (up (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) 22 (3 * n + 25)))
        = exec prog2 ρ (S - 6) 155 r (memOf w g5) := by
      rw [exec_sub_step (by omega)
        (show prog2.getD 154 Instr.reject = Instr.sub 12 12 12 by rfl) g4f (Nat.le_refl _),
        Nat.sub_self, show S - 4 - 1 - 1 = S - 6 from by omega]
    rw [hsub]
    have g5f : ∀ q, g5 q < 2 ^ w := by
      show ∀ q, (up (up (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) 22 (3 * n + 25)) 12 0) q < 2 ^ w
      exact up_fit g4f (by
        have h : (0:Nat) < 2 ^ w := Nat.one_le_two_pow
        omega)
    have g512 : g5 12 = 0 := by
      show (up (up (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) 22 (3 * n + 25)) 12 0) 12 = 0
      exact up_eq _ _ _
    have g511 : g5 11 = 2 ^ (n / 2) := by
      show (up (up (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) 22 (3 * n + 25)) 12 0) 11 = 2 ^ (n / 2)
      rw [up_ne (show (11:Nat) ≠ 12 by omega), g11]
    have g518 : g5 18 = 3 * n + 25 + 2 ^ (n / 2) + 1 := by
      show (up (up (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) 22 (3 * n + 25)) 12 0) 18 = 3 * n + 25 + 2 ^ (n / 2) + 1
      rw [up_ne (show (18:Nat) ≠ 12 by omega), g18, hbdB]
    have g520 : g5 20 = 3 * n + 25 := by
      show (up (up (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) 22 (3 * n + 25)) 12 0) 20 = 3 * n + 25
      rw [up_ne (show (20:Nat) ≠ 12 by omega), g20]
    have g51 : g5 1 = 1 := by
      show (up (up (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) 22 (3 * n + 25)) 12 0) 1 = 1
      rw [up_ne (show (1:Nat) ≠ 12 by omega), g1]
    have g52 : g5 2 = 0 := by
      show (up (up (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) 22 (3 * n + 25)) 12 0) 2 = 0
      rw [up_ne (show (2:Nat) ≠ 12 by omega), g2]
    have g5src : ∀ q, q < 2 ^ (n / 2) → g5 (3 * n + 25 + 2 ^ (n / 2) + 1 + q)
        = (arrL g5 (3 * n + 25 + 2 ^ (n / 2) + 1) (2 ^ (n / 2))).getD q 0 := by
      intro q hq
      rw [getD_arrL hq]
    have g522 : g5 22 = 3 * n + 25 := by
      show (up (up (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) 22 (3 * n + 25)) 12 0) 22 = 3 * n + 25
      rw [up_ne (show (22:Nat) ≠ 12 by omega), g22]
    have g59 : g5 9 = n / 2 := by
      show (up (up (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) 22 (3 * n + 25)) 12 0) 9 = n / 2
      rw [up_ne (show (9:Nat) ≠ 12 by omega), g9]
    have g57 : g5 7 = n := by
      show (up (up (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) 22 (3 * n + 25)) 12 0) 7 = n
      rw [up_ne (show (7:Nat) ≠ 12 by omega), g7]
    have g58 : g5 8 = 2 * n + 23 := by
      show (up (up (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) 22 (3 * n + 25)) 12 0) 8 = 2 * n + 23
      rw [up_ne (show (8:Nat) ≠ 12 by omega), g8]
    have g5mid : ∀ i, g5 (2 * n + 23 + i) = f1 (2 * n + 23 + i) := by
      intro i
      show (up (up (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) 22 (3 * n + 25)) 12 0) (2 * n + 23 + i) = f1 (2 * n + 23 + i)
      rw [up_ne (show 2 * n + 23 + i ≠ 12 by omega), gmid i]
    obtain ⟨c2, f2, hc2, hex2, hA2, hB2, h112, h182, h202, h12, h22, hfit2, hpres2⟩ :=
      canLoop_exec ρ (2 ^ (n / 2)) (2 ^ (n / 2)) (3 * n + 25 + 2 ^ (n / 2) + 1) (3 * n + 25)
        (arrL g5 (3 * n + 25 + 2 ^ (n / 2) + 1) (2 ^ (n / 2))) g5 0 (S - 6) r
        (by simp [arrL])
        (by have hpp : (1:Nat) ≤ 2 ^ (n / 2) := Nat.one_le_two_pow; omega)
        (by omega)
        g512 g511 g518 g520 g51 g52 g5src (by omega) g5f
        (haddr _ (by
          have hpp : 2 ^ (n / 2) ≤ 2 ^ (n - n / 2) :=
            Nat.pow_le_pow_right (n := 2) (by omega) (by omega)
          omega))
        (haddr _ (by
          have hpp : 2 ^ (n / 2) ≤ 2 ^ (n - n / 2) :=
            Nat.pow_le_pow_right (n := 2) (by omega) (by omega)
          omega))
        (by omega) (by omega) (by omega)
        (by omega)
    refine ⟨6 + c2, f2, ?_, ?_, ?_, h112, ?_, ?_, ?_, h12, h22, ?_, ?_, ?_, hfit2⟩
    · omega
    · have hSc : S - 6 - c2 = S - (6 + c2) := by omega
      rw [hex2, hSc]
    · -- [22] = ARR1 survives the loop (22 ∉ CanReg) and equals 3n+25
      have h22c : ¬ CanReg (3 * n + 25) (2 ^ (n / 2)) 22 := by
        intro hc
        rcases hc with h | h | h | ⟨h1', h2'⟩ <;> omega
      have e22 : f2 22 = g5 22 := hpres2 22 h22c
      rw [e22, g522]
    · -- [9] = n/2 survives
      have h9c : ¬ CanReg (3 * n + 25) (2 ^ (n / 2)) 9 := by
        intro hc
        rcases hc with h | h | h | ⟨h1', h2'⟩ <;> omega
      have e9 : f2 9 = g5 9 := hpres2 9 h9c
      rw [e9, g59]
    · have h7c : ¬ CanReg (3 * n + 25) (2 ^ (n / 2)) 7 := by
        intro hc
        rcases hc with h | h | h | ⟨h1', h2'⟩ <;> omega
      have e7 : f2 7 = g5 7 := hpres2 7 h7c
      rw [e7, g57]
    · have h8c : ¬ CanReg (3 * n + 25) (2 ^ (n / 2)) 8 := by
        intro hc
        rcases hc with h | h | h | ⟨h1', h2'⟩ <;> omega
      have e8 : f2 8 = g5 8 := hpres2 8 h8c
      rw [e8, g58]
    · -- the arrL contract: f2's ARR1 strip = g5's bd strip = f1's bd strip = halfSums
      have hcong : arrL f2 (3 * n + 25) (2 ^ (n / 2))
          = arrL g5 (3 * n + 25 + 2 ^ (n / 2) + 1) (2 ^ (n / 2)) := by
        unfold arrL
        refine List.map_congr_left (fun q hq => ?_)
        have hq' : q < 2 ^ (n / 2) := List.mem_range.mp hq
        show f2 (3 * n + 25 + q) = g5 (3 * n + 25 + 2 ^ (n / 2) + 1 + q)
        rw [hA2 q hq', getD_arrL hq']
      have hup1 : arrL g5 (3 * n + 25 + 2 ^ (n / 2) + 1) (2 ^ (n / 2))
          = arrL (up (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) 22 (3 * n + 25))
              (3 * n + 25 + 2 ^ (n / 2) + 1) (2 ^ (n / 2)) :=
        arrL_up_out (fun q _ => show (12:Nat) ≠ 3 * n + 25 + 2 ^ (n / 2) + 1 + q by omega)
      have hup2 : arrL (up (up (up (up f1 20 (3 * n + 23)) 20 (3 * n + 24)) 20 (3 * n + 25)) 22 (3 * n + 25))
              (3 * n + 25 + 2 ^ (n / 2) + 1) (2 ^ (n / 2))
          = arrL f1 (3 * n + 25 + 2 ^ (n / 2) + 1) (2 ^ (n / 2)) := by
        rw [arrL_up_out (fun q _ => show (22:Nat) ≠ 3 * n + 25 + 2 ^ (n / 2) + 1 + q by omega),
          arrL_up_out (fun q _ => show (20:Nat) ≠ 3 * n + 25 + 2 ^ (n / 2) + 1 + q by omega),
          arrL_up_out (fun q _ => show (20:Nat) ≠ 3 * n + 25 + 2 ^ (n / 2) + 1 + q by omega),
          arrL_up_out (fun q _ => show (20:Nat) ≠ 3 * n + 25 + 2 ^ (n / 2) + 1 + q by omega)]
      rw [hcong, hup1, hup2, ← hbdB]
      exact harr
    · intro i hi1 hin
      have hc : ¬ CanReg (3 * n + 25) (2 ^ (n / 2)) (2 * n + 23 + i) := by
        intro hx
        rcases hx with h | h | h | ⟨h1', h2'⟩ <;> omega
      have e : f2 (2 * n + 23 + i) = g5 (2 * n + 23 + i) := hpres2 _ hc
      rw [e, g5mid i, hrel i hi1 hin]
    · have hc : ¬ CanReg (3 * n + 25) (2 ^ (n / 2)) (2 * n + 23 + (n + 1)) := by
        intro hx
        rcases hx with h | h | h | ⟨h1', h2'⟩ <;> omega
      have e : f2 (2 * n + 23 + (n + 1)) = g5 (2 * n + 23 + (n + 1)) := hpres2 _ hc
      rw [e, g5mid (n + 1), hft]

end SubsetSum.MITM
