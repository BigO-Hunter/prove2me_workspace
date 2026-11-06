import Submission.Prog2Layout
import Submission.Prog2Canon
set_option autoImplicit true

/-!
# phaseA2: the second-half merge, pcs 161 → 224 (R2125607749 Lane 2)

phaseA2 runs Phase A's doubling-merge machine on the second half
`a_{h+1}..a_n` (`m = n − h` elements, `h = n/2`), producing sorted
`S₂ = halfSums (instA2 x h) m` (`2^m` values) at base `B2`/`B3`
(`B2 = 3n+26+2^h` = the old ARR2 slot, `B3 = B2 + 2^m + 1`).

§1 is the scripted port of PhaseA.lean's three loop drivers
(`diLoop_exec`, `djLoop_exec`, `merge_exec`) into
`namespace SubsetSum.MITM.P2M` at the re-based pcs (LMERGE2=179 …
LSWAP2=217 — instruction-for-instruction identical to phaseA's
103…141 per prog2_dump.txt, jump targets included).  §2 (hand-written)
adapts the round driver: `init2_exec` (161–172), `lswap2_exec` (the
LSWAP tail reading `[4] = m` instead of `[9] = h` at pc 222),
`round2_exec` (173→223), `lround2_exec` (all m rounds, 173→224) and
`phaseA2_exec` (161→224, the segment contract canon_exec's output
feeds and scanB_exec consumes).
-/

namespace SubsetSum.MITM.P2M

open BigOSpeedrun.SubsetSum SubsetSum.MITM.Spec

/-! ## §1. The merge loops at re-based pcs (scripted port) -/

/-! ## §4. The merge loops -/

/-- `getD` of a `(+ak)`-shifted map. -/
theorem getD_map_add (sl : List Nat) (ak : Nat) (j : Nat) (hj : j < sl.length) :
    (sl.map (fun z => z + ak)).getD j 0 = sl.getD j 0 + ak := by
  induction sl generalizing j with
  | nil => exact absurd hj (by simp)
  | cons a t ih =>
    cases j with
    | zero => rfl
    | succ j =>
      rw [List.getD_cons_succ, List.map_cons, List.getD_cons_succ]
      apply ih
      simpa using hj

/-- The merge-loop write region. -/
def MReg (d L : Nat) (c : Nat) : Prop :=
  c = 12 ∨ c = 13 ∨ c = 14 ∨ c = 15 ∨ c = 16 ∨ c = 20 ∨ c = 21 ∨ (d ≤ c ∧ c < d + 2 * L)

/-- `getD i` of a list is a member when `i < length`. -/
theorem mem_getD {l : List Nat} {i : Nat} (h : i < l.length) : l.getD i 0 ∈ l := by
  induction l generalizing i with
  | nil => exact absurd h (by simp)
  | cons a t ihl =>
    cases i with
    | zero => simp
    | succ i => exact List.mem_cons_of_mem _ (ihl (by simpa using h))

/-- Array view ignores register writes below the base. -/
theorem arrL_up_regs {f : Nat → Nat} {d L c v : Nat} (hd : d + 2 * L ≤ c ∨ c < d)
    (hfit : ∀ q, f q < 2 ^ w) : True := trivial

theorem MReg_dst {d L : Nat} {c : Nat} (h1 : d ≤ c) (h2 : c < d + 2 * L) :
    MReg d L c := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩))))))

/-- Drain-i body loop (pc 201 → 217). -/
theorem diLoop_exec_m2 {w : Nat} (ρ : Nat → BitVec w) :
    ∀ (N L b d : Nat) (sl out : List Nat) (f : Nat → Nat) (i wq S r : Nat),
    sl.length = L →
    i < L → wq = L + i → f 12 = i → f 14 = wq → f 11 = L →
    f 18 = b → f 19 = d → f 1 = 1 → f 2 = 0 →
    (∀ q, q < L → f (b + q) = sl.getD q 0) →
    (∀ v ∈ sl, v < 2 ^ w) →
    (out.take wq = (arrL f d (2 * L)).take wq) →
    out.drop wq = sl.drop i →
    (∀ q, f q < 2 ^ w) → b + L < 2 ^ w → d + 2 * L < 2 ^ w → 2 * L < 2 ^ w →
    33 ≤ b → 33 ≤ d → (∀ p q, p < 2 * L → q < L → d + p ≠ b + q) →
    L - i ≤ N → 8 * N + 9 ≤ S →
    ∃ c f', c ≤ 8 * N + 9 ∧
      exec prog2 ρ S 201 r (memOf w f) = exec prog2 ρ (S - c) 217 r (memOf w f') ∧
      arrL f' d (2 * L) = out ∧ f' 12 = L ∧ f' 14 = 2 * L ∧
      (∀ q, f' q < 2 ^ w) ∧ Pres (MReg d L) f f' := by
  intro N
  induction N with
  | zero =>
    intro L b d sl out f i wq S r hsL hiL hwi hf12 hf14 hf11 hf18 hf19 h1 h2
      hsrc hvfit htake hdrop hfit hbL hdL h2L hb33 hd33 hdisj hN hS
    omega
  | succ N ih =>
    intro L b d sl out f i wq S r hsL hiL hwi hf12 hf14 hf11 hf18 hf19 h1 h2
      hsrc hvfit htake hdrop hfit hbL hdL h2L hb33 hd33 hdisj hN hS
    have hvsl : sl.getD i 0 < 2 ^ w := hvfit _ (mem_getD (by omega))
    have fi1 : ∀ q, (up f 20 (b + i)) q < 2 ^ w := up_fit hfit (by have := hbL; omega)
    have fi2 : ∀ q, (up (up f 20 (b + i)) 15 (sl.getD i 0)) q < 2 ^ w := up_fit fi1 (by omega)
    have fi3 : ∀ q, (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) q < 2 ^ w := up_fit fi2 (by have := hdL; omega)
    have fi4 : ∀ q, (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) q < 2 ^ w := up_fit fi3 (by omega)
    have fi5 : ∀ q, (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) q < 2 ^ w := up_fit fi4 (by omega)
    have fi6 : ∀ q, (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) q < 2 ^ w := up_fit fi5 (by omega)
    -- array views
    have hA2 : arrL (up (up f 20 (b + i)) 15 (sl.getD i 0)) d (2 * L) = arrL f d (2 * L) := by
      rw [show arrL (up (up f 20 (b + i)) 15 (sl.getD i 0)) d (2 * L) = arrL (up f 20 (b + i)) d (2 * L) from
          arrL_up_out (fun q _ => show (15:Nat) ≠ d + q by omega),
        show arrL (up f 20 (b + i)) d (2 * L) = arrL f d (2 * L) from
          arrL_up_out (fun q _ => show (20:Nat) ≠ d + q by omega)]
    have hA3 : arrL (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) d (2 * L) = arrL f d (2 * L) := by
      rw [show arrL (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) d (2 * L) = arrL (up (up f 20 (b + i)) 15 (sl.getD i 0)) d (2 * L) from
          arrL_up_out (fun q _ => show (21:Nat) ≠ d + q by omega), hA2]
    have hA6 : arrL (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) d (2 * L) = arrL (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) d (2 * L) := by
      rw [show arrL (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) d (2 * L) = arrL (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) d (2 * L) from
          arrL_up_out (fun q _ => show (14:Nat) ≠ d + q by omega),
        show arrL (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) d (2 * L) = arrL (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) d (2 * L) from
          arrL_up_out (fun q _ => show (12:Nat) ≠ d + q by omega)]
    have hleno : out.length = 2 * L := by
      have h1l := List.length_drop (l := out) (i := wq)
      rw [hdrop, List.length_drop (l := sl) (i := i)] at h1l
      omega
    -- list facts
    have hisl : i < sl.length := by omega
    have hwqo : wq < out.length := by omega
    have hwq2L : wq < 2 * L := by omega
    have htake1 : out.take (wq + 1) = (arrL (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) d (2 * L)).take (wq + 1) := by
      rw [hA6, arrL_take_up hwq2L, hA3, ← htake, takeSucc hwqo]
      congr 1
      rw [← getDDrop, hdrop, dropCons hisl]
      simp
    have hdrop1 : out.drop (wq + 1) = sl.drop (i + 1) := by
      rw [dropSucc, hdrop, dropCons hisl]
      simp
    -- G6 register facts
    have e12g : (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 12 = i + 1 := by
      rw [up_ne (show (12:Nat) ≠ 14 by omega), up_eq]
    have e14g : (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 14 = wq + 1 := up_eq _ _ _
    have e11g : (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 11 = L := by rw [up_ne (show (11:Nat) ≠ 14 by omega), up_ne (show (11:Nat) ≠ 12 by omega), up_ne (show (11:Nat) ≠ d + wq by omega), up_ne (show (11:Nat) ≠ 21 by omega), up_ne (show (11:Nat) ≠ 15 by omega), up_ne (show (11:Nat) ≠ 20 by omega), hf11]
    have e18g : (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 18 = b := by rw [up_ne (show (18:Nat) ≠ 14 by omega), up_ne (show (18:Nat) ≠ 12 by omega), up_ne (show (18:Nat) ≠ d + wq by omega), up_ne (show (18:Nat) ≠ 21 by omega), up_ne (show (18:Nat) ≠ 15 by omega), up_ne (show (18:Nat) ≠ 20 by omega), hf18]
    have e19g : (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 19 = d := by rw [up_ne (show (19:Nat) ≠ 14 by omega), up_ne (show (19:Nat) ≠ 12 by omega), up_ne (show (19:Nat) ≠ d + wq by omega), up_ne (show (19:Nat) ≠ 21 by omega), up_ne (show (19:Nat) ≠ 15 by omega), up_ne (show (19:Nat) ≠ 20 by omega), hf19]
    have e1g : (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 1 = 1 := by rw [up_ne (show (1:Nat) ≠ 14 by omega), up_ne (show (1:Nat) ≠ 12 by omega), up_ne (show (1:Nat) ≠ d + wq by omega), up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (1:Nat) ≠ 15 by omega), up_ne (show (1:Nat) ≠ 20 by omega), h1]
    have e2g : (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 2 = 0 := by rw [up_ne (show (2:Nat) ≠ 14 by omega), up_ne (show (2:Nat) ≠ 12 by omega), up_ne (show (2:Nat) ≠ d + wq by omega), up_ne (show (2:Nat) ≠ 21 by omega), up_ne (show (2:Nat) ≠ 15 by omega), up_ne (show (2:Nat) ≠ 20 by omega), h2]
    have esrcg : ∀ q, q < L → (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) (b + q) = sl.getD q 0 := by
      intro q hq
      rw [up_ne (show b + q ≠ 14 by omega),
        up_ne (show b + q ≠ 12 by omega),
        up_ne (Ne.symm (hdisj wq q (by omega) hq)),
        up_ne (show b + q ≠ 21 by omega),
        up_ne (show b + q ≠ 15 by omega), up_ne (show b + q ≠ 20 by omega)]
      exact hsrc q hq
    -- the shared 7-step prefix (201..206) with inline normalization
    have hsteps : exec prog2 ρ S 201 r (memOf w f)
        = exec prog2 ρ (S - 6) 207 r (memOf w (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1))) := by
      rw [exec_add_step (by omega)
          (show prog2.getD 201 Instr.reject = Instr.add 20 18 12 by rfl),
          show f 18 + f 12 = b + i from by rw [hf18, hf12],
        exec_load_step (by omega)
          (show prog2.getD 202 Instr.reject = Instr.load 15 20 by rfl) fi1,
          up_eq, up_ne (show b + i ≠ 20 by omega), hsrc i hiL,
        exec_add_step (by omega)
          (show prog2.getD 203 Instr.reject = Instr.add 21 19 14 by rfl),
          show (up (up f 20 (b + i)) 15 (sl.getD i 0)) 19 + (up (up f 20 (b + i)) 15 (sl.getD i 0)) 14 = d + wq from by
            rw [up_ne (show (19:Nat) ≠ 15 by omega),
              up_ne (show (14:Nat) ≠ 15 by omega),
              up_ne (show (19:Nat) ≠ 20 by omega),
              up_ne (show (14:Nat) ≠ 20 by omega), hf19, hf14],
        exec_store_step (by omega)
          (show prog2.getD 204 Instr.reject = Instr.store 21 15 by rfl) fi3,
          up_eq, up_ne (show (15:Nat) ≠ 21 by omega), up_eq,
        exec_add_step (by omega)
          (show prog2.getD 205 Instr.reject = Instr.add 12 12 1 by rfl),
          show (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 + (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 1 = i + 1 from by
            rw [up_ne (show (12:Nat) ≠ d + wq by omega),
              up_ne (show (12:Nat) ≠ 21 by omega), up_ne (show (12:Nat) ≠ 15 by omega),
              up_ne (show (12:Nat) ≠ 20 by omega), hf12,
              up_ne (show (1:Nat) ≠ d + wq by omega),
              up_ne (show (1:Nat) ≠ 21 by omega),
              up_ne (show (1:Nat) ≠ 15 by omega),
              up_ne (show (1:Nat) ≠ 20 by omega), h1],
        exec_add_step (by omega)
          (show prog2.getD 206 Instr.reject = Instr.add 14 14 1 by rfl),
          show (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 + (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 1 = wq + 1 from by
            rw [up_ne (show (14:Nat) ≠ 12 by omega),
              up_ne (show (14:Nat) ≠ d + wq by omega),
              up_ne (show (14:Nat) ≠ 21 by omega),
              up_ne (show (14:Nat) ≠ 15 by omega),
              up_ne (show (14:Nat) ≠ 20 by omega), hf14,
              up_ne (show (1:Nat) ≠ 12 by omega),
              up_ne (show (1:Nat) ≠ d + wq by omega),
              up_ne (show (1:Nat) ≠ 21 by omega),
              up_ne (show (1:Nat) ≠ 15 by omega),
              up_ne (show (1:Nat) ≠ 20 by omega), h1]]
      simp only [Nat.sub_sub, Nat.reduceAdd]
    by_cases hnext : i + 1 < L
    · have h131 : (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 12 < (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 11 := by

        rw [e12g, e11g]
        exact hnext
      rw [hsteps, exec_blt_lt_step (by omega)
        (show prog2.getD 207 Instr.reject = Instr.blt 12 11 201 by rfl) fi6 h131]
      obtain ⟨c2, f2, hc2, hex2, harr2, h122, h142, hfit2, hpres2⟩ :=
        ih L b d sl out (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) (i + 1) (wq + 1) (S - 7) r hsL hnext (by omega)
          e12g e14g e11g e18g e19g e1g e2g esrcg hvfit htake1 hdrop1 fi6 hbL hdL
          h2L hb33 hd33 hdisj (by omega) (by omega)
      refine ⟨7 + c2, f2, by omega, ?_, harr2, h122, h142, hfit2, ?_⟩
      · have hS7 : S - 6 - 1 = S - 7 := by omega
        have hS2 : S - 7 - c2 = S - (7 + c2) := by omega
        rw [hS7, hex2, hS2]
      · have q1 : Pres (MReg d L) f (up f 20 (b + i)) :=
          pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
        have q2 : Pres (MReg d L) (up f 20 (b + i)) (up (up f 20 (b + i)) 15 (sl.getD i 0)) :=
          pres_up (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        have q3 : Pres (MReg d L) (up (up f 20 (b + i)) 15 (sl.getD i 0)) (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) :=
          pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
        have q4 : Pres (MReg d L) (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) := pres_up (MReg_dst (by omega) (by omega))
        have q5 : Pres (MReg d L) (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) := pres_up (Or.inl rfl)
        have q6 : Pres (MReg d L) (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) :=
          pres_up (Or.inr (Or.inr (Or.inl rfl)))
        exact pres_trans q1 (pres_trans q2 (pres_trans q3 (pres_trans q4
          (pres_trans q5 (pres_trans q6 hpres2)))))
    · have h131 : ¬ (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 12 < (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 11 := by

        rw [e12g, e11g]
        omega
      have h132 : (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 2 < (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 1 := by rw [e2g, e1g]; omega
      have hrw2 : exec prog2 ρ S 201 r (memOf w f)
          = exec prog2 ρ (S - 8) 217 r (memOf w (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1))) := by
        rw [hsteps,
          exec_blt_ge_step (by omega)
            (show prog2.getD 207 Instr.reject = Instr.blt 12 11 201 by rfl) fi6 h131,
          exec_blt_lt_step (by omega)
            (show prog2.getD 208 Instr.reject = Instr.blt 2 1 217 by rfl) fi6 h132]
        simp only [Nat.sub_sub, Nat.reduceAdd]
      have hfull : arrL (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) d (2 * L) = out := by
        have hq2 : wq + 1 = 2 * L := by omega
        rw [hq2] at htake1
        have hto := takeAll (l := out) (n := 2 * L) (by omega)
        have hla : (arrL (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) d (2 * L)).length = 2 * L := by simp [arrL]
        have hta := takeAll (l := arrL (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) d (2 * L)) (n := 2 * L) (by omega)
        rw [← hta, ← hto, htake1, hq2]
      refine ⟨8, (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)), by omega, hrw2, hfull, by rw [e12g]; omega,
        by rw [e14g]; omega, fi6, ?_⟩
      have q1 : Pres (MReg d L) f (up f 20 (b + i)) :=
        pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      have q2 : Pres (MReg d L) (up f 20 (b + i)) (up (up f 20 (b + i)) 15 (sl.getD i 0)) :=
        pres_up (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      have q3 : Pres (MReg d L) (up (up f 20 (b + i)) 15 (sl.getD i 0)) (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) :=
        pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
      have q4 : Pres (MReg d L) (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) := pres_up (MReg_dst (by omega) (by omega))
      have q5 : Pres (MReg d L) (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) := pres_up (Or.inl rfl)
      exact pres_trans q1 (pres_trans q2 (pres_trans q3 (pres_trans q4
        (pres_trans q5 (pres_up (Or.inr (Or.inr (Or.inl rfl))))))))

/-- Drain-j do-while loop (pc 209 → 217). -/
theorem djLoop_exec_m2 {w : Nat} (ρ : Nat → BitVec w) :
    ∀ (N L b d ak : Nat) (sl out : List Nat) (f : Nat → Nat) (j wq S r : Nat),
    sl.length = L →
    j < L → wq = L + j → f 12 = L → f 13 = j → f 14 = wq → f 11 = L →
    f 17 = ak → f 18 = b → f 19 = d → f 1 = 1 → f 2 = 0 →
    (∀ q, q < L → f (b + q) = sl.getD q 0) →
    (∀ v ∈ sl, v + ak < 2 ^ w) →
    (out.take wq = (arrL f d (2 * L)).take wq) →
    out.drop wq = (sl.map (fun z => z + ak)).drop j →
    (∀ q, f q < 2 ^ w) → b + L < 2 ^ w → d + 2 * L < 2 ^ w → 2 * L < 2 ^ w →
    33 ≤ b → 33 ≤ d → (∀ p q, p < 2 * L → q < L → d + p ≠ b + q) →
    L - j ≤ N → 8 * N + 8 ≤ S →
    ∃ c f', c ≤ 8 * N + 8 ∧
      exec prog2 ρ S 209 r (memOf w f) = exec prog2 ρ (S - c) 217 r (memOf w f') ∧
      arrL f' d (2 * L) = out ∧ f' 12 = L ∧ f' 13 = L ∧ f' 14 = 2 * L ∧
      (∀ q, f' q < 2 ^ w) ∧ Pres (MReg d L) f f' := by
  intro N
  induction N with
  | zero =>
    intro L b d ak sl out f j wq S r hsL hjL hwj hf12 hf13 hf14 hf11 hf17 hf18
      hf19 h1 h2 hsrc hvfit htake hdrop hfit hbL hdL h2L hb33 hd33 hdisj hN hS
    exact absurd hN (by omega)
  | succ N ih =>
    intro L b d ak sl out f j wq S r hsL hjL hwj hf12 hf13 hf14 hf11 hf17 hf18
      hf19 h1 h2 hsrc hvfit htake hdrop hfit hbL hdL h2L hb33 hd33 hdisj hN hS
    have hvj : sl.getD j 0 + ak < 2 ^ w := hvfit _ (mem_getD (by omega))
    have fi1 : ∀ q, (up f 21 (b + j)) q < 2 ^ w := up_fit hfit (by have := hbL; omega)
    have fi2 : ∀ q, (up (up f 21 (b + j)) 16 (sl.getD j 0)) q < 2 ^ w := up_fit fi1 (by omega)
    have fi3 : ∀ q, (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) q < 2 ^ w := up_fit fi2 hvj
    have fi4 : ∀ q, (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) q < 2 ^ w := up_fit fi3 (by have := hdL; omega)
    have fi5 : ∀ q, (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) q < 2 ^ w := up_fit fi4 (by omega)
    have fi6 : ∀ q, (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) q < 2 ^ w := up_fit fi5 (by omega)
    have fi7 : ∀ q, (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) q < 2 ^ w := up_fit fi6 (by omega)
    have hA4 : arrL (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) d (2 * L) = arrL f d (2 * L) := by
      rw [show arrL (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) d (2 * L) = arrL (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) d (2 * L) from
          arrL_up_out (fun q _ => show (20:Nat) ≠ d + q by omega),
        show arrL (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) d (2 * L) = arrL (up (up f 21 (b + j)) 16 (sl.getD j 0)) d (2 * L) from
          arrL_up_out (fun q _ => show (16:Nat) ≠ d + q by omega),
        show arrL (up (up f 21 (b + j)) 16 (sl.getD j 0)) d (2 * L) = arrL (up f 21 (b + j)) d (2 * L) from
          arrL_up_out (fun q _ => show (16:Nat) ≠ d + q by omega),
        show arrL (up f 21 (b + j)) d (2 * L) = arrL f d (2 * L) from
          arrL_up_out (fun q _ => show (21:Nat) ≠ d + q by omega)]
    have hA7 : arrL (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) d (2 * L) = arrL (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) d (2 * L) := by
      rw [show arrL (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) d (2 * L) = arrL (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) d (2 * L) from
          arrL_up_out (fun q _ => show (14:Nat) ≠ d + q by omega),
        show arrL (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) d (2 * L) = arrL (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) d (2 * L) from
          arrL_up_out (fun q _ => show (13:Nat) ≠ d + q by omega)]
    have hMlen : (sl.map (fun z => z + ak)).length = L := by
      simp [List.length_map, hsL]
    have hleno : out.length = 2 * L := by
      have h1l := List.length_drop (l := out) (i := wq)
      rw [hdrop] at h1l
      rw [List.length_drop (l := sl.map (fun z => z + ak)) (i := j)] at h1l
      have : (sl.map (fun z => z + ak)).length = L := hMlen
      omega
    have hjM : j < (sl.map (fun z => z + ak)).length := by omega
    have hjl : j < sl.length := by omega
    have hjm : j < (sl.map (fun z => z + ak)).length := by
      simp [List.length_map, hsL]
      omega
    have hdrop1 : out.drop (wq + 1) = (sl.map (fun z => z + ak)).drop (j + 1) := by
      rw [dropSucc, hdrop, dropCons hjM, getD_map_add sl ak j hjl]
      simp
    have hwqo : wq < out.length := by omega
    have hwq2L : wq < 2 * L := by omega
    have htake1 : out.take (wq + 1) = (arrL (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) d (2 * L)).take (wq + 1) := by
      rw [hA7, arrL_take_up hwq2L, hA4, ← htake, takeSucc hwqo]
      congr 1
      rw [← getDDrop, hdrop, dropCons hjM, getD_map_add sl ak j hjl]
      rfl
    -- register facts on T7
    have e13g : (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 13 = j + 1 := by
      rw [up_ne (show (13:Nat) ≠ 14 by omega), up_eq]
    have e14g : (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 14 = wq + 1 := up_eq _ _ _
    have e11g : (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 11 = L := by rw [up_ne (show (11:Nat) ≠ 14 by omega), up_ne (show (11:Nat) ≠ 13 by omega), up_ne (show (11:Nat) ≠ d + wq by omega), up_ne (show (11:Nat) ≠ 20 by omega), up_ne (show (11:Nat) ≠ 16 by omega), up_ne (show (11:Nat) ≠ 16 by omega), up_ne (show (11:Nat) ≠ 21 by omega), hf11]
    have e12g : (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 12 = L := by
      rw [up_ne (show (12:Nat) ≠ 14 by omega), up_ne (show (12:Nat) ≠ 13 by omega), up_ne (show (12:Nat) ≠ d + wq by omega), up_ne (show (12:Nat) ≠ 20 by omega), up_ne (show (12:Nat) ≠ 16 by omega), up_ne (show (12:Nat) ≠ 16 by omega), up_ne (show (12:Nat) ≠ 21 by omega), hf12]
    have e17g : (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 17 = ak := by
      rw [up_ne (show (17:Nat) ≠ 14 by omega), up_ne (show (17:Nat) ≠ 13 by omega), up_ne (show (17:Nat) ≠ d + wq by omega), up_ne (show (17:Nat) ≠ 20 by omega), up_ne (show (17:Nat) ≠ 16 by omega), up_ne (show (17:Nat) ≠ 16 by omega), up_ne (show (17:Nat) ≠ 21 by omega), hf17]
    have e18g : (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 18 = b := by rw [up_ne (show (18:Nat) ≠ 14 by omega), up_ne (show (18:Nat) ≠ 13 by omega), up_ne (show (18:Nat) ≠ d + wq by omega), up_ne (show (18:Nat) ≠ 20 by omega), up_ne (show (18:Nat) ≠ 16 by omega), up_ne (show (18:Nat) ≠ 16 by omega), up_ne (show (18:Nat) ≠ 21 by omega), hf18]
    have e19g : (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 19 = d := by rw [up_ne (show (19:Nat) ≠ 14 by omega), up_ne (show (19:Nat) ≠ 13 by omega), up_ne (show (19:Nat) ≠ d + wq by omega), up_ne (show (19:Nat) ≠ 20 by omega), up_ne (show (19:Nat) ≠ 16 by omega), up_ne (show (19:Nat) ≠ 16 by omega), up_ne (show (19:Nat) ≠ 21 by omega), hf19]
    have e1g : (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 1 = 1 := by rw [up_ne (show (1:Nat) ≠ 14 by omega), up_ne (show (1:Nat) ≠ 13 by omega), up_ne (show (1:Nat) ≠ d + wq by omega), up_ne (show (1:Nat) ≠ 20 by omega), up_ne (show (1:Nat) ≠ 16 by omega), up_ne (show (1:Nat) ≠ 16 by omega), up_ne (show (1:Nat) ≠ 21 by omega), h1]
    have e2g : (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 2 = 0 := by rw [up_ne (show (2:Nat) ≠ 14 by omega), up_ne (show (2:Nat) ≠ 13 by omega), up_ne (show (2:Nat) ≠ d + wq by omega), up_ne (show (2:Nat) ≠ 20 by omega), up_ne (show (2:Nat) ≠ 16 by omega), up_ne (show (2:Nat) ≠ 16 by omega), up_ne (show (2:Nat) ≠ 21 by omega), h2]
    have hdisj2 : ∀ q, q < L → b + q ≠ d + wq := by
      intro q hq
      exact Ne.symm (hdisj wq q (by omega) hq)
    have esrcg : ∀ q, q < L → (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) (b + q) = sl.getD q 0 := by
      intro q hq
      rw [up_ne (show b + q ≠ 14 by omega), up_ne (show b + q ≠ 13 by omega),
        up_ne (hdisj2 q hq), up_ne (show b + q ≠ 20 by omega),
        up_ne (show b + q ≠ 16 by omega), up_ne (show b + q ≠ 16 by omega),
        up_ne (show b + q ≠ 21 by omega)]
      exact hsrc q hq
    -- the seven body steps with inline normalization
    have hsteps : exec prog2 ρ S 209 r (memOf w f)
        = exec prog2 ρ (S - 6) 215 r (memOf w (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1))) := by
      rw [exec_add_step (by omega)
          (show prog2.getD 209 Instr.reject = Instr.add 21 18 13 by rfl),
          show f 18 + f 13 = b + j from by rw [hf18, hf13],
        exec_load_step (by omega)
          (show prog2.getD 210 Instr.reject = Instr.load 16 21 by rfl) fi1,
          up_eq, up_ne (show b + j ≠ 21 by omega), hsrc j hjL,
        exec_add_step (by omega)
          (show prog2.getD 211 Instr.reject = Instr.add 16 16 17 by rfl),
          show (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 + (up (up f 21 (b + j)) 16 (sl.getD j 0)) 17 = sl.getD j 0 + ak from by
            rw [up_eq, up_ne (show (17:Nat) ≠ 16 by omega),
              up_ne (show (17:Nat) ≠ 21 by omega), hf17],
        exec_add_step (by omega)
          (show prog2.getD 212 Instr.reject = Instr.add 20 19 14 by rfl),
          show (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 19 + (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 14 = d + wq from by
            rw [up_ne (show (19:Nat) ≠ 16 by omega),
              up_ne (show (19:Nat) ≠ 16 by omega),
              up_ne (show (19:Nat) ≠ 21 by omega), hf19,
              up_ne (show (14:Nat) ≠ 16 by omega),
              up_ne (show (14:Nat) ≠ 16 by omega),
              up_ne (show (14:Nat) ≠ 21 by omega), hf14],
        exec_store_step (by omega)
          (show prog2.getD 213 Instr.reject = Instr.store 20 16 by rfl) fi4,
          up_eq,
          show (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) 16 = sl.getD j 0 + ak from by
            rw [up_ne (show (16:Nat) ≠ 20 by omega), up_eq],
        exec_add_step (by omega)
          (show prog2.getD 214 Instr.reject = Instr.add 13 13 1 by rfl),
          show (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 + (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 1 = j + 1 from by
            rw [up_ne (show (13:Nat) ≠ d + wq by omega),
              up_ne (show (13:Nat) ≠ 20 by omega),
              up_ne (show (13:Nat) ≠ 16 by omega),
              up_ne (show (13:Nat) ≠ 16 by omega),
              up_ne (show (13:Nat) ≠ 21 by omega), hf13,
              up_ne (show (1:Nat) ≠ d + wq by omega),
              up_ne (show (1:Nat) ≠ 20 by omega),
              up_ne (show (1:Nat) ≠ 16 by omega),
              up_ne (show (1:Nat) ≠ 16 by omega),
              up_ne (show (1:Nat) ≠ 21 by omega), h1]]
      simp only [Nat.sub_sub, Nat.reduceAdd]
    by_cases hnext : j + 1 < L
    · have h140 : (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 13 < (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 11 := by rw [e13g, e11g]; exact hnext
      have hS8 : S - 6 - 1 - 1 = S - 8 := by omega
      rw [hsteps, exec_add_step (by omega)
          (show prog2.getD 215 Instr.reject = Instr.add 14 14 1 by rfl),
          show (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 + (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 1 = wq + 1 from by
            rw [up_ne (show (14:Nat) ≠ 13 by omega),
              up_ne (show (14:Nat) ≠ d + wq by omega),
              up_ne (show (14:Nat) ≠ 20 by omega),
              up_ne (show (14:Nat) ≠ 16 by omega),
              up_ne (show (14:Nat) ≠ 16 by omega),
              up_ne (show (14:Nat) ≠ 21 by omega), hf14,
              up_ne (show (1:Nat) ≠ 13 by omega),
              up_ne (show (1:Nat) ≠ d + wq by omega),
              up_ne (show (1:Nat) ≠ 20 by omega),
              up_ne (show (1:Nat) ≠ 16 by omega),
              up_ne (show (1:Nat) ≠ 16 by omega),
              up_ne (show (1:Nat) ≠ 21 by omega), h1],
          exec_blt_lt_step (by omega)
          (show prog2.getD 216 Instr.reject = Instr.blt 13 11 209 by rfl) fi7
          h140, hS8]
      have hwj2 : wq + 1 = L + (j + 1) := by omega
      have hN2 : L - (j + 1) ≤ N := by omega
      have hS2 : 8 * N + 8 ≤ S - 8 := by omega
      obtain ⟨c2, f2, hc2, hex2, harr2, h122, h132, h142, hfit2, hpres2⟩ :=
        ih L b d ak sl out (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) (j + 1) (wq + 1) (S - 8) r hsL hnext hwj2
          e12g e13g e14g e11g e17g e18g e19g e1g e2g esrcg hvfit htake1 hdrop1
          fi7 hbL hdL h2L hb33 hd33 hdisj hN2 hS2
      refine ⟨8 + c2, f2, by omega, ?_, harr2, h122, h132, h142, hfit2, ?_⟩
      · rw [hex2]
        have hS9 : S - 8 - c2 = S - (8 + c2) := by omega
        rw [hS9]
      have q1 : Pres (MReg d L) f (up f 21 (b + j)) := pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
      have q2 : Pres (MReg d L) (up f 21 (b + j)) (up (up f 21 (b + j)) 16 (sl.getD j 0)) := pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      have q3 : Pres (MReg d L) (up (up f 21 (b + j)) 16 (sl.getD j 0)) (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) := pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      have q4 : Pres (MReg d L) (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) := pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      have q5 : Pres (MReg d L) (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) := pres_up (MReg_dst (by omega) (by omega))
      have q6 : Pres (MReg d L) (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) := pres_up (Or.inr (Or.inl rfl))
      have q7 : Pres (MReg d L) (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) := pres_up (Or.inr (Or.inr (Or.inl rfl)))
      exact pres_trans q1 (pres_trans q2 (pres_trans q3 (pres_trans q4
        (pres_trans q5 (pres_trans q6 (pres_trans q7 hpres2))))))
    · have h140 : ¬ (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 13 < (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 11 := by rw [e13g, e11g]; omega
      have hrw2 : exec prog2 ρ S 209 r (memOf w f)
          = exec prog2 ρ (S - 8) 217 r (memOf w (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1))) := by
        rw [hsteps,
          exec_add_step (by omega)
            (show prog2.getD 215 Instr.reject = Instr.add 14 14 1 by rfl),
          show (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 + (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 1 = wq + 1 from by
            rw [up_ne (show (14:Nat) ≠ 13 by omega),
              up_ne (show (14:Nat) ≠ d + wq by omega),
              up_ne (show (14:Nat) ≠ 20 by omega),
              up_ne (show (14:Nat) ≠ 16 by omega),
              up_ne (show (14:Nat) ≠ 16 by omega),
              up_ne (show (14:Nat) ≠ 21 by omega), hf14,
              up_ne (show (1:Nat) ≠ 13 by omega),
              up_ne (show (1:Nat) ≠ d + wq by omega),
              up_ne (show (1:Nat) ≠ 20 by omega),
              up_ne (show (1:Nat) ≠ 16 by omega),
              up_ne (show (1:Nat) ≠ 16 by omega),
              up_ne (show (1:Nat) ≠ 21 by omega), h1],
          exec_blt_ge_step (by omega)
            (show prog2.getD 216 Instr.reject = Instr.blt 13 11 209 by rfl) fi7 h140]
        simp only [Nat.sub_sub, Nat.reduceAdd]
      have hfull : arrL (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) d (2 * L) = out := by
        have hq2 : wq + 1 = 2 * L := by omega
        rw [hq2] at htake1
        have hto := takeAll (l := out) (n := 2 * L) (by omega)
        have hla : (arrL (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) d (2 * L)).length = 2 * L := by simp [arrL]
        have hta := takeAll (l := arrL (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) d (2 * L)) (n := 2 * L) (by omega)
        rw [← hta, ← hto, htake1, hq2]
      refine ⟨8, (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)), by omega, hrw2, hfull, e12g, by rw [e13g]; omega,
        by rw [e14g]; omega, fi7, ?_⟩
      have q1 : Pres (MReg d L) f (up f 21 (b + j)) := pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
      have q2 : Pres (MReg d L) (up f 21 (b + j)) (up (up f 21 (b + j)) 16 (sl.getD j 0)) := pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      have q3 : Pres (MReg d L) (up (up f 21 (b + j)) 16 (sl.getD j 0)) (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) := pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      have q4 : Pres (MReg d L) (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) := pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      have q5 : Pres (MReg d L) (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) := pres_up (MReg_dst (by omega) (by omega))
      have q6 : Pres (MReg d L) (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) := pres_up (Or.inr (Or.inl rfl))
      have q7 : Pres (MReg d L) (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) := pres_up (Or.inr (Or.inr (Or.inl rfl)))
      exact pres_trans q1 (pres_trans q2 (pres_trans q3 (pres_trans q4
        (pres_trans q5 (pres_trans q6 (pres_up (Or.inr (Or.inr (Or.inl rfl)))))))))

/-- Length of a merge, by total-length induction (the `b < a` branch
recurses with `a :: l'` unchanged, so structure-on-`l` induction fails). -/
theorem mmerge_length_aux : ∀ (N : Nat) (l r : List Nat),
    l.length + r.length ≤ N → (mmerge l r).length = l.length + r.length := by
  intro N
  induction N with
  | zero =>
    intro l r hlen
    cases l with
    | nil => simp [mmerge]
    | cons a l' => exact absurd hlen (by simp only [List.length_cons]; omega)
  | succ N ih =>
    intro l r hlen
    cases l with
    | nil => simp [mmerge]
    | cons a l' =>
      cases r with
      | nil => simp [mmerge]
      | cons b r' =>
        rw [mmerge]
        by_cases h : b < a
        · rw [if_pos h]
          have ih2 := ih (a :: l') r' (by simp only [List.length_cons] at hlen ⊢; omega)
          rw [List.length_cons, ih2]
          simp only [List.length_cons]
          omega
        · rw [if_neg h]
          have ih2 := ih l' (b :: r') (by simp only [List.length_cons] at hlen ⊢; omega)
          rw [List.length_cons, ih2]
          simp only [List.length_cons]
          omega

theorem mmerge_length (l r : List Nat) : (mmerge l r).length = l.length + r.length :=
  mmerge_length_aux (l.length + r.length) l r (Nat.le_refl _)

/-- `drop` past the end is empty. -/
theorem dropNil {l : List Nat} {n : Nat} (h : l.length ≤ n) : l.drop n = [] := by
  cases hll : l.drop n with
  | nil => rfl
  | cons x r =>
      have hlen := List.length_drop (l := l) (i := n)
      rw [hll] at hlen
      have h0 : (x :: r).length = r.length + 1 := rfl
      omega

theorem mmerge_nil_l (l : List Nat) : mmerge [] l = l := by
  cases l <;> simp [mmerge]
--
/-! ## §5. The merge loop (pc 179 → 217). -/
/-- Merge loop: both-sides iterations until one side exhausts, then the
matching drain finishes the array.  `wq = i + j` throughout; each
both-sides step is 14 instructions, consuming `mmerge_stepL/J` for the
take/drop invariants. -/
theorem merge_exec_m2 {w : Nat} (ρ : Nat → BitVec w) :
    ∀ (N L b d ak : Nat) (sl out : List Nat) (f : Nat → Nat) (i j wq S r : Nat),
    sl.length = L →
    i ≤ L → j ≤ L → wq = i + j → f 12 = i → f 13 = j → f 14 = wq → f 11 = L →
    f 17 = ak → f 18 = b → f 19 = d → f 1 = 1 → f 2 = 0 →
    (∀ q, q < L → f (b + q) = sl.getD q 0) →
    (∀ v ∈ sl, v + ak < 2 ^ w) →
    (out.take wq = (arrL f d (2 * L)).take wq) →
    (out.drop wq = mmerge (sl.drop i) ((sl.map (fun z => z + ak)).drop j)) →
    out = mmerge sl (sl.map (fun z => z + ak)) →
    (∀ q, f q < 2 ^ w) → b + L < 2 ^ w → d + 2 * L < 2 ^ w → 2 * L < 2 ^ w →
    33 ≤ b → 33 ≤ d → (∀ p q, p < 2 * L → q < L → d + p ≠ b + q) →
    (L - i) + (L - j) ≤ N → 22 * N + 12 ≤ S →
    ∃ c f', c ≤ 22 * N + 12 ∧
      exec prog2 ρ S 179 r (memOf w f) = exec prog2 ρ (S - c) 217 r (memOf w f') ∧
      arrL f' d (2 * L) = out ∧ f' 12 = L ∧ f' 14 = 2 * L ∧
      (∀ q, f' q < 2 ^ w) ∧ Pres (MReg d L) f f' := by
  intro N
  induction N with
  | zero =>
    intro L b d ak sl out f i j wq S r hsL hiLe hjLe hwq hf12 hf13 hf14 hf11 hf17 hf18 hf19 h1 h2 hsrc hvfit htake hdrop hout hfit hbL hdL h2L hb33 hd33 hdisj hfuel hhor
    have hiL : i = L := by omega
    have hjL : j = L := by omega
    have hw2 : wq = 2 * L := by omega
    have hlen : out.length = 2 * L := by
      rw [hout, mmerge_length, List.length_map, hsL]
      omega
    have hfull : arrL f d (2 * L) = out := by
      rw [hw2] at htake
      have hto := takeAll (l := out) (n := 2 * L) (by omega)
      have hla : (arrL f d (2 * L)).length = 2 * L := by simp [arrL]
      have hta := takeAll (l := arrL f d (2 * L)) (n := 2 * L) (by omega)
      rw [← hta, ← hto, htake]
    refine ⟨4, f, by omega, ?_, hfull, by omega, by omega, hfit, ?_⟩
    · rw [exec_blt_ge_step (by omega)
          (show prog2.getD 179 Instr.reject = Instr.blt 13 11 181 by rfl) hfit
          (by rw [hf13, hf11]; omega),
        exec_blt_lt_step (by omega)
          (show prog2.getD 180 Instr.reject = Instr.blt 2 1 199 by rfl) hfit
          (by rw [h2, h1]; omega),
        exec_blt_ge_step (by omega)
          (show prog2.getD 199 Instr.reject = Instr.blt 12 11 201 by rfl) hfit
          (by rw [hf12, hf11]; omega),
        exec_blt_lt_step (by omega)
          (show prog2.getD 200 Instr.reject = Instr.blt 2 1 217 by rfl) hfit
          (by rw [h2, h1]; omega)]
      simp only [Nat.sub_sub, Nat.reduceAdd]
    · intro x hx
      rfl
  | succ N ih =>
    intro L b d ak sl out f i j wq S r hsL hiLe hjLe hwq hf12 hf13 hf14 hf11 hf17 hf18 hf19 h1 h2 hsrc hvfit htake hdrop hout hfit hbL hdL h2L hb33 hd33 hdisj hfuel hhor
    have hMlen : (sl.map (fun z => z + ak)).length = L := by simp [List.length_map, hsL]
    by_cases hj : j < L
    · by_cases hi : i < L
      ·         -- both-sides merge iteration
        have hjl : j < sl.length := by omega
        have fi1 : ∀ q, (up f 20 (b + i)) q < 2 ^ w := up_fit hfit (by have := hbL; omega)
        have fi2 : ∀ q, (up (up f 20 (b + i)) 15 (sl.getD i 0)) q < 2 ^ w := up_fit fi1 (by have := hvfit _ (mem_getD (i := i) (by omega)); omega)
        have fi3 : ∀ q, (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) q < 2 ^ w := up_fit fi2 (by have := hbL; omega)
        have fi4 : ∀ q, (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) q < 2 ^ w := up_fit fi3 (by have := hvfit _ (mem_getD (i := j) (by omega)); omega)
        have hvj : sl.getD j 0 + ak < 2 ^ w := hvfit _ (mem_getD (i := j) (by omega))
        have fi5 : ∀ q, (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) q < 2 ^ w := up_fit fi4 hvj
        have fi6 : ∀ q, (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) q < 2 ^ w := up_fit fi5 (by have := hdL; omega)
        have fi7 : ∀ q, (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) q < 2 ^ w := up_fit fi6 hvj
        have fi8 : ∀ q, (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) q < 2 ^ w := up_fit fi7 (by have := h2L; omega)
        have fi9 : ∀ q, (up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) q < 2 ^ w := up_fit fi8 (by have := h2L; omega)
        have hvi : sl.getD i 0 < 2 ^ w := by have := hvfit _ (mem_getD (i := i) (by omega)); omega
        have fi7U : ∀ q, (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) q < 2 ^ w := up_fit fi6 hvi
        have fi8U : ∀ q, (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) q < 2 ^ w := up_fit fi7U (by have := h2L; omega)
        have fi9U : ∀ q, (up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) q < 2 ^ w := up_fit fi8U (by have := h2L; omega)
        have e15_5 : up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak) 15 = sl.getD i 0 := by
          rw [up_ne (show (15:Nat) ≠ (16 : Nat) by omega), up_ne (show (15:Nat) ≠ (16 : Nat) by omega), up_ne (show (15:Nat) ≠ (21 : Nat) by omega), up_eq]
        have e16_5 : up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak) 16 = sl.getD j 0 + ak := up_eq _ _ _
        have hlen : out.length = 2 * L := by
          rw [hout, mmerge_length, List.length_map, hsL]
          omega
        have hwqo : wq < out.length := by rw [hlen]; omega
        have hwq2L : wq < 2 * L := by omega
        have hB : (mmerge sl (sl.map (fun z => z + ak))).drop (i + j)
            = mmerge (sl.drop i) ((sl.map (fun z => z + ak)).drop j) := by
          rw [← hwq, ← hout]
          exact hdrop
        by_cases hcmp : sl.getD j 0 + ak < sl.getD i 0
        · -- LTAKEJ
          have hcmpJ : (sl.map (fun z => z + ak)).getD j 0 < sl.getD i 0 := by
            rw [getD_map_add sl ak j hjl]
            exact hcmp
          have hstep := mmerge_stepJ sl (sl.map (fun z => z + ak)) i j
              (by omega) (by omega) hcmpJ hB
          have houtwq : out.getD wq 0 = sl.getD j 0 + ak := by
            rw [hout, hwq, hstep.1, getD_map_add sl ak j hjl]
          have hdrop1 : out.drop (wq + 1)
              = mmerge (sl.drop i) ((sl.map (fun z => z + ak)).drop (j + 1)) := by
            rw [hout, show wq + 1 = i + j + 1 from by omega, hstep.2]
          have hA9 : arrL (up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) d (2 * L) = arrL (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) d (2 * L) := by
            rw [show arrL (up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) d (2 * L) = arrL (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) d (2 * L) from arrL_up_out (fun q _ => show (14:Nat) ≠ d + q by omega), show arrL (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) d (2 * L) = arrL (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) d (2 * L) from arrL_up_out (fun q _ => show (13:Nat) ≠ d + q by omega)]
          have hA6 : arrL (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) d (2 * L) = arrL f d (2 * L) := by
            rw [show arrL (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) d (2 * L) = arrL (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) d (2 * L) from arrL_up_out (fun q _ => show (20:Nat) ≠ d + q by omega), show arrL (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) d (2 * L) = arrL (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) d (2 * L) from arrL_up_out (fun q _ => show (16:Nat) ≠ d + q by omega), show arrL (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) d (2 * L) = arrL (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) d (2 * L) from arrL_up_out (fun q _ => show (16:Nat) ≠ d + q by omega), show arrL (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) d (2 * L) = arrL (up (up f 20 (b + i)) 15 (sl.getD i 0)) d (2 * L) from arrL_up_out (fun q _ => show (21:Nat) ≠ d + q by omega), show arrL (up (up f 20 (b + i)) 15 (sl.getD i 0)) d (2 * L) = arrL (up f 20 (b + i)) d (2 * L) from arrL_up_out (fun q _ => show (15:Nat) ≠ d + q by omega), show arrL (up f 20 (b + i)) d (2 * L) = arrL (f) d (2 * L) from arrL_up_out (fun q _ => show (20:Nat) ≠ d + q by omega)]
          have htake1 : out.take (wq + 1) = (arrL (up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) d (2 * L)).take (wq + 1) := by
            rw [hA9, arrL_take_up hwq2L, hA6, ← htake, takeSucc hwqo, houtwq]
          have e1_8 : up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1) 1 = 1 := by
            rw [up_ne (show (1:Nat) ≠ (13 : Nat) by omega), up_ne (show (1:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (21 : Nat) by omega), up_ne (show (1:Nat) ≠ (15 : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), h1]
          have e2_8 : up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1) 2 = 0 := by
            rw [up_ne (show (2:Nat) ≠ (13 : Nat) by omega), up_ne (show (2:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (2:Nat) ≠ (20 : Nat) by omega), up_ne (show (2:Nat) ≠ (16 : Nat) by omega), up_ne (show (2:Nat) ≠ (16 : Nat) by omega), up_ne (show (2:Nat) ≠ (21 : Nat) by omega), up_ne (show (2:Nat) ≠ (15 : Nat) by omega), up_ne (show (2:Nat) ≠ (20 : Nat) by omega), h2]
          have e12_9 : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1) 12 = i := by
            rw [up_ne (show (12:Nat) ≠ (14 : Nat) by omega), up_ne (show (12:Nat) ≠ (13 : Nat) by omega), up_ne (show (12:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (12:Nat) ≠ (20 : Nat) by omega), up_ne (show (12:Nat) ≠ (16 : Nat) by omega), up_ne (show (12:Nat) ≠ (16 : Nat) by omega), up_ne (show (12:Nat) ≠ (21 : Nat) by omega), up_ne (show (12:Nat) ≠ (15 : Nat) by omega), up_ne (show (12:Nat) ≠ (20 : Nat) by omega), hf12]
          have e13_9 : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1) 13 = j + 1 := by
            rw [up_ne (show (13:Nat) ≠ (14 : Nat) by omega), up_eq]
          have e14_9 : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1) 14 = wq + 1 := by
            rw [up_eq]
          have e11_9 : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1) 11 = L := by
            rw [up_ne (show (11:Nat) ≠ (14 : Nat) by omega), up_ne (show (11:Nat) ≠ (13 : Nat) by omega), up_ne (show (11:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (11:Nat) ≠ (20 : Nat) by omega), up_ne (show (11:Nat) ≠ (16 : Nat) by omega), up_ne (show (11:Nat) ≠ (16 : Nat) by omega), up_ne (show (11:Nat) ≠ (21 : Nat) by omega), up_ne (show (11:Nat) ≠ (15 : Nat) by omega), up_ne (show (11:Nat) ≠ (20 : Nat) by omega), hf11]
          have e17_9 : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1) 17 = ak := by
            rw [up_ne (show (17:Nat) ≠ (14 : Nat) by omega), up_ne (show (17:Nat) ≠ (13 : Nat) by omega), up_ne (show (17:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (17:Nat) ≠ (20 : Nat) by omega), up_ne (show (17:Nat) ≠ (16 : Nat) by omega), up_ne (show (17:Nat) ≠ (16 : Nat) by omega), up_ne (show (17:Nat) ≠ (21 : Nat) by omega), up_ne (show (17:Nat) ≠ (15 : Nat) by omega), up_ne (show (17:Nat) ≠ (20 : Nat) by omega), hf17]
          have e18_9 : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1) 18 = b := by
            rw [up_ne (show (18:Nat) ≠ (14 : Nat) by omega), up_ne (show (18:Nat) ≠ (13 : Nat) by omega), up_ne (show (18:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (18:Nat) ≠ (20 : Nat) by omega), up_ne (show (18:Nat) ≠ (16 : Nat) by omega), up_ne (show (18:Nat) ≠ (16 : Nat) by omega), up_ne (show (18:Nat) ≠ (21 : Nat) by omega), up_ne (show (18:Nat) ≠ (15 : Nat) by omega), up_ne (show (18:Nat) ≠ (20 : Nat) by omega), hf18]
          have e19_9 : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1) 19 = d := by
            rw [up_ne (show (19:Nat) ≠ (14 : Nat) by omega), up_ne (show (19:Nat) ≠ (13 : Nat) by omega), up_ne (show (19:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (19:Nat) ≠ (20 : Nat) by omega), up_ne (show (19:Nat) ≠ (16 : Nat) by omega), up_ne (show (19:Nat) ≠ (16 : Nat) by omega), up_ne (show (19:Nat) ≠ (21 : Nat) by omega), up_ne (show (19:Nat) ≠ (15 : Nat) by omega), up_ne (show (19:Nat) ≠ (20 : Nat) by omega), hf19]
          have e1_9 : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1) 1 = 1 := by
            rw [up_ne (show (1:Nat) ≠ (14 : Nat) by omega), up_ne (show (1:Nat) ≠ (13 : Nat) by omega), up_ne (show (1:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (21 : Nat) by omega), up_ne (show (1:Nat) ≠ (15 : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), h1]
          have e2_9 : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1) 2 = 0 := by
            rw [up_ne (show (2:Nat) ≠ (14 : Nat) by omega), up_ne (show (2:Nat) ≠ (13 : Nat) by omega), up_ne (show (2:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (2:Nat) ≠ (20 : Nat) by omega), up_ne (show (2:Nat) ≠ (16 : Nat) by omega), up_ne (show (2:Nat) ≠ (16 : Nat) by omega), up_ne (show (2:Nat) ≠ (21 : Nat) by omega), up_ne (show (2:Nat) ≠ (15 : Nat) by omega), up_ne (show (2:Nat) ≠ (20 : Nat) by omega), h2]
          have esrc_9 : ∀ q, q < L → up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1) (b + q) = sl.getD q 0 := by
            intro q hq
            rw [up_ne (show b + q ≠ (14 : Nat) by omega), up_ne (show b + q ≠ (13 : Nat) by omega), up_ne (Ne.symm (hdisj wq q (by omega) hq)), up_ne (show b + q ≠ (20 : Nat) by omega), up_ne (show b + q ≠ (16 : Nat) by omega), up_ne (show b + q ≠ (16 : Nat) by omega), up_ne (show b + q ≠ (21 : Nat) by omega), up_ne (show b + q ≠ (15 : Nat) by omega), up_ne (show b + q ≠ (20 : Nat) by omega)]
            exact hsrc q hq
          have hwalk : exec prog2 ρ S 179 r (memOf w f)
              = exec prog2 ρ (S - 14) 179 r (memOf w (up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1))) := by
            rw [exec_blt_lt_step (by omega) (show prog2.getD 179 Instr.reject = Instr.blt 13 11 181 by rfl) hfit (by rw [hf13, hf11]; exact hj),
              exec_blt_lt_step (by omega) (show prog2.getD 181 Instr.reject = Instr.blt 12 11 183 by rfl) hfit (by rw [hf12, hf11]; exact hi),
              exec_add_step (by omega) (show prog2.getD 183 Instr.reject = Instr.add 20 18 12 by rfl), show f 18 + f 12 = b + i from by rw [hf18, hf12],
              exec_load_step (by omega) (show prog2.getD 184 Instr.reject = Instr.load 15 20 by rfl) fi1, up_eq, up_ne (show b + i ≠ 20 by omega), hsrc i hi,
              exec_add_step (by omega) (show prog2.getD 185 Instr.reject = Instr.add 21 18 13 by rfl), show up (up f 20 (b + i)) 15 (sl.getD i 0) 18 + up (up f 20 (b + i)) 15 (sl.getD i 0) 13 = b + j from by rw [up_ne (show (18:Nat) ≠ (15 : Nat) by omega), up_ne (show (18:Nat) ≠ (20 : Nat) by omega), hf18, up_ne (show (13:Nat) ≠ (15 : Nat) by omega), up_ne (show (13:Nat) ≠ (20 : Nat) by omega), hf13],
              exec_load_step (by omega) (show prog2.getD 186 Instr.reject = Instr.load 16 21 by rfl) fi3, up_eq, up_ne (show b + j ≠ 21 by omega), up_ne (show b + j ≠ (15 : Nat) by omega), up_ne (show b + j ≠ (20 : Nat) by omega), hsrc j hj,
              exec_add_step (by omega) (show prog2.getD 187 Instr.reject = Instr.add 16 16 17 by rfl), show up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0) 16 + up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0) 17 = sl.getD j 0 + ak from by rw [up_eq, up_ne (show (17:Nat) ≠ (16 : Nat) by omega), up_ne (show (17:Nat) ≠ (21 : Nat) by omega), up_ne (show (17:Nat) ≠ (15 : Nat) by omega), up_ne (show (17:Nat) ≠ (20 : Nat) by omega), hf17],
              exec_blt_lt_step (by omega) (show prog2.getD 188 Instr.reject = Instr.blt 16 15 190 by rfl) fi5 (by rw [e16_5, e15_5]; exact hcmp),
              exec_add_step (by omega) (show prog2.getD 190 Instr.reject = Instr.add 20 19 14 by rfl), show up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak) 19 + up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak) 14 = d + wq from by rw [up_ne (show (19:Nat) ≠ (16 : Nat) by omega), up_ne (show (19:Nat) ≠ (16 : Nat) by omega), up_ne (show (19:Nat) ≠ (21 : Nat) by omega), up_ne (show (19:Nat) ≠ (15 : Nat) by omega), up_ne (show (19:Nat) ≠ (20 : Nat) by omega), hf19, up_ne (show (14:Nat) ≠ (16 : Nat) by omega), up_ne (show (14:Nat) ≠ (16 : Nat) by omega), up_ne (show (14:Nat) ≠ (21 : Nat) by omega), up_ne (show (14:Nat) ≠ (15 : Nat) by omega), up_ne (show (14:Nat) ≠ (20 : Nat) by omega), hf14],
              exec_store_step (by omega) (show prog2.getD 191 Instr.reject = Instr.store 20 16 by rfl) fi6, up_eq, up_ne (show (16:Nat) ≠ 20 by omega), up_eq,
              exec_add_step (by omega) (show prog2.getD 192 Instr.reject = Instr.add 13 13 1 by rfl), show up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak) 13 + up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak) 1 = j + 1 from by rw [up_ne (show (13:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (13:Nat) ≠ (20 : Nat) by omega), up_ne (show (13:Nat) ≠ (16 : Nat) by omega), up_ne (show (13:Nat) ≠ (16 : Nat) by omega), up_ne (show (13:Nat) ≠ (21 : Nat) by omega), up_ne (show (13:Nat) ≠ (15 : Nat) by omega), up_ne (show (13:Nat) ≠ (20 : Nat) by omega), hf13, up_ne (show (1:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (21 : Nat) by omega), up_ne (show (1:Nat) ≠ (15 : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), h1],
              exec_blt_lt_step (by omega) (show prog2.getD 193 Instr.reject = Instr.blt 2 1 197 by rfl) fi8 (by rw [e2_8, e1_8]; omega),
              exec_add_step (by omega) (show prog2.getD 197 Instr.reject = Instr.add 14 14 1 by rfl), show up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1) 14 + up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1) 1 = wq + 1 from by rw [up_ne (show (14:Nat) ≠ (13 : Nat) by omega), up_ne (show (14:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (14:Nat) ≠ (20 : Nat) by omega), up_ne (show (14:Nat) ≠ (16 : Nat) by omega), up_ne (show (14:Nat) ≠ (16 : Nat) by omega), up_ne (show (14:Nat) ≠ (21 : Nat) by omega), up_ne (show (14:Nat) ≠ (15 : Nat) by omega), up_ne (show (14:Nat) ≠ (20 : Nat) by omega), hf14, up_ne (show (1:Nat) ≠ (13 : Nat) by omega), up_ne (show (1:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (21 : Nat) by omega), up_ne (show (1:Nat) ≠ (15 : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), h1],
              exec_blt_lt_step (by omega) (show prog2.getD 198 Instr.reject = Instr.blt 2 1 179 by rfl) fi9 (by rw [e2_9, e1_9]; omega)]
            simp only [Nat.sub_sub, Nat.reduceAdd]
          obtain ⟨c2, f2, hc2, hex2, harr2, h122, h142, hfit2, hpres2⟩ :=
            ih L b d ak sl out (up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) i (j + 1) (wq + 1) (S - 14) r hsL
              (by omega) (by omega) (by omega)
              e12_9 e13_9 e14_9 e11_9 e17_9 e18_9 e19_9 e1_9 e2_9 esrc_9
              hvfit htake1 hdrop1 hout fi9 hbL hdL h2L hb33 hd33 hdisj
              (by omega) (by omega)
          refine ⟨14 + c2, f2, by omega, ?_, harr2, h122, h142, hfit2, ?_⟩
          · rw [hwalk, hex2]
            have hS14 : S - 14 - c2 = S - (14 + c2) := by omega
            rw [hS14]
          · exact pres_trans (pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) (pres_trans (pres_up (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (pres_trans (pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))) (pres_trans (pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (pres_trans (pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (pres_trans (pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) (pres_trans (pres_up (MReg_dst (by omega) (by omega))) (pres_trans (pres_up (Or.inr (Or.inl rfl))) (pres_trans (pres_up (Or.inr (Or.inr (Or.inl rfl)))) (hpres2)))))))))
        · -- LTAKEL
          have hcmpL : ¬ (sl.map (fun z => z + ak)).getD j 0 < sl.getD i 0 := by
            rw [getD_map_add sl ak j hjl]
            exact hcmp
          have hstep := mmerge_stepL sl (sl.map (fun z => z + ak)) i j
              (by omega) (by omega) hcmpL hB
          have houtwq : out.getD wq 0 = sl.getD i 0 := by
            rw [hout, hwq, hstep.1]
          have hdrop1 : out.drop (wq + 1)
              = mmerge (sl.drop (i + 1)) ((sl.map (fun z => z + ak)).drop j) := by
            rw [hout, show wq + 1 = i + j + 1 from by omega, hstep.2]
          have hA9 : arrL (up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) d (2 * L) = arrL (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) d (2 * L) := by
            rw [show arrL (up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) d (2 * L) = arrL (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) d (2 * L) from arrL_up_out (fun q _ => show (14:Nat) ≠ d + q by omega), show arrL (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) d (2 * L) = arrL (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) d (2 * L) from arrL_up_out (fun q _ => show (12:Nat) ≠ d + q by omega)]
          have hA6 : arrL (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) d (2 * L) = arrL f d (2 * L) := by
            rw [show arrL (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) d (2 * L) = arrL (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) d (2 * L) from arrL_up_out (fun q _ => show (20:Nat) ≠ d + q by omega), show arrL (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) d (2 * L) = arrL (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) d (2 * L) from arrL_up_out (fun q _ => show (16:Nat) ≠ d + q by omega), show arrL (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) d (2 * L) = arrL (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) d (2 * L) from arrL_up_out (fun q _ => show (16:Nat) ≠ d + q by omega), show arrL (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) d (2 * L) = arrL (up (up f 20 (b + i)) 15 (sl.getD i 0)) d (2 * L) from arrL_up_out (fun q _ => show (21:Nat) ≠ d + q by omega), show arrL (up (up f 20 (b + i)) 15 (sl.getD i 0)) d (2 * L) = arrL (up f 20 (b + i)) d (2 * L) from arrL_up_out (fun q _ => show (15:Nat) ≠ d + q by omega), show arrL (up f 20 (b + i)) d (2 * L) = arrL (f) d (2 * L) from arrL_up_out (fun q _ => show (20:Nat) ≠ d + q by omega)]
          have htake1 : out.take (wq + 1) = (arrL (up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) d (2 * L)).take (wq + 1) := by
            rw [hA9, arrL_take_up hwq2L, hA6, ← htake, takeSucc hwqo, houtwq]
          have e1_5 : up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak) 1 = 1 := by
            rw [up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (21 : Nat) by omega), up_ne (show (1:Nat) ≠ (15 : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), h1]
          have e2_5 : up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak) 2 = 0 := by
            rw [up_ne (show (2:Nat) ≠ (16 : Nat) by omega), up_ne (show (2:Nat) ≠ (16 : Nat) by omega), up_ne (show (2:Nat) ≠ (21 : Nat) by omega), up_ne (show (2:Nat) ≠ (15 : Nat) by omega), up_ne (show (2:Nat) ≠ (20 : Nat) by omega), h2]
          have e12_9U : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1) 12 = i + 1 := by
            rw [up_ne (show (12:Nat) ≠ (14 : Nat) by omega), up_eq]
          have e13_9U : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1) 13 = j := by
            rw [up_ne (show (13:Nat) ≠ (14 : Nat) by omega), up_ne (show (13:Nat) ≠ (12 : Nat) by omega), up_ne (show (13:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (13:Nat) ≠ (20 : Nat) by omega), up_ne (show (13:Nat) ≠ (16 : Nat) by omega), up_ne (show (13:Nat) ≠ (16 : Nat) by omega), up_ne (show (13:Nat) ≠ (21 : Nat) by omega), up_ne (show (13:Nat) ≠ (15 : Nat) by omega), up_ne (show (13:Nat) ≠ (20 : Nat) by omega), hf13]
          have e14_9U : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1) 14 = wq + 1 := by
            rw [up_eq]
          have e11_9U : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1) 11 = L := by
            rw [up_ne (show (11:Nat) ≠ (14 : Nat) by omega), up_ne (show (11:Nat) ≠ (12 : Nat) by omega), up_ne (show (11:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (11:Nat) ≠ (20 : Nat) by omega), up_ne (show (11:Nat) ≠ (16 : Nat) by omega), up_ne (show (11:Nat) ≠ (16 : Nat) by omega), up_ne (show (11:Nat) ≠ (21 : Nat) by omega), up_ne (show (11:Nat) ≠ (15 : Nat) by omega), up_ne (show (11:Nat) ≠ (20 : Nat) by omega), hf11]
          have e17_9U : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1) 17 = ak := by
            rw [up_ne (show (17:Nat) ≠ (14 : Nat) by omega), up_ne (show (17:Nat) ≠ (12 : Nat) by omega), up_ne (show (17:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (17:Nat) ≠ (20 : Nat) by omega), up_ne (show (17:Nat) ≠ (16 : Nat) by omega), up_ne (show (17:Nat) ≠ (16 : Nat) by omega), up_ne (show (17:Nat) ≠ (21 : Nat) by omega), up_ne (show (17:Nat) ≠ (15 : Nat) by omega), up_ne (show (17:Nat) ≠ (20 : Nat) by omega), hf17]
          have e18_9U : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1) 18 = b := by
            rw [up_ne (show (18:Nat) ≠ (14 : Nat) by omega), up_ne (show (18:Nat) ≠ (12 : Nat) by omega), up_ne (show (18:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (18:Nat) ≠ (20 : Nat) by omega), up_ne (show (18:Nat) ≠ (16 : Nat) by omega), up_ne (show (18:Nat) ≠ (16 : Nat) by omega), up_ne (show (18:Nat) ≠ (21 : Nat) by omega), up_ne (show (18:Nat) ≠ (15 : Nat) by omega), up_ne (show (18:Nat) ≠ (20 : Nat) by omega), hf18]
          have e19_9U : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1) 19 = d := by
            rw [up_ne (show (19:Nat) ≠ (14 : Nat) by omega), up_ne (show (19:Nat) ≠ (12 : Nat) by omega), up_ne (show (19:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (19:Nat) ≠ (20 : Nat) by omega), up_ne (show (19:Nat) ≠ (16 : Nat) by omega), up_ne (show (19:Nat) ≠ (16 : Nat) by omega), up_ne (show (19:Nat) ≠ (21 : Nat) by omega), up_ne (show (19:Nat) ≠ (15 : Nat) by omega), up_ne (show (19:Nat) ≠ (20 : Nat) by omega), hf19]
          have e1_9U : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1) 1 = 1 := by
            rw [up_ne (show (1:Nat) ≠ (14 : Nat) by omega), up_ne (show (1:Nat) ≠ (12 : Nat) by omega), up_ne (show (1:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (21 : Nat) by omega), up_ne (show (1:Nat) ≠ (15 : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), h1]
          have e2_9U : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1) 2 = 0 := by
            rw [up_ne (show (2:Nat) ≠ (14 : Nat) by omega), up_ne (show (2:Nat) ≠ (12 : Nat) by omega), up_ne (show (2:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (2:Nat) ≠ (20 : Nat) by omega), up_ne (show (2:Nat) ≠ (16 : Nat) by omega), up_ne (show (2:Nat) ≠ (16 : Nat) by omega), up_ne (show (2:Nat) ≠ (21 : Nat) by omega), up_ne (show (2:Nat) ≠ (15 : Nat) by omega), up_ne (show (2:Nat) ≠ (20 : Nat) by omega), h2]
          have esrc_9U : ∀ q, q < L → up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1) (b + q) = sl.getD q 0 := by
            intro q hq
            rw [up_ne (show b + q ≠ (14 : Nat) by omega), up_ne (show b + q ≠ (12 : Nat) by omega), up_ne (Ne.symm (hdisj wq q (by omega) hq)), up_ne (show b + q ≠ (20 : Nat) by omega), up_ne (show b + q ≠ (16 : Nat) by omega), up_ne (show b + q ≠ (16 : Nat) by omega), up_ne (show b + q ≠ (21 : Nat) by omega), up_ne (show b + q ≠ (15 : Nat) by omega), up_ne (show b + q ≠ (20 : Nat) by omega)]
            exact hsrc q hq
          have hwalk : exec prog2 ρ S 179 r (memOf w f)
              = exec prog2 ρ (S - 14) 179 r (memOf w (up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1))) := by
            rw [exec_blt_lt_step (by omega) (show prog2.getD 179 Instr.reject = Instr.blt 13 11 181 by rfl) hfit (by rw [hf13, hf11]; exact hj),
              exec_blt_lt_step (by omega) (show prog2.getD 181 Instr.reject = Instr.blt 12 11 183 by rfl) hfit (by rw [hf12, hf11]; exact hi),
              exec_add_step (by omega) (show prog2.getD 183 Instr.reject = Instr.add 20 18 12 by rfl), show f 18 + f 12 = b + i from by rw [hf18, hf12],
              exec_load_step (by omega) (show prog2.getD 184 Instr.reject = Instr.load 15 20 by rfl) fi1, up_eq, up_ne (show b + i ≠ 20 by omega), hsrc i hi,
              exec_add_step (by omega) (show prog2.getD 185 Instr.reject = Instr.add 21 18 13 by rfl), show up (up f 20 (b + i)) 15 (sl.getD i 0) 18 + up (up f 20 (b + i)) 15 (sl.getD i 0) 13 = b + j from by rw [up_ne (show (18:Nat) ≠ (15 : Nat) by omega), up_ne (show (18:Nat) ≠ (20 : Nat) by omega), hf18, up_ne (show (13:Nat) ≠ (15 : Nat) by omega), up_ne (show (13:Nat) ≠ (20 : Nat) by omega), hf13],
              exec_load_step (by omega) (show prog2.getD 186 Instr.reject = Instr.load 16 21 by rfl) fi3, up_eq, up_ne (show b + j ≠ 21 by omega), up_ne (show b + j ≠ (15 : Nat) by omega), up_ne (show b + j ≠ (20 : Nat) by omega), hsrc j hj,
              exec_add_step (by omega) (show prog2.getD 187 Instr.reject = Instr.add 16 16 17 by rfl), show up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0) 16 + up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0) 17 = sl.getD j 0 + ak from by rw [up_eq, up_ne (show (17:Nat) ≠ (16 : Nat) by omega), up_ne (show (17:Nat) ≠ (21 : Nat) by omega), up_ne (show (17:Nat) ≠ (15 : Nat) by omega), up_ne (show (17:Nat) ≠ (20 : Nat) by omega), hf17],
              exec_blt_ge_step (by omega) (show prog2.getD 188 Instr.reject = Instr.blt 16 15 190 by rfl) fi5 (by rw [e16_5, e15_5]; exact hcmp),
              exec_blt_lt_step (by omega) (show prog2.getD 189 Instr.reject = Instr.blt 2 1 194 by rfl) fi5 (by rw [e2_5, e1_5]; omega),
              exec_add_step (by omega) (show prog2.getD 194 Instr.reject = Instr.add 20 19 14 by rfl), show up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak) 19 + up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak) 14 = d + wq from by rw [up_ne (show (19:Nat) ≠ (16 : Nat) by omega), up_ne (show (19:Nat) ≠ (16 : Nat) by omega), up_ne (show (19:Nat) ≠ (21 : Nat) by omega), up_ne (show (19:Nat) ≠ (15 : Nat) by omega), up_ne (show (19:Nat) ≠ (20 : Nat) by omega), hf19, up_ne (show (14:Nat) ≠ (16 : Nat) by omega), up_ne (show (14:Nat) ≠ (16 : Nat) by omega), up_ne (show (14:Nat) ≠ (21 : Nat) by omega), up_ne (show (14:Nat) ≠ (15 : Nat) by omega), up_ne (show (14:Nat) ≠ (20 : Nat) by omega), hf14],
              exec_store_step (by omega) (show prog2.getD 195 Instr.reject = Instr.store 20 15 by rfl) fi6, up_eq, up_ne (show (15:Nat) ≠ 20 by omega), e15_5,
              exec_add_step (by omega) (show prog2.getD 196 Instr.reject = Instr.add 12 12 1 by rfl), show up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0) 12 + up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0) 1 = i + 1 from by rw [up_ne (show (12:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (12:Nat) ≠ (20 : Nat) by omega), up_ne (show (12:Nat) ≠ (16 : Nat) by omega), up_ne (show (12:Nat) ≠ (16 : Nat) by omega), up_ne (show (12:Nat) ≠ (21 : Nat) by omega), up_ne (show (12:Nat) ≠ (15 : Nat) by omega), up_ne (show (12:Nat) ≠ (20 : Nat) by omega), hf12, up_ne (show (1:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (21 : Nat) by omega), up_ne (show (1:Nat) ≠ (15 : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), h1],
              exec_add_step (by omega) (show prog2.getD 197 Instr.reject = Instr.add 14 14 1 by rfl), show up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1) 14 + up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1) 1 = wq + 1 from by rw [up_ne (show (14:Nat) ≠ (12 : Nat) by omega), up_ne (show (14:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (14:Nat) ≠ (20 : Nat) by omega), up_ne (show (14:Nat) ≠ (16 : Nat) by omega), up_ne (show (14:Nat) ≠ (16 : Nat) by omega), up_ne (show (14:Nat) ≠ (21 : Nat) by omega), up_ne (show (14:Nat) ≠ (15 : Nat) by omega), up_ne (show (14:Nat) ≠ (20 : Nat) by omega), hf14, up_ne (show (1:Nat) ≠ (12 : Nat) by omega), up_ne (show (1:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (21 : Nat) by omega), up_ne (show (1:Nat) ≠ (15 : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), h1],
              exec_blt_lt_step (by omega) (show prog2.getD 198 Instr.reject = Instr.blt 2 1 179 by rfl) fi9U (by rw [e2_9U, e1_9U]; omega)]
            simp only [Nat.sub_sub, Nat.reduceAdd]
          obtain ⟨c2, f2, hc2, hex2, harr2, h122, h142, hfit2, hpres2⟩ :=
            ih L b d ak sl out (up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) (i + 1) j (wq + 1) (S - 14) r hsL
              (by omega) (by omega) (by omega)
              e12_9U e13_9U e14_9U e11_9U e17_9U e18_9U e19_9U e1_9U e2_9U esrc_9U
              hvfit htake1 hdrop1 hout fi9U hbL hdL h2L hb33 hd33 hdisj
              (by omega) (by omega)
          refine ⟨14 + c2, f2, by omega, ?_, harr2, h122, h142, hfit2, ?_⟩
          · rw [hwalk, hex2]
            have hS14 : S - 14 - c2 = S - (14 + c2) := by omega
            rw [hS14]
          · exact pres_trans (pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) (pres_trans (pres_up (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (pres_trans (pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))) (pres_trans (pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (pres_trans (pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (pres_trans (pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) (pres_trans (pres_up (MReg_dst (by omega) (by omega))) (pres_trans (pres_up (Or.inl rfl)) (pres_trans (pres_up (Or.inr (Or.inr (Or.inl rfl)))) (hpres2)))))))))
      · have hiL : i = L := by omega
        have hdropDJ : out.drop wq = (sl.map (fun z => z + ak)).drop j := by
          rw [hdrop, hiL, dropNil (by rw [hsL]; exact Nat.le_refl L), mmerge_nil_l]
        have hwalkB : exec prog2 ρ S 179 r (memOf w f)
            = exec prog2 ρ (S - 3) 209 r (memOf w f) := by
          rw [exec_blt_lt_step (by omega)
              (show prog2.getD 179 Instr.reject = Instr.blt 13 11 181 by rfl) hfit
              (by rw [hf13, hf11]; exact hj),
            exec_blt_ge_step (by omega)
              (show prog2.getD 181 Instr.reject = Instr.blt 12 11 183 by rfl) hfit
              (by rw [hf12, hf11, hiL]; omega),
            exec_blt_lt_step (by omega)
              (show prog2.getD 182 Instr.reject = Instr.blt 2 1 209 by rfl) hfit
              (by rw [h2, h1]; omega)]
          simp only [Nat.sub_sub, Nat.reduceAdd]
        obtain ⟨c2, f2, hc2, hex2, harr2, h122, h132, h142, hfit2, hpres2⟩ :=
          djLoop_exec_m2 ρ (L - j) L b d ak sl out f j wq (S - 3) r hsL hj
            (by omega) (by rw [hf12, hiL]) hf13 hf14 hf11 hf17 hf18 hf19 h1 h2
            hsrc hvfit htake hdropDJ hfit hbL hdL h2L hb33 hd33 hdisj
            (Nat.le_refl _) (by omega)
        refine ⟨3 + c2, f2, by omega, ?_, harr2, h122, h142, hfit2, hpres2⟩
        · rw [hwalkB, hex2]
          have hS3 : S - 3 - c2 = S - (3 + c2) := by omega
          rw [hS3]
    · have hjL : j = L := by omega
      by_cases hi2 : i < L
      · have hdropDI : out.drop wq = sl.drop i := by
          have hmd : (sl.map (fun z => z + ak)).drop L = [] := dropNil (by omega)
          rw [hdrop, hjL, hmd, mmerge_nil_r]
        have hvfit0 : ∀ v ∈ sl, v < 2 ^ w := fun v hv => by
          have := hvfit v hv
          omega
        have hwalkA1 : exec prog2 ρ S 179 r (memOf w f)
            = exec prog2 ρ (S - 3) 201 r (memOf w f) := by
          rw [exec_blt_ge_step (by omega)
              (show prog2.getD 179 Instr.reject = Instr.blt 13 11 181 by rfl) hfit
              (by rw [hf13, hf11]; exact hj),
            exec_blt_lt_step (by omega)
              (show prog2.getD 180 Instr.reject = Instr.blt 2 1 199 by rfl) hfit
              (by rw [h2, h1]; omega),
            exec_blt_lt_step (by omega)
              (show prog2.getD 199 Instr.reject = Instr.blt 12 11 201 by rfl) hfit
              (by rw [hf12, hf11]; exact hi2)]
          simp only [Nat.sub_sub, Nat.reduceAdd]
        obtain ⟨c2, f2, hc2, hex2, harr2, h122, h142, hfit2, hpres2⟩ :=
          diLoop_exec_m2 ρ (L - i) L b d sl out f i wq (S - 3) r hsL hi2
            (by omega) hf12 hf14 hf11 hf18 hf19 h1 h2
            hsrc hvfit0 htake hdropDI hfit hbL hdL h2L hb33 hd33 hdisj
            (Nat.le_refl _) (by omega)
        refine ⟨3 + c2, f2, by omega, ?_, harr2, h122, h142, hfit2, hpres2⟩
        · rw [hwalkA1, hex2]
          have hS3 : S - 3 - c2 = S - (3 + c2) := by omega
          rw [hS3]
      · have hw2 : wq = 2 * L := by omega
        have hlen : out.length = 2 * L := by
          rw [hout, mmerge_length, List.length_map, hsL]
          omega
        have hfull : arrL f d (2 * L) = out := by
          rw [hw2] at htake
          have hto := takeAll (l := out) (n := 2 * L) (by omega)
          have hla : (arrL f d (2 * L)).length = 2 * L := by simp [arrL]
          have hta := takeAll (l := arrL f d (2 * L)) (n := 2 * L) (by omega)
          rw [← hta, ← hto, htake]
        refine ⟨4, f, by omega, ?_, hfull, by omega, by omega, hfit, ?_⟩
        · rw [exec_blt_ge_step (by omega)
              (show prog2.getD 179 Instr.reject = Instr.blt 13 11 181 by rfl) hfit
              (by rw [hf13, hf11]; omega),
            exec_blt_lt_step (by omega)
              (show prog2.getD 180 Instr.reject = Instr.blt 2 1 199 by rfl) hfit
              (by rw [h2, h1]; omega),
            exec_blt_ge_step (by omega)
              (show prog2.getD 199 Instr.reject = Instr.blt 12 11 201 by rfl) hfit
              (by rw [hf12, hf11]; omega),
            exec_blt_lt_step (by omega)
              (show prog2.getD 200 Instr.reject = Instr.blt 2 1 217 by rfl) hfit
              (by rw [h2, h1]; omega)]
          simp only [Nat.sub_sub, Nat.reduceAdd]
        · intro x hx
          rfl
/-! ## §2. The phaseA2 drivers (hand-adapted) -/

namespace Merge2

/-- The LSWAP2 tail (pc 217–222): like `lswap_exec` but the guard bound
`[21] := [4]+1 = m+1` reads cell 4 (phaseA read `[9] = h`). -/
theorem lswap2_exec {w : Nat} {P : List Instr} {ρ : Nat → BitVec w} {f : Nat → Nat}
    {S r pc L b d k mb : Nat}
    (h11 : f 11 = L) (h1 : f 1 = 1) (h2 : f 2 = 0) (h4 : f 4 = mb)
    (h10 : f 10 = k) (h18 : f 18 = b) (h19 : f 19 = d)
    (c1 : P.getD pc Instr.reject = Instr.add 11 11 11)
    (c2 : P.getD (pc + 1) Instr.reject = Instr.add 20 18 2)
    (c3 : P.getD (pc + 2) Instr.reject = Instr.add 18 19 2)
    (c4 : P.getD (pc + 3) Instr.reject = Instr.add 19 20 2)
    (c5 : P.getD (pc + 4) Instr.reject = Instr.add 10 10 1)
    (c6 : P.getD (pc + 5) Instr.reject = Instr.add 21 4 1)
    (hS : 6 ≤ S) :
    exec P ρ S pc r (memOf w f)
      = exec P ρ (S - 6) (pc + 6) r
          (memOf w (up (up (up (up (up (up f 11 (2 * L)) 20 b) 18 d) 19 b)
            10 (k + 1)) 21 (mb + 1))) := by
  rw [exec_add_step (by omega) c1,
      show f 11 + f 11 = 2 * L from by omega,
      exec_add_step (by omega) c2,
      show (up f 11 (2 * L)) 18 + (up f 11 (2 * L)) 2 = b from by
        rw [up_ne (show (18:Nat) ≠ 11 by omega),
            up_ne (show (2:Nat) ≠ 11 by omega), h18, h2, Nat.add_zero],
      exec_add_step (by omega) c3,
      show (up (up f 11 (2 * L)) 20 b) 19 + (up (up f 11 (2 * L)) 20 b) 2 = d from by
        rw [up_ne (show (19:Nat) ≠ 20 by omega),
            up_ne (show (19:Nat) ≠ 11 by omega),
            up_ne (show (2:Nat) ≠ 20 by omega),
            up_ne (show (2:Nat) ≠ 11 by omega), h19, h2, Nat.add_zero],
      exec_add_step (by omega) c4,
      show (up (up (up f 11 (2 * L)) 20 b) 18 d) 20
          + (up (up (up f 11 (2 * L)) 20 b) 18 d) 2 = b from by
        rw [up_ne (show (20:Nat) ≠ 18 by omega), up_eq,
            up_ne (show (2:Nat) ≠ 18 by omega),
            up_ne (show (2:Nat) ≠ 20 by omega),
            up_ne (show (2:Nat) ≠ 11 by omega), h2, Nat.add_zero],
      exec_add_step (by omega) c5,
      show (up (up (up (up f 11 (2 * L)) 20 b) 18 d) 19 b) 10
          + (up (up (up (up f 11 (2 * L)) 20 b) 18 d) 19 b) 1 = k + 1 from by
        rw [up_ne (show (10:Nat) ≠ 19 by omega),
            up_ne (show (10:Nat) ≠ 18 by omega),
            up_ne (show (10:Nat) ≠ 20 by omega),
            up_ne (show (10:Nat) ≠ 11 by omega), h10,
            up_ne (show (1:Nat) ≠ 19 by omega),
            up_ne (show (1:Nat) ≠ 18 by omega),
            up_ne (show (1:Nat) ≠ 20 by omega),
            up_ne (show (1:Nat) ≠ 11 by omega), h1],
      exec_add_step (by omega) c6,
      show (up (up (up (up (up f 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 4
          + (up (up (up (up (up f 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 1
          = mb + 1 from by
        rw [up_ne (show (4:Nat) ≠ 10 by omega),
            up_ne (show (4:Nat) ≠ 19 by omega),
            up_ne (show (4:Nat) ≠ 18 by omega),
            up_ne (show (4:Nat) ≠ 20 by omega),
            up_ne (show (4:Nat) ≠ 11 by omega), h4,
            up_ne (show (1:Nat) ≠ 10 by omega),
            up_ne (show (1:Nat) ≠ 19 by omega),
            up_ne (show (1:Nat) ≠ 18 by omega),
            up_ne (show (1:Nat) ≠ 20 by omega),
            up_ne (show (1:Nat) ≠ 11 by omega), h1]]
  simp only [Nat.sub_sub, Nat.reduceAdd]

/-- phaseA2 init (pcs 161–172, 12 steps): `[5] := H`, `[4] := m = n−h`,
`M := 1 <<< m = 2^m`, `B2 := [22]+H+1`, `B3 := B2+M+1`, `L := 1`,
`S₂₀ := [0]` at B2, `k := 1`.  Lands at LROUND2 = 173. -/
theorem init2_exec {w n : Nat} (ρ : Nat → BitVec w) {x : Instance n}
    (hn : 4 ≤ n)
    (f0 : Nat → Nat) (r S : Nat) (h m H M B2 B3 A1 : Nat)
    (hfit : ∀ q, f0 q < 2 ^ w)
    (h1 : f0 1 = 1) (h2 : f0 2 = 0) (h7 : f0 7 = n) (h8 : f0 8 = 2 * n + 23)
    (h9 : f0 9 = h) (hh : h = n / 2) (hm : m = n - h)
    (h11 : f0 11 = H) (hH : H = 2 ^ (n / 2))
    (h22 : f0 22 = A1) (hA1 : A1 = 3 * n + 25)
    (hB2 : B2 = A1 + H + 1) (hB3 : B3 = B2 + M + 1) (hM : M = 2 ^ m)
    (hpow : 2 ^ (2 * n) ≤ 2 ^ w)
    (harr : arrL f0 A1 H = halfSums (instA x) h)
    (hS : 12 ≤ S) :
    ∃ f1, exec prog2 ρ S 161 r (memOf w f0)
        = exec prog2 ρ (S - 12) 173 r (memOf w f1) ∧
      (∀ q, f1 q < 2 ^ w) ∧
      f1 4 = m ∧ f1 5 = H ∧ f1 9 = h ∧ f1 10 = 1 ∧ f1 11 = 1 ∧
      f1 18 = B2 ∧ f1 19 = B3 ∧ f1 22 = A1 ∧
      f1 1 = 1 ∧ f1 2 = 0 ∧ f1 7 = n ∧ f1 8 = 2 * n + 23 ∧
      arrL f1 B2 1 = [0] ∧
      arrL f1 A1 H = halfSums (instA x) h ∧
      Pres (AReg2 n) f0 f1 := by
  have hm_eq : h + m = n := by omega
  have hmn : m ≤ n := by omega
  have henv : ∀ c, c ≤ 3 * n + 27 + 2 ^ (n / 2) + 2 * 2 ^ (n - n / 2) → c < 2 ^ w := by
    intro c hc
    have := pro_addr_lt2 n hn
    omega
  have hHe : H = 2 ^ (n / 2) := hH
  have h2m : 2 ^ m < 2 ^ w := by
    have hle : m ≤ n - n / 2 := by omega
    have hpx : 2 ^ m ≤ 2 ^ (n - n / 2) :=
      Nat.pow_le_pow_right (n := 2) (by omega) hle
    exact henv (2 ^ m) (by omega)
  have hHw : H < 2 ^ w := henv H (by omega)
  have hmw : m < 2 ^ w := henv m (by omega)
  have h1w : (1:Nat) < 2 ^ w := by
    have := Nat.one_le_two_pow (n := w)
    omega
  have h0w : (0:Nat) < 2 ^ w := by
    have := Nat.one_le_two_pow (n := w)
    omega
  have f1f : ∀ q, (up f0 5 H) q < 2 ^ w := up_fit hfit hHw
  have he162 : (up f0 5 H) 7 - (up f0 5 H) 9 = m := by
    rw [up_ne (show (7:Nat) ≠ 5 by omega), h7,
      up_ne (show (9:Nat) ≠ 5 by omega), h9]
    omega
  have f2f : ∀ q, (up (up f0 5 H) 4 m) q < 2 ^ w := up_fit f1f hmw
  have he163 : (up (up f0 5 H) 4 m) 1 + (up (up f0 5 H) 4 m) 2 = 1 := by
    rw [up_ne (show (1:Nat) ≠ 4 by omega), up_ne (show (1:Nat) ≠ 5 by omega), h1,
      up_ne (show (2:Nat) ≠ 4 by omega), up_ne (show (2:Nat) ≠ 5 by omega), h2]
  have f3f : ∀ q, (up (up (up f0 5 H) 4 m) 20 1) q < 2 ^ w :=
    up_fit f2f h1w
  have he164 : (up (up (up f0 5 H) 4 m) 20 1) 20
      * 2 ^ (up (up (up f0 5 H) 4 m) 20 1) 4 = 2 ^ m := by
    rw [up_eq, up_ne (show (4:Nat) ≠ 20 by omega), up_eq, Nat.one_mul]
  have f4f : ∀ q, (up (up (up (up f0 5 H) 4 m) 20 1) 20 (2 ^ m)) q < 2 ^ w :=
    up_fit f3f h2m
  have he165 : (up (up (up (up f0 5 H) 4 m) 20 1) 20 (2 ^ m)) 22
      + (up (up (up (up f0 5 H) 4 m) 20 1) 20 (2 ^ m)) 11 = A1 + H := by
    rw [up_ne (show (22:Nat) ≠ 20 by omega), up_ne (show (22:Nat) ≠ 20 by omega),
      up_ne (show (22:Nat) ≠ 4 by omega), up_ne (show (22:Nat) ≠ 5 by omega), h22,
      up_ne (show (11:Nat) ≠ 20 by omega), up_ne (show (11:Nat) ≠ 20 by omega),
      up_ne (show (11:Nat) ≠ 4 by omega), up_ne (show (11:Nat) ≠ 5 by omega), h11]
  have f5f : ∀ q, (up (up (up (up (up f0 5 H) 4 m) 20 1) 20 (2 ^ m)) 18 (A1 + H)) q < 2 ^ w :=
    up_fit f4f (henv (A1 + H) (by
      have hA1e : A1 = 3 * n + 25 := hA1
      omega))
  have he166 : (up (up (up (up (up f0 5 H) 4 m) 20 1) 20 (2 ^ m)) 18 (A1 + H)) 18
      + (up (up (up (up (up f0 5 H) 4 m) 20 1) 20 (2 ^ m)) 18 (A1 + H)) 1 = B2 := by
    rw [up_eq,
      up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 20 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega), up_ne (show (1:Nat) ≠ 4 by omega),
      up_ne (show (1:Nat) ≠ 5 by omega), h1]
    omega
  have f6f : ∀ q, (up (up (up (up (up (up f0 5 H) 4 m) 20 1) 20 (2 ^ m)) 18 (A1 + H)) 18 B2) q < 2 ^ w :=
    up_fit f5f (henv B2 (by
      have hB2e : B2 = 3 * n + 26 + 2 ^ (n / 2) := by
        rw [hB2, hA1, hH]
        omega
      omega))
  have he167 : (up (up (up (up (up (up f0 5 H) 4 m) 20 1) 20 (2 ^ m)) 18 (A1 + H)) 18 B2) 18
      + (up (up (up (up (up (up f0 5 H) 4 m) 20 1) 20 (2 ^ m)) 18 (A1 + H)) 18 B2) 20 = B2 + M := by
    rw [up_eq,
      up_ne (show (20:Nat) ≠ 18 by omega),
      up_ne (show (20:Nat) ≠ 18 by omega), up_eq,
      show (2:Nat) ^ m = M from by rw [← hM]]
  have f7f : ∀ q, (up (up (up (up (up (up (up f0 5 H) 4 m) 20 1) 20 (2 ^ m)) 18 (A1 + H)) 18 B2) 19 (B2 + M)) q < 2 ^ w :=
    up_fit f6f (henv (B2 + M) (by
      have hB2e : B2 = 3 * n + 26 + 2 ^ (n / 2) := by
        rw [hB2, hA1, hH]
        omega
      have hMe : M = 2 ^ (n - n / 2) := by rw [hM, hm, hh]
      omega))
  have he168 : (up (up (up (up (up (up (up f0 5 H) 4 m) 20 1) 20 (2 ^ m)) 18 (A1 + H)) 18 B2) 19 (B2 + M)) 19
      + (up (up (up (up (up (up (up f0 5 H) 4 m) 20 1) 20 (2 ^ m)) 18 (A1 + H)) 18 B2) 19 (B2 + M)) 1 = B3 := by
    rw [up_eq,
      up_ne (show (1:Nat) ≠ 19 by omega), up_ne (show (1:Nat) ≠ 18 by omega),
      up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 20 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega), up_ne (show (1:Nat) ≠ 4 by omega),
      up_ne (show (1:Nat) ≠ 5 by omega), h1]
    omega
  have f8f : ∀ q, (up (up (up (up (up (up (up (up f0 5 H) 4 m) 20 1) 20 (2 ^ m)) 18 (A1 + H)) 18 B2) 19 (B2 + M)) 19 B3) q < 2 ^ w :=
    up_fit f7f (henv B3 (by
      have hB2e : B2 = 3 * n + 26 + 2 ^ (n / 2) := by
        rw [hB2, hA1, hH]
        omega
      have hMe : M = 2 ^ (n - n / 2) := by rw [hM, hm, hh]
      omega))
  have he169 : (up (up (up (up (up (up (up (up f0 5 H) 4 m) 20 1) 20 (2 ^ m)) 18 (A1 + H)) 18 B2) 19 (B2 + M)) 19 B3) 1
      + (up (up (up (up (up (up (up (up f0 5 H) 4 m) 20 1) 20 (2 ^ m)) 18 (A1 + H)) 18 B2) 19 (B2 + M)) 19 B3) 2 = 1 := by
    rw [up_ne (show (1:Nat) ≠ 19 by omega), up_ne (show (1:Nat) ≠ 19 by omega),
      up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 18 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega), up_ne (show (1:Nat) ≠ 20 by omega),
      up_ne (show (1:Nat) ≠ 4 by omega), up_ne (show (1:Nat) ≠ 5 by omega), h1,
      up_ne (show (2:Nat) ≠ 19 by omega), up_ne (show (2:Nat) ≠ 19 by omega),
      up_ne (show (2:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega),
      up_ne (show (2:Nat) ≠ 20 by omega), up_ne (show (2:Nat) ≠ 20 by omega),
      up_ne (show (2:Nat) ≠ 4 by omega), up_ne (show (2:Nat) ≠ 5 by omega), h2]
  have f9f : ∀ q, (up (up (up (up (up (up (up (up (up f0 5 H) 4 m) 20 1) 20 (2 ^ m)) 18 (A1 + H)) 18 B2) 19 (B2 + M)) 19 B3) 11 1) q < 2 ^ w :=
    up_fit f8f h1w
  have he170 : (up (up (up (up (up (up (up (up (up f0 5 H) 4 m) 20 1) 20 (2 ^ m)) 18 (A1 + H)) 18 B2) 19 (B2 + M)) 19 B3) 11 1) 18
      + (up (up (up (up (up (up (up (up (up f0 5 H) 4 m) 20 1) 20 (2 ^ m)) 18 (A1 + H)) 18 B2) 19 (B2 + M)) 19 B3) 11 1) 2 = B2 := by
    rw [up_ne (show (18:Nat) ≠ 11 by omega), up_ne (show (18:Nat) ≠ 19 by omega),
      up_ne (show (18:Nat) ≠ 19 by omega), up_eq,
      up_ne (show (2:Nat) ≠ 11 by omega), up_ne (show (2:Nat) ≠ 19 by omega),
      up_ne (show (2:Nat) ≠ 19 by omega), up_ne (show (2:Nat) ≠ 18 by omega),
      up_ne (show (2:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 20 by omega),
      up_ne (show (2:Nat) ≠ 20 by omega), up_ne (show (2:Nat) ≠ 4 by omega),
      up_ne (show (2:Nat) ≠ 5 by omega), h2, Nat.add_zero]
  have f10f : ∀ q, (up (up (up (up (up (up (up (up (up (up f0 5 H) 4 m) 20 1) 20 (2 ^ m)) 18 (A1 + H)) 18 B2) 19 (B2 + M)) 19 B3) 11 1) 20 B2) q < 2 ^ w :=
    up_fit f9f (henv B2 (by
      have hB2e : B2 = 3 * n + 26 + 2 ^ (n / 2) := by
        rw [hB2, hA1, hH]
        omega
      omega))
  have h2B2 : (up (up (up (up (up (up (up (up (up (up f0 5 H) 4 m) 20 1) 20 (2 ^ m)) 18 (A1 + H)) 18 B2) 19 (B2 + M)) 19 B3) 11 1) 20 B2) 2 = 0 := by
    rw [up_ne (show (2:Nat) ≠ 20 by omega), up_ne (show (2:Nat) ≠ 11 by omega),
      up_ne (show (2:Nat) ≠ 19 by omega), up_ne (show (2:Nat) ≠ 19 by omega),
      up_ne (show (2:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega),
      up_ne (show (2:Nat) ≠ 20 by omega), up_ne (show (2:Nat) ≠ 20 by omega),
      up_ne (show (2:Nat) ≠ 4 by omega), up_ne (show (2:Nat) ≠ 5 by omega), h2]
  have f11f : ∀ q, (up (up (up (up (up (up (up (up (up (up (up f0 5 H) 4 m) 20 1) 20 (2 ^ m)) 18 (A1 + H)) 18 B2) 19 (B2 + M)) 19 B3) 11 1) 20 B2) B2 0) q < 2 ^ w :=
    up_fit f10f h0w
  have he172 : (up (up (up (up (up (up (up (up (up (up (up f0 5 H) 4 m) 20 1) 20 (2 ^ m)) 18 (A1 + H)) 18 B2) 19 (B2 + M)) 19 B3) 11 1) 20 B2) B2 0) 1
      + (up (up (up (up (up (up (up (up (up (up (up f0 5 H) 4 m) 20 1) 20 (2 ^ m)) 18 (A1 + H)) 18 B2) 19 (B2 + M)) 19 B3) 11 1) 20 B2) B2 0) 2 = 1 := by
    rw [up_ne (show (1:Nat) ≠ B2 by omega), up_ne (show (1:Nat) ≠ 20 by omega),
      up_ne (show (1:Nat) ≠ 11 by omega), up_ne (show (1:Nat) ≠ 19 by omega),
      up_ne (show (1:Nat) ≠ 19 by omega), up_ne (show (1:Nat) ≠ 18 by omega),
      up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 20 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega), up_ne (show (1:Nat) ≠ 4 by omega),
      up_ne (show (1:Nat) ≠ 5 by omega), h1,
      up_ne (show (2:Nat) ≠ B2 by omega), h2B2]
  have f12f : ∀ q, (up (up (up (up (up (up (up (up (up (up (up (up f0 5 H) 4 m) 20 1) 20 (2 ^ m)) 18 (A1 + H)) 18 B2) 19 (B2 + M)) 19 B3) 11 1) 20 B2) B2 0) 10 1) q < 2 ^ w :=
    up_fit f11f h1w
  have harrA1 : arrL (up (up (up (up (up (up (up (up (up (up (up (up f0 5 H) 4 m) 20 1) 20 (2 ^ m)) 18 (A1 + H)) 18 B2) 19 (B2 + M)) 19 B3) 11 1) 20 B2) B2 0) 10 1) A1 H
      = halfSums (instA x) h := by
    have hcong : arrL (up (up (up (up (up (up (up (up (up (up (up (up f0 5 H) 4 m) 20 1) 20 (2 ^ m)) 18 (A1 + H)) 18 B2) 19 (B2 + M)) 19 B3) 11 1) 20 B2) B2 0) 10 1) A1 H
        = arrL f0 A1 H := by
      rw [arrL_up_out (fun q _ => show (10:Nat) ≠ A1 + q by
            have hA1e : A1 = 3 * n + 25 := hA1; omega),
        arrL_up_out (fun q hq => show B2 ≠ A1 + q by
          have hB2e : B2 = A1 + H + 1 := hB2
          omega),
        arrL_up_out (fun q _ => show (20:Nat) ≠ A1 + q by
            have hA1e : A1 = 3 * n + 25 := hA1; omega),
        arrL_up_out (fun q _ => show (11:Nat) ≠ A1 + q by
            have hA1e : A1 = 3 * n + 25 := hA1; omega),
        arrL_up_out (fun q _ => show (19:Nat) ≠ A1 + q by
            have hA1e : A1 = 3 * n + 25 := hA1; omega),
        arrL_up_out (fun q _ => show (19:Nat) ≠ A1 + q by
            have hA1e : A1 = 3 * n + 25 := hA1; omega),
        arrL_up_out (fun q _ => show (18:Nat) ≠ A1 + q by
            have hA1e : A1 = 3 * n + 25 := hA1; omega),
        arrL_up_out (fun q _ => show (18:Nat) ≠ A1 + q by
            have hA1e : A1 = 3 * n + 25 := hA1; omega),
        arrL_up_out (fun q _ => show (20:Nat) ≠ A1 + q by
            have hA1e : A1 = 3 * n + 25 := hA1; omega),
        arrL_up_out (fun q _ => show (20:Nat) ≠ A1 + q by
            have hA1e : A1 = 3 * n + 25 := hA1; omega),
        arrL_up_out (fun q _ => show (4:Nat) ≠ A1 + q by
            have hA1e : A1 = 3 * n + 25 := hA1; omega),
        arrL_up_out (fun q _ => show (5:Nat) ≠ A1 + q by
            have hA1e : A1 = 3 * n + 25 := hA1; omega)]
    rw [hcong, harr]
  have hpresA : Pres (AReg2 n) f0 (up (up (up (up (up (up (up (up (up (up (up (up f0 5 H) 4 m) 20 1) 20 (2 ^ m)) 18 (A1 + H)) 18 B2) 19 (B2 + M)) 19 B3) 11 1) 20 B2) B2 0) 10 1) := by
      have hreg : ∀ c, c ≤ 22 → AReg2 n c := fun c hc => Or.inl hc
      have hB2reg : AReg2 n B2 := by
        refine Or.inr ⟨?_, ?_⟩
        · have hB2e : B2 = 3 * n + 26 + 2 ^ (n / 2) := by
            rw [hB2, hA1, hH]
            omega
          omega
        · have hB2e : B2 = 3 * n + 26 + 2 ^ (n / 2) := by
            rw [hB2, hA1, hH]
            omega
          have hpp : 2 ^ (n / 2) ≤ 2 ^ (n - n / 2) :=
            Nat.pow_le_pow_right (n := 2) (by omega) (by omega)
          omega
      exact pres_trans (pres_up (hreg 5 (by omega)))
        (pres_trans (pres_up (hreg 4 (by omega)))
        (pres_trans (pres_up (hreg 20 (by omega)))
        (pres_trans (pres_up (hreg 20 (by omega)))
        (pres_trans (pres_up (hreg 18 (by omega)))
        (pres_trans (pres_up (hreg 18 (by omega)))
        (pres_trans (pres_up (hreg 19 (by omega)))
        (pres_trans (pres_up (hreg 19 (by omega)))
        (pres_trans (pres_up (hreg 11 (by omega)))
        (pres_trans (pres_up (hreg 20 (by omega)))
        (pres_trans (pres_up hB2reg)
        (pres_up (hreg 10 (by omega)))))))))))))
  refine ⟨(up (up (up (up (up (up (up (up (up (up (up (up f0 5 H) 4 m) 20 1) 20 (2 ^ m)) 18 (A1 + H)) 18 B2) 19 (B2 + M)) 19 B3) 11 1) 20 B2) B2 0) 10 1),
    ?_, f12f, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, harrA1, hpresA⟩
  · rw [exec_add_step (by omega)
        (show prog2.getD 161 Instr.reject = Instr.add 5 11 2 by rfl),
      show f0 11 + f0 2 = H from by rw [h11, h2, Nat.add_zero],
    exec_sub_step (by omega)
        (show prog2.getD 162 Instr.reject = Instr.sub 4 7 9 by rfl) f1f
      (by rw [up_ne (show (9:Nat) ≠ 5 by omega), h9,
            up_ne (show (7:Nat) ≠ 5 by omega), h7]; omega),
      he162,
    exec_add_step (by omega)
        (show prog2.getD 163 Instr.reject = Instr.add 20 1 2 by rfl), he163,
    exec_shl_step (by omega)
        (show prog2.getD 164 Instr.reject = Instr.shl 20 20 4 by rfl) f3f
      (by rw [he164]; exact h2m),
      he164,
    exec_add_step (by omega)
        (show prog2.getD 165 Instr.reject = Instr.add 18 22 11 by rfl), he165,
    exec_add_step (by omega)
        (show prog2.getD 166 Instr.reject = Instr.add 18 18 1 by rfl), he166,
    exec_add_step (by omega)
        (show prog2.getD 167 Instr.reject = Instr.add 19 18 20 by rfl), he167,
    exec_add_step (by omega)
        (show prog2.getD 168 Instr.reject = Instr.add 19 19 1 by rfl), he168,
    exec_add_step (by omega)
        (show prog2.getD 169 Instr.reject = Instr.add 11 1 2 by rfl), he169,
    exec_add_step (by omega)
        (show prog2.getD 170 Instr.reject = Instr.add 20 18 2 by rfl), he170,
    exec_store_step (by omega)
        (show prog2.getD 171 Instr.reject = Instr.store 20 2 by rfl) f10f,
      up_eq, h2B2,
    exec_add_step (by omega)
        (show prog2.getD 172 Instr.reject = Instr.add 10 1 2 by rfl), he172]
    simp only [Nat.sub_sub, Nat.reduceAdd]
  · rw [up_ne (show (4:Nat) ≠ 10 by omega), up_ne (show (4:Nat) ≠ B2 by omega),
      up_ne (show (4:Nat) ≠ 20 by omega), up_ne (show (4:Nat) ≠ 11 by omega),
      up_ne (show (4:Nat) ≠ 19 by omega), up_ne (show (4:Nat) ≠ 19 by omega),
      up_ne (show (4:Nat) ≠ 18 by omega), up_ne (show (4:Nat) ≠ 18 by omega),
      up_ne (show (4:Nat) ≠ 20 by omega), up_ne (show (4:Nat) ≠ 20 by omega),
      up_eq]
  · rw [up_ne (show (5:Nat) ≠ 10 by omega), up_ne (show (5:Nat) ≠ B2 by omega),
      up_ne (show (5:Nat) ≠ 20 by omega), up_ne (show (5:Nat) ≠ 11 by omega),
      up_ne (show (5:Nat) ≠ 19 by omega), up_ne (show (5:Nat) ≠ 19 by omega),
      up_ne (show (5:Nat) ≠ 18 by omega), up_ne (show (5:Nat) ≠ 18 by omega),
      up_ne (show (5:Nat) ≠ 20 by omega), up_ne (show (5:Nat) ≠ 20 by omega),
      up_ne (show (5:Nat) ≠ 4 by omega), up_eq]
  · rw [up_ne (show (9:Nat) ≠ 10 by omega), up_ne (show (9:Nat) ≠ B2 by omega),
      up_ne (show (9:Nat) ≠ 20 by omega), up_ne (show (9:Nat) ≠ 11 by omega),
      up_ne (show (9:Nat) ≠ 19 by omega), up_ne (show (9:Nat) ≠ 19 by omega),
      up_ne (show (9:Nat) ≠ 18 by omega), up_ne (show (9:Nat) ≠ 18 by omega),
      up_ne (show (9:Nat) ≠ 20 by omega), up_ne (show (9:Nat) ≠ 20 by omega),
      up_ne (show (9:Nat) ≠ 4 by omega), up_ne (show (9:Nat) ≠ 5 by omega), h9]
  · exact up_eq _ _ _
  · rw [up_ne (show (11:Nat) ≠ 10 by omega), up_ne (show (11:Nat) ≠ B2 by omega),
      up_ne (show (11:Nat) ≠ 20 by omega), up_eq]
  · rw [up_ne (show (18:Nat) ≠ 10 by omega), up_ne (show (18:Nat) ≠ B2 by omega),
      up_ne (show (18:Nat) ≠ 20 by omega), up_ne (show (18:Nat) ≠ 11 by omega),
      up_ne (show (18:Nat) ≠ 19 by omega), up_ne (show (18:Nat) ≠ 19 by omega),
      up_eq]
  · rw [up_ne (show (19:Nat) ≠ 10 by omega), up_ne (show (19:Nat) ≠ B2 by omega),
      up_ne (show (19:Nat) ≠ 20 by omega), up_ne (show (19:Nat) ≠ 11 by omega),
      up_eq]
  · rw [up_ne (show (22:Nat) ≠ 10 by omega), up_ne (show (22:Nat) ≠ B2 by omega),
      up_ne (show (22:Nat) ≠ 20 by omega), up_ne (show (22:Nat) ≠ 11 by omega),
      up_ne (show (22:Nat) ≠ 19 by omega), up_ne (show (22:Nat) ≠ 19 by omega),
      up_ne (show (22:Nat) ≠ 18 by omega), up_ne (show (22:Nat) ≠ 18 by omega),
      up_ne (show (22:Nat) ≠ 20 by omega), up_ne (show (22:Nat) ≠ 20 by omega),
      up_ne (show (22:Nat) ≠ 4 by omega), up_ne (show (22:Nat) ≠ 5 by omega), h22]
  · rw [up_ne (show (1:Nat) ≠ 10 by omega), up_ne (show (1:Nat) ≠ B2 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega), up_ne (show (1:Nat) ≠ 11 by omega),
      up_ne (show (1:Nat) ≠ 19 by omega), up_ne (show (1:Nat) ≠ 19 by omega),
      up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 18 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega), up_ne (show (1:Nat) ≠ 20 by omega),
      up_ne (show (1:Nat) ≠ 4 by omega), up_ne (show (1:Nat) ≠ 5 by omega), h1]
  · rw [up_ne (show (2:Nat) ≠ 10 by omega), up_ne (show (2:Nat) ≠ B2 by omega),
      up_ne (show (2:Nat) ≠ 20 by omega), up_ne (show (2:Nat) ≠ 11 by omega),
      up_ne (show (2:Nat) ≠ 19 by omega), up_ne (show (2:Nat) ≠ 19 by omega),
      up_ne (show (2:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega),
      up_ne (show (2:Nat) ≠ 20 by omega), up_ne (show (2:Nat) ≠ 20 by omega),
      up_ne (show (2:Nat) ≠ 4 by omega), up_ne (show (2:Nat) ≠ 5 by omega), h2]
  · rw [up_ne (show (7:Nat) ≠ 10 by omega), up_ne (show (7:Nat) ≠ B2 by omega),
      up_ne (show (7:Nat) ≠ 20 by omega), up_ne (show (7:Nat) ≠ 11 by omega),
      up_ne (show (7:Nat) ≠ 19 by omega), up_ne (show (7:Nat) ≠ 19 by omega),
      up_ne (show (7:Nat) ≠ 18 by omega), up_ne (show (7:Nat) ≠ 18 by omega),
      up_ne (show (7:Nat) ≠ 20 by omega), up_ne (show (7:Nat) ≠ 20 by omega),
      up_ne (show (7:Nat) ≠ 4 by omega), up_ne (show (7:Nat) ≠ 5 by omega), h7]
  · rw [up_ne (show (8:Nat) ≠ 10 by omega), up_ne (show (8:Nat) ≠ B2 by omega),
      up_ne (show (8:Nat) ≠ 20 by omega), up_ne (show (8:Nat) ≠ 11 by omega),
      up_ne (show (8:Nat) ≠ 19 by omega), up_ne (show (8:Nat) ≠ 19 by omega),
      up_ne (show (8:Nat) ≠ 18 by omega), up_ne (show (8:Nat) ≠ 18 by omega),
      up_ne (show (8:Nat) ≠ 20 by omega), up_ne (show (8:Nat) ≠ 20 by omega),
      up_ne (show (8:Nat) ≠ 4 by omega), up_ne (show (8:Nat) ≠ 5 by omega), h8]
  · show [(up (up (up (up (up (up (up (up (up (up (up (up f0 5 H) 4 m) 20 1) 20 (2 ^ m)) 18 (A1 + H)) 18 B2) 19 (B2 + M)) 19 B3) 11 1) 20 B2) B2 0) 10 1) (B2 + 0)] = [0]
    rw [Nat.add_zero, up_ne (show B2 ≠ 10 by omega), up_eq]
set_option maxHeartbeats 2000000 in
/-- One phaseA2 round `k` (1 ≤ k ≤ m): LROUND2 setup (173–178, the
3-instruction element load `mem[RELOC+h+k]` = `instA2 x h (k-1)`), the merge
(179→217 via `merge_exec_m2`), the LSWAP2 tail (217→222 via `lswap2_exec`).
Lands at pc 223 with the guard `blt 10 21 173` pending.  Carries S₁ at A1,
`[22] = A1`, `[5] = H`, `[4] = m`, and the relocated array. -/
theorem round2_exec {w n : Nat} (ρ : Nat → BitVec w) {x : Instance n}
    (hn : 4 ≤ n) (hw : wordLength n x.bits ≤ w) :
    ∀ (h m k L b d A1 H B2 B3 : Nat) (f : Nat → Nat) (S r : Nat),
    h = n / 2 → m = n - h → 1 ≤ k → k ≤ m → L = 2 ^ (k - 1) →
    f 1 = 1 → f 2 = 0 → f 7 = n → f 8 = 2 * n + 23 → f 9 = h →
    f 10 = k → f 11 = L → f 18 = b → f 19 = d →
    f 22 = A1 → A1 = 3 * n + 25 → f 5 = H → H = 2 ^ (n / 2) → f 4 = m →
    B2 = 3 * n + 25 + H + 1 → B3 = B2 + 2 ^ m + 1 →
    (b = B2 ∧ d = B3 ∨ d = B2 ∧ b = B3) →
    arrL f b L = halfSums (instA2 x h) (k - 1) →
    arrL f A1 H = halfSums (instA x) h →
    (∀ i, 1 ≤ i → i ≤ n → f (2 * n + 23 + i) = instA x (i - 1)) →
    (∀ i, i < n → instA x i < 2 ^ w) →
    (∀ q, f q < 2 ^ w) →
    (∀ c, c ≤ B3 + 2 ^ m → c < 2 ^ w) →
    44 * L + 24 ≤ S →
    ∃ c f', c ≤ 44 * L + 24 ∧
      exec prog2 ρ S 173 r (memOf w f) = exec prog2 ρ (S - c) 223 r (memOf w f') ∧
      f' 10 = k + 1 ∧ f' 11 = 2 * L ∧ f' 18 = d ∧ f' 19 = b ∧ f' 21 = m + 1 ∧
      f' 22 = A1 ∧ f' 5 = H ∧ f' 4 = m ∧ f' 9 = h ∧
      f' 1 = 1 ∧ f' 2 = 0 ∧ f' 7 = n ∧ f' 8 = 2 * n + 23 ∧
      arrL f' d (2 * L) = halfSums (instA2 x h) k ∧
      arrL f' A1 H = halfSums (instA x) h ∧
      (∀ i, 1 ≤ i → i ≤ n → f' (2 * n + 23 + i) = instA x (i - 1)) ∧
      f' (2 * n + 23 + (n + 1)) = f (2 * n + 23 + (n + 1)) ∧
      (∀ q, f' q < 2 ^ w) ∧ Pres (AReg2 n) f f' := by
  intro h m k L b d A1 H B2 B3 f S r hh hm hk1 hkm hL hf1 hf2 hf7 hf8 hf9 hf10
    hf11 hf18 hf19 hf22 hA1 hf5 hH hf4 hB2 hB3 hbases harr2 harrS1 hrel hin hfit
    haddr hS
  have hm_eq : h + m = n := by omega
  have hposY : 1 ≤ 2 ^ (n / 2) := Nat.one_le_two_pow
  have hposZ : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hposH : 1 ≤ H := by rw [hH]; exact Nat.one_le_two_pow
  have hposL : 1 ≤ L := by rw [hL]; exact Nat.one_le_two_pow
  have hH1 : 1 ≤ H := by
    have e : H = 2 ^ (n / 2) := hH
    have := Nat.one_le_two_pow (n := n / 2)
    omega
  have hB2v : B2 = 3 * n + 26 + 2 ^ (n / 2) := by rw [hB2, hH]; omega
  have hB3v : B3 = 3 * n + 27 + 2 ^ (n / 2) + 2 ^ m := by rw [hB3, hB2v]; omega
  have hbd33 : 33 ≤ b ∧ 33 ≤ d := by
    have hB233 : 33 ≤ B2 := by rw [hB2v]; omega
    have hB333 : 33 ≤ B3 := by rw [hB3v]; omega
    rcases hbases with ⟨hb, hd⟩|⟨hd, hb⟩ <;> omega
  obtain ⟨hb33, hd33⟩ := hbd33
  have hLm : L ≤ 2 ^ (m - 1) := by
    rw [hL]
    exact Nat.pow_le_pow_right (n := 2) (by omega) (by omega)
  have hk2m : 2 ^ k ≤ 2 ^ m := Nat.pow_le_pow_right (n := 2) (by omega) hkm
  have h2k : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← Nat.pow_succ', show (k - 1).succ = k from by omega]
  have h2Lm : 2 * L ≤ 2 ^ m := by
    rw [hL, ← h2k]
    exact hk2m
  -- element value and its fit
  have hakNat : instA2 x h (k - 1) = instA x (h + k - 1) := by
    show instA x (k - 1 + h) = instA x (h + k - 1)
    have e : k - 1 + h = h + k - 1 := by omega
    rw [e]
  have hak : instA x (h + k - 1) < 2 ^ w := hin (h + k - 1) (by omega)
  have hak2 : instA2 x h (k - 1) < 2 ^ w := by rw [hakNat]; exact hak
  have haddr1 : 2 * n + 23 + h + k ≤ B3 + 2 ^ m := by
    rw [hB3v]
    have := Nat.one_le_two_pow (n := m)
    omega
  have hfit1 : ∀ q, (up f 20 (2 * n + 23 + h)) q < 2 ^ w :=
    up_fit hfit (haddr _ (by
      rw [hB3v]
      have := Nat.one_le_two_pow (n := m)
      omega))
  have hfit2 : ∀ q, (up (up f 20 (2 * n + 23 + h)) 20 (2 * n + 23 + h + k)) q < 2 ^ w :=
    up_fit hfit1 (haddr _ haddr1)
  have hfit3 : ∀ q, (up (up (up f 20 (2 * n + 23 + h)) 20 (2 * n + 23 + h + k)) 17 (instA2 x h (k - 1))) q < 2 ^ w :=
    up_fit hfit2 hak2
  have hwalk6 : exec prog2 ρ S 173 r (memOf w f)
      = exec prog2 ρ (S - 6) 179 r
          (memOf w (up (up (up (up (up (up f 20 (2 * n + 23 + h)) 20 (2 * n + 23 + h + k)) 17 (instA2 x h (k - 1))) 12 0) 13 0) 14 0)) := by
    rw [exec_add_step (by omega)
          (show prog2.getD 173 Instr.reject = Instr.add 20 8 9 by rfl),
        show f 8 + f 9 = 2 * n + 23 + h from by rw [hf8, hf9],
      exec_add_step (by omega)
          (show prog2.getD 174 Instr.reject = Instr.add 20 20 10 by rfl),
        show (up f 20 (2 * n + 23 + h)) 20 + (up f 20 (2 * n + 23 + h)) 10
            = 2 * n + 23 + h + k from by
          rw [up_eq, up_ne (show (10:Nat) ≠ 20 by omega), hf10],
      exec_load_step (by omega)
          (show prog2.getD 175 Instr.reject = Instr.load 17 20 by rfl) hfit2,
        up_eq, up_ne (show 2 * n + 23 + h + k ≠ 20 by omega),
        up_ne (show 2 * n + 23 + h + k ≠ 20 by omega),
        show f (2 * n + 23 + h + k) = instA2 x h (k - 1) from by
          have e1 : 2 * n + 23 + h + k = 2 * n + 23 + (h + k) := by omega
          rw [e1, hrel (h + k) (by omega) (by omega)]
          exact hakNat.symm,
        subs3_exec hfit3
          (show prog2.getD 176 Instr.reject = Instr.sub 12 12 12 by rfl)
          (show prog2.getD 177 Instr.reject = Instr.sub 13 13 13 by rfl)
          (show prog2.getD 178 Instr.reject = Instr.sub 14 14 14 by rfl)
          (by omega)]
    simp only [Nat.sub_sub, Nat.reduceAdd]
  -- register facts about the post-setup state v6
  have g12 : (up (up (up (up (up (up f 20 (2 * n + 23 + h)) 20 (2 * n + 23 + h + k)) 17 (instA2 x h (k - 1))) 12 0) 13 0) 14 0) 12 = 0 := by
    rw [up_ne (show (12:Nat) ≠ 14 by omega), up_ne (show (12:Nat) ≠ 13 by omega), up_eq]
  have g13 : (up (up (up (up (up (up f 20 (2 * n + 23 + h)) 20 (2 * n + 23 + h + k)) 17 (instA2 x h (k - 1))) 12 0) 13 0) 14 0) 13 = 0 := by
    rw [up_ne (show (13:Nat) ≠ 14 by omega), up_eq]
  have g14 : (up (up (up (up (up (up f 20 (2 * n + 23 + h)) 20 (2 * n + 23 + h + k)) 17 (instA2 x h (k - 1))) 12 0) 13 0) 14 0) 14 = 0 := by rw [up_eq]
  have g11 : (up (up (up (up (up (up f 20 (2 * n + 23 + h)) 20 (2 * n + 23 + h + k)) 17 (instA2 x h (k - 1))) 12 0) 13 0) 14 0) 11 = L := by
    rw [up_ne (show (11:Nat) ≠ 14 by omega), up_ne (show (11:Nat) ≠ 13 by omega),
      up_ne (show (11:Nat) ≠ 12 by omega), up_ne (show (11:Nat) ≠ 17 by omega),
      up_ne (show (11:Nat) ≠ 20 by omega), up_ne (show (11:Nat) ≠ 20 by omega), hf11]
  have g17 : (up (up (up (up (up (up f 20 (2 * n + 23 + h)) 20 (2 * n + 23 + h + k)) 17 (instA2 x h (k - 1))) 12 0) 13 0) 14 0) 17 = instA2 x h (k - 1) := by
    rw [up_ne (show (17:Nat) ≠ 14 by omega), up_ne (show (17:Nat) ≠ 13 by omega),
      up_ne (show (17:Nat) ≠ 12 by omega), up_eq]
  have g18 : (up (up (up (up (up (up f 20 (2 * n + 23 + h)) 20 (2 * n + 23 + h + k)) 17 (instA2 x h (k - 1))) 12 0) 13 0) 14 0) 18 = b := by
    rw [up_ne (show (18:Nat) ≠ 14 by omega), up_ne (show (18:Nat) ≠ 13 by omega),
      up_ne (show (18:Nat) ≠ 12 by omega), up_ne (show (18:Nat) ≠ 17 by omega),
      up_ne (show (18:Nat) ≠ 20 by omega), up_ne (show (18:Nat) ≠ 20 by omega), hf18]
  have g19 : (up (up (up (up (up (up f 20 (2 * n + 23 + h)) 20 (2 * n + 23 + h + k)) 17 (instA2 x h (k - 1))) 12 0) 13 0) 14 0) 19 = d := by
    rw [up_ne (show (19:Nat) ≠ 14 by omega), up_ne (show (19:Nat) ≠ 13 by omega),
      up_ne (show (19:Nat) ≠ 12 by omega), up_ne (show (19:Nat) ≠ 17 by omega),
      up_ne (show (19:Nat) ≠ 20 by omega), up_ne (show (19:Nat) ≠ 20 by omega), hf19]
  have g1 : (up (up (up (up (up (up f 20 (2 * n + 23 + h)) 20 (2 * n + 23 + h + k)) 17 (instA2 x h (k - 1))) 12 0) 13 0) 14 0) 1 = 1 := by
    rw [up_ne (show (1:Nat) ≠ 14 by omega), up_ne (show (1:Nat) ≠ 13 by omega),
      up_ne (show (1:Nat) ≠ 12 by omega), up_ne (show (1:Nat) ≠ 17 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega), up_ne (show (1:Nat) ≠ 20 by omega), hf1]
  have g2 : (up (up (up (up (up (up f 20 (2 * n + 23 + h)) 20 (2 * n + 23 + h + k)) 17 (instA2 x h (k - 1))) 12 0) 13 0) 14 0) 2 = 0 := by
    rw [up_ne (show (2:Nat) ≠ 14 by omega), up_ne (show (2:Nat) ≠ 13 by omega),
      up_ne (show (2:Nat) ≠ 12 by omega), up_ne (show (2:Nat) ≠ 17 by omega),
      up_ne (show (2:Nat) ≠ 20 by omega), up_ne (show (2:Nat) ≠ 20 by omega), hf2]
  have g22 : (up (up (up (up (up (up f 20 (2 * n + 23 + h)) 20 (2 * n + 23 + h + k)) 17 (instA2 x h (k - 1))) 12 0) 13 0) 14 0) 22 = A1 := by
    rw [up_ne (show (22:Nat) ≠ 14 by omega), up_ne (show (22:Nat) ≠ 13 by omega),
      up_ne (show (22:Nat) ≠ 12 by omega), up_ne (show (22:Nat) ≠ 17 by omega),
      up_ne (show (22:Nat) ≠ 20 by omega), up_ne (show (22:Nat) ≠ 20 by omega), hf22]
  have g5 : (up (up (up (up (up (up f 20 (2 * n + 23 + h)) 20 (2 * n + 23 + h + k)) 17 (instA2 x h (k - 1))) 12 0) 13 0) 14 0) 5 = H := by
    rw [up_ne (show (5:Nat) ≠ 14 by omega), up_ne (show (5:Nat) ≠ 13 by omega),
      up_ne (show (5:Nat) ≠ 12 by omega), up_ne (show (5:Nat) ≠ 17 by omega),
      up_ne (show (5:Nat) ≠ 20 by omega), up_ne (show (5:Nat) ≠ 20 by omega), hf5]
  have g4 : (up (up (up (up (up (up f 20 (2 * n + 23 + h)) 20 (2 * n + 23 + h + k)) 17 (instA2 x h (k - 1))) 12 0) 13 0) 14 0) 4 = m := by
    rw [up_ne (show (4:Nat) ≠ 14 by omega), up_ne (show (4:Nat) ≠ 13 by omega),
      up_ne (show (4:Nat) ≠ 12 by omega), up_ne (show (4:Nat) ≠ 17 by omega),
      up_ne (show (4:Nat) ≠ 20 by omega), up_ne (show (4:Nat) ≠ 20 by omega), hf4]
  have g7 : (up (up (up (up (up (up f 20 (2 * n + 23 + h)) 20 (2 * n + 23 + h + k)) 17 (instA2 x h (k - 1))) 12 0) 13 0) 14 0) 7 = n := by
    rw [up_ne (show (7:Nat) ≠ 14 by omega), up_ne (show (7:Nat) ≠ 13 by omega),
      up_ne (show (7:Nat) ≠ 12 by omega), up_ne (show (7:Nat) ≠ 17 by omega),
      up_ne (show (7:Nat) ≠ 20 by omega), up_ne (show (7:Nat) ≠ 20 by omega), hf7]
  have g8 : (up (up (up (up (up (up f 20 (2 * n + 23 + h)) 20 (2 * n + 23 + h + k)) 17 (instA2 x h (k - 1))) 12 0) 13 0) 14 0) 8 = 2 * n + 23 := by
    rw [up_ne (show (8:Nat) ≠ 14 by omega), up_ne (show (8:Nat) ≠ 13 by omega),
      up_ne (show (8:Nat) ≠ 12 by omega), up_ne (show (8:Nat) ≠ 17 by omega),
      up_ne (show (8:Nat) ≠ 20 by omega), up_ne (show (8:Nat) ≠ 20 by omega), hf8]
  have g9 : (up (up (up (up (up (up f 20 (2 * n + 23 + h)) 20 (2 * n + 23 + h + k)) 17 (instA2 x h (k - 1))) 12 0) 13 0) 14 0) 9 = h := by
    rw [up_ne (show (9:Nat) ≠ 14 by omega), up_ne (show (9:Nat) ≠ 13 by omega),
      up_ne (show (9:Nat) ≠ 12 by omega), up_ne (show (9:Nat) ≠ 17 by omega),
      up_ne (show (9:Nat) ≠ 20 by omega), up_ne (show (9:Nat) ≠ 20 by omega), hf9]
  have g10 : (up (up (up (up (up (up f 20 (2 * n + 23 + h)) 20 (2 * n + 23 + h + k)) 17 (instA2 x h (k - 1))) 12 0) 13 0) 14 0) 10 = k := by
    rw [up_ne (show (10:Nat) ≠ 14 by omega), up_ne (show (10:Nat) ≠ 13 by omega),
      up_ne (show (10:Nat) ≠ 12 by omega), up_ne (show (10:Nat) ≠ 17 by omega),
      up_ne (show (10:Nat) ≠ 20 by omega), up_ne (show (10:Nat) ≠ 20 by omega), hf10]
  have h0lt : (0:Nat) < 2 ^ w := Nat.one_le_two_pow (n := w)
  have gfit : ∀ q, (up (up (up (up (up (up f 20 (2 * n + 23 + h)) 20 (2 * n + 23 + h + k)) 17 (instA2 x h (k - 1))) 12 0) 13 0) 14 0) q < 2 ^ w :=
    up_fit (up_fit (up_fit hfit3 h0lt) h0lt) h0lt
  have hgsrc : ∀ q, q < L → (up (up (up (up (up (up f 20 (2 * n + 23 + h)) 20 (2 * n + 23 + h + k)) 17 (instA2 x h (k - 1))) 12 0) 13 0) 14 0) (b + q) = (halfSums (instA2 x h) (k - 1)).getD q 0 := by
    intro q hq
    rw [up_ne (show b + q ≠ 14 by omega), up_ne (show b + q ≠ 13 by omega),
      up_ne (show b + q ≠ 12 by omega), up_ne (show b + q ≠ 17 by omega),
      up_ne (show b + q ≠ 20 by omega), up_ne (show b + q ≠ 20 by omega),
      ← harr2, getD_arrL hq]
  have hsL' : (halfSums (instA2 x h) (k - 1)).length = L := by
    rw [length_halfSums, hL]
  have hLm2 : L ≤ 2 ^ m := by
    have hpx : 2 ^ (m - 1) ≤ 2 ^ m :=
      Nat.pow_le_pow_right (n := 2) (by omega) (by omega)
    omega
  have hbL : b + L < 2 ^ w := haddr _ (by
    rcases hbases with ⟨hb, hd⟩|⟨hd, hb⟩ <;> omega)
  have hdL : d + 2 * L < 2 ^ w := haddr _ (by
    rcases hbases with ⟨hb, hd⟩|⟨hd, hb⟩ <;> omega)
  have h2L : 2 * L < 2 ^ w := haddr _ (by
    have hB3pos : 0 < B3 := by rw [hB3v]; omega
    omega)
  have hdisj : ∀ p q, p < 2 * L → q < L → d + p ≠ b + q := by
    intro p q hp hq
    rcases hbases with ⟨hb, hd⟩|⟨hd, hb⟩ <;> omega
  have hout : halfSums (instA2 x h) k
      = mmerge (halfSums (instA2 x h) (k - 1))
          ((halfSums (instA2 x h) (k - 1)).map (fun z => z + instA2 x h (k - 1))) := by
    rw [show k = (k - 1) + 1 from by omega, halfSums,
        show k - 1 + 1 - 1 = k - 1 from by omega]
  obtain ⟨c2, fm, hc2, hex2, harrm, h12m, h14m, hfitm, hpm⟩ :=
    merge_exec_m2 ρ (2 * L) L b d (instA2 x h (k - 1)) (halfSums (instA2 x h) (k - 1))
      (halfSums (instA2 x h) k)
      (up (up (up (up (up (up f 20 (2 * n + 23 + h)) 20 (2 * n + 23 + h + k)) 17 (instA2 x h (k - 1))) 12 0) 13 0) 14 0)
      0 0 0 (S - 6) r hsL'
      (by omega) (by omega) (by omega) g12 g13 g14 g11 g17 g18 g19 g1 g2
      hgsrc (fun v hv => halfSumAddFit2 (by omega) hw (k - 1) (by omega) v hv)
      (by exact rfl) (by exact hout) hout gfit hbL hdL h2L hb33 hd33 hdisj
      (by omega) (by omega)
  -- registers fm keeps (cells outside MReg d L)
  have fm11 : fm 11 = L := by
    rw [hpm 11 (mreg_ne_small hd33 (Or.inl (by omega))), g11]
  have fm18 : fm 18 = b := by
    rw [hpm 18 (mreg_ne_small hd33 (Or.inr (Or.inl ⟨by omega, by omega⟩))), g18]
  have fm19 : fm 19 = d := by
    rw [hpm 19 (mreg_ne_small hd33 (Or.inr (Or.inl ⟨by omega, by omega⟩))), g19]
  have fm1 : fm 1 = 1 := by rw [hpm 1 (mreg_ne_small hd33 (Or.inl (by omega))), g1]
  have fm2 : fm 2 = 0 := by rw [hpm 2 (mreg_ne_small hd33 (Or.inl (by omega))), g2]
  have fm4 : fm 4 = m := by rw [hpm 4 (mreg_ne_small hd33 (Or.inl (by omega))), g4]
  have fm5 : fm 5 = H := by rw [hpm 5 (mreg_ne_small hd33 (Or.inl (by omega))), g5]
  have fm7 : fm 7 = n := by rw [hpm 7 (mreg_ne_small hd33 (Or.inl (by omega))), g7]
  have fm8 : fm 8 = 2 * n + 23 := by rw [hpm 8 (mreg_ne_small hd33 (Or.inl (by omega))), g8]
  have fm9 : fm 9 = h := by rw [hpm 9 (mreg_ne_small hd33 (Or.inl (by omega))), g9]
  have fm10 : fm 10 = k := by rw [hpm 10 (mreg_ne_small hd33 (Or.inl (by omega))), g10]
  have fm22 : fm 22 = A1 := by
    rw [hpm 22 (mreg_ne_small hd33 (Or.inr (Or.inr rfl))), g22]
  -- S₁ at A1 survives the merge (A1+q ∉ MReg d L)
  have hS1m : arrL fm A1 H = arrL (up (up (up (up (up (up f 20 (2 * n + 23 + h)) 20 (2 * n + 23 + h + k)) 17 (instA2 x h (k - 1))) 12 0) 13 0) 14 0) A1 H := by
    refine arrL_congr (fun q hq => ?_)
    have hqA : A1 + q < B2 := by
      have e : A1 = 3 * n + 25 := hA1
      rw [hB2v]
      omega
    have hnM : ¬ MReg d L (A1 + q) := by
      intro hM
      rcases hM with h|h|h|h|h|h|h|⟨h1', h2'⟩ <;>
        (try omega) <;>
        (try { rcases hbases with ⟨hb, hd⟩|⟨hd, hb⟩ <;> omega })
    rw [hpm (A1 + q) hnM]
  have hS1w : arrL (up (up (up (up (up (up f 20 (2 * n + 23 + h)) 20 (2 * n + 23 + h + k)) 17 (instA2 x h (k - 1))) 12 0) 13 0) 14 0) A1 H
      = arrL f A1 H := by
    rw [arrL_up_out (fun q _ => show (14:Nat) ≠ A1 + q by have := hA1; omega),
      arrL_up_out (fun q _ => show (13:Nat) ≠ A1 + q by have := hA1; omega),
      arrL_up_out (fun q _ => show (12:Nat) ≠ A1 + q by have := hA1; omega),
      arrL_up_out (fun q _ => show (17:Nat) ≠ A1 + q by have := hA1; omega),
      arrL_up_out (fun q _ => show (20:Nat) ≠ A1 + q by have := hA1; omega),
      arrL_up_out (fun q _ => show (20:Nat) ≠ A1 + q by have := hA1; omega)]
  -- LSWAP2 tail (217..222)
  have htail : exec prog2 ρ (S - 6 - c2) 217 r (memOf w fm)
      = exec prog2 ρ (S - 6 - c2 - 6) 223 r
          (memOf w (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 21 (m + 1))) :=
    lswap2_exec fm11 fm1 fm2 fm4 fm10 fm18 fm19
      (show prog2.getD 217 Instr.reject = Instr.add 11 11 11 by rfl)
      (show prog2.getD 218 Instr.reject = Instr.add 20 18 2 by rfl)
      (show prog2.getD 219 Instr.reject = Instr.add 18 19 2 by rfl)
      (show prog2.getD 220 Instr.reject = Instr.add 19 20 2 by rfl)
      (show prog2.getD 221 Instr.reject = Instr.add 10 10 1 by rfl)
      (show prog2.getD 222 Instr.reject = Instr.add 21 4 1 by rfl)
      (by omega)
  -- f' = the post-swap state; conclude everything
  have f'10 : (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 21 (m + 1)) 10 = k + 1 := by
    rw [up_ne (show (10:Nat) ≠ 21 by omega), up_eq]
  have f'11 : (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 21 (m + 1)) 11 = 2 * L := by
    rw [up_ne (show (11:Nat) ≠ 21 by omega), up_ne (show (11:Nat) ≠ 10 by omega),
      up_ne (show (11:Nat) ≠ 19 by omega), up_ne (show (11:Nat) ≠ 18 by omega),
      up_ne (show (11:Nat) ≠ 20 by omega), up_eq]
  have f'18 : (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 21 (m + 1)) 18 = d := by
    rw [up_ne (show (18:Nat) ≠ 21 by omega), up_ne (show (18:Nat) ≠ 10 by omega),
      up_ne (show (18:Nat) ≠ 19 by omega), up_eq]
  have f'19 : (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 21 (m + 1)) 19 = b := by
    rw [up_ne (show (19:Nat) ≠ 21 by omega), up_ne (show (19:Nat) ≠ 10 by omega), up_eq]
  have f'21 : (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 21 (m + 1)) 21 = m + 1 := by rw [up_eq]
  have f'22 : (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 21 (m + 1)) 22 = A1 := by
    rw [up_ne (show (22:Nat) ≠ 21 by omega), up_ne (show (22:Nat) ≠ 10 by omega),
      up_ne (show (22:Nat) ≠ 19 by omega), up_ne (show (22:Nat) ≠ 18 by omega),
      up_ne (show (22:Nat) ≠ 20 by omega), up_ne (show (22:Nat) ≠ 11 by omega), fm22]
  have f'5 : (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 21 (m + 1)) 5 = H := by
    rw [up_ne (show (5:Nat) ≠ 21 by omega), up_ne (show (5:Nat) ≠ 10 by omega),
      up_ne (show (5:Nat) ≠ 19 by omega), up_ne (show (5:Nat) ≠ 18 by omega),
      up_ne (show (5:Nat) ≠ 20 by omega), up_ne (show (5:Nat) ≠ 11 by omega), fm5]
  have f'4 : (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 21 (m + 1)) 4 = m := by
    rw [up_ne (show (4:Nat) ≠ 21 by omega), up_ne (show (4:Nat) ≠ 10 by omega),
      up_ne (show (4:Nat) ≠ 19 by omega), up_ne (show (4:Nat) ≠ 18 by omega),
      up_ne (show (4:Nat) ≠ 20 by omega), up_ne (show (4:Nat) ≠ 11 by omega), fm4]
  have f'9 : (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 21 (m + 1)) 9 = h := by
    rw [up_ne (show (9:Nat) ≠ 21 by omega), up_ne (show (9:Nat) ≠ 10 by omega),
      up_ne (show (9:Nat) ≠ 19 by omega), up_ne (show (9:Nat) ≠ 18 by omega),
      up_ne (show (9:Nat) ≠ 20 by omega), up_ne (show (9:Nat) ≠ 11 by omega), fm9]
  have f'1 : (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 21 (m + 1)) 1 = 1 := by
    rw [up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (1:Nat) ≠ 10 by omega),
      up_ne (show (1:Nat) ≠ 19 by omega), up_ne (show (1:Nat) ≠ 18 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega), up_ne (show (1:Nat) ≠ 11 by omega), fm1]
  have f'2 : (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 21 (m + 1)) 2 = 0 := by
    rw [up_ne (show (2:Nat) ≠ 21 by omega), up_ne (show (2:Nat) ≠ 10 by omega),
      up_ne (show (2:Nat) ≠ 19 by omega), up_ne (show (2:Nat) ≠ 18 by omega),
      up_ne (show (2:Nat) ≠ 20 by omega), up_ne (show (2:Nat) ≠ 11 by omega), fm2]
  have f'7 : (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 21 (m + 1)) 7 = n := by
    rw [up_ne (show (7:Nat) ≠ 21 by omega), up_ne (show (7:Nat) ≠ 10 by omega),
      up_ne (show (7:Nat) ≠ 19 by omega), up_ne (show (7:Nat) ≠ 18 by omega),
      up_ne (show (7:Nat) ≠ 20 by omega), up_ne (show (7:Nat) ≠ 11 by omega), fm7]
  have f'8 : (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 21 (m + 1)) 8 = 2 * n + 23 := by
    rw [up_ne (show (8:Nat) ≠ 21 by omega), up_ne (show (8:Nat) ≠ 10 by omega),
      up_ne (show (8:Nat) ≠ 19 by omega), up_ne (show (8:Nat) ≠ 18 by omega),
      up_ne (show (8:Nat) ≠ 20 by omega), up_ne (show (8:Nat) ≠ 11 by omega), fm8]
  have f'arr : arrL (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 21 (m + 1)) d (2 * L) = halfSums (instA2 x h) k := by
    rw [arrL_up_out (fun q _ => show (21:Nat) ≠ d + q by omega),
        arrL_up_out (fun q _ => show (10:Nat) ≠ d + q by omega),
        arrL_up_out (fun q _ => show (19:Nat) ≠ d + q by omega),
        arrL_up_out (fun q _ => show (18:Nat) ≠ d + q by omega),
        arrL_up_out (fun q _ => show (20:Nat) ≠ d + q by omega),
        arrL_up_out (fun q _ => show (11:Nat) ≠ d + q by omega),
        harrm]
  have f'S1 : arrL (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 21 (m + 1)) A1 H = halfSums (instA x) h := by
    rw [arrL_up_out (fun q _ => show (21:Nat) ≠ A1 + q by have := hA1; omega),
      arrL_up_out (fun q _ => show (10:Nat) ≠ A1 + q by have := hA1; omega),
      arrL_up_out (fun q _ => show (19:Nat) ≠ A1 + q by have := hA1; omega),
      arrL_up_out (fun q _ => show (18:Nat) ≠ A1 + q by have := hA1; omega),
      arrL_up_out (fun q _ => show (20:Nat) ≠ A1 + q by have := hA1; omega),
      arrL_up_out (fun q _ => show (11:Nat) ≠ A1 + q by have := hA1; omega),
      hS1m, hS1w, harrS1]
  have f'fit : ∀ q, (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 21 (m + 1)) q < 2 ^ w :=
    up_fit (up_fit (up_fit (up_fit (up_fit (up_fit hfitm
      (haddr _ (by omega)))
      (haddr _ (by rcases hbases with ⟨hb, hd⟩|⟨hd, hb⟩ <;> omega)))
      (haddr _ (by rcases hbases with ⟨hb, hd⟩|⟨hd, hb⟩ <;> omega)))
      (haddr _ (by omega)))
      (haddr _ (by omega)))
      (haddr _ (by omega))
  -- Pres (AReg2 n): setup writes are registers; merge ⊆ MReg→AReg2; swap writes registers
  have hsub2 : ∀ c, MReg d L c → AReg2 n c := by
    intro c hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|hstrip
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · refine Or.inr ⟨?_, ?_⟩
      · rcases hstrip with ⟨h1', h2'⟩
        have hdl : B2 ≤ d := by
          rcases hbases with ⟨hb, hd⟩|⟨hd, hb⟩
          · rw [hd, hB3v, hB2v]; omega
          · omega
        omega
      · have henv : B3 + 2 ^ m = 3 * n + 27 + 2 ^ (n / 2) + 2 * 2 ^ (n - n / 2) := by
          rw [hB3v, hm, hh]
          omega
        rcases hstrip with ⟨h1', h2'⟩
        rcases hbases with ⟨hb, hd⟩|⟨hd, hb⟩ <;> omega
  have hpres6 : Pres (AReg2 n) f
      (up (up (up (up (up (up f 20 (2 * n + 23 + h)) 20 (2 * n + 23 + h + k)) 17 (instA2 x h (k - 1))) 12 0) 13 0) 14 0) :=
    pres_trans (pres_up (Or.inl (by omega)))
      (pres_trans (pres_up (Or.inl (by omega)))
      (pres_trans (pres_up (Or.inl (by omega)))
      (pres_trans (pres_up (Or.inl (by omega)))
      (pres_trans (pres_up (Or.inl (by omega)))
      (pres_up (Or.inl (by omega)))))))
  have hpresA : Pres (AReg2 n) f
      (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 21 (m + 1)) :=
    pres_trans hpres6
      (pres_trans (pres_mono hsub2 hpm)
      (pres_trans (pres_up (Or.inl (by omega)))
      (pres_trans (pres_up (Or.inl (by omega)))
      (pres_trans (pres_up (Or.inl (by omega)))
      (pres_trans (pres_up (Or.inl (by omega)))
      (pres_trans (pres_up (Or.inl (by omega)))
      (pres_up (Or.inl (by omega)))))))))
  have hrel' : ∀ i, 1 ≤ i → i ≤ n →
      (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 21 (m + 1)) (2 * n + 23 + i) = instA x (i - 1) := by
    intro i hi1 hin'
    have hnA : ¬ AReg2 n (2 * n + 23 + i) := by
      intro hA
      rcases hA with hA|hA <;> omega
    rw [hpresA _ hnA, hrel i hi1 hin']
  have hft' : (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 21 (m + 1)) (2 * n + 23 + (n + 1))
      = f (2 * n + 23 + (n + 1)) := by
    have hnA : ¬ AReg2 n (2 * n + 23 + (n + 1)) := by
      intro hA
      rcases hA with hA|hA <;> omega
    exact hpresA _ hnA
  refine ⟨6 + c2 + 6, (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 21 (m + 1)),
    by omega, ?_, f'10, f'11, f'18, f'19, f'21, f'22, f'5, f'4, f'9, f'1, f'2, f'7, f'8,
    f'arr, f'S1, hrel', hft', f'fit, hpresA⟩
  rw [hwalk6, hex2, htail]
  simp only [Nat.sub_sub]

set_option maxHeartbeats 2000000 in
/-- All phaseA2 rounds `k..m` from pc 173: each round merges with
`+a_{h+k}`, doubles `L`, swaps B2/B3; after round `m` the guard at 223
falls through to scanB (pc 224) with `halfSums (instA2 x h) m` at `[rSRC]`,
S₁ at A1 intact, `[22] = A1`, `[5] = H`, `[4] = m`. -/
theorem lround2_exec {w n : Nat} (ρ : Nat → BitVec w) {x : Instance n}
    (hn : 4 ≤ n) (hw : wordLength n x.bits ≤ w) :
    ∀ F (h m k L b d A1 H B2 B3 : Nat) (f : Nat → Nat) (S r : Nat),
    h = n / 2 → m = n - h → 1 ≤ k → k ≤ m → L = 2 ^ (k - 1) →
    f 1 = 1 → f 2 = 0 → f 7 = n → f 8 = 2 * n + 23 → f 9 = h →
    f 10 = k → f 11 = L → f 18 = b → f 19 = d →
    f 22 = A1 → A1 = 3 * n + 25 → f 5 = H → H = 2 ^ (n / 2) → f 4 = m →
    B2 = 3 * n + 25 + H + 1 → B3 = B2 + 2 ^ m + 1 →
    (b = B2 ∧ d = B3 ∨ d = B2 ∧ b = B3) →
    arrL f b L = halfSums (instA2 x h) (k - 1) →
    arrL f A1 H = halfSums (instA x) h →
    (∀ i, 1 ≤ i → i ≤ n → f (2 * n + 23 + i) = instA x (i - 1)) →
    f (2 * n + 23 + (n + 1)) = x.t →
    (∀ i, i < n → instA x i < 2 ^ w) →
    (∀ q, f q < 2 ^ w) →
    (∀ c, c ≤ B3 + 2 ^ m → c < 2 ^ w) →
    m + 1 - k ≤ F →
    44 * (2 ^ m - 2 ^ (k - 1)) + 25 * (m - k + 1) ≤ S →
    ∃ c f' bd2, c ≤ 44 * (2 ^ m - 2 ^ (k - 1)) + 25 * (m - k + 1) ∧
      exec prog2 ρ S 173 r (memOf w f) = exec prog2 ρ (S - c) 224 r (memOf w f') ∧
      f' 10 = m + 1 ∧ f' 11 = 2 ^ m ∧ f' 18 = bd2 ∧
      (bd2 = B2 ∨ bd2 = B3) ∧
      arrL f' bd2 (2 ^ m) = halfSums (instA2 x h) m ∧
      f' 22 = A1 ∧ f' 5 = H ∧ f' 4 = m ∧ f' 9 = h ∧
      f' 1 = 1 ∧ f' 2 = 0 ∧ f' 7 = n ∧ f' 8 = 2 * n + 23 ∧
      arrL f' A1 H = halfSums (instA x) h ∧
      (∀ i, 1 ≤ i → i ≤ n → f' (2 * n + 23 + i) = instA x (i - 1)) ∧
      f' (2 * n + 23 + (n + 1)) = x.t ∧
      (∀ q, f' q < 2 ^ w) := by
  intro F
  induction F with
  | zero =>
    intro h m k L b d A1 H B2 B3 f S r hh hm hk1 hkm hL hf1 hf2 hf7 hf8 hf9 hf10 hf11
      hf18 hf19 hf22 hA1 hf5 hH hf4 hB2 hB3 hbases harr2 harrS1 hrel hft hin hfit haddr
      hfuel hS
    omega
  | succ F ih =>
    intro h m k L b d A1 H B2 B3 f S r hh hm hk1 hkm hL hf1 hf2 hf7 hf8 hf9 hf10 hf11
      hf18 hf19 hf22 hA1 hf5 hH hf4 hB2 hB3 hbases harr2 harrS1 hrel hft hin hfit haddr
      hfuel hS
    have h2k : 2 ^ k = 2 * 2 ^ (k - 1) := by
      rw [← Nat.pow_succ', show (k - 1).succ = k from by omega]
    have hk2m : 2 ^ k ≤ 2 ^ m := Nat.pow_le_pow_right (n := 2) (by omega) hkm
    have hY1 : 1 ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
    have hYX : 2 ^ (k - 1) ≤ 2 ^ m := by omega
    obtain ⟨c1, fr, hc1, hex1, hfr10, hfr11, hfr18, hfr19, hfr21, hfr22, hfr5, hfr4, hfr9,
      hfr1, hfr2, hfr7, hfr8, hfrarr, hfrS1, hfrrel, hfrft, hfrfit, hfrpres⟩ :=
      round2_exec ρ hn hw h m k L b d A1 H B2 B3 f S r hh hm hk1 hkm hL hf1 hf2 hf7 hf8 hf9
        hf10 hf11 hf18 hf19 hf22 hA1 hf5 hH hf4 hB2 hB3 hbases harr2 harrS1 hrel hin hfit
        haddr (by omega)
    have hfrftx : fr (2 * n + 23 + (n + 1)) = x.t := by rw [hfrft, hft]
    by_cases hkl : k < m
    · -- guard taken: 223 → 173, round k+1 with (b, d) swapped
      have hwalk : exec prog2 ρ S 173 r (memOf w f)
          = exec prog2 ρ (S - (c1 + 1)) 173 r (memOf w fr) := by
        rw [hex1,
          exec_blt_lt_step (by omega)
            (show prog2.getD 223 Instr.reject = Instr.blt 10 21 173 by rfl) hfrfit
            (by rw [hfr10, hfr21]; omega)]
        simp only [Nat.sub_sub]
      have hL' : 2 * L = 2 ^ (k + 1 - 1) := by
        rw [show k + 1 - 1 = k from by omega, h2k, ← hL]
      have hbases' : (d = B2 ∧ b = B3 ∨ b = B2 ∧ d = B3) := by
        rcases hbases with ⟨hb, hd⟩|⟨hd, hb⟩
        · exact Or.inr ⟨hb, hd⟩
        · exact Or.inl ⟨hd, hb⟩
      obtain ⟨c2, f2', bd2, hc2, hex2, hf210, hf211, hf218, hf2bd, hf2arr, hf222, hf25,
        hf24, hf29, hf21, hf22, hf27, hf28, hf2S1, hf2rel, hf2ft, hf2fit⟩ :=
        ih h m (k + 1) (2 * L) d b A1 H B2 B3 fr (S - (c1 + 1)) r hh hm (by omega) (by omega)
          hL' hfr1 hfr2 hfr7 hfr8 hfr9 hfr10 hfr11 hfr18 hfr19 hfr22 hA1 hfr5 hH hfr4
          hB2 hB3 hbases'
          (by rw [show k + 1 - 1 = k from by omega]; exact hfrarr)
          hfrS1 hfrrel hfrftx hin hfrfit haddr (by omega) (by omega)
      refine ⟨c1 + 1 + c2, f2', bd2, by omega, ?_, hf210, hf211, hf218, hf2bd, hf2arr,
        hf222, hf25, hf24, hf29, hf21, hf22, hf27, hf28, hf2S1, hf2rel, hf2ft, hf2fit⟩
      rw [hwalk, hex2]
      rw [show S - (c1 + 1) - c2 = S - (c1 + 1 + c2) from by omega]
    · -- k = m: the guard at 223 falls through to scanB (224)
      have hkm2 : k = m := by omega
      have h2mL : 2 * L = 2 ^ m := by
        rw [hL, ← h2k, hkm2]
      have hwalkE : exec prog2 ρ S 173 r (memOf w f)
          = exec prog2 ρ (S - (c1 + 1)) 224 r (memOf w fr) := by
        rw [hex1,
          exec_blt_ge_step (by omega)
            (show prog2.getD 223 Instr.reject = Instr.blt 10 21 173 by rfl) hfrfit
            (by rw [hfr10, hfr21]; omega)]
        simp only [Nat.sub_sub]
      refine ⟨c1 + 1, fr, d, by omega, hwalkE, by rw [hfr10, hkm2], by rw [hfr11, h2mL],
        hfr18, ?_, by rw [← h2mL, ← hkm2]; exact hfrarr, hfr22, hfr5, hfr4, hfr9, hfr1, hfr2,
        hfr7, hfr8, hfrS1, hfrrel, hfrftx, hfrfit⟩
      rcases hbases with ⟨hb, hd⟩|⟨hd, hb⟩
      · exact Or.inr hd
      · exact Or.inl hd

set_option maxHeartbeats 2000000 in
/-- The whole phaseA2 segment (pcs 161 → 224): init + all `m` rounds.
Consumes canon_exec's output contract verbatim; produces the scanB entry
contract: S₂ = `halfSums (instA2 x (n/2)) (n−n/2)` sorted at `[rSRC] ∈
{B2, B3}`, S₁ canonical at ARR1 = `[22]`, `[5] = 2^(n/2)`, `[4] = n−n/2`,
relocated array and `t` intact. -/
theorem phaseA2_exec {w n : Nat} (ρ : Nat → BitVec w) {x : Instance n}
    (hn : 4 ≤ n) (hw : wordLength n x.bits ≤ w)
    (f2 : Nat → Nat) (r S : Nat)
    (hfit : ∀ q, f2 q < 2 ^ w)
    (h1 : f2 1 = 1) (h2 : f2 2 = 0) (h7 : f2 7 = n) (h8 : f2 8 = 2 * n + 23)
    (h9 : f2 9 = n / 2) (h11 : f2 11 = 2 ^ (n / 2))
    (h22 : f2 22 = 3 * n + 25)
    (harrS1 : arrL f2 (3 * n + 25) (2 ^ (n / 2)) = halfSums (instA x) (n / 2))
    (hrel : ∀ i, 1 ≤ i → i ≤ n → f2 (2 * n + 23 + i) = instA x (i - 1))
    (hft : f2 (2 * n + 23 + (n + 1)) = x.t)
    (hin : ∀ i, i < n → instA x i < 2 ^ w)
    (hpow : 2 ^ (2 * n) ≤ 2 ^ w)
    (hS : 12 + 44 * (2 ^ (n - n / 2) - 1) + 25 * (n - n / 2) ≤ S) :
    ∃ c f' bd2, c ≤ 12 + 44 * (2 ^ (n - n / 2) - 1) + 25 * (n - n / 2) ∧
      exec prog2 ρ S 161 r (memOf w f2) = exec prog2 ρ (S - c) 224 r (memOf w f') ∧
      f' 11 = 2 ^ (n - n / 2) ∧ f' 18 = bd2 ∧
      (bd2 = 3 * n + 26 + 2 ^ (n / 2) ∨
        bd2 = 3 * n + 27 + 2 ^ (n / 2) + 2 ^ (n - n / 2)) ∧
      arrL f' bd2 (2 ^ (n - n / 2)) = halfSums (instA2 x (n / 2)) (n - n / 2) ∧
      f' 22 = 3 * n + 25 ∧ f' 5 = 2 ^ (n / 2) ∧ f' 4 = n - n / 2 ∧ f' 9 = n / 2 ∧
      f' 1 = 1 ∧ f' 2 = 0 ∧ f' 7 = n ∧ f' 8 = 2 * n + 23 ∧
      arrL f' (3 * n + 25) (2 ^ (n / 2)) = halfSums (instA x) (n / 2) ∧
      (∀ i, 1 ≤ i → i ≤ n → f' (2 * n + 23 + i) = instA x (i - 1)) ∧
      f' (2 * n + 23 + (n + 1)) = x.t ∧
      (∀ q, f' q < 2 ^ w) := by
  obtain ⟨f1, hinit, hfit1, h14, h15, h19, h110, h111, h118, h119, h122, h11', h12', h17',
    h18', h1B2, h1S1, h1pres⟩ :=
    init2_exec ρ hn f2 r S (n / 2) (n - n / 2) (2 ^ (n / 2)) (2 ^ (n - n / 2))
      (3 * n + 26 + 2 ^ (n / 2)) (3 * n + 27 + 2 ^ (n / 2) + 2 ^ (n - n / 2)) (3 * n + 25)
      hfit h1 h2 h7 h8 h9 rfl (by omega) h11 rfl h22 rfl
      (by omega) (by omega) (by simp) hpow harrS1 (by omega)
  -- haddr for the rounds: c ≤ B3 + 2^m → c < 2^w
  have haddrR : ∀ c, c ≤ 3 * n + 27 + 2 ^ (n / 2) + 2 ^ (n - n / 2) + 2 ^ (n - n / 2) → c < 2 ^ w := by
    intro c hc
    have := pro_addr_lt2 n hn
    omega
  -- the relocated array and t survive init2 (cells ∉ AReg2 n)
  have hrel1 : ∀ i, 1 ≤ i → i ≤ n → f1 (2 * n + 23 + i) = instA x (i - 1) := by
    intro i hi1 hin'
    have hnA : ¬ AReg2 n (2 * n + 23 + i) := by
      intro hA
      rcases hA with hA|hA <;> omega
    rw [h1pres _ hnA, hrel i hi1 hin']
  have hft1 : f1 (2 * n + 23 + (n + 1)) = x.t := by
    have hnA : ¬ AReg2 n (2 * n + 23 + (n + 1)) := by
      intro hA
      rcases hA with hA|hA <;> omega
    rw [h1pres _ hnA, hft]
  obtain ⟨c2, f2', bd2, hc2, hex2, hf210, hf211, hf218, hf2bd, hf2arr, hf222, hf25, hf24,
    hf29, hf21, hf22, hf27, hf28, hf2S1, hf2rel, hf2ft, hf2fit⟩ :=
    lround2_exec ρ hn hw (n - n / 2) (n / 2) (n - n / 2) (1:Nat) (1:Nat)
      (3 * n + 26 + 2 ^ (n / 2)) (3 * n + 27 + 2 ^ (n / 2) + 2 ^ (n - n / 2))
      (3 * n + 25) (2 ^ (n / 2))
      (3 * n + 26 + 2 ^ (n / 2)) (3 * n + 27 + 2 ^ (n / 2) + 2 ^ (n - n / 2))
      f1 (S - 12) r
      (by omega) (by omega) (by omega)
      (by omega)
      (by rw [show (1:Nat) - 1 = 0 from rfl, Nat.pow_zero])
      h11' h12' h17' h18' h19 h110 h111 h118 h119 h122 rfl h15 rfl h14
      (by omega) (by omega)
      (Or.inl ⟨rfl, rfl⟩)
      (by rw [show (1:Nat) - 1 = 0 from rfl, h1B2]; exact (rfl : halfSums (instA2 x (n / 2)) 0 = [0]).symm)
      h1S1 hrel1 hft1 hin hfit1 haddrR (by omega)
      (by rw [show (1:Nat) - 1 = 0 from rfl, Nat.pow_zero]; omega)
  refine ⟨12 + c2, f2', bd2, by omega, ?_, hf211, hf218, ?_, ?_, hf222, hf25, hf24, hf29,
    hf21, hf22, hf27, hf28, hf2S1, hf2rel, hf2ft, hf2fit⟩
  · rw [hinit, hex2]
    rw [show S - 12 - c2 = S - (12 + c2) from by omega]
  · exact hf2bd
  · exact hf2arr

end Merge2

end SubsetSum.MITM.P2M
