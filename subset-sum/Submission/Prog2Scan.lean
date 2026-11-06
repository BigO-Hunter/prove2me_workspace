import Submission.Prog2Merge2
import Submission.Bridge
set_option autoImplicit true

/-!
# scanB: the two-pointer sweep, pcs 224 → verdict (R2125607749 Lane 3)

Entry (from `phaseA2_exec`): S₁ = `halfSums (instA x) h` sorted ascending at
ARR1 = `[22]` (`H = 2^h` values), S₂ = `halfSums (instA2 x h) m` sorted
ascending at `[18] ∈ {B2,B3}` (`M = 2^m` values), `t` readable at
`mem[RELOC+n+1]`.  The sweep: `i` ascending over S₁, `j` descending over
S₂, `s := S₁[i]+S₂[j]` (NO WRAP: `s ≤ Σa < 2^w` by `halfSumsSumLe`);
`s < t ⇒ i++` (row `i` dies below `j`: S₂ ascending), `s > t ⇒ j−−`
(column `j` dies right of `i`: S₁ ascending), `s = t ⇒ ACCEPT`, reject on
`i = H` or `j = 0 ∧ s > t`.

The invariant is the CORNER form: no witness pair in `{p < i} ∪ {q > j}`
(the row-based form `p = i ∧ q > j` is NOT inductive — `i++` puts fresh
pairs `(i+1, q>j)` into it).  Fuel `N = (H−i) + j` (pointer monotonicity),
budget `10·N + 8` PROVEN: i-step 8 instructions, j-step 10, rejects ≤ 9,
accept 8 (counted from prog2_dump.txt pcs 229–243).

THE VERDICT LEMMA (`scanB_exec`): within `10·(2^h + 2^m) + 3` steps the
run HALTS with verdict `v` and `v = true ↔ x.yes` — both directions
through the invariant and the `isSum_split`/`mem_halfSums` bridge.
-/

namespace SubsetSum.MITM

open BigOSpeedrun.SubsetSum SubsetSum.MITM.Spec

set_option maxHeartbeats 2000000 in
/-- The sweep loop at LSCAN = 229.  Corner invariant: no pair `(p,q)` with
`p < i` or `q > j` sums to `t`.  Fuel `10·((H−i)+j) + 8`. -/
theorem scanLoop_exec {w n : Nat} (ρ : Nat → BitVec w) {x : Instance n}
    (hn : 4 ≤ n) (hw : wordLength n x.bits ≤ w) :
    ∀ (N : Nat) (H M A1 bd2 i j t : Nat) (A B : List Nat) (f : Nat → Nat) (S r : Nat),
    A.length = H → B.length = M → 0 < M →
    i < H → j < M → (H - i) + j ≤ N →
    f 12 = i → f 13 = j → f 17 = t → f 22 = A1 → f 18 = bd2 → f 5 = H → f 11 = M →
    f 1 = 1 → f 2 = 0 →
    (∀ q, q < H → f (A1 + q) = A.getD q 0) →
    (∀ q, q < M → f (bd2 + q) = B.getD q 0) →
    List.Pairwise (· ≤ ·) A → List.Pairwise (· ≤ ·) B →
    B.getD 0 0 = 0 →
    (∀ v, v ∈ A → ∀ u, u ∈ B → v + u < 2 ^ w) →
    t < 2 ^ w →
    (∀ q, f q < 2 ^ w) →
    A1 + H < 2 ^ w → bd2 + M < 2 ^ w → 33 ≤ A1 → 33 ≤ bd2 →
    (∀ p q, p < H → q < M → (p < i ∨ j < q) → A.getD p 0 + B.getD q 0 ≠ t) →
    10 * ((H - i) + j) + 8 ≤ S →
    ∃ c v, c ≤ 10 * ((H - i) + j) + 8 ∧
      exec prog2 ρ S 229 r (memOf w f) = some v ∧
      (v = true → ∃ p q, p < H ∧ q < M ∧ A.getD p 0 + B.getD q 0 = t) ∧
      (v = false → ¬∃ p q, p < H ∧ q < M ∧ A.getD p 0 + B.getD q 0 = t) := by
  intro N
  induction N with
  | zero =>
    intro H M A1 bd2 i j t A B f S r hAlen hBlen hM0 hiH hjM hN hf12 hf13 hf17 hf22 hf18
      hf5 hf11 hf1 hf2 hAget hBget hAsort hBsort hB0 hvsum htfit hfit hA1fit hB2fit
      hA133 hBd33 hinv hS
    omega
  | succ N ih =>
    intro H M A1 bd2 i j t A B f S r hAlen hBlen hM0 hiH hjM hN hf12 hf13 hf17 hf22 hf18
      hf5 hf11 hf1 hf2 hAget hBget hAsort hBsort hB0 hvsum htfit hfit hA1fit hB2fit
      hA133 hBd33 hinv hS
    -- cell/value fits
    have hAi : A1 + i < 2 ^ w := by omega
    have hBj : bd2 + j < 2 ^ w := by omega
    have hvi : A.getD i 0 < 2 ^ w := by
      have e := hAget i hiH
      rw [← e]
      exact hfit _
    have hvj : B.getD j 0 < 2 ^ w := by
      have e := hBget j hjM
      rw [← e]
      exact hfit _
    have hvmem1 : A.getD i 0 ∈ A := mem_getD (by rw [hAlen]; exact hiH)
    have hvmem2 : B.getD j 0 ∈ B := mem_getD (by rw [hBlen]; exact hjM)
    have hsv : A.getD i 0 + B.getD j 0 < 2 ^ w := hvsum _ hvmem1 _ hvmem2
    -- the 5-step read/compute prefix 229..233
    have f1f : ∀ q, (up f 20 (A1 + i)) q < 2 ^ w := up_fit hfit hAi
    have f2f : ∀ q, (up (up f 20 (A1 + i)) 15 (A.getD i 0)) q < 2 ^ w := up_fit f1f hvi
    have f3f : ∀ q, (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) q < 2 ^ w := up_fit f2f hBj
    have f4f : ∀ q, (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) q < 2 ^ w := up_fit f3f hvj
    have f5f : ∀ q, (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) q < 2 ^ w := up_fit f4f hsv
    have e229 : f 22 + f 12 = A1 + i := by rw [hf22, hf12]
    have e231 : (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 18
        + (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 13 = bd2 + j := by
      rw [up_ne (show (18:Nat) ≠ 15 by omega), up_ne (show (18:Nat) ≠ 20 by omega), hf18,
        up_ne (show (13:Nat) ≠ 15 by omega), up_ne (show (13:Nat) ≠ 20 by omega), hf13]
    have e233 : (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 15
        + (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 16
        = A.getD i 0 + B.getD j 0 := by
      rw [up_ne (show (15:Nat) ≠ 16 by omega), up_ne (show (15:Nat) ≠ 21 by omega), up_eq,
        up_eq]
    have hsteps5 : exec prog2 ρ S 229 r (memOf w f)
        = exec prog2 ρ (S - 5) 234 r
            (memOf w (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0))) := by
      rw [exec_add_step (by omega)
            (show prog2.getD 229 Instr.reject = Instr.add 20 22 12 by rfl), e229,
        exec_load_step (by omega)
            (show prog2.getD 230 Instr.reject = Instr.load 15 20 by rfl) f1f,
          up_eq, up_ne (show A1 + i ≠ 20 by omega), hAget i hiH,
        exec_add_step (by omega)
            (show prog2.getD 231 Instr.reject = Instr.add 21 18 13 by rfl), e231,
        exec_load_step (by omega)
            (show prog2.getD 232 Instr.reject = Instr.load 16 21 by rfl) f3f,
          up_eq, up_ne (show bd2 + j ≠ 21 by omega), up_ne (show bd2 + j ≠ 15 by omega),
          up_ne (show bd2 + j ≠ 20 by omega), hBget j hjM,
        exec_add_step (by omega)
            (show prog2.getD 233 Instr.reject = Instr.add 14 15 16 by rfl), e233]
      simp only [Nat.sub_sub, Nat.reduceAdd]
    -- u5 register facts (u5 = the post-prefix state)
    have u14 : (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 14 = A.getD i 0 + B.getD j 0 := up_eq _ _ _
    have u17 : (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 17 = t := by
      rw [up_ne (show (17:Nat) ≠ 14 by omega), up_ne (show (17:Nat) ≠ 16 by omega),
        up_ne (show (17:Nat) ≠ 21 by omega), up_ne (show (17:Nat) ≠ 15 by omega),
        up_ne (show (17:Nat) ≠ 20 by omega), hf17]
    have u12 : (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 12 = i := by
      rw [up_ne (show (12:Nat) ≠ 14 by omega), up_ne (show (12:Nat) ≠ 16 by omega),
        up_ne (show (12:Nat) ≠ 21 by omega), up_ne (show (12:Nat) ≠ 15 by omega),
        up_ne (show (12:Nat) ≠ 20 by omega), hf12]
    have u13 : (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 13 = j := by
      rw [up_ne (show (13:Nat) ≠ 14 by omega), up_ne (show (13:Nat) ≠ 16 by omega),
        up_ne (show (13:Nat) ≠ 21 by omega), up_ne (show (13:Nat) ≠ 15 by omega),
        up_ne (show (13:Nat) ≠ 20 by omega), hf13]
    have u1v : (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 1 = 1 := by
      rw [up_ne (show (1:Nat) ≠ 14 by omega), up_ne (show (1:Nat) ≠ 16 by omega),
        up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (1:Nat) ≠ 15 by omega),
        up_ne (show (1:Nat) ≠ 20 by omega), hf1]
    have u2v : (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 2 = 0 := by
      rw [up_ne (show (2:Nat) ≠ 14 by omega), up_ne (show (2:Nat) ≠ 16 by omega),
        up_ne (show (2:Nat) ≠ 21 by omega), up_ne (show (2:Nat) ≠ 15 by omega),
        up_ne (show (2:Nat) ≠ 20 by omega), hf2]
    by_cases hlt : A.getD i 0 + B.getD j 0 < t
    · -- CASE s < t: i++ at 237, then 238 decides
      have hwalk7 : exec prog2 ρ (S - 5) 234 r
          (memOf w (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)))
          = exec prog2 ρ (S - 7) 238 r
              (memOf w (up (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 12 (i + 1))) := by
        rw [exec_blt_lt_step (by omega)
              (show prog2.getD 234 Instr.reject = Instr.blt 14 17 237 by rfl) f5f
              (by rw [u14, u17]; exact hlt),
          exec_add_step (by omega)
              (show prog2.getD 237 Instr.reject = Instr.add 12 12 1 by rfl),
            show (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 12
                + (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 1
                = i + 1 from by rw [u12, u1v]]
        simp only [Nat.sub_sub, Nat.reduceAdd]
      -- u6 = up u5 12 (i+1) facts
      have u12' : (up (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 12 (i + 1)) 12 = i + 1 := up_eq _ _ _
      have u5' : (up (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 12 (i + 1)) 5 = H := by
        rw [up_ne (show (5:Nat) ≠ 12 by omega), up_ne (show (5:Nat) ≠ 14 by omega),
          up_ne (show (5:Nat) ≠ 16 by omega), up_ne (show (5:Nat) ≠ 21 by omega),
          up_ne (show (5:Nat) ≠ 15 by omega), up_ne (show (5:Nat) ≠ 20 by omega), hf5]
      have u6f : ∀ q, (up (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 12 (i + 1)) q < 2 ^ w :=
        up_fit f5f (by omega)
      have u13' : (up (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 12 (i + 1)) 13 = j := by
        rw [up_ne (show (13:Nat) ≠ 12 by omega), u13]
      have u17' : (up (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 12 (i + 1)) 17 = t := by
        rw [up_ne (show (17:Nat) ≠ 12 by omega), u17]
      have u22' : (up (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 12 (i + 1)) 22 = A1 := by
        rw [up_ne (show (22:Nat) ≠ 12 by omega), up_ne (show (22:Nat) ≠ 14 by omega),
          up_ne (show (22:Nat) ≠ 16 by omega), up_ne (show (22:Nat) ≠ 21 by omega),
          up_ne (show (22:Nat) ≠ 15 by omega), up_ne (show (22:Nat) ≠ 20 by omega), hf22]
      have u18' : (up (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 12 (i + 1)) 18 = bd2 := by
        rw [up_ne (show (18:Nat) ≠ 12 by omega), up_ne (show (18:Nat) ≠ 14 by omega),
          up_ne (show (18:Nat) ≠ 16 by omega), up_ne (show (18:Nat) ≠ 21 by omega),
          up_ne (show (18:Nat) ≠ 15 by omega), up_ne (show (18:Nat) ≠ 20 by omega), hf18]
      have u11' : (up (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 12 (i + 1)) 11 = M := by
        rw [up_ne (show (11:Nat) ≠ 12 by omega), up_ne (show (11:Nat) ≠ 14 by omega),
          up_ne (show (11:Nat) ≠ 16 by omega), up_ne (show (11:Nat) ≠ 21 by omega),
          up_ne (show (11:Nat) ≠ 15 by omega), up_ne (show (11:Nat) ≠ 20 by omega), hf11]
      have u1'' : (up (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 12 (i + 1)) 1 = 1 := by
        rw [up_ne (show (1:Nat) ≠ 12 by omega), u1v]
      have u2'' : (up (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 12 (i + 1)) 2 = 0 := by
        rw [up_ne (show (2:Nat) ≠ 12 by omega), u2v]
      have gA' : ∀ q, q < H → (up (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 12 (i + 1)) (A1 + q) = A.getD q 0 := by
        intro q hq
        rw [up_ne (show A1 + q ≠ 12 by omega), up_ne (show A1 + q ≠ 14 by omega),
          up_ne (show A1 + q ≠ 16 by omega), up_ne (show A1 + q ≠ 21 by omega),
          up_ne (show A1 + q ≠ 15 by omega), up_ne (show A1 + q ≠ 20 by omega),
          hAget q hq]
      have gB' : ∀ q, q < M → (up (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 12 (i + 1)) (bd2 + q) = B.getD q 0 := by
        intro q hq
        rw [up_ne (show bd2 + q ≠ 12 by omega), up_ne (show bd2 + q ≠ 14 by omega),
          up_ne (show bd2 + q ≠ 16 by omega), up_ne (show bd2 + q ≠ 21 by omega),
          up_ne (show bd2 + q ≠ 15 by omega), up_ne (show bd2 + q ≠ 20 by omega),
          hBget q hq]
      -- corner invariant after i++: row i dies below j by B-monotonicity
      have hinv' : ∀ p q, p < H → q < M → (p < i + 1 ∨ j < q) →
          A.getD p 0 + B.getD q 0 ≠ t := by
        intro p q hp hq hex
        rcases hex with hex | hex
        · by_cases hpi : p < i
          · exact hinv p q hp hq (Or.inl hpi)
          · by_cases hqj : q ≤ j
            · have hmono : B.getD q 0 ≤ B.getD j 0 :=
                pairwise_getD_mono hBsort q j hqj (by rw [hBlen]; exact hjM)
              have hpe : p = i := by omega
              rw [hpe]
              omega
            · exact hinv p q hp hq (Or.inr (by omega))
        · exact hinv p q hp hq (Or.inr hex)
      by_cases hnext : i + 1 < H
      · -- loop back to 229
        have hlt238 : (up (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 12 (i + 1)) 12
            < (up (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 12 (i + 1)) 5 := by
          rw [u12', u5']
          exact hnext
        obtain ⟨c2, v, hc2, hex2, hvt, hvf⟩ :=
          ih H M A1 bd2 (i + 1) j t A B
            (up (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 12 (i + 1))
            (S - 8) r hAlen hBlen hM0 hnext hjM (by omega)
            u12' u13' u17' u22' u18' u5' u11' u1'' u2'' gA' gB' hAsort hBsort hB0 hvsum
            htfit u6f hA1fit hB2fit hA133 hBd33 hinv' (by omega)
        refine ⟨8 + c2, v, by omega, ?_, hvt, hvf⟩
        rw [hsteps5, hwalk7,
          exec_blt_lt_step (by omega)
            (show prog2.getD 238 Instr.reject = Instr.blt 12 5 229 by rfl) u6f hlt238,
          show S - 7 - 1 = S - 8 from by omega, hex2]
      · -- i exhausted: reject at 239; corner {p < H} covers everything
        have hge238 : ¬ ((up (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 12 (i + 1)) 12
            < (up (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 12 (i + 1)) 5) := by
          rw [u12', u5']
          omega
        refine ⟨9, false, by omega, ?_, ?_, ?_⟩
        · rw [hsteps5, hwalk7,
            exec_blt_ge_step (by omega)
              (show prog2.getD 238 Instr.reject = Instr.blt 12 5 229 by rfl) u6f hge238,
            exec_reject_step (by omega)
              (show prog2.getD 239 Instr.reject = Instr.reject by rfl)]
        · intro hv
          exact absurd hv (by decide)
        · intro hv hp
          obtain ⟨p, q, hpH, hqM, hsum⟩ := hp
          have hiH' : i + 1 = H := by omega
          by_cases hpi : p < i
          · exact absurd hsum (hinv p q hpH hqM (Or.inl hpi))
          · by_cases hqj : q ≤ j
            · have hmono : B.getD q 0 ≤ B.getD j 0 :=
                pairwise_getD_mono hBsort q j hqj (by rw [hBlen]; exact hjM)
              have hpe : p = i := by omega
              subst hpe
              omega
            · exact absurd hsum (hinv p q hpH hqM (Or.inr (by omega)))
    · -- CASE s ≥ t: 235 decides t < s
      by_cases hgt : t < A.getD i 0 + B.getD j 0
      · -- s > t
        have hge234 : ¬ ((up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 14
            < (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 17) := by
          rw [u14, u17]
          omega
        have hwalk240 : exec prog2 ρ (S - 5) 234 r
            (memOf w (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)))
            = exec prog2 ρ (S - 7) 240 r
                (memOf w (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0))) := by
          rw [exec_blt_ge_step (by omega)
                (show prog2.getD 234 Instr.reject = Instr.blt 14 17 237 by rfl) f5f hge234,
            exec_blt_lt_step (by omega)
                (show prog2.getD 235 Instr.reject = Instr.blt 17 14 240 by rfl) f5f
                (by rw [u17, u14]; exact hgt)]
          simp only [Nat.sub_sub, Nat.reduceAdd]
        by_cases hj0 : 0 < j
        · -- j--: back to 229 with j−1 (u7 = up u5 13 (j−1))
          have hlt240 : (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 2
              < (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 13 := by
            rw [u2v, u13]
            exact hj0
          have hwalkj : exec prog2 ρ (S - 7) 240 r
              (memOf w (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)))
              = exec prog2 ρ (S - 10) 229 r
                  (memOf w (up (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 13 (j - 1))) := by
            rw [exec_blt_lt_step (by omega)
                  (show prog2.getD 240 Instr.reject = Instr.blt 2 13 242 by rfl) f5f hlt240,
              exec_sub_step (by omega)
                  (show prog2.getD 242 Instr.reject = Instr.sub 13 13 1 by rfl) f5f
                  (by rw [u13]; omega),
                show (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 13
                    - (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 1
                    = j - 1 from by rw [u13, u1v],
              exec_blt_lt_step (by omega)
                  (show prog2.getD 243 Instr.reject = Instr.blt 2 1 229 by rfl)
                  (up_fit f5f (by omega))
                  (by rw [up_ne (show (2:Nat) ≠ 13 by omega), u2v,
                        up_ne (show (1:Nat) ≠ 13 by omega), u1v]; omega)]
            simp only [Nat.sub_sub, Nat.reduceAdd]
          have u13'' : (up (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 13 (j - 1)) 13 = j - 1 := up_eq _ _ _
          have u12j : (up (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 13 (j - 1)) 12 = i := by
            rw [up_ne (show (12:Nat) ≠ 13 by omega), u12]
          have u17j : (up (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 13 (j - 1)) 17 = t := by
            rw [up_ne (show (17:Nat) ≠ 13 by omega), u17]
          have u22j : (up (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 13 (j - 1)) 22 = A1 := by
            rw [up_ne (show (22:Nat) ≠ 13 by omega), up_ne (show (22:Nat) ≠ 14 by omega),
              up_ne (show (22:Nat) ≠ 16 by omega), up_ne (show (22:Nat) ≠ 21 by omega),
              up_ne (show (22:Nat) ≠ 15 by omega), up_ne (show (22:Nat) ≠ 20 by omega), hf22]
          have u18j : (up (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 13 (j - 1)) 18 = bd2 := by
            rw [up_ne (show (18:Nat) ≠ 13 by omega), up_ne (show (18:Nat) ≠ 14 by omega),
              up_ne (show (18:Nat) ≠ 16 by omega), up_ne (show (18:Nat) ≠ 21 by omega),
              up_ne (show (18:Nat) ≠ 15 by omega), up_ne (show (18:Nat) ≠ 20 by omega), hf18]
          have u5j : (up (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 13 (j - 1)) 5 = H := by
            rw [up_ne (show (5:Nat) ≠ 13 by omega), up_ne (show (5:Nat) ≠ 14 by omega),
              up_ne (show (5:Nat) ≠ 16 by omega), up_ne (show (5:Nat) ≠ 21 by omega),
              up_ne (show (5:Nat) ≠ 15 by omega), up_ne (show (5:Nat) ≠ 20 by omega), hf5]
          have u11j : (up (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 13 (j - 1)) 11 = M := by
            rw [up_ne (show (11:Nat) ≠ 13 by omega), up_ne (show (11:Nat) ≠ 14 by omega),
              up_ne (show (11:Nat) ≠ 16 by omega), up_ne (show (11:Nat) ≠ 21 by omega),
              up_ne (show (11:Nat) ≠ 15 by omega), up_ne (show (11:Nat) ≠ 20 by omega), hf11]
          have u1j : (up (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 13 (j - 1)) 1 = 1 := by
            rw [up_ne (show (1:Nat) ≠ 13 by omega), u1v]
          have u2j : (up (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 13 (j - 1)) 2 = 0 := by
            rw [up_ne (show (2:Nat) ≠ 13 by omega), u2v]
          have u7f : ∀ q, (up (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 13 (j - 1)) q < 2 ^ w :=
            up_fit f5f (by omega)
          have gA'' : ∀ q, q < H → (up (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 13 (j - 1)) (A1 + q) = A.getD q 0 := by
            intro q hq
            rw [up_ne (show A1 + q ≠ 13 by omega), up_ne (show A1 + q ≠ 14 by omega),
              up_ne (show A1 + q ≠ 16 by omega), up_ne (show A1 + q ≠ 21 by omega),
              up_ne (show A1 + q ≠ 15 by omega), up_ne (show A1 + q ≠ 20 by omega),
              hAget q hq]
          have gB'' : ∀ q, q < M → (up (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 13 (j - 1)) (bd2 + q) = B.getD q 0 := by
            intro q hq
            rw [up_ne (show bd2 + q ≠ 13 by omega), up_ne (show bd2 + q ≠ 14 by omega),
              up_ne (show bd2 + q ≠ 16 by omega), up_ne (show bd2 + q ≠ 21 by omega),
              up_ne (show bd2 + q ≠ 15 by omega), up_ne (show bd2 + q ≠ 20 by omega),
              hBget q hq]
          have hjM' : j - 1 < M := by omega
          -- corner invariant after j--: column j dies right of i by A-monotonicity
          have hinv'' : ∀ p q, p < H → q < M → (p < i ∨ j - 1 < q) →
              A.getD p 0 + B.getD q 0 ≠ t := by
            intro p q hp hq hex
            rcases hex with hex | hex
            · exact hinv p q hp hq (Or.inl hex)
            · by_cases hqj : q = j
              · rw [hqj]
                by_cases hpi : p < i
                · exact hinv p j hp hjM (Or.inl hpi)
                · have hmono : A.getD i 0 ≤ A.getD p 0 :=
                    pairwise_getD_mono hAsort i p (by omega) (by rw [hAlen]; exact hp)
                  omega
              · have hqg : j < q := by omega
                exact hinv p q hp hq (Or.inr hqg)
          obtain ⟨c2, v, hc2, hex2, hvt, hvf⟩ :=
            ih H M A1 bd2 i (j - 1) t A B
              (up (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 13 (j - 1))
              (S - 10) r hAlen hBlen hM0 hiH hjM' (by omega)
              u12j u13'' u17j u22j u18j u5j u11j u1j u2j gA'' gB'' hAsort hBsort hB0 hvsum
              htfit u7f hA1fit hB2fit hA133 hBd33 hinv'' (by omega)
          refine ⟨10 + c2, v, by omega, ?_, hvt, hvf⟩
          rw [hsteps5, hwalk240, hwalkj, hex2]
        · -- j = 0 and s > t: reject at 241; rows ≥ i all exceed t
          have hjz : j = 0 := by omega
          have hge240 : ¬ ((up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 2
              < (up (up (up (up (up f 20 (A1 + i)) 15 (A.getD i 0)) 21 (bd2 + j)) 16 (B.getD j 0)) 14 (A.getD i 0 + B.getD j 0)) 13) := by
            rw [u2v, u13]
            omega
          refine ⟨9, false, by omega, ?_, ?_, ?_⟩
          · rw [hsteps5, hwalk240,
              exec_blt_ge_step (by omega)
                (show prog2.getD 240 Instr.reject = Instr.blt 2 13 242 by rfl) f5f hge240,
              exec_reject_step (by omega)
                (show prog2.getD 241 Instr.reject = Instr.reject by rfl)]
          · intro hv
            exact absurd hv (by decide)
          · intro hv hp
            obtain ⟨p, q, hpH, hqM, hsum⟩ := hp
            by_cases hpi : p < i
            · exact absurd hsum (hinv p q hpH hqM (Or.inl hpi))
            · by_cases hqz : q = 0
              · have hjq : q = j := by omega
                have hmono : A.getD i 0 ≤ A.getD p 0 :=
                  pairwise_getD_mono hAsort i p (by omega) (by rw [hAlen]; exact hpH)
                have e0 : B.getD q 0 = B.getD j 0 := by rw [hjq]
                omega
              · exact absurd hsum (hinv p q hpH hqM (Or.inr (by omega)))
      · -- s = t: ACCEPT at 236
        refine ⟨8, true, by omega, ?_, ?_, ?_⟩
        · rw [hsteps5,
            exec_blt_ge_step (by omega)
              (show prog2.getD 234 Instr.reject = Instr.blt 14 17 237 by rfl) f5f
              (by rw [u14, u17]; omega),
            exec_blt_ge_step (by omega)
              (show prog2.getD 235 Instr.reject = Instr.blt 17 14 240 by rfl) f5f
              (by rw [u17, u14]; exact hgt),
            exec_accept_step (by omega)
              (show prog2.getD 236 Instr.reject = Instr.accept by rfl)]
        · intro hv
          exact ⟨i, j, hiH, hjM, by omega⟩
        · intro hv
          exact absurd hv (by decide)

end SubsetSum.MITM

namespace SubsetSum.MITM

open BigOSpeedrun.SubsetSum SubsetSum.MITM.Spec

set_option maxHeartbeats 2000000 in
/-- THE scanB segment contract (pcs 224 → accept/reject).  Consumes
`phaseA2_exec`'s output verbatim.  Within `10·(2^(n/2) + 2^(n−n/2)) + 3`
steps the run HALTS with verdict `v`, and `v = true ↔ x.yes`. -/
theorem scanB_exec {w n : Nat} (ρ : Nat → BitVec w) {x : Instance n}
    (hn : 4 ≤ n) (hw : wordLength n x.bits ≤ w)
    (f : Nat → Nat) (r S : Nat) (bd2 : Nat)
    (hfit : ∀ q, f q < 2 ^ w)
    (h1 : f 1 = 1) (h2 : f 2 = 0) (h7 : f 7 = n) (h8 : f 8 = 2 * n + 23)
    (h11 : f 11 = 2 ^ (n - n / 2)) (h18 : f 18 = bd2)
    (hbd2 : bd2 = 3 * n + 26 + 2 ^ (n / 2) ∨
      bd2 = 3 * n + 27 + 2 ^ (n / 2) + 2 ^ (n - n / 2))
    (harr2 : arrL f bd2 (2 ^ (n - n / 2))
      = halfSums (instA2 x (n / 2)) (n - n / 2))
    (h22 : f 22 = 3 * n + 25) (h5 : f 5 = 2 ^ (n / 2))
    (harr1 : arrL f (3 * n + 25) (2 ^ (n / 2)) = halfSums (instA x) (n / 2))
    (hft : f (2 * n + 23 + (n + 1)) = x.t)
    (haddr : ∀ c, c ≤ 3 * n + 27 + 2 ^ (n / 2) + 2 * 2 ^ (n - n / 2) → c < 2 ^ w)
    (hS : 10 * (2 ^ (n / 2) + 2 ^ (n - n / 2)) + 3 ≤ S) :
    ∃ c v, c ≤ 10 * (2 ^ (n / 2) + 2 ^ (n - n / 2)) + 3 ∧
      exec prog2 ρ S 224 r (memOf w f) = some v ∧ (v = true ↔ x.yes) := by
  -- fit facts used repeatedly
  have htfit : x.t < 2 ^ w := by
    have := hfit (2 * n + 23 + (n + 1))
    rw [hft] at this
    exact this
  have hX1 : 1 ≤ 2 ^ (n / 2) := Nat.one_le_two_pow
  have hY1 : 1 ≤ 2 ^ (n - n / 2) := Nat.one_le_two_pow
  have hMw : 2 ^ (n - n / 2) < 2 ^ w := haddr _ (by omega)
  have hHw : 2 ^ (n / 2) < 2 ^ w := haddr _ (by omega)
  -- the 5-step setup 224..228
  have v1f : ∀ q, (up f 20 (3 * n + 23)) q < 2 ^ w :=
    up_fit hfit (haddr _ (by omega))
  have v2f : ∀ q, (up (up f 20 (3 * n + 23)) 20 (3 * n + 24)) q < 2 ^ w :=
    up_fit v1f (haddr _ (by omega))
  have v3f : ∀ q, (up (up (up f 20 (3 * n + 23)) 20 (3 * n + 24)) 17 x.t) q < 2 ^ w :=
    up_fit v2f htfit
  have v4f : ∀ q, (up (up (up (up f 20 (3 * n + 23)) 20 (3 * n + 24)) 17 x.t) 12 0) q < 2 ^ w :=
    up_fit v3f (by omega)
  have v5f : ∀ q, (up (up (up (up (up f 20 (3 * n + 23)) 20 (3 * n + 24)) 17 x.t) 12 0) 13 (2 ^ (n - n / 2) - 1)) q < 2 ^ w :=
    up_fit v4f (by omega)
  have e224 : f 8 + f 7 = 3 * n + 23 := by rw [h8, h7]; omega
  have e225 : (up f 20 (3 * n + 23)) 20 + (up f 20 (3 * n + 23)) 1 = 3 * n + 24 := by
    rw [up_eq, up_ne (show (1:Nat) ≠ 20 by omega), h1]
  have e226 : f (3 * n + 24) = x.t := by
    have e : 3 * n + 24 = 2 * n + 23 + (n + 1) := by omega
    rw [e, hft]
  have e228 : (up (up (up (up f 20 (3 * n + 23)) 20 (3 * n + 24)) 17 x.t) 12 0) 11
      - (up (up (up (up f 20 (3 * n + 23)) 20 (3 * n + 24)) 17 x.t) 12 0) 1
      = 2 ^ (n - n / 2) - 1 := by
    rw [up_ne (show (11:Nat) ≠ 12 by omega), up_ne (show (11:Nat) ≠ 17 by omega),
      up_ne (show (11:Nat) ≠ 20 by omega), up_ne (show (11:Nat) ≠ 20 by omega), h11,
      up_ne (show (1:Nat) ≠ 12 by omega), up_ne (show (1:Nat) ≠ 17 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega), up_ne (show (1:Nat) ≠ 20 by omega), h1]
  have e228le : (up (up (up (up f 20 (3 * n + 23)) 20 (3 * n + 24)) 17 x.t) 12 0) 1
      ≤ (up (up (up (up f 20 (3 * n + 23)) 20 (3 * n + 24)) 17 x.t) 12 0) 11 := by
    rw [up_ne (show (1:Nat) ≠ 12 by omega), up_ne (show (1:Nat) ≠ 17 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega), up_ne (show (1:Nat) ≠ 20 by omega), h1,
      up_ne (show (11:Nat) ≠ 12 by omega), up_ne (show (11:Nat) ≠ 17 by omega),
      up_ne (show (11:Nat) ≠ 20 by omega), up_ne (show (11:Nat) ≠ 20 by omega), h11]
    exact Nat.one_le_two_pow
  have hsetup : exec prog2 ρ S 224 r (memOf w f)
      = exec prog2 ρ (S - 5) 229 r
          (memOf w (up (up (up (up (up f 20 (3 * n + 23)) 20 (3 * n + 24)) 17 x.t) 12 0) 13 (2 ^ (n - n / 2) - 1))) := by
    rw [exec_add_step (by omega)
          (show prog2.getD 224 Instr.reject = Instr.add 20 8 7 by rfl), e224,
      exec_add_step (by omega)
          (show prog2.getD 225 Instr.reject = Instr.add 20 20 1 by rfl), e225,
      exec_load_step (by omega)
          (show prog2.getD 226 Instr.reject = Instr.load 17 20 by rfl) v2f,
        up_eq, up_ne (show 3 * n + 24 ≠ 20 by omega),
        up_ne (show 3 * n + 24 ≠ 20 by omega), e226,
      exec_sub_step (by omega)
          (show prog2.getD 227 Instr.reject = Instr.sub 12 12 12 by rfl) v3f
        (Nat.le_refl _),
        Nat.sub_self,
      exec_sub_step (by omega)
          (show prog2.getD 228 Instr.reject = Instr.sub 13 11 1 by rfl) v4f e228le,
        e228]
    simp only [Nat.sub_sub, Nat.reduceAdd]
  -- register/array facts about the loop-entry state g
  have g12 : (up (up (up (up (up f 20 (3 * n + 23)) 20 (3 * n + 24)) 17 x.t) 12 0) 13 (2 ^ (n - n / 2) - 1)) 12 = 0 := by
    rw [up_ne (show (12:Nat) ≠ 13 by omega), up_eq]
  have g13 : (up (up (up (up (up f 20 (3 * n + 23)) 20 (3 * n + 24)) 17 x.t) 12 0) 13 (2 ^ (n - n / 2) - 1)) 13 = 2 ^ (n - n / 2) - 1 := up_eq _ _ _
  have g17 : (up (up (up (up (up f 20 (3 * n + 23)) 20 (3 * n + 24)) 17 x.t) 12 0) 13 (2 ^ (n - n / 2) - 1)) 17 = x.t := by
    rw [up_ne (show (17:Nat) ≠ 13 by omega), up_ne (show (17:Nat) ≠ 12 by omega), up_eq]
  have g22 : (up (up (up (up (up f 20 (3 * n + 23)) 20 (3 * n + 24)) 17 x.t) 12 0) 13 (2 ^ (n - n / 2) - 1)) 22 = 3 * n + 25 := by
    rw [up_ne (show (22:Nat) ≠ 13 by omega), up_ne (show (22:Nat) ≠ 12 by omega),
      up_ne (show (22:Nat) ≠ 17 by omega), up_ne (show (22:Nat) ≠ 20 by omega),
      up_ne (show (22:Nat) ≠ 20 by omega), h22]
  have g18 : (up (up (up (up (up f 20 (3 * n + 23)) 20 (3 * n + 24)) 17 x.t) 12 0) 13 (2 ^ (n - n / 2) - 1)) 18 = bd2 := by
    rw [up_ne (show (18:Nat) ≠ 13 by omega), up_ne (show (18:Nat) ≠ 12 by omega),
      up_ne (show (18:Nat) ≠ 17 by omega), up_ne (show (18:Nat) ≠ 20 by omega),
      up_ne (show (18:Nat) ≠ 20 by omega), h18]
  have g5 : (up (up (up (up (up f 20 (3 * n + 23)) 20 (3 * n + 24)) 17 x.t) 12 0) 13 (2 ^ (n - n / 2) - 1)) 5 = 2 ^ (n / 2) := by
    rw [up_ne (show (5:Nat) ≠ 13 by omega), up_ne (show (5:Nat) ≠ 12 by omega),
      up_ne (show (5:Nat) ≠ 17 by omega), up_ne (show (5:Nat) ≠ 20 by omega),
      up_ne (show (5:Nat) ≠ 20 by omega), h5]
  have g11 : (up (up (up (up (up f 20 (3 * n + 23)) 20 (3 * n + 24)) 17 x.t) 12 0) 13 (2 ^ (n - n / 2) - 1)) 11 = 2 ^ (n - n / 2) := by
    rw [up_ne (show (11:Nat) ≠ 13 by omega), up_ne (show (11:Nat) ≠ 12 by omega),
      up_ne (show (11:Nat) ≠ 17 by omega), up_ne (show (11:Nat) ≠ 20 by omega),
      up_ne (show (11:Nat) ≠ 20 by omega), h11]
  have g1 : (up (up (up (up (up f 20 (3 * n + 23)) 20 (3 * n + 24)) 17 x.t) 12 0) 13 (2 ^ (n - n / 2) - 1)) 1 = 1 := by
    rw [up_ne (show (1:Nat) ≠ 13 by omega), up_ne (show (1:Nat) ≠ 12 by omega),
      up_ne (show (1:Nat) ≠ 17 by omega), up_ne (show (1:Nat) ≠ 20 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega), h1]
  have g2 : (up (up (up (up (up f 20 (3 * n + 23)) 20 (3 * n + 24)) 17 x.t) 12 0) 13 (2 ^ (n - n / 2) - 1)) 2 = 0 := by
    rw [up_ne (show (2:Nat) ≠ 13 by omega), up_ne (show (2:Nat) ≠ 12 by omega),
      up_ne (show (2:Nat) ≠ 17 by omega), up_ne (show (2:Nat) ≠ 20 by omega),
      up_ne (show (2:Nat) ≠ 20 by omega), h2]
  have gA : ∀ q, q < 2 ^ (n / 2) →
      (up (up (up (up (up f 20 (3 * n + 23)) 20 (3 * n + 24)) 17 x.t) 12 0) 13 (2 ^ (n - n / 2) - 1)) (3 * n + 25 + q)
        = (halfSums (instA x) (n / 2)).getD q 0 := by
    intro q hq
    rw [up_ne (show 3 * n + 25 + q ≠ 13 by omega),
      up_ne (show 3 * n + 25 + q ≠ 12 by omega),
      up_ne (show 3 * n + 25 + q ≠ 17 by omega),
      up_ne (show 3 * n + 25 + q ≠ 20 by omega),
      up_ne (show 3 * n + 25 + q ≠ 20 by omega),
      ← harr1, getD_arrL hq]
  have gB : ∀ q, q < 2 ^ (n - n / 2) →
      (up (up (up (up (up f 20 (3 * n + 23)) 20 (3 * n + 24)) 17 x.t) 12 0) 13 (2 ^ (n - n / 2) - 1)) (bd2 + q)
        = (halfSums (instA2 x (n / 2)) (n - n / 2)).getD q 0 := by
    intro q hq
    rw [up_ne (show bd2 + q ≠ 13 by omega),
      up_ne (show bd2 + q ≠ 12 by omega),
      up_ne (show bd2 + q ≠ 17 by omega),
      up_ne (show bd2 + q ≠ 20 by omega),
      up_ne (show bd2 + q ≠ 20 by omega),
      ← harr2, getD_arrL hq]
  have hA1fit : 3 * n + 25 + 2 ^ (n / 2) < 2 ^ w := haddr _ (by omega)
  have hB2fit : bd2 + 2 ^ (n - n / 2) < 2 ^ w := by
    rcases hbd2 with e | e <;> rw [e] <;> exact haddr _ (by omega)
  obtain ⟨c2, v, hc2, hexec, hvt, hvf⟩ :=
    scanLoop_exec ρ hn hw (2 ^ (n / 2) + 2 ^ (n - n / 2))
      (2 ^ (n / 2)) (2 ^ (n - n / 2)) (3 * n + 25) bd2 0 (2 ^ (n - n / 2) - 1) x.t
      (halfSums (instA x) (n / 2)) (halfSums (instA2 x (n / 2)) (n - n / 2))
      (up (up (up (up (up f 20 (3 * n + 23)) 20 (3 * n + 24)) 17 x.t) 12 0) 13 (2 ^ (n - n / 2) - 1))
      (S - 5) r
      (by rw [length_halfSums]) (by rw [length_halfSums])
      (by exact Nat.one_le_two_pow)
      (by exact Nat.one_le_two_pow) (by omega) (by omega)
      g12 g13 g17 g22 g18 g5 g11 g1 g2 gA gB
      (halfSums_sorted (instA x) (n / 2))
      (halfSums_sorted (instA2 x (n / 2)) (n - n / 2))
      (halfSums_head_zero (instA2 x (n / 2)) (n - n / 2))
      (fun v' hv' u' hu' => halfSumsSumLe (by omega) hw (by omega) v' u' hv' hu')
      htfit v5f hA1fit hB2fit
      (by omega)
      (by rcases hbd2 with e | e <;> omega)
      (by
        intro p q hp hq hex
        rcases hex with h | hq' <;> omega)
      (by omega)
  -- the verdict ↔ isSum bridge
  have hnm : n / 2 + (n - n / 2) = n := by omega
  have pair_to_yes : (∃ p q, p < 2 ^ (n / 2) ∧ q < 2 ^ (n - n / 2) ∧
      (halfSums (instA x) (n / 2)).getD p 0
        + (halfSums (instA2 x (n / 2)) (n - n / 2)).getD q 0 = x.t) → x.yes := by
    rintro ⟨p, q, hp, hq, hsum⟩
    have hA : (halfSums (instA x) (n / 2)).getD p 0 ∈ halfSums (instA x) (n / 2) :=
      mem_getD (by rw [length_halfSums]; exact hp)
    have hB : (halfSums (instA2 x (n / 2)) (n - n / 2)).getD q 0
        ∈ halfSums (instA2 x (n / 2)) (n - n / 2) :=
      mem_getD (by rw [length_halfSums]; exact hq)
    have hS1 : isSum (instA x) (n / 2) ((halfSums (instA x) (n / 2)).getD p 0) :=
      (mem_halfSums _ _ _).mp hA
    have hS2 : isSum (fun i => instA x (i + n / 2)) (n - n / 2)
        ((halfSums (instA2 x (n / 2)) (n - n / 2)).getD q 0) :=
      (mem_halfSums _ _ _).mp hB
    have hsplit : isSum (instA x) n x.t := by
      have h2 : isSum (instA x) (n / 2 + (n - n / 2)) x.t := by
        refine (isSum_split _ _ _ _).mpr ⟨(halfSums (instA x) (n / 2)).getD p 0, by omega, hS1, ?_⟩
        have e : x.t - (halfSums (instA x) (n / 2)).getD p 0
            = (halfSums (instA2 x (n / 2)) (n - n / 2)).getD q 0 := by omega
        rw [e]
        exact hS2
      rw [hnm] at h2
      exact h2
    exact (instance_yes_iff x).mpr hsplit
  have yes_to_pair : x.yes → ∃ p q, p < 2 ^ (n / 2) ∧ q < 2 ^ (n - n / 2) ∧
      (halfSums (instA x) (n / 2)).getD p 0
        + (halfSums (instA2 x (n / 2)) (n - n / 2)).getD q 0 = x.t := by
    intro hyes
    have hsum0 : isSum (instA x) n x.t := (instance_yes_iff x).mp hyes
    have hsum : isSum (instA x) (n / 2 + (n - n / 2)) x.t := by
      rw [hnm]
      exact hsum0
    obtain ⟨s, hs, hS1, hS2⟩ := (isSum_split _ _ _ _).mp hsum
    have hmemA : s ∈ arrL f (3 * n + 25) (2 ^ (n / 2)) := by
      rw [harr1]
      exact (mem_halfSums _ _ _).mpr hS1
    have hmemB : (x.t - s) ∈ arrL f bd2 (2 ^ (n - n / 2)) := by
      rw [harr2]
      exact (mem_halfSums _ _ _).mpr hS2
    obtain ⟨p, hp, hpA⟩ := mem_arrL.mp hmemA
    obtain ⟨q, hq, hqB⟩ := mem_arrL.mp hmemB
    refine ⟨p, q, hp, hq, ?_⟩
    have e1 : (halfSums (instA x) (n / 2)).getD p 0 = s := by
      rw [← harr1, getD_arrL hp, hpA]
    have e2 : (halfSums (instA2 x (n / 2)) (n - n / 2)).getD q 0 = x.t - s := by
      rw [← harr2, getD_arrL hq, hqB]
    omega
  refine ⟨5 + c2, v, by omega, ?_, ?_⟩
  · rw [hsetup, hexec]
  · constructor
    · intro hv
      exact pair_to_yes (hvt hv)
    · intro hyes
      by_cases hvb : v = true
      · exact hvb
      · have hvf' : v = false := by cases v <;> simp_all
        exact absurd (yes_to_pair hyes) (hvf hvf')

end SubsetSum.MITM
