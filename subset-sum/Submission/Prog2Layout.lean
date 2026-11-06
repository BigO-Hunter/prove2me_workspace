import Submission.PhaseA
import Submission.Prog2
set_option autoImplicit true

/-!
# Prog2 layout extension + spec-level helpers (R2125607749 Lanes 2+3)

The three new `prog2` segments (canon 148–160, phaseA2 161–223, scanB
224–243) need a WIDER address envelope than the filed `pro_addr_lt`:
phaseA2's second big slot `B2 = 3n+26+2^(n/2)` and swap slot
`B3 = B2+2^(n−n/2)+1` push the top touched cell to
`B3+2^m−1 = 3n+26+2^(n/2)+2·2^(n−n/2)`.  Per the charter rule the filed
Prologue lemmas are NOT edited; the wider envelope is proven here as a
standalone variant (`pro_addr_lt2`, same induction shape), plus the
second-half spec facts (`instA2`, shifted-sum bounds, no-wrap total
bound, `halfSums` head-zero, `Pairwise` getD monotonicity) that scanB's
two-pointer verdict argument consumes.

Everything here is program-agnostic except `prog2`'s presence via the
import; no filed module is modified.
-/

namespace SubsetSum.MITM

open BigOSpeedrun.SubsetSum SubsetSum.MITM.Spec

/-! ## The wide address envelope -/

/-- `pro_addr_lt` variant for prog2's three-slot layout:
`3m+27+2^(m/2)+2·2^(m−m/2) < 2^(2m)` on `4 ≤ m`.  Same induction. -/
theorem pro_addr_lt2 (m : Nat) (hm : 4 ≤ m) :
    3 * m + 27 + 2 ^ (m / 2) + 2 * 2 ^ (m - m / 2) < 2 ^ (2 * m) := by
  have hbase : 3 * 4 + 27 + 2 ^ (4 / 2) + 2 * 2 ^ (4 - 4 / 2) < 2 ^ (2 * 4) := by decide
  induction m with
  | zero => omega
  | succ k ih =>
    by_cases hk : 4 ≤ k
    · have h1 : (k + 1) / 2 ≤ k / 2 + 1 := by omega
      have hp1 : 2 ^ ((k + 1) / 2) ≤ 2 ^ (k / 2 + 1) :=
        Nat.pow_le_pow_right (n := 2) (by omega) h1
      have h3 : (2 : Nat) ^ (k / 2 + 1) = 2 * 2 ^ (k / 2) := by
        rw [Nat.pow_add 2 (k / 2) 1, show (2:Nat) ^ 1 = 2 from rfl]
        omega
      have h1' : (k + 1) - (k + 1) / 2 ≤ k - k / 2 + 1 := by omega
      have hp1' : 2 ^ ((k + 1) - (k + 1) / 2) ≤ 2 ^ (k - k / 2 + 1) :=
        Nat.pow_le_pow_right (n := 2) (by omega) h1'
      have h3' : (2 : Nat) ^ (k - k / 2 + 1) = 2 * 2 ^ (k - k / 2) := by
        rw [Nat.pow_add 2 (k - k / 2) 1, show (2:Nat) ^ 1 = 2 from rfl]
        omega
      have h4 : (2 : Nat) ^ (2 * (k + 1)) = 4 * 2 ^ (2 * k) := by
        rw [show 2 * (k + 1) = 2 * k + 2 from by omega,
          Nat.pow_add 2 (2 * k) 2, show (2:Nat) ^ 2 = 4 from rfl]
        omega
      have ihm := ih hk
      omega
    · rw [show k + 1 = 4 from by omega]
      exact hbase

/-- The wide haddr envelope for prog2's exec walks, from the standing
`2^(2n) ≤ 2^w` hypothesis (the way `pro_addr_lt` feeds the filed walks). -/
theorem haddr2_wide {w n : Nat} (x : Instance n) (hn : 4 ≤ n)
    (hw : wordLength n x.bits ≤ w) :
    ∀ c, c ≤ 3 * n + 27 + 2 ^ (n / 2) + 2 * 2 ^ (n - n / 2) → c < 2 ^ w := by
  intro c hc
  have hpow := pro_pow2n x hn hw
  have := pro_addr_lt2 n hn
  omega

/-- The wide write region for prog2: registers plus all three big slots
(ARR1 = 3n+25 through B3+2^m).  `AReg n ⊆ AReg2 n`. -/
def AReg2 (n : Nat) (c : Nat) : Prop :=
  c ≤ 22 ∨ (3 * n + 25 ≤ c ∧ c < 3 * n + 27 + 2 ^ (n / 2) + 2 * 2 ^ (n - n / 2))

theorem AReg_le_AReg2 (n c : Nat) : AReg n c → AReg2 n c := by
  intro h
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · refine Or.inr ⟨h1, ?_⟩
    have h2p1 : 2 ^ (n / 2 + 1) = 2 * 2 ^ (n / 2) := by
      rw [Nat.pow_add 2 (n / 2) 1, show (2:Nat) ^ 1 = 2 from rfl]
      omega
    have hmn : n / 2 ≤ n - n / 2 := by omega
    have hpp : 2 ^ (n / 2) ≤ 2 ^ (n - n / 2) :=
      Nat.pow_le_pow_right (n := 2) (by omega) hmn
    omega

/-! ## The second-half family -/

/-- The shifted input family phaseA2 sorts: `instA2 x h i = a_{i+h}`. -/
def instA2 {n : Nat} (x : Instance n) (h : Nat) : Nat → Nat :=
  fun i => instA x (i + h)

theorem halfSums_congr {a b : Nat → Nat} (hab : ∀ i, a i = b i) (k : Nat) :
    halfSums a k = halfSums b k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show mmerge (halfSums a k) ((halfSums a k).map fun x => x + a k)
      = mmerge (halfSums b k) ((halfSums b k).map fun x => x + b k)
    rw [ih, hab k]

/-! ## Shifted-range sum arithmetic -/

theorem range_add_map (h q : Nat) :
    List.range (h + q) = List.range h ++ (List.range q).map (fun i => i + h) := by
  induction q with
  | zero => simp
  | succ q ih =>
    have e1 : h + (q + 1) = h + q + 1 := by omega
    have e2 : h + q = q + h := by omega
    rw [e1, List.range_succ, ih, List.range_succ, List.map_append,
      List.map_singleton]
    rw [List.append_assoc, e2]

theorem sum_map_add_split (g : Nat → Nat) (h q : Nat) :
    ((List.range (h + q)).map g).sum
      = ((List.range h).map g).sum
        + ((List.range q).map (fun i => g (i + h))).sum := by
  rw [range_add_map, List.map_append, List.sum_append]
  congr 1
  rw [List.map_map]
  rfl

theorem sum_map_add_le (g : Nat → Nat) (h q n : Nat) (hqn : h + q ≤ n) :
    ((List.range q).map (fun i => g (i + h))).sum
      ≤ ((List.range n).map g).sum := by
  have e := sum_map_add_split g h q
  have hle := sumRangeMono g hqn
  omega

theorem sum_split_le (g : Nat → Nat) (h q n : Nat) (hqn : h + q ≤ n) :
    ((List.range h).map g).sum
        + ((List.range q).map (fun i => g (i + h))).sum
      ≤ ((List.range n).map g).sum := by
  rw [← sum_map_add_split]
  exact sumRangeMono g hqn

/-! ## Fit facts for the second half and the scan sum -/

/-- Second-half analogue of `halfSumAddFit`: a half-sum of `a_{h}..a_{h+q-1}`
plus `a_{q+h}` fits a word. -/
theorem halfSumAddFit2 {n w h : Nat} {x : Instance n} (hn : 2 ≤ n)
    (hw : wordLength n x.bits ≤ w) (q : Nat) (hq : h + q < n)
    (v : Nat) (hv : v ∈ halfSums (instA2 x h) q) :
    v + instA x (q + h) < 2 ^ w := by
  have hsum : 2 * ((List.range n).map (instA x)).sum
      < 2 ^ (wordLength n x.bits) := two_sum_lt_pow_wordLength x hn
  have hvle : v ≤ ((List.range q).map (instA2 x h)).sum := halfSumsLe _ _ _ hv
  have hsplit := sum_split_le (instA x) h (q + 1) n (by omega)
  have e : ((List.range q).map (instA2 x h)).sum + instA x (q + h)
      = ((List.range (q + 1)).map (instA2 x h)).sum := by
    rw [sumRangeSucc]
    rfl
  have hpow : 2 ^ (wordLength n x.bits) ≤ 2 ^ w :=
    Nat.pow_le_pow_right (n := 2) (by omega) hw
  unfold instA2 at hvle e
  omega

/-- NO-WRAP for scanB: a first-half sum plus a second-half sum is
`≤ Σa < 2^w` (both halves over disjoint index ranges covering `≤ n`). -/
theorem halfSumsSumLe {n w h m : Nat} {x : Instance n} (hn : 2 ≤ n)
    (hw : wordLength n x.bits ≤ w) (hm : h + m ≤ n)
    (v1 v2 : Nat) (hv1 : v1 ∈ halfSums (instA x) h)
    (hv2 : v2 ∈ halfSums (instA2 x h) m) :
    v1 + v2 < 2 ^ w := by
  have h1 : v1 ≤ ((List.range h).map (instA x)).sum := halfSumsLe _ _ _ hv1
  have h2 : v2 ≤ ((List.range m).map (instA2 x h)).sum := halfSumsLe _ _ _ hv2
  have hsplit := sum_split_le (instA x) h m n hm
  have hsum : 2 * ((List.range n).map (instA x)).sum
      < 2 ^ (wordLength n x.bits) := two_sum_lt_pow_wordLength x hn
  have hpow : 2 ^ (wordLength n x.bits) ≤ 2 ^ w :=
    Nat.pow_le_pow_right (n := 2) (by omega) hw
  unfold instA2 at h2
  omega

/-! ## Sorted-array access facts scanB consumes -/

/-- `halfSums` always starts with `0` (the empty subset) — scanB's
reject-at-j=0 arm needs `S₂[0] = 0` as the minimum. -/
theorem halfSums_head_zero (a : Nat → Nat) : ∀ k : Nat,
    (halfSums a k).getD 0 0 = 0
  | 0 => by simp [halfSums]
  | k + 1 => by
    have hne : halfSums a k ≠ [] := by
      intro hc
      have hl := length_halfSums a k
      rw [hc] at hl
      simp at hl
      have h1 : (1:Nat) ≤ 2 ^ k := Nat.one_le_two_pow
      omega
    cases hL : halfSums a k with
    | nil => exact absurd hL hne
    | cons x l =>
      have hx : x = 0 := by
        have hrec := halfSums_head_zero a k
        rw [hL] at hrec
        simpa using hrec
      show (mmerge (halfSums a k) ((halfSums a k).map fun z => z + a k)).getD 0 0 = 0
      rw [hL, List.map_cons, mmerge]
      rw [if_neg (show ¬ (x + a k < x) by omega)]
      rw [hx]
      simp

/-- On a `Pairwise (· ≤ ·)` list, `getD` is monotone within bounds. -/
theorem pairwise_getD_mono {l : List Nat} : List.Pairwise (· ≤ ·) l →
    ∀ (i j : Nat), i ≤ j → j < l.length → l.getD i 0 ≤ l.getD j 0 := by
  induction l with
  | nil => intro _ i j _ hj; exact absurd hj (by simp)
  | cons a l ih =>
    intro hl i j hij hj
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hl
    cases i with
    | zero =>
      cases j with
      | zero => exact Nat.le_refl _
      | succ j =>
        have hjl : j < l.length := by simpa using hj
        exact hhead _ (mem_getD hjl)
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        have hjl : j < l.length := by simpa using hj
        have hi' : i ≤ j := by omega
        simpa using ih htail i j hi' hjl

/-- Array membership is a cell read. -/
theorem mem_arrL {f : Nat → Nat} {b L v : Nat} :
    v ∈ arrL f b L ↔ ∃ q, q < L ∧ f (b + q) = v := by
  simp only [arrL, List.mem_map, List.mem_range, arrAt]

/-- Membership transport along pointwise-equal families. -/
theorem halfSums_shift_comm {n : Nat} {x : Instance n} (h k : Nat) :
    halfSums (fun i => instA x (h + i)) k = halfSums (instA2 x h) k :=
  halfSums_congr (fun i => by
    have e : h + i = i + h := by omega
    rw [e]
    rfl) k

end SubsetSum.MITM
