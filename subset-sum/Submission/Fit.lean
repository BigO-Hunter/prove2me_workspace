import Submission.Bridge
set_option autoImplicit true

/-!
# Word-length fit: `2·Σa < 2^w` (R2125607414)

The wrapped-complement safety argument: every value the program handles is
at most `Σa`, while a wrapped complement `t − s (mod 2^w)` with `s > t` is
`2^w − (s − t) ≥ 2^w − Σa > Σa`.  Both need `2·Σa < 2^w`, which the
word-length formula `w = 4(n+b) + ⌈log₂(n+2)⁴⌉ + 1` gives with slack.

Core Lean ships no `Nat.log2` facts, so we first derive the recursion
equation (the definition hides a budget argument) and `n < 2^(log₂n+1)`.
-/

namespace SubsetSum.MITM

open BigOSpeedrun.SubsetSum SubsetSum.MITM.Spec

/-! ## `Nat.log2` facts, from first principles -/

/-- The budgeted recursion behind `Nat.log2` (same shape as the core def).
Proof-only, hence noncomputable (code generator rejects raw `Bool.rec`). -/
noncomputable def lgB : Nat → Nat → Nat :=
  fun k =>
    Nat.rec (motive := fun _ => Nat → Nat)
      (fun _ => 0)
      (fun _ ih m => Bool.rec 0 (ih (m / 2) + 1) (Nat.ble 2 m))
      k

theorem log2_eq_lgB (n : Nat) : Nat.log2 n = lgB n n := rfl

theorem lgB_step (k m : Nat) :
    lgB (k + 1) m = Bool.rec 0 (lgB k (m / 2) + 1) (Nat.ble 2 m) := rfl

theorem log2_succ_eq (m : Nat) :
    Nat.log2 (m + 1) = Bool.rec 0 (lgB m ((m + 1) / 2) + 1) (Nat.ble 2 (m + 1)) := by
  rw [log2_eq_lgB]
  rfl

/-- The budget is irrelevant: `lgB j m = log2 m` whenever `m ≤ j ≤ k`. -/
theorem lgB_budget_aux : ∀ k j, j ≤ k → ∀ m, m ≤ j → lgB j m = Nat.log2 m := by
  intro k
  induction k with
  | zero =>
    intro j hj m hm
    have hj0 : j = 0 := by omega
    subst hj0
    have hm0 : m = 0 := by omega
    subst hm0
    rfl
  | succ k ih =>
    intro j hj
    match j with
    | 0 =>
      intro m hm
      have hm0 : m = 0 := by omega
      subst hm0
      rfl
    | j' + 1 =>
      intro m
      match m with
      | 0 => intro _; rfl
      | m' + 1 =>
        intro hm
        rw [lgB_step, log2_succ_eq]
        cases hb : Nat.ble 2 (m' + 1) with
        | false => rfl
        | true =>
          have hmk : m' ≤ k := by omega
          have hjk : j' ≤ k := by omega
          have hdivj : (m' + 1) / 2 ≤ j' := by omega
          have hdivm : (m' + 1) / 2 ≤ m' := by omega
          rw [ih j' hjk _ hdivj, ih m' hmk _ hdivm]

theorem lgB_budget (j m : Nat) (h : m ≤ j) : lgB j m = Nat.log2 m :=
  lgB_budget_aux j j (Nat.le_refl j) m h

/-- The recursion equation. -/
theorem log2_step (m : Nat) :
    Nat.log2 (m + 1) = if 2 ≤ m + 1 then Nat.log2 ((m + 1) / 2) + 1 else 0 := by
  rw [log2_succ_eq]
  cases hb : Nat.ble 2 (m + 1) with
  | false =>
    have hle : ¬ 2 ≤ m + 1 := by
      intro h
      rw [Nat.ble_eq.mpr h] at hb
      simp at hb
    rw [if_neg hle]
  | true =>
    have hle : 2 ≤ m + 1 := Nat.ble_eq.mp hb
    rw [if_pos hle, lgB_budget _ _ (by omega)]

theorem log2_two_step {n : Nat} (h : 2 ≤ n) :
    Nat.log2 n = Nat.log2 (n / 2) + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [log2_step, if_pos (by omega)]

theorem log2_one : Nat.log2 1 = 0 := rfl

/-- The upper bound `n < 2^(log₂n+1)` — by bounded prefix induction. -/
theorem log2_lt_aux : ∀ k n, n ≤ k → 0 < n → n < 2 ^ (Nat.log2 n + 1) := by
  intro k
  induction k with
  | zero =>
    intro n hn hpos
    exact absurd hpos (Nat.not_lt.2 hn)
  | succ k ih =>
    intro n hn hpos
    by_cases h2 : 2 ≤ n
    · rw [log2_two_step h2]
      have hd : 0 < n / 2 := by omega
      have hilt := ih (n / 2) (by omega) hd
      have hexp : 2 ^ (Nat.log2 (n / 2) + 1 + 1)
          = 2 * 2 ^ (Nat.log2 (n / 2) + 1) := by
        rw [Nat.pow_succ]
        omega
      have hilt' : n / 2 + 1 ≤ 2 ^ (Nat.log2 (n / 2) + 1) := by omega
      calc n ≤ 2 * (n / 2) + 1 := by omega
        _ < 2 * 2 ^ (Nat.log2 (n / 2) + 1) := by omega
        _ = 2 ^ (Nat.log2 (n / 2) + 1 + 1) := hexp.symm
    · have hn1 : n = 1 := by omega
      subst hn1
      rw [log2_one]
      omega

theorem log2_lt {n : Nat} (h : 0 < n) : n < 2 ^ (Nat.log2 n + 1) :=
  log2_lt_aux (n + 1) n (by omega) h

/-! ## `foldl max` facts -/

theorem foldl_max_ge_init (l : List Nat) (j : Nat) : j ≤ l.foldl max j := by
  induction l generalizing j with
  | nil => simp [List.foldl]
  | cons a l' ih =>
    show j ≤ l'.foldl max (max j a)
    have base : max j a ≤ l'.foldl max (max j a) := ih (max j a)
    omega

theorem foldl_max_mono {l : List Nat} {j j' : Nat} (h : j ≤ j') :
    l.foldl max j ≤ l.foldl max j' := by
  induction l generalizing j j' with
  | nil => simpa using h
  | cons a l' ih =>
    show l'.foldl max (max j a) ≤ l'.foldl max (max j' a)
    exact ih (by omega)

theorem mem_le_foldl_max {l : List Nat} {v init : Nat} (h : v ∈ l) :
    v ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => cases h
  | cons a l' ih =>
    rcases List.mem_cons.mp h with h | h
    · rw [h]
      have hbase : max init a ≤ l'.foldl max (max init a) :=
        foldl_max_ge_init l' _
      have hdef : (a :: l').foldl max init = l'.foldl max (max init a) := rfl
      omega
    · have hv : v ≤ l'.foldl max init := ih h
      have hmono : l'.foldl max init ≤ l'.foldl max (max init a) :=
        foldl_max_mono (by omega)
      have hdef : (a :: l').foldl max init = l'.foldl max (max init a) := rfl
      omega

/-! ## `maxValue` facts -/

theorem maxValue_ge_a {n : Nat} (x : Instance n) (i : Fin n) :
    x.a i ≤ x.maxValue := by
  have hmem : x.a i ∈ List.ofFn x.a :=
    List.mem_ofFn.mpr ⟨i, rfl⟩
  exact mem_le_foldl_max hmem

theorem maxValue_ge_t {n : Nat} (x : Instance n) : x.t ≤ x.maxValue :=
  foldl_max_ge_init _ x.t

theorem maxValue_pos {n : Nat} (x : Instance n) (hn : 0 < n) : 0 < x.maxValue :=
  Nat.lt_of_lt_of_le (x.pos ⟨0, hn⟩) (maxValue_ge_a x ⟨0, hn⟩)

theorem maxValue_lt_pow {n : Nat} (x : Instance n) (hn : 0 < n) :
    x.maxValue < 2 ^ x.bits := by
  have h := log2_lt (maxValue_pos x hn)
  rw [show x.bits = Nat.log2 x.maxValue + 1 from rfl]
  exact h

/-! ## The sum bound -/

theorem sum_range_le {f : Nat → Nat} {B n : Nat} (h : ∀ i, i < n → f i ≤ B) :
    ((List.range n).map f).sum ≤ n * B := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hmap : (List.range (n + 1)).map f
        = (List.range n).map f ++ [f n] := by
      rw [List.range_succ, List.map_append, List.map_singleton]
    rw [hmap, List.sum_append, List.sum_singleton]
    have hB : f n ≤ B := h n (Nat.lt_succ_self n)
    have ih' : ((List.range n).map f).sum ≤ n * B :=
      ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have hprod : (n + 1) * B = n * B + B := by
      rw [Nat.add_mul, Nat.one_mul]
    omega

/-- The total input sum fits: `2·Σa < 2^w`. -/
theorem two_sum_lt_pow_wordLength {n : Nat} (x : Instance n) (hn : 2 ≤ n) :
    2 * ((List.range n).map (instA x)).sum
      < 2 ^ (wordLength n x.bits) := by
  have hmem : ∀ i, i < n → instA x i ≤ x.maxValue := by
    intro i hi
    unfold instA
    rw [dif_pos hi]
    exact maxValue_ge_a x ⟨i, hi⟩
  have hsum : ((List.range n).map (instA x)).sum ≤ n * x.maxValue :=
    sum_range_le hmem
  have hmax : x.maxValue < 2 ^ x.bits := maxValue_lt_pow x (by omega)
  have hnpos : 0 < n := by omega
  have hnlt : n * x.maxValue < n * 2 ^ x.bits :=
    Nat.mul_lt_mul_of_pos_left hmax hnpos
  have hlogn : Nat.log2 n ≤ n := Nat.log2_le_self n
  have hwdef : wordLength n x.bits
      = 4 * (n + x.bits) + Nat.log2 ((n + 2) ^ 4 - 1) + 1 := rfl
  have hexp : x.bits + Nat.log2 n + 2
      ≤ 4 * (n + x.bits) + Nat.log2 ((n + 2) ^ 4 - 1) + 1 := by omega
  have hexpW : x.bits + Nat.log2 n + 2 ≤ wordLength n x.bits := hwdef ▸ hexp
  have hloglt : n + 1 ≤ 2 ^ (Nat.log2 n + 1) := by
    have := log2_lt (by omega)
    omega
  -- explicit product steps (omega only abstracts whole products)
  have pA : 2 * ((List.range n).map (instA x)).sum
      ≤ 2 * (n * x.maxValue) := Nat.mul_le_mul_left 2 hsum
  have p1 : 2 * (n * x.maxValue) < 2 * (n * 2 ^ x.bits) :=
    Nat.mul_lt_mul_of_pos_left hnlt (by omega)
  have p2 : 2 * (n * 2 ^ x.bits) = 2 ^ x.bits * (2 * n) := by
    rw [← Nat.mul_assoc, Nat.mul_comm (2 * n)]
  have p3 : 2 * n < 2 * 2 ^ (Nat.log2 n + 1) :=
    Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  have e3 : 2 * 2 ^ (Nat.log2 n + 1) = 2 ^ ((Nat.log2 n + 1) + 1) := by
    rw [Nat.mul_comm, ← Nat.pow_succ]
  have p4 : 2 ^ x.bits * (2 * 2 ^ (Nat.log2 n + 1))
      = 2 ^ (x.bits + ((Nat.log2 n + 1) + 1)) := by
    rw [e3]
    exact (Nat.pow_add 2 x.bits ((Nat.log2 n + 1) + 1)).symm
  have p5 : 2 ^ (x.bits + ((Nat.log2 n + 1) + 1)) ≤ 2 ^ (wordLength n x.bits) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have p3' : 2 ^ x.bits * (2 * n)
      < 2 ^ x.bits * (2 * 2 ^ (Nat.log2 n + 1)) :=
    Nat.mul_lt_mul_of_pos_left p3 (by omega)
  calc 2 * ((List.range n).map (instA x)).sum
      ≤ 2 * (n * x.maxValue) := pA
    _ < 2 * (n * 2 ^ x.bits) := p1
    _ = 2 ^ x.bits * (2 * n) := p2
    _ < 2 ^ x.bits * (2 * 2 ^ (Nat.log2 n + 1)) := p3'
    _ = 2 ^ (x.bits + ((Nat.log2 n + 1) + 1)) := p4
    _ ≤ 2 ^ (wordLength n x.bits) := p5

end SubsetSum.MITM
