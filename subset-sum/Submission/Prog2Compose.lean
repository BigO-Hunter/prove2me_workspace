import Submission.Prog2Pro
import Submission.Prog2PhaseA
import Submission.Race
set_option autoImplicit true

/-!
# The prog2 chain composed (R2125607749 Lanes 2+3 → L4)

`bign2_run`: for `n ≥ 4`, `run prog2 x ρ T` halts within `total2 n ≤ T` steps
with verdict `v`, and `v = true ↔ x.yes`.  The chain:

    prologue_exec (P2Pro)  0 → 86    ≤ 236 + 6·(n+2−23)
    phaseA_exec_p2 (P2)   86 → 148   ≤ 12 + 44·(2^(n/2)−1) + 24·(n/2)
    canon_exec           148 → 161   ≤ 6·2^(n/2) + 6
    phaseA2_exec         161 → 224   ≤ 12 + 44·(2^(n−n/2)−1) + 25·(n−n/2)
    scanB_exec           224 → halt  ≤ 10·(2^(n/2) + 2^(n−n/2)) + 3

`total2_le` folds the sum under Lane-1's recommended horizon
`256·2^(n/2) + 300·(n+2)` (worst coefficient sum: 44 + 6 + 88 + 30 = 168
per `2^(n/2)`, via `2^(n−n/2) ≤ 2·2^(n/2)`).  L4: take
`T₂ := fun n => if 4 ≤ n then 256·2^(n/2)+300·(n+2) else …small-n…`, or
keep `total2` directly (it is already `Θ(2^(n/2))`); BigO (1/2) per the
lit rider's K-lemma with `2^(2·(n/2)) ≤ 2^n` carried explicitly.

REMAINING for a full `SolvedInTime (1/2)` (the small-n lane, mechanical):
port Race's `pro_segA23`/`pro_dispatch23` (dispatch target literal
192 → 244 — the pc-12 instruction fact) and SmallN.lean at the uniform
+52 pc shift (192–248 → 244–300; jump-target literals shift identically;
register cells ≤ 22 and budgets < 192 are untouched by the map), then
`smalln2/3_run` analogues with the unchanged 34/48 budgets.
-/

namespace SubsetSum.MITM

open BigOSpeedrun.SubsetSum SubsetSum.MITM.Spec

/-- The proven prog2 budget sum for `n ≥ 4`. -/
def total2 (n : Nat) : Nat :=
  (236 + 6 * (n + 2 - 23))
  + (12 + 44 * (2 ^ (n / 2) - 1) + 24 * (n / 2))
  + (6 * 2 ^ (n / 2) + 6)
  + (12 + 44 * (2 ^ (n - n / 2) - 1) + 25 * (n - n / 2))
  + (10 * (2 ^ (n / 2) + 2 ^ (n - n / 2)) + 3)

/-- The budget folds under the Lane-1 horizon `256·2^(n/2) + 300·(n+2)`. -/
theorem total2_le (n : Nat) (hn : 4 ≤ n) :
    total2 n ≤ 256 * 2 ^ (n / 2) + 300 * (n + 2) := by
  have hmh : n - n / 2 ≤ n / 2 + 1 := by omega
  have hpowm : 2 ^ (n - n / 2) ≤ 2 * 2 ^ (n / 2) := by
    have h1 : 2 ^ (n - n / 2) ≤ 2 ^ (n / 2 + 1) :=
      Nat.pow_le_pow_right (by omega) hmh
    have h2 : 2 ^ (n / 2 + 1) = 2 * 2 ^ (n / 2) := by
      rw [Nat.pow_succ]
      omega
    omega
  have hq1 : 44 * (2 ^ (n / 2) - 1) = 44 * 2 ^ (n / 2) - 44 := by omega
  have hq2 : 44 * (2 ^ (n - n / 2) - 1) ≤ 44 * 2 ^ (n - n / 2) := by omega
  have hq3 : 44 * 2 ^ (n - n / 2) ≤ 88 * 2 ^ (n / 2) := by
    have h : 44 * 2 ^ (n - n / 2) ≤ 44 * (2 * 2 ^ (n / 2)) :=
      Nat.mul_le_mul (Nat.le_refl _) hpowm
    omega
  have hq4 : 10 * (2 ^ (n / 2) + 2 ^ (n - n / 2)) ≤ 30 * 2 ^ (n / 2) := by
    have h : 10 * (2 ^ (n / 2) + 2 ^ (n - n / 2))
        ≤ 10 * (2 ^ (n / 2) + 2 * 2 ^ (n / 2)) :=
      Nat.mul_le_mul (Nat.le_refl _) (Nat.add_le_add (Nat.le_refl _) hpowm)
    omega
  simp only [total2]
  omega

open scoped Classical in
/-- THE n ≥ 4 driver for prog2: within `total2 n` steps the run halts with
the membership verdict (independent of the tape — prog2 has no rand). -/
theorem bign2_run {n : Nat} (x : Instance n) (hn : 4 ≤ n)
    (ρ : Nat → BitVec (wordLength n x.bits)) (T : Nat) (hT : total2 n ≤ T) :
    ∃ v : Bool, run prog2 x ρ T = some v ∧ (v = true ↔ x.yes) := by
  have hw : wordLength n x.bits ≤ wordLength n x.bits := Nat.le_refl _
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
  have hwide : ∀ c, c ≤ 3 * n + 27 + 2 ^ (n / 2) + 2 * 2 ^ (n - n / 2)
      → c < 2 ^ (wordLength n x.bits) :=
    haddr2_wide x hn hw
  simp only [total2] at hT
  -- prologue: 0 → 86
  obtain ⟨g, c₁, hc₁, hex₁, hgfit, hg1, hg2, hg7, hg8, hgaddr, hgrel, hgtgt⟩ :=
    P2Pro.prologue_exec x ρ hn hpow hif 0 T (by omega)
  -- phaseA: 86 → 148 (sorted first-half sums, bd-disjunction)
  obtain ⟨c₂, f₁, bd, hc₂, hex₂, hf110, hf111, hf118, hbd, harr, hf11, hf12,
    hf17, hf18, hf19, hf1fit, hf1pres⟩ :=
    P2.phaseA_exec_p2 ρ hn hw g 0 (T - c₁) hgfit hg1 hg2 hg7 hg8 hgaddr
      hgrel hin (by omega)
  have hrel₁ : ∀ i, 1 ≤ i → i ≤ n → f₁ (2 * n + 23 + i) = instA x (i - 1) := by
    intro i hi1 hin'
    have hnA : ¬ AReg n (2 * n + 23 + i) := by
      intro hA
      rcases hA with hA|hA <;> omega
    rw [hf1pres _ hnA]
    exact hgrel i hi1 hin'
  have htgt₁ : f₁ (2 * n + 23 + (n + 1)) = x.t := by
    have hnA : ¬ AReg n (2 * n + 23 + (n + 1)) := by
      intro hA
      rcases hA with hA|hA <;> omega
    rw [hf1pres _ hnA]
    exact hgtgt
  -- canon: 148 → 161 (S₁ canonical at ARR1, bd-disjunction killed)
  obtain ⟨c₃, f₂, hc₃, hex₃, hf222, hf211, hf29, hf27, hf28, hf21, hf22,
    hf2arr, hf2rel, hf2ft, hf2fit⟩ :=
    canon_exec ρ hn f₁ bd 0 (T - c₁ - c₂) hf1fit hf11 hf12 hf17 hf18 hf19
      hf111 hf118 hbd harr hrel₁ htgt₁ hwide (by omega)
  -- phaseA2: 161 → 224 (sorted second-half sums at bd2)
  obtain ⟨c₄, f₃, bd2, hc₄, hex₄, hf311, hf318, hbd2, hf3arr, hf322, hf35,
    hf34, hf39, hf31, hf32, hf37, hf38, hf3S1, hf3rel, hf3ft, hf3fit⟩ :=
    P2M.Merge2.phaseA2_exec ρ hn hw f₂ 0 (T - c₁ - c₂ - c₃) hf2fit hf21 hf22 hf27 hf28
      hf29 hf211 hf222 hf2arr hf2rel hf2ft hin hpow (by omega)
  -- scanB: 224 → verdict
  obtain ⟨c₅, v, hc₅, hex₅, hv⟩ :=
    scanB_exec ρ hn hw f₃ 0 (T - c₁ - c₂ - c₃ - c₄) bd2 hf3fit hf31 hf32
      hf37 hf38 hf311 hf318 hbd2 hf3arr hf322 hf35 hf3S1 hf3ft hwide (by omega)
  refine ⟨v, ?_, hv⟩
  show exec prog2 ρ T 0 0 (loadWords (wordLength n x.bits) x.input) = some v
  rw [← memOf_inF x (wordLength n x.bits)]
  exact hex₁.trans (hex₂.trans (hex₃.trans (hex₄.trans hex₅)))

/-- prog2 halts on every `n ≥ 4` input within `total2 n` steps. -/
theorem bign2_halts (n : Nat) (x : Instance n) (hn : 4 ≤ n)
    (ρ : Nat → BitVec (wordLength n x.bits)) :
    (run prog2 x ρ (total2 n)).isSome := by
  obtain ⟨v, hv, _⟩ := bign2_run x hn ρ (total2 n) (Nat.le_refl _)
  rw [hv]
  simp

open scoped Classical in
/-- The verdict form L4's `correct_of_det` consumes. -/
theorem bign2_verdict {n : Nat} (x : Instance n) (hn : 4 ≤ n)
    (ρ : Nat → BitVec (wordLength n x.bits)) (T : Nat) (hT : total2 n ≤ T) :
    run prog2 x ρ T = some (decide (isSum (instA x) n x.t)) := by
  obtain ⟨v, hv, hvyes⟩ := bign2_run x hn ρ T hT
  have hdec : v = decide (isSum (instA x) n x.t) := by
    have hiff : v = true ↔ isSum (instA x) n x.t := by
      rw [hvyes, instance_yes_iff]
    cases v with
    | true => exact (decide_eq_true (hiff.mp rfl)).symm
    | false =>
      have hnp : ¬ isSum (instA x) n x.t := by
        intro hp
        exact absurd (hiff.mpr hp) (by decide)
      exact (decide_eq_false hnp).symm
  rw [hv, hdec]

end SubsetSum.MITM
