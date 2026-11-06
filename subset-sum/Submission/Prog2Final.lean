import Submission.Prog2Compose
import Submission.Prog2Small
set_option autoImplicit true

/-!
# prog2 correctness, all n ≥ 2 (R2125607749 Lanes 2+3 → L4 handoff)

THE package L4 consumes for `Race_bound' : SolvedInTime (1/2)`:

* `T2` — the horizon: small-n uses the filed budgets (`stepBound n +
  constOverhead` covers 34/48), big-n uses `256·2^(n/2) + 300·(n+2)`
  (≥ `total2 n` by `total2_le`, ≥ 3.3× the measured worst case).
* `prog2_verdict_all` — `run prog2 x ρ (T2 n) = some (decide (isSum …))`.
* `prog2_halts_all` — the `Correct` horizon obligation.
* `prog2_correct` — `Correct prog2 x` via `correct_of_det` + the
  decide-proven `prog2_no_rand`.

L4's remaining step is one `refine`:
`SolvedInTime (1/2) := ⟨prog2, prog2_correct, fun c => ⟨T2, bigO_T2, …⟩⟩`
with `bigO_T2 : BigO T2 (1/2)` — pure arithmetic: `(1/2 : Rat)` has
`den = 2`, `num.toNat = 1`, so the obligation is `T2 n ^ 2 ≤ K · 2^n`
for `n ≥ 2`; the if-false branch is the lit rider's K-lemma
(`K = C²+2CD+2D²` with `C = 256`, `D = 900` since `300(n+2) ≤ 900n`;
support: `2·(n/2) ≤ n` ⇒ `2^(2·(n/2)) ≤ 2^n` carried EXPLICITLY —
omega treats powers as atoms; `n ≤ 2^(n−n/2)`; `n² ≤ 2·2^n`), and the
if-true branch (`n ∈ {2,3}`) is absorbed by the same K (`decide` the two
constants).  Halting at `T2 n` is `prog2_halts_all`.
-/

namespace SubsetSum.MITM

open BigOSpeedrun.SubsetSum SubsetSum.MITM.Spec

/-- The prog2 horizon: filed small-n budgets below 4, the α=1/2 shape above. -/
def T2 (n : Nat) : Nat :=
  if n ≤ 3 then Runtime.stepBound n + Runtime.constOverhead
  else 256 * 2 ^ (n / 2) + 300 * (n + 2)

theorem T2_small (n : Nat) (h : n ≤ 3) :
    T2 n = Runtime.stepBound n + Runtime.constOverhead := if_pos h

theorem T2_big (n : Nat) (h : 4 ≤ n) :
    T2 n = 256 * 2 ^ (n / 2) + 300 * (n + 2) := if_neg (by omega)

open scoped Classical in
/-- THE verdict theorem: prog2 halts within `T2 n` returning exactly the
membership decision — every n ≥ 2, every tape. -/
theorem prog2_verdict_all : ∀ (n : Nat) (x : Instance n), 2 ≤ n →
    ∀ ρ, run prog2 x ρ (T2 n) = some (decide (isSum (instA x) n x.t)) := by
  intro n x hn ρ
  rcases Nat.lt_or_ge n 4 with hsmall | hbig
  · have h23 : n = 2 ∨ n = 3 := by omega
    rw [T2_small n (by omega)]
    obtain ⟨v, hvrun, hyes, hno⟩ := P2Small.smalln_verdict n x h23
    have hdec : v = decide (isSum (instA x) n x.t) := by
      cases v with
      | true =>
        exact (decide_eq_true (by
          by_cases hy : x.yes
          · exact (instance_yes_iff x).mp hy
          · exact absurd (hno hy) (by decide))).symm
      | false =>
        exact (decide_eq_false (by
          intro hyes'
          exact absurd (hyes ((instance_yes_iff x).mpr hyes')) (by decide))).symm
    rw [hvrun ρ, hdec]
  · rw [T2_big n hbig]
    exact bign2_verdict x hbig ρ _ (total2_le n hbig)

/-- prog2 halts on every input within the horizon. -/
theorem prog2_halts_all : ∀ (n : Nat) (x : Instance n), 2 ≤ n →
    ∀ ρ, (run prog2 x ρ (T2 n)).isSome := by
  intro n x hn ρ
  rw [prog2_verdict_all n x hn ρ]
  simp

open scoped Classical in
/-- prog2 is CORRECT on every instance with n ≥ 2 — the first half of
`SolvedInTime (1/2)`. -/
theorem prog2_correct : ∀ (n : Nat) (x : Instance n), 2 ≤ n → Correct prog2 x := by
  intro n x hn
  refine correct_of_det (T2 n) ?_ (decide (isSum (instA x) n x.t)) ?_ ?_ ?_
  · exact prog2_halts_all n x hn
  · exact prog2_verdict_all n x hn
  · intro hyes
    exact decide_eq_true ((instance_yes_iff x).mp hyes)
  · intro hno
    exact decide_eq_false (fun h => hno ((instance_yes_iff x).mpr h))

end SubsetSum.MITM
