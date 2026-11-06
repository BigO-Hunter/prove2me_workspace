import Theorems.Thm_oneRunNB_certs
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 200000

/-!
# Stage word gates for the genuine R8 program

The gate lists of the two stage words decompose into the R6 `G1`/`G2` block
structure with R8 components: producer sandwich `Ag … Ag⁻¹`, scatter `Sg`,
injections `Ig`, source copies `Cg`, temporaries `Tg ++ STg`.  Everything here
is generic plumbing over the hand-written builders; the deep producer
simulation is taken as a certificate in the next file.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.OneRunNB

open IntMul.Kappa IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank IntMul.Kappa.R8.Bit.Oppbank.NB
open IntMul.Kappa.R8.Bit.Oppbank.Gen IntMul.Kappa.R8.Bit.Oppbank.GenData
open IntMul.Kappa.R8.Bit.Oppbank.LocGrecDense

/-! ## Generic XOR-run lemmas -/

section XorRun

variable {M : Type*} [AddCommGroup M]

theorem xrL_nil (u : ℕ → M) : xrL [] u = u := rfl

theorem xrL_zero : ∀ (l : List (ℕ × ℕ)), xrL l (0 : ℕ → M) = 0
  | [] => rfl
  | p :: l => by
    rw [show xrL (p :: l) (0 : ℕ → M) = xrL l
        (Function.update (0 : ℕ → M) p.1 ((0 : ℕ → M) p.1 + (0 : ℕ → M) p.2)) from rfl]
    have hz : Function.update (0 : ℕ → M) p.1 ((0 : ℕ → M) p.1 + (0 : ℕ → M) p.2) = 0 := by
      funext w; by_cases hw : w = p.1 <;> simp [hw]
    rw [hz, xrL_zero l]

theorem xrL_zero_src : ∀ (l : List (ℕ × ℕ)) (u : ℕ → M), (∀ p ∈ l, u p.2 = 0) → xrL l u = u
  | [], _, _ => rfl
  | p :: l, u, h => by
    rw [show xrL (p :: l) u = xrL l
        (Function.update u p.1 (u p.1 + u p.2)) from rfl, h p (by simp), add_zero,
      Function.update_eq_self]
    exact xrL_zero_src l u (fun q hq => h q (by simp [hq]))

theorem xrL_notdst : ∀ (l : List (ℕ × ℕ)) (u : ℕ → M) (w : ℕ), (∀ p ∈ l, p.1 ≠ w) →
    xrL l u w = u w
  | [], _, _, _ => rfl
  | p :: l, u, w, h => xrL_untouched (p :: l) u h

theorem xrL_add : ∀ (l : List (ℕ × ℕ)) (u u' : ℕ → M), xrL l (u + u') = xrL l u + xrL l u'
  | [], _, _ => rfl
  | p :: l, u, u' => by
    rw [show xrL (p :: l) (u + u') = xrL l
        (Function.update (u + u') p.1 ((u + u') p.1 + (u + u') p.2)) from rfl,
      show xrL (p :: l) u = xrL l (Function.update u p.1 (u p.1 + u p.2)) from rfl,
      show xrL (p :: l) u' = xrL l (Function.update u' p.1 (u' p.1 + u' p.2)) from rfl,
      ← xrL_add l]
    congr 1
    funext w
    by_cases hw : w = p.1
    · subst hw; simp; abel
    · simp [Function.update_of_ne hw]

/-- Read/write separated gate lists add their sources. -/
theorem xrL_sep : ∀ (l : List (ℕ × ℕ)) (u : ℕ → M), (∀ p ∈ l, ∀ q ∈ l, p.1 ≠ q.2) → ∀ w,
    xrL l u w = u w + (l.map fun p => if p.1 = w then u p.2 else 0).sum
  | [], _, _, _ => by simp [xrL_nil]
  | p :: l, u, h, w => by
    rw [show xrL (p :: l) u = xrL l (Function.update u p.1 (u p.1 + u p.2)) from rfl,
      xrL_sep l _ (fun a ha b hb => h a (by simp [ha]) b (by simp [hb])) w]
    have hsrc : ∀ q ∈ l, Function.update u p.1 (u p.1 + u p.2) q.2 = u q.2 := fun q hq =>
      Function.update_of_ne (fun e => h p (by simp) q (by simp [hq]) e.symm) _ _
    rw [List.map_congr_left (fun q hq => by rw [hsrc q hq])]
    simp only [List.map_cons, List.sum_cons]
    by_cases hw : p.1 = w
    · subst hw; simp only [Function.update_self, if_true]; abel
    · rw [Function.update_of_ne (Ne.symm hw), if_neg hw, zero_add]

theorem xrL_app (l l' : List (ℕ × ℕ)) (u : ℕ → M) :
    xrL (l ++ l') u = xrL l' (xrL l u) := by
  simp [xrL, List.foldl_append]

/-- **The reversed run inverts** (characteristic two, no gate `x_d ← x_d + x_d`). -/
theorem xrL_rev (h2 : ∀ a : M, a + a = 0) : ∀ (l : List (ℕ × ℕ)), (∀ p ∈ l, p.1 ≠ p.2) →
    ∀ u : ℕ → M, xrL l.reverse (xrL l u) = u := by
  intro l
  induction l with
  | nil => intro _ u; rfl
  | cons p l ih =>
    intro h u
    have e1 : xrL (p :: l) u = xrL l (Function.update u p.1 (u p.1 + u p.2)) := rfl
    rw [e1, List.reverse_cons, xrL_app, ih (fun q hq => h q (by simp [hq]))]
    show Function.update (Function.update u p.1 (u p.1 + u p.2)) p.1
        (Function.update u p.1 (u p.1 + u p.2) p.1 +
          Function.update u p.1 (u p.1 + u p.2) p.2) = u
    have hne : p.2 ≠ p.1 := (h p (by simp)).symm
    rw [Function.update_of_ne hne, Function.update_self, Function.update_idem,
      add_assoc, h2, add_zero, Function.update_eq_self]

end XorRun

end IntMul.Kappa.R8.Bit.Oppbank.OneRunNB
