import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLocSlots
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankProjB
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 2000

/-!
# Opp-bank Lab0 / Pl geometry certificates (NetFB)

Kernel-checked triple popcounts on densified `LocSlots.TPTS` (via ProjB `tri`),
then `yx` / `Pl_idem` / `hLab0` / `hPis0Pl` for later
`flagBasis Lab0 hLab0 Pis0Pl hPis0Pl`.

ND `Dm` / full `ProjB.Pis0` still need `Pnd(supG)` (honest NetD gap).
-/

open Matrix
open scoped BigOperators
open IntMul.Kappa.R8.Bit.Oppbank.ProjB

namespace IntMul.Kappa.R8.Bit.Oppbank.NetFB

def popc : ℕ → ℕ → ℕ
  | _, 0 => 0
  | x, n + 1 => popc x n + (x.shiftRight n).land 1

def allN (n : ℕ) (p : ℕ → Bool) : Bool := (List.range n).all p

/-- The points of a mask. -/
def F (m : ℕ) : Finset (Fin 23) := Finset.univ.filter fun p => m.testBit p = true

theorem land1 (x i : ℕ) :
    (x.shiftRight i).land 1 = if x.testBit i = true then 1 else 0 := by
  simp [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ i) with h | h <;> simp [h]

theorem popc_eq (x : ℕ) : ∀ n, popc x n = ∑ i ∈ Finset.range n, if x.testBit i then 1 else 0
  | 0 => rfl
  | n + 1 => by
    rw [Finset.sum_range_succ, ← popc_eq x n]
    show popc x n + (x.shiftRight n).land 1 = _
    rw [land1]

theorem popc_card (x : ℕ) : popc x 23 = (F x).card := by
  rw [popc_eq, F, Finset.card_filter,
    ← Fin.sum_univ_eq_sum_range (fun i => if x.testBit i then 1 else 0)]

theorem allN_spec {n : ℕ} {p : ℕ → Bool} (h : allN n p = true) : ∀ i < n, p i = true := by
  have : ∀ a ∈ List.range n, p a = true := by simpa [allN, List.all_eq_true] using h
  intro i hi
  exact this i (List.mem_range.2 hi)

theorem blt_dec (a b : ℕ) : Nat.blt a b = decide (a < b) := by
  rw [Bool.eq_iff_iff, Nat.blt_eq, decide_eq_true_iff]

theorem tri_chk :
    allN 1771 (fun i => Nat.blt (tri i) (2 ^ 23) && Nat.beq (popc (tri i) 23) 3) = true := by
  decide +kernel

theorem tri_spec {i : ℕ} (hi : i < 1771) : tri i < 2 ^ 23 ∧ (F (tri i)).card = 3 := by
  have this := allN_spec tri_chk i hi
  simp only [Bool.and_eq_true, Nat.beq_eq, blt_dec, decide_eq_true_eq] at this
  exact ⟨this.1, popc_card _ ▸ this.2⟩

theorem sum_tvQ {T : ℕ} (hT : T < 1771) : ∑ p : Fin 23, tvQ T p = 3 := by
  have h := (tri_spec hT).2
  have : ∑ p, tvQ T p = ((F (tri T)).card : ℚ) := by
    rw [F, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [tvQ]; split_ifs <;> simp_all
  rw [this, h]; norm_num

theorem dot_tvQ (i j : ℕ) : tvQ i ⬝ᵥ tvQ j = ((F (tri i) ∩ F (tri j)).card : ℚ) := by
  have : F (tri i) ∩ F (tri j) = Finset.univ.filter
      (fun p : Fin 23 => (tri i).testBit p = true ∧ (tri j).testBit p = true) := by
    ext p; simp [F]
  rw [this, Finset.card_filter, Nat.cast_sum, dotProduct]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [tvQ]; split_ifs <;> simp_all

noncomputable def bfF (u v : V23) : ℚ := u ⬝ᵥ v - (∑ p, u p) * (∑ p, v p) / 9

theorem bf_tvQ {i j : ℕ} (hi : i < 1771) (hj : j < 1771) :
    bfF (tvQ i) (tvQ j) = ((F (tri i) ∩ F (tri j)).card : ℚ) - 1 := by
  rw [bfF, dot_tvQ, sum_tvQ hi, sum_tvQ hj]; norm_num

theorem yv_dot (T : ℕ) (v : V23) : yv T ⬝ᵥ v = bfF (xv T) v / 2 := by
  have : ∀ p, (tvQ T p - (∑ q, tvQ T q) / 9) / 2 * v p =
      (tvQ T p * v p) / 2 - (∑ q, tvQ T q) / 18 * v p := fun p => by ring
  simp only [yv, xv, bfF, dotProduct, this, Finset.sum_sub_distrib, ← Finset.sum_div,
    ← Finset.mul_sum]
  ring

theorem xv_ne {T : ℕ} (hT : T < 1771) : bfF (xv T) (xv T) = 2 := by
  rw [xv, bf_tvQ hT hT, Finset.inter_self, (tri_spec hT).2]; norm_num

theorem yx {T : ℕ} (hT : T < 1771) : yv T ⬝ᵥ xv T = 1 := by
  rw [yv_dot, xv_ne hT]; norm_num

theorem Pl_idem {T : ℕ} (hT : T < 1771) : Pl T * Pl T = Pl T := by
  have hyx := yx hT
  ext i j
  change ∑ k : Fin 23, (xv T i * yv T k) * (xv T k * yv T j) = xv T i * yv T j
  have hsum :
      ∑ k : Fin 23, xv T i * yv T k * xv T k * yv T j =
        xv T i * yv T j * ∑ k : Fin 23, yv T k * xv T k := by
    have h1 :
        ∀ k, xv T i * yv T k * xv T k * yv T j =
          xv T i * yv T j * (yv T k * xv T k) := fun k => by ring
    simp only [h1, Finset.mul_sum]
  have : ∑ k : Fin 23, yv T k * xv T k = 1 := by
    simpa [dotProduct] using hyx
  calc
    ∑ k : Fin 23, (xv T i * yv T k) * (xv T k * yv T j)
        = ∑ k : Fin 23, xv T i * yv T k * xv T k * yv T j := by
          refine Finset.sum_congr rfl fun k _ => by ring
    _ = xv T i * yv T j * ∑ k : Fin 23, yv T k * xv T k := hsum
    _ = xv T i * yv T j * 1 := by rw [this]
    _ = xv T i * yv T j := by ring

theorem hLab0 : ∀ p ∈ Lab0, p.2 ⬝ᵥ p.1 = 1 := by
  intro p hp
  unfold Lab0 at hp
  obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hp
  exact yx (Finset.mem_range.1 hT)

noncomputable def Pis0Pl : Finset M23 := (Finset.range 1771).image Pl

theorem hPis0Pl : ∀ A ∈ Pis0Pl, A * A = A := by
  intro A hA
  obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hA
  exact Pl_idem (Finset.mem_range.1 hT)

end IntMul.Kappa.R8.Bit.Oppbank.NetFB
