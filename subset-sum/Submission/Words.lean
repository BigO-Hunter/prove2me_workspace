import Submission.Fit
set_option autoImplicit true

/-!
# The BitVec↔Nat vocabulary (R2125607414)

The program computes in `BitVec w`; the spec computes in `Nat`.  Every
value the program ever holds fits below `2^w` (Fit), so each word
operation implements the corresponding Nat operation.  This module is the
vocabulary every exec-level phase invariant speaks: ofNat roundtrips,
comparison/equality transfer, fitting addition, both subtraction modes
(no-wrap and the wrapped complement), input-cell fit, and the canonical
memory form.
-/

namespace SubsetSum.MITM

open BigOSpeedrun.SubsetSum SubsetSum.MITM.Spec

/-! ## ofNat roundtrips (values below 2^w) -/

theorem toNat_ofNat_lt {w v : Nat} (h : v < 2 ^ w) :
    (BitVec.ofNat w v).toNat = v := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem ofNat_lt_ofNat {w x y : Nat} (hx : x < 2 ^ w) (hy : y < 2 ^ w) :
    BitVec.ofNat w x < BitVec.ofNat w y ↔ x < y := by
  rw [BitVec.lt_def, toNat_ofNat_lt hx, toNat_ofNat_lt hy]

theorem ofNat_eq_ofNat {w x y : Nat} (hx : x < 2 ^ w) (hy : y < 2 ^ w) :
    BitVec.ofNat w x = BitVec.ofNat w y ↔ x = y := by
  rw [BitVec.toNat_eq, toNat_ofNat_lt hx, toNat_ofNat_lt hy]

theorem ofNat_le_ofNat_of_le {w x y : Nat} (hx : x < 2 ^ w) (hy : y < 2 ^ w)
    (h : x ≤ y) : BitVec.ofNat w x ≤ BitVec.ofNat w y := by
  by_cases hlt : x < y
  · exact Nat.le_of_lt ((ofNat_lt_ofNat hx hy).mpr hlt)
  · have hxy : x = y := by omega
    rw [hxy]
    show (BitVec.ofNat w y).toNat ≤ (BitVec.ofNat w y).toNat
    exact Nat.le_refl _

theorem ofNat_lt_ofNat_of_lt {w x y : Nat} (hx : x < 2 ^ w) (hy : y < 2 ^ w)
    (h : x < y) : BitVec.ofNat w x < BitVec.ofNat w y :=
  (ofNat_lt_ofNat hx hy).mpr h

/-! ## Fitting addition -/

theorem toNat_add {w x y : Nat} (h : x + y < 2 ^ w) :
    (BitVec.ofNat w x + BitVec.ofNat w y).toNat = x + y := by
  have hx : x < 2 ^ w := by omega
  have hy : y < 2 ^ w := by omega
  rw [BitVec.add_def, toNat_ofNat_lt hx, toNat_ofNat_lt hy, toNat_ofNat_lt h]

/-! ## Subtraction, both modes -/

/-- No-wrap subtraction (`s ≤ t`): the word holds the true difference. -/
theorem toNat_sub_nowrap {w s t : Nat} (hle : s ≤ t) (ht : t < 2 ^ w) :
    (BitVec.ofNat w t - BitVec.ofNat w s).toNat = t - s := by
  rw [BitVec.toNat_sub, toNat_ofNat_lt ht, toNat_ofNat_lt (by omega : s < 2 ^ w)]
  have hz : t - s < 2 ^ w := by omega
  have harg : 2 ^ w - s + t = 2 ^ w + (t - s) := by omega
  rw [harg, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt hz,
    Nat.mod_eq_of_lt hz]

/-- The wrapped complement (`t < s`): the word holds `2^w − (s − t)`,
which exceeds every half-sum (Fit) and so can never match spuriously. -/
theorem toNat_sub_wrap {w s t : Nat} (hlt : t < s) (hs : s < 2 ^ w) :
    (BitVec.ofNat w t - BitVec.ofNat w s).toNat = 2 ^ w - (s - t) := by
  rw [BitVec.toNat_sub, toNat_ofNat_lt (by omega : t < 2 ^ w), toNat_ofNat_lt hs,
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- THE unmatchability fact: a wrapped complement exceeds any fitting
value bounded by `total` with `2·total < 2^w`. -/
theorem wrapped_gt {w total s t f : Nat} (hfit : 2 * total < 2 ^ w)
    (hs : s ≤ total) (hf : f ≤ total) (hlt : t < s) :
    f < 2 ^ w - (s - t) := by omega

/-! ## The input cells fit -/

/-- Every input word (n, the aᵢ, t) is below `2^w`: the aᵢ and t by
`maxValue < 2^bits ≤ 2^w`, and n itself because `w ≥ 4(n+bits)+1 > n`. -/
theorem input_mem_lt_pow {n : Nat} (x : Instance n) (hn : 2 ≤ n) :
    ∀ v ∈ x.input, v < 2 ^ (wordLength n x.bits) := by
  have hge : 2 ^ x.bits ≤ 2 ^ (wordLength n x.bits) := by
    have hw : x.bits ≤ wordLength n x.bits := by
      have hlog := Nat.log2_le_self ((n + 2) ^ 4 - 1)
      rw [show wordLength n x.bits
          = 4 * (n + x.bits) + Nat.log2 ((n + 2) ^ 4 - 1) + 1 from rfl]
      omega
    exact Nat.pow_le_pow_right (by omega) hw
  intro v hv
  unfold Instance.input at hv
  rcases List.mem_cons.mp hv with hv | hv
  · -- v = n: n < 2^(wordLength n bits) — wordLength ≥ 4(n+bits)+1 > n
    rw [hv]
    have hw : n < 4 * (n + x.bits) + Nat.log2 ((n + 2) ^ 4 - 1) + 1 := by
      have := Nat.log2_le_self ((n + 2) ^ 4 - 1)
      omega
    calc n < 4 * (n + x.bits) + Nat.log2 ((n + 2) ^ 4 - 1) + 1 := hw
      _ ≤ 2 ^ (4 * (n + x.bits) + Nat.log2 ((n + 2) ^ 4 - 1) + 1) :=
          Nat.le_of_lt Nat.lt_two_pow_self
  · rcases List.mem_append.mp hv with hv | hv
    · rcases List.mem_ofFn.mp hv with ⟨i, hi⟩
      subst hi
      have hmax := maxValue_ge_a x i
      have hlt := maxValue_lt_pow x (by omega)
      omega
    · rw [List.mem_singleton.mp hv]
      have hmax := maxValue_ge_t x
      have hlt := maxValue_lt_pow x (by omega)
      omega

end SubsetSum.MITM
