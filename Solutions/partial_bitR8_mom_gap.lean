import Definitions.Def_IntMul_Kappa_RG_Defs
import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_K_Defs2
import Definitions.Def_IntMul_KappaJainData
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

/-!
# Partial for `IntMul.Kappa.R8.bitNetR8_mom` — the cheap-witness template and the exact gap

`BitNetMomStmtG 104719230 529 Jain.bitR8` needs a QHNet `C : QHNet (ZMod 2) 104719230 T 529`
with `RunsOK`, `EdgesOK`/`FormalOK` at all large prime powers, and child-width moments
dominated by `Jain.bitR8` on `(0, 1]`.

This file builds the **uniform cheap witness**: one edge per role, `E₁ = E₂ = 1`, runs
`(0, 0, 528), (528, 528, 1)` — the two block transpositions whose product is the full chunk
swap.  For this network obligations 2 and 3 discharge at **every** modulus `N` (so `q₀ = 0`),
and the histogram moment is computed exactly.  Together: a complete proof of

`BitNetMomStmtG 104719230 529 [(528, 104719230), (1, 104719230)]`  (`cheap_witness_stmt`).

The residual gap to the real target is then purely arithmetic, recorded in `bitR8_rank` /
`cheap_rank` / `rank_gap`: the cheap witness has rank sum `529 * 104719230 = 55396472670`,
while `Jain.bitR8` has rank sum `55395128481` — short by `1344189 = 1771 * 759`, the exact
saving shared by the frozen R6/R7plain/R8 histograms.  Since the τ = 1 moment of a histogram
is `rank / 529`, **no** network whose role frames are assembled from its own edges alone can
pass τ = 1 (each role frame needs the full swap permutation as its permutation content,
hence ≥ 529 transpositions on its own line; gate-sharing via Jain's copy-correction is
*necessary*).  The count arm is fine (`209438460 ≤ 749446467`); the crossing is only in
rank.  So the real witness must be the `net0P`-family certificate — whose `RunsOK` is
already proved (`BitOppbankGoodPrimes.runsOK0`) and whose `EdgesOK`/`FormalOK` at good
primes is the open `GoodPrimesStmt`/`Net0OkStmt`.
-/

namespace IntMul.Kappa.R8.Gap

open IntMul.Kappa
open IntMul.Kappa.R6.Bit
open Matrix

/-! ## 0. Small list helpers -/

theorem filterMap_eq_map_of {α β : Type*} {l : List α} {f : α → Option β} {g : α → β}
    (h : ∀ x ∈ l, f x = some (g x)) : l.filterMap f = l.map g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx : f x = some (g x) := h x (by simp)
    have ih' : xs.filterMap f = xs.map g := ih fun y hy => h y (by simp [hy])
    simp only [List.filterMap_cons, List.map_cons, hx, ih']

theorem flatMap_eq_map_of {α β : Type*} {l : List α} {f : α → List β} {g : α → β}
    (h : ∀ x ∈ l, f x = [g x]) : l.flatMap f = l.map g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx : f x = [g x] := h x (by simp)
    have ih' : xs.flatMap f = xs.map g := ih fun y hy => h y (by simp [hy])
    simp only [List.flatMap_cons, List.map_cons, hx, ih']
    rfl

/-! ## 1. The uniform edge at width 529 -/

/-- The two-run edge at width 529: `E₁ = E₂ = 1`, runs covering every pivot `H_k ↔ D_k`. -/
def uEdge : Edge 529 := ⟨1, [(0, 0, 528), (528, 528, 1)], 1⟩

/-- The `(H_k, D_k)` pair as a total function of `k`. -/
def pairF (k : ℕ) : Fin 1058 × Fin 1058 :=
  if h : k < 529 then (Fin.castAdd 529 ⟨k, h⟩, Fin.natAdd 529 ⟨k, h⟩)
  else (⟨k % 1058, by omega⟩, ⟨k % 1058, by omega⟩)

theorem pairF_eq {k : ℕ} (hk : k < 529) :
    pairF k = (Fin.castAdd 529 ⟨k, hk⟩, Fin.natAdd 529 ⟨k, hk⟩) :=
  dif_pos hk

theorem runPiv_long :
    runPiv 529 (0, 0, 528) = ((List.range 528).map pairF) := by
  unfold runPiv
  show (List.range 528).filterMap
      (fun k => if h : 0 + k < 529 ∧ 0 + k < 529 then
        some (Fin.castAdd 529 ⟨0 + k, h.1⟩, Fin.natAdd 529 ⟨0 + k, h.2⟩) else none)
    = (List.range 528).map pairF
  refine filterMap_eq_map_of fun k hk => ?_
  have hk' : k < 528 := List.mem_range.1 hk
  have hk529 : k < 529 := by omega
  have hc : 0 + k < 529 ∧ 0 + k < 529 := by omega
  have hL : (if h : 0 + k < 529 ∧ 0 + k < 529 then
      some (Fin.castAdd 529 ⟨0 + k, h.1⟩, Fin.natAdd 529 ⟨0 + k, h.2⟩) else none)
      = some (Fin.castAdd 529 ⟨0 + k, hc.1⟩, Fin.natAdd 529 ⟨0 + k, hc.2⟩) :=
    dif_pos hc
  have hR : pairF k = (Fin.castAdd 529 ⟨k, hk529⟩, Fin.natAdd 529 ⟨k, hk529⟩) := pairF_eq hk529
  have hcast : (Fin.castAdd 529 ⟨0 + k, hc.1⟩ : Fin 1058) = Fin.castAdd 529 ⟨k, hk529⟩ := by
    apply Fin.eq_of_val_eq; simp
  have hnat : (Fin.natAdd 529 ⟨0 + k, hc.2⟩ : Fin 1058) = Fin.natAdd 529 ⟨k, hk529⟩ := by
    apply Fin.eq_of_val_eq; simp
  rw [hL, hcast, hnat, hR]

theorem runPiv_short :
    runPiv 529 (528, 528, 1) = [pairF 528] := by
  unfold runPiv
  show (List.range 1).filterMap
      (fun k => if h : 528 + k < 529 ∧ 528 + k < 529 then
        some (Fin.castAdd 529 ⟨528 + k, h.1⟩, Fin.natAdd 529 ⟨528 + k, h.2⟩) else none)
    = [pairF 528]
  rw [filterMap_eq_map_of (g := fun _ => pairF 528) (fun k hk => by
    have hk' : k = 0 := by simpa using hk
    subst hk'
    have hc : 528 + 0 < 529 ∧ 528 + 0 < 529 := by omega
    have hL : (if h : 528 + 0 < 529 ∧ 528 + 0 < 529 then
        some (Fin.castAdd 529 ⟨528 + 0, h.1⟩, Fin.natAdd 529 ⟨528 + 0, h.2⟩) else none)
        = some (Fin.castAdd 529 ⟨528 + 0, hc.1⟩, Fin.natAdd 529 ⟨528 + 0, hc.2⟩) :=
      dif_pos hc
    have hk529 : 528 < 529 := by omega
    have hR : pairF 528 = (Fin.castAdd 529 ⟨528, hk529⟩, Fin.natAdd 529 ⟨528, hk529⟩) :=
      pairF_eq hk529
    have hcast : (Fin.castAdd 529 ⟨528 + 0, hc.1⟩ : Fin 1058) = Fin.castAdd 529 ⟨528, hk529⟩ := by
      apply Fin.eq_of_val_eq; simp
    have hnat : (Fin.natAdd 529 ⟨528 + 0, hc.2⟩ : Fin 1058) = Fin.natAdd 529 ⟨528, hk529⟩ := by
      apply Fin.eq_of_val_eq; simp
    rw [hL, hcast, hnat, hR])]
  rfl

/-- The flattened pivot list of `uEdge`: all pairs `(H_k, D_k)`, `k < 529`. -/
theorem uEdge_runPiv :
    (uEdge.runs.flatMap (runPiv 529)) = ((List.range 529).map pairF) := by
  simp only [uEdge, List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
    runPiv_long, runPiv_short]
  rw [show List.range 529 = List.range 528 ++ [528] from List.range_succ,
    List.map_append, List.map_singleton]

/-! ## 2. The run permutation is the block swap -/

/-- `H_k` as a total function (junk outside `k < 529`). -/
def upH (k : ℕ) : Fin 1058 :=
  if h : k < 529 then Fin.natAdd 529 ⟨k, h⟩ else ⟨k % 1058, by omega⟩

/-- `D_k` as a total function (junk outside `k < 529`). -/
def dnH (k : ℕ) : Fin 1058 :=
  if h : k < 529 then Fin.castAdd 529 ⟨k, h⟩ else ⟨k % 1058, by omega⟩

theorem upH_eq {k : ℕ} (hk : k < 529) : upH k = Fin.natAdd 529 ⟨k, hk⟩ := dif_pos hk
theorem dnH_eq {k : ℕ} (hk : k < 529) : dnH k = Fin.castAdd 529 ⟨k, hk⟩ := dif_pos hk

/-- The block swap on `Fin 1058`: `H_k ↔ D_k` for every `k < 529`. -/
def swapE (x : Fin 1058) : Fin 1058 :=
  if x.val < 529 then upH x.val else dnH (x.val - 529)

theorem swapE_apply (y : Fin 1058) :
    swapE y = if y.val < 529 then upH y.val else dnH (y.val - 529) := rfl

theorem swapE_swapE (x : Fin 1058) : swapE (swapE x) = x := by
  simp only [swapE_apply]
  by_cases h : x.val < 529
  · rw [if_pos h]
    rw [upH_eq (by omega : x.val < 529)]
    simp only [Fin.val_natAdd]
    rw [if_neg (by omega : ¬(529 + x.val < 529))]
    rw [dnH_eq (by omega : 529 + x.val - 529 < 529)]
    apply Fin.eq_of_val_eq
    simp only [Fin.val_castAdd]
    omega
  · rw [if_neg h]
    rw [dnH_eq (by omega : x.val - 529 < 529)]
    simp only [Fin.val_castAdd]
    rw [if_pos (by omega : x.val - 529 < 529)]
    rw [upH_eq (by omega : x.val - 529 < 529)]
    apply Fin.eq_of_val_eq
    simp only [Fin.val_natAdd]
    omega

/-- The swap performed by `pairF k`, as a total function of `k`. -/
def swapF (k : ℕ) : Equiv.Perm (Fin 1058) :=
  if h : k < 529 then Equiv.swap (Fin.castAdd 529 ⟨k, h⟩) (Fin.natAdd 529 ⟨k, h⟩) else 1

theorem swapF_coe {k : ℕ} (hk : k < 529) :
    swapF k = Equiv.swap (Fin.castAdd 529 ⟨k, hk⟩) (Fin.natAdd 529 ⟨k, hk⟩) :=
  dif_pos hk

theorem uEdge_swaps :
    ((uEdge.runs.flatMap (runPiv 529)).map fun p => Equiv.swap p.1 p.2)
      = ((List.range 529).map swapF) := by
  rw [uEdge_runPiv, List.map_map]
  refine List.map_congr_left fun k hk => ?_
  have hk' : k < 529 := List.mem_range.1 hk
  show Equiv.swap (pairF k).1 (pairF k).2 = swapF k
  rw [pairF_eq hk', swapF_coe hk']

/-- Pointwise form of the product of the first `j` swaps. -/
theorem prod_swapF_apply : ∀ (j : ℕ) (_ : j ≤ 529) (x : Fin 1058),
    ((List.range j).map swapF).prod x
      = if x.val < j then upH x.val
        else if 529 ≤ x.val ∧ x.val - 529 < j then dnH (x.val - 529)
        else x := by
  intro j
  induction j with
  | zero =>
    intro _ x
    simp
  | succ j ih =>
    intro hj x
    have hjm : j ≤ 529 := by omega
    have hstep : ((List.range (j + 1)).map swapF).prod x
        = ((List.range j).map swapF).prod (swapF j x) := by
      rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
        List.prod_singleton]
      simp only [HMul.hMul, Mul.mul]
      rfl
    rw [hstep]
    have hj529 : j < 529 := by omega
    have hswap : swapF j x
        = if x = Fin.castAdd 529 ⟨j, hj529⟩ then Fin.natAdd 529 ⟨j, hj529⟩
          else if x = Fin.natAdd 529 ⟨j, hj529⟩ then Fin.castAdd 529 ⟨j, hj529⟩
          else x := by
      rw [swapF_coe hj529]
      split_ifs with h1 h2
      · rw [h1]
        exact Equiv.swap_apply_left _ _
      · rw [h2]
        exact Equiv.swap_apply_right _ _
      · exact Equiv.swap_apply_of_ne_of_ne h1 h2
    by_cases hA : x = Fin.castAdd 529 ⟨j, hj529⟩
    · -- x = H_j → swap to D_j
      have hx : x.val = j := by rw [hA, Fin.val_castAdd]
      rw [hswap, if_pos hA]
      rw [ih hjm (Fin.natAdd 529 ⟨j, hj529⟩)]
      simp only [Fin.val_natAdd]
      rw [if_neg (by omega : ¬(529 + j < j)),
        if_neg (by omega : ¬(529 ≤ 529 + j ∧ 529 + j - 529 < j))]
      rw [if_pos (by omega : x.val < j + 1)]
      rw [upH_eq (by omega : x.val < 529)]
      exact Fin.eq_of_val_eq (by simp [hx])
    · by_cases hB : x = Fin.natAdd 529 ⟨j, hj529⟩
      · -- x = D_j → swap to H_j
        have hx : x.val = 529 + j := by rw [hB, Fin.val_natAdd]
        rw [hswap, if_neg hA, if_pos hB]
        rw [ih hjm (Fin.castAdd 529 ⟨j, hj529⟩)]
        simp only [Fin.val_castAdd]
        rw [if_neg (by omega : ¬(j < j)), if_neg (by omega : ¬(529 ≤ j ∧ j - 529 < j))]
        rw [if_neg (by omega : ¬(x.val < j + 1))]
        rw [if_pos (by omega : 529 ≤ x.val ∧ x.val - 529 < j + 1)]
        rw [dnH_eq (by omega : x.val - 529 < 529)]
        exact Fin.eq_of_val_eq (by simp [hx])
      · -- x untouched by the `j`-th swap
        have hne1 : x.val ≠ j := by
          intro h
          exact hA (Fin.eq_of_val_eq (by rw [h, Fin.val_castAdd]))
        have hne2 : x.val ≠ 529 + j := by
          intro h
          exact hB (Fin.eq_of_val_eq (by rw [h, Fin.val_natAdd]))
        rw [hswap, if_neg hA, if_neg hB]
        rw [ih hjm x]
        by_cases h3 : x.val < j
        · rw [if_pos h3, if_pos (by omega : x.val < j + 1)]
        · by_cases h4 : 529 ≤ x.val ∧ x.val - 529 < j
          · rw [if_neg h3, if_pos h4]
            rw [if_neg (by omega : ¬(x.val < j + 1))]
            rw [if_pos (by omega : 529 ≤ x.val ∧ x.val - 529 < j + 1)]
          · rw [if_neg h3, if_neg (by omega : ¬(529 ≤ x.val ∧ x.val - 529 < j))]
            rw [if_neg (by omega : ¬(x.val < j + 1))]
            rw [if_neg (by omega : ¬(529 ≤ x.val ∧ x.val - 529 < j + 1))]

/-! ## 3. The run permutation equals the block swap -/

def swapEquiv : Equiv.Perm (Fin 1058) where
  toFun := swapE
  invFun := swapE
  left_inv := swapE_swapE
  right_inv := swapE_swapE

theorem uEdge_prod_apply (x : Fin 1058) :
    ((uEdge.runs.flatMap (runPiv 529)).map fun p => Equiv.swap p.1 p.2).prod x = swapEquiv x := by
  rw [uEdge_swaps, prod_swapF_apply 529 le_rfl x]
  show (if x.val < 529 then upH x.val
      else if 529 ≤ x.val ∧ x.val - 529 < 529 then dnH (x.val - 529) else x) = swapEquiv x
  rw [show swapEquiv x = swapE x from rfl, swapE_apply]
  split_ifs
  · rfl
  · rfl
  · next h1 h2 =>
    exact absurd (by have := x.isLt; omega : 529 ≤ x.val ∧ x.val - 529 < 529) h2

theorem uEdge_prod :
    ((uEdge.runs.flatMap (runPiv 529)).map fun p => Equiv.swap p.1 p.2).prod = swapEquiv :=
  Equiv.ext fun x => uEdge_prod_apply x

/-! ## 4. `redQ` on 0 and 1; `redM N 1 = 1` -/

theorem redQ_zero (N : ℕ) : AModelFac.redQ N 0 = 0 := by
  have hd : Nat.Coprime ((0 : ℚ).den) N := by
    rw [Rat.den_zero]; exact Nat.coprime_one_left N
  unfold AModelFac.redQ AModelFac.toGood
  rw [dif_pos hd]
  show AModelFac.redHom N (⟨(0 : ℚ), hd⟩ : AModelFac.goodSub N) = 0
  exact (AModelFac.redHom N).map_zero

theorem redQ_one (N : ℕ) : AModelFac.redQ N 1 = 1 := by
  have hd : Nat.Coprime ((1 : ℚ).den) N := by
    rw [Rat.den_one]; exact Nat.coprime_one_left N
  unfold AModelFac.redQ AModelFac.toGood
  rw [dif_pos hd]
  show AModelFac.redHom N (⟨(1 : ℚ), hd⟩ : AModelFac.goodSub N) = 1
  exact (AModelFac.redHom N).map_one

theorem redM_one (N : ℕ) : redM N (1 : QMat2 529) = 1 := by
  ext i j
  simp only [redM, Matrix.map_apply]
  by_cases h : i = j
  · subst h; simp [Matrix.one_apply_eq, redQ_one]
  · simp [Matrix.one_apply_ne h, redQ_zero]

/-! ## 5. `edgeMat N uEdge = swapMat` -/

theorem swapMat_apply {Q m : ℕ} (i j : Fin (m + m)) :
    (AModel.swapMat (Q := Q) i j : ZMod Q)
      = if (i.val < m ∧ j.val = i.val + m) ∨ (j.val < m ∧ i.val = j.val + m) then 1 else 0 := by
  simp only [AModel.swapMat, AModel.blk, reindex_apply, Matrix.submatrix_apply]
  have hi : i = finSumFinEquiv (finSumFinEquiv.symm i) := (Equiv.apply_symm_apply _ _).symm
  have hj : j = finSumFinEquiv (finSumFinEquiv.symm j) := (Equiv.apply_symm_apply _ _).symm
  generalize hs : finSumFinEquiv.symm i = si
  generalize ht : finSumFinEquiv.symm j = sj
  cases si with
  | inl a =>
    cases sj with
    | inl b =>
      rw [Matrix.fromBlocks_apply₁₁]
      have hiv : i.val = a.val := by rw [hi, hs, finSumFinEquiv_apply_left, Fin.val_castAdd]
      have hjv : j.val = b.val := by rw [hj, ht, finSumFinEquiv_apply_left, Fin.val_castAdd]
      rw [if_neg (by omega : ¬((i.val < m ∧ j.val = i.val + m) ∨ (j.val < m ∧ i.val = j.val + m)))]
      rfl
    | inr b =>
      rw [Matrix.fromBlocks_apply₁₂]
      have hiv : i.val = a.val := by rw [hi, hs, finSumFinEquiv_apply_left, Fin.val_castAdd]
      have hjv : j.val = m + b.val := by rw [hj, ht, finSumFinEquiv_apply_right, Fin.val_natAdd]
      have hcond : ((i.val < m ∧ j.val = i.val + m) ∨ (j.val < m ∧ i.val = j.val + m)) ↔ a = b := by
        rw [hiv, hjv]
        constructor
        · intro h
          rcases h with ⟨_, h2⟩ | ⟨h1, _⟩
          · exact Fin.eq_of_val_eq (by omega)
          · exact absurd h1 (by omega)
        · intro h
          have hval : (a : ℕ) = b := congrArg Fin.val h
          exact Or.inl ⟨by omega, by omega⟩
      simp only [Matrix.one_apply]
      by_cases hab : a = b
      · rw [if_pos hab, if_pos (hcond.2 hab)]
      · rw [if_neg hab, if_neg (fun hh => hab (hcond.1 hh))]
  | inr a =>
    cases sj with
    | inl b =>
      rw [Matrix.fromBlocks_apply₂₁]
      have hiv : i.val = m + a.val := by rw [hi, hs, finSumFinEquiv_apply_right, Fin.val_natAdd]
      have hjv : j.val = b.val := by rw [hj, ht, finSumFinEquiv_apply_left, Fin.val_castAdd]
      have hcond : ((i.val < m ∧ j.val = i.val + m) ∨ (j.val < m ∧ i.val = j.val + m)) ↔ a = b := by
        rw [hiv, hjv]
        constructor
        · intro h
          rcases h with ⟨h1, _⟩ | ⟨_, h2⟩
          · exact absurd h1 (by omega)
          · exact Fin.eq_of_val_eq (by omega)
        · intro h
          have hval : (a : ℕ) = b := congrArg Fin.val h
          exact Or.inr ⟨by omega, by omega⟩
      simp only [Matrix.one_apply]
      by_cases hab : a = b
      · rw [if_pos hab, if_pos (hcond.2 hab)]
      · rw [if_neg hab, if_neg (fun hh => hab (hcond.1 hh))]
    | inr b =>
      rw [Matrix.fromBlocks_apply₂₂]
      have hiv : i.val = m + a.val := by rw [hi, hs, finSumFinEquiv_apply_right, Fin.val_natAdd]
      have hjv : j.val = m + b.val := by rw [hj, ht, finSumFinEquiv_apply_right, Fin.val_natAdd]
      rw [if_neg (by omega : ¬((i.val < m ∧ j.val = i.val + m) ∨ (j.val < m ∧ i.val = j.val + m)))]
      rfl

theorem permMatrix_swapE (N : ℕ) :
    swapEquiv.permMatrix (ZMod N) = AModel.swapMat (m := 529) (Q := N) := by
  ext i j
  have key : (j = swapEquiv i) ↔ (i.val < 529 ∧ j.val = i.val + 529) ∨ (j.val < 529 ∧ i.val = j.val + 529) := by
    rw [show swapEquiv i = swapE i from rfl, swapE_apply]
    by_cases h : i.val < 529
    · rw [if_pos h, upH_eq (by omega : i.val < 529)]
      constructor
      · intro hj
        exact Or.inl ⟨h, by simp [Fin.ext_iff] at hj; omega⟩
      · intro hj
        rcases hj with ⟨_, hj⟩ | ⟨hj, _⟩
        · exact Fin.eq_of_val_eq (by simp; omega)
        · omega
    · rw [if_neg h, dnH_eq (by omega : i.val - 529 < 529)]
      constructor
      · intro hj
        exact Or.inr ⟨by simp [Fin.ext_iff] at hj; omega, by simp [Fin.ext_iff] at hj; omega⟩
      · intro hj
        rcases hj with ⟨hj, _⟩ | ⟨_, hj⟩
        · omega
        · exact Fin.eq_of_val_eq (by simp; omega)
  rw [swapMat_apply]
  by_cases h1 : swapEquiv i = j
  · have hmem : j ∈ Equiv.toPEquiv swapEquiv i := by
      rw [Equiv.toPEquiv_apply]
      simpa using h1
    have hL : swapEquiv.permMatrix (ZMod N) i j = 1 := by
      simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
      rw [if_pos hmem]
    rw [hL, if_pos (key.1 h1.symm)]
  · have hmem : ¬(j ∈ Equiv.toPEquiv swapEquiv i) := by
      intro hm
      rw [Equiv.toPEquiv_apply] at hm
      exact h1 (by simpa using hm)
    have hL : swapEquiv.permMatrix (ZMod N) i j = 0 := by
      simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
      rw [if_neg hmem]
    rw [hL, if_neg (fun hh => h1 (key.2 hh).symm)]

theorem edgeMat_uEdge (N : ℕ) : edgeMat N uEdge = AModel.swapMat := by
  have h1 : uEdge.E₁ = 1 := rfl
  have h2 : uEdge.E₂ = 1 := rfl
  unfold edgeMat
  rw [h1, h2, redM_one, uEdge_prod, one_mul, mul_one]
  exact permMatrix_swapE N

/-! ## 6. Formal values: `lmulF` on a single term -/

theorem lmulF_single {R : Type*} [CommRing R] {U : Type*} {m N : ℕ}
    (L : FMat m N) (F : FMat m N) (u : U) (c : R) :
    lmulF (R := R) L (Finsupp.single (F, u) c) = Finsupp.single (L * F, u) c := by
  simp [lmulF, Finsupp.lmapDomain]

/-! ## 7. The uniform program and its formal evaluation -/

variable {W T : ℕ}

/-- Instruction `k` of the uniform program: the edge on role `k`. -/
def uInstr (k : ℕ) : Instr (Fin W ⊕ Fin T) (ZMod 2) 529 :=
  if h : k < W then .edge (.inl ⟨k, h⟩) uEdge else .gate 1 ∅

/-- The formal state after `k` steps of the uniform program. -/
noncomputable def uTgt (N k : ℕ) : (Fin W ⊕ Fin T) → FV (ZMod 2) (Fin W) 529 N :=
  Sum.elim (fun w => if w.val < k then Finsupp.single (AModel.swapMat, w) 1
    else Finsupp.single (1, w) 1) (fun _ => 0)

theorem fold_uInstr (N : ℕ) : ∀ (k : ℕ) (_ : k ≤ W),
    ((List.range k).map uInstr).foldl (fStep N) (QHNet.fInit N) = uTgt (W := W) (T := T) N k := by
  intro k
  induction k with
  | zero =>
    intro _
    ext z
    cases z with
    | inl w => simp [uTgt, QHNet.fInit]
    | inr t => simp [uTgt, QHNet.fInit]
  | succ k ih =>
    intro hk
    have hk' : k ≤ W := by omega
    have hkW : k < W := by omega
    rw [List.range_succ, List.map_append, List.foldl_append]
    show fStep N (((List.range k).map uInstr).foldl (fStep N) (QHNet.fInit N)) (uInstr k) = _
    rw [ih hk']
    have hInstr : uInstr (W := W) (T := T) k = .edge (.inl ⟨k, hkW⟩) uEdge := by
      simp [uInstr, dif_pos hkW]
    rw [hInstr]
    funext z
    cases z with
    | inl w =>
      simp only [fStep]
      by_cases hw : w = (⟨k, hkW⟩ : Fin W)
      · subst hw
        rw [Function.update_self]
        have hst : uTgt (W := W) (T := T) N k (.inl ⟨k, hkW⟩)
            = Finsupp.single ((1 : FMat 529 N), (⟨k, hkW⟩ : Fin W)) 1 := by
          simp [uTgt]
        rw [hst, lmulF_single, edgeMat_uEdge N, Matrix.mul_one]
        simp [uTgt]
      · rw [Function.update_apply, if_neg (fun h => hw (Sum.inl.inj h))]
        have hne : w.val ≠ k := fun h => hw (Fin.eq_of_val_eq (by simp [h]))
        show (if w.val < k then Finsupp.single (AModel.swapMat, w) 1
            else Finsupp.single ((1 : FMat 529 N), w) 1)
          = if w.val < k + 1 then Finsupp.single (AModel.swapMat, w) 1
            else Finsupp.single ((1 : FMat 529 N), w) 1
        by_cases hlt : w.val < k
        · rw [if_pos hlt, if_pos (Nat.lt_of_lt_of_le hlt (Nat.le_succ k))]
        · rw [if_neg hlt]
          rw [if_neg (fun h => hne (Nat.le_antisymm (Nat.le_of_lt_succ h) (Nat.not_lt.mp hlt)))]
    | inr t =>
      simp only [fStep]
      rw [Function.update_apply, if_neg (by simp)]
      simp [uTgt]

/-! ## 8. The network and its three obligations -/

/-- The uniform network at `W` roles, width 529, no temporaries. -/
def uNet : QHNet (ZMod 2) W 0 529 := ⟨(List.range W).map uInstr, id⟩

theorem uNet_edges : (uNet (W := W)).edges = List.replicate W uEdge := by
  have hkey : ∀ x ∈ (List.range W).map (uInstr (W := W) (T := 0)), Instr.edgeOf x = some uEdge := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    have hk' : k < W := List.mem_range.1 hk
    simp [uInstr, dif_pos hk', Instr.edgeOf]
  simp only [QHNet.edges, progEdges, uNet]
  rw [filterMap_eq_map_of hkey, List.map_map]
  show List.map (fun _ : ℕ => uEdge) (List.range W) = List.replicate W uEdge
  simp [List.map_const']

theorem uEdge_RunsOK : ∀ ρ ∈ uEdge.runs, RunOK 529 ρ := by
  intro ρ h
  have hmem : ρ ∈ [(0, 0, 528), (528, 528, 1)] := by simpa [uEdge] using h
  rcases List.mem_cons.1 hmem with h | h
  · subst h
    show 0 < 528 ∧ 528 < 529 ∧ 0 + 528 ≤ 529 ∧ 0 + 528 ≤ 529
    exact ⟨by omega, by omega, by omega, by omega⟩
  · rcases List.mem_cons.1 h with h | h
    · subst h
      show 0 < 1 ∧ 1 < 529 ∧ 528 + 1 ≤ 529 ∧ 528 + 1 ≤ 529
      exact ⟨by omega, by omega, by omega, by omega⟩
    · exact absurd h List.not_mem_nil

theorem uNet_RunsOK : (uNet (W := W)).RunsOK := by
  intro e he ρ hρ
  rw [uNet_edges] at he
  rcases List.mem_replicate.1 he with ⟨_, he⟩
  rw [he] at hρ
  exact uEdge_RunsOK ρ hρ

theorem uEdge_EdgeOK (N : ℕ) : EdgeOK N uEdge := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij
    show (1 : QMat2 529) i j = 0
    exact Matrix.one_apply_ne (ne_of_lt hij)
  · intro i j hij
    show (1 : QMat2 529) i j = 0
    exact Matrix.one_apply_ne (ne_of_lt hij)
  · intro i
    show IsUnit (AModelFac.redQ N ((1 : QMat2 529) i i))
    rw [Matrix.one_apply_eq, redQ_one]
    exact isUnit_one
  · intro i
    show IsUnit (AModelFac.redQ N ((1 : QMat2 529) i i))
    rw [Matrix.one_apply_eq, redQ_one]
    exact isUnit_one

theorem uNet_EdgesOK (N : ℕ) : (uNet (W := W)).EdgesOK N := by
  intro e he
  rw [uNet_edges] at he
  rcases List.mem_replicate.1 he with ⟨_, he⟩
  rw [he]
  exact uEdge_EdgeOK N

theorem uNet_FormalOK (N : ℕ) : (uNet (W := W)).FormalOK N := by
  intro w
  show ((List.range W).map uInstr).foldl (fStep N) (QHNet.fInit N) (.inl w)
    = Finsupp.single (AModel.swapMat, w) 1
  rw [fold_uInstr N W le_rfl]
  simp [uTgt]

/-! ## 9. The histogram moment -/

theorem histMoment_append (l₁ l₂ : List (ℕ × ℕ)) (τ : ℝ) :
    histMoment (l₁ ++ l₂) 529 τ = histMoment l₁ 529 τ + histMoment l₂ 529 τ := by
  simp [histMoment, List.map_append, List.sum_append]

theorem histMoment_pair (a b : ℕ) (τ : ℝ) :
    histMoment [(a, 1), (b, 1)] 529 τ = ((a : ℝ) / 529) ^ τ + ((b : ℝ) / 529) ^ τ := by
  simp only [histMoment, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  push_cast
  ring

theorem histMoment_replicate2 (k : ℕ) (a b : ℕ) (τ : ℝ) :
    histMoment (((List.replicate k [a, b]).flatten).map fun w => (w, 1)) 529 τ
      = k * (((a : ℝ) / 529) ^ τ + ((b : ℝ) / 529) ^ τ) := by
  induction k with
  | zero => simp [histMoment]
  | succ k ih =>
    have h : (List.replicate (k + 1) [a, b]).flatten
        = [a, b] ++ (List.replicate k [a, b]).flatten := by
      rw [List.replicate_succ, List.flatten_cons]
    rw [h, List.map_append, histMoment_append]
    simp only [List.map_cons, List.map_nil]
    rw [histMoment_pair, ih]
    push_cast
    ring

theorem uNet_hist : (uNet (W := W)).hist
    = ((List.replicate W [528, 1]).flatten).map fun w => (w, 1) := by
  have h1 : (uNet (W := W)).widths = (List.replicate W [528, 1]).flatten := by
    rw [QHNet.widths, uNet_edges]
    induction W with
    | zero => rfl
    | succ W ih =>
      have hr : uEdge.runs.map (fun ρ => ρ.2.2) = [528, 1] := by simp [uEdge]
      rw [List.replicate_succ, List.flatMap_cons, hr, List.replicate_succ, List.flatten_cons, ih]
  simp only [QHNet.hist, h1]

theorem histMoment_uNet (τ : ℝ) :
    histMoment (uNet (W := W)).hist 529 τ
      = W * (((((528 : ℕ) : ℝ)) / 529) ^ τ + ((((1 : ℕ) : ℝ)) / 529) ^ τ) := by
  rw [uNet_hist, histMoment_replicate2]

theorem histMoment_hb0 (τ : ℝ) :
    histMoment [(528, 104719230), (1, 104719230)] 529 τ
      = (((104719230 : ℕ) : ℝ)) * (((((528 : ℕ) : ℝ)) / 529) ^ τ + ((((1 : ℕ) : ℝ)) / 529) ^ τ) := by
  simp only [histMoment, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  push_cast
  ring

/-! ## 10. Packaging: the cheap witness -/

def hb0 : List (ℕ × ℕ) := [(528, 104719230), (1, 104719230)]

theorem cheap_witness_stmt : BitNetMomStmtG 104719230 529 hb0 := by
  refine ⟨0, uNet (W := 104719230), 0, uNet_RunsOK, ?_, ?_⟩
  · intro q _ _ f
    exact ⟨uNet_EdgesOK _, uNet_FormalOK _⟩
  · intro τ _ _
    simp only [hb0]
    rw [histMoment_uNet, histMoment_hb0]
    try exact le_rfl

/-! ## 11. The arithmetic gap (τ = 1 is rank / 529) -/

theorem bitR8_rank : histRankSum Jain.bitR8 = 55395128481 := by decide

theorem cheap_rank : histRankSum hb0 = 529 * 104719230 := by decide

theorem rank_gap : 529 * 104719230 > 55395128481 := by decide

theorem deficit_factor : 529 * 104719230 - 55395128481 = 1771 * 759 := by decide

theorem count_arm : (hb0.map (·.2)).sum ≤ (Jain.bitR8.map (·.2)).sum := by decide

end IntMul.Kappa.R8.Gap
