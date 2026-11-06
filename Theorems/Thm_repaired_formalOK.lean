import Theorems.Thm_bitNetR7plain_mom_repaired
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 200000

/-!
# Formal-correctness obstruction for the repaired one-run network

The selected role `auxRole = 2N` is fixed by the output merge and is touched by
exactly one instruction: the stage-one slot-zero `oneEdge (auxWidth 0)`.  Formal
correctness would therefore force that edge matrix to be `swapMat`.  But its
permutation fixes the top coordinate indexed by `auxWidth 0`, whereas the full
swap has a zero diagonal there.  This proves `not_RepairedFormalOKLarge`; no
large-prime bridge exists for this particular repaired witness.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.Repaired

open IntMul.Kappa
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank

/-- An instruction that cannot change one selected wire. -/
def Avoids (z : Wr) : NI → Prop
  | .gate _ S => z ∉ S
  | .edge w _ => w ≠ z

theorem fStep_avoids (M : ℕ) (z : Wr) (f : Wr → FV (ZMod 2) (Fin W) 529 M)
    (i : NI) (h : Avoids z i) : fStep M f i z = f z := by
  cases i with
  | gate g S =>
      simp only [Avoids] at h
      simp [fStep, gateVecM, h]
  | edge w e =>
      simp only [Avoids] at h
      simp [fStep, Function.update_apply, Ne.symm h]

theorem foldl_avoids (M : ℕ) (z : Wr) (f : Wr → FV (ZMod 2) (Fin W) 529 M)
    (p : List NI) (h : ∀ i ∈ p, Avoids z i) :
    (p.foldl (fStep M) f) z = f z := by
  induction p generalizing f with
  | nil => rfl
  | cons i p ih =>
      rw [List.foldl_cons, ih]
      · exact fStep_avoids M z f i (h i (by simp))
      · intro j hj
        exact h j (by simp [hj])

/-- The first stage-one aux role.  It is fixed by the output merge. -/
def auxRole : Fin W := ⟨2 * N, by norm_num [N, W]⟩
def auxWire : Wr := .inl auxRole

theorem auxRole_merge : NB.ρ auxRole = auxRole := by
  apply Fin.ext
  simp [NB.ρ, ρn, auxRole, N]

theorem two_N_lt_W : 2 * N < W := by norm_num [N, W]

theorem gw_eq_auxWire_iff {g : ℕ} (hg : g < W) : NB.gw g = auxWire ↔ g = 2 * N := by
  simp [NB.gw, auxWire, auxRole, hg, two_N_lt_W, Fin.ext_iff]

theorem gw_ne_auxWire_of_ge_W {g : ℕ} (hg : W ≤ g) : NB.gw g ≠ auxWire := by
  simp [NB.gw, not_lt_of_ge hg, auxWire]

theorem g1_eq_two_N_iff {b w : ℕ} (hb : b < v) :
    g1 b w = 2 * N ↔ b = 0 ∧ w = wEnt := by
  have hv : v = 1771 := rfl
  have hN : N = 3136441 := rfl
  have hW : W = 104719230 := rfl
  have hNR : NR = 27794 := rfl
  have hEnt : wEnt = 3542 := rfl
  have hAux : wAuxEnd = 31336 := rfl
  unfold g1
  split_ifs <;> simp only [hv, hN, hW, hNR, hEnt, hAux] at * <;> omega

theorem g2_ne_two_N {a w : ℕ} (ha : a < v) : g2 a w ≠ 2 * N := by
  have hv : v = 1771 := rfl
  have hN : N = 3136441 := rfl
  have hW : W = 104719230 := rfl
  have hNR : NR = 27794 := rfl
  have hEnt : wEnt = 3542 := rfl
  have hAux : wAuxEnd = 31336 := rfl
  have hNL : NL = 31359 := rfl
  unfold g2
  split_ifs <;> simp only [hv, hN, hW, hNR, hEnt, hAux, hNL] at * <;> omega

/-- Stage one touches the selected aux role only at block zero, slot zero. -/
theorem iota1_eq_auxWire_iff {b w : ℕ} (hb : b < v) :
    NB.ι1 b w = auxWire ↔ b = 0 ∧ w = wEnt := by
  by_cases hg : g1 b w < W
  · rw [show NB.ι1 b w = NB.gw (g1 b w) from rfl, gw_eq_auxWire_iff hg,
      g1_eq_two_N_iff hb]
  · have hne := gw_ne_auxWire_of_ge_W (g := g1 b w) (Nat.le_of_not_gt hg)
    constructor
    · intro h
      exact absurd h hne
    · intro h
      have he := (g1_eq_two_N_iff hb).2 h
      rw [he] at hg
      exact absurd two_N_lt_W hg

/-- Stage two never touches the first stage-one aux role. -/
theorem iota2_ne_auxWire {a w : ℕ} (ha : a < v) : NB.ι2 a w ≠ auxWire := by
  by_cases hg : g2 a w < W
  · intro h
    exact g2_ne_two_N ha ((gw_eq_auxWire_iff hg).1 h)
  · exact gw_ne_auxWire_of_ge_W (Nat.le_of_not_gt hg)

/-- The unique instruction touching `auxWire`, and the program around it. -/
noncomputable def auxInstr : NI := .edge (NB.ι1 0 wEnt) (ch0R.ex 0 0)
noncomputable def auxPre : List NI := sideProg (NB.ι1 0) (ch0R.e1 0) sideSchedule1
noncomputable def auxTail1 : List NI :=
  (List.range' (wEnt + 1) (NR - 1)).map fun w =>
    Instr.edge (NB.ι1 0 w) (ch0R.ex 0 (w - wEnt))
noncomputable def auxRest1 : List NI := (List.range' 1 (v - 1)).flatMap (blk1 ch0R)
noncomputable def auxRest2 : List NI := (List.range v).flatMap (blk2 ch0R)
noncomputable def auxPost : List NI := auxTail1 ++ (auxRest1 ++ auxRest2)

theorem range_v_split : List.range v = 0 :: List.range' 1 (v - 1) := by
  native_decide

theorem range_aux_split :
    List.range' wEnt NR = wEnt :: List.range' (wEnt + 1) (NR - 1) := by
  native_decide

theorem blk1_zero : blk1 ch0R 0 = auxPre ++ auxInstr :: auxTail1 := by
  simp [blk1, auxPre, auxInstr, auxTail1, range_aux_split, List.append_assoc]

theorem repaired_prog_split : repairedNet.prog = auxPre ++ auxInstr :: auxPost := by
  change prog ch0R = _
  unfold prog
  nth_rewrite 1 [range_v_split]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_assoc]
  rw [blk1_zero]
  simp [auxPost, auxRest1, auxRest2, List.append_assoc]

theorem avoids_edge1 {b w : ℕ} (hb : b < v) (h : ¬ (b = 0 ∧ w = wEnt))
    (e : Edge 529) : Avoids auxWire (.edge (NB.ι1 b w) e) := by
  change NB.ι1 b w ≠ auxWire
  intro heq
  exact h ((iota1_eq_auxWire_iff hb).1 heq)

theorem avoids_edge2 {a w : ℕ} (ha : a < v) (e : Edge 529) :
    Avoids auxWire (.edge (NB.ι2 a w) e) := by
  exact iota2_ne_auxWire ha

theorem avoids_xor2 {a : ℕ} (ha : a < v) (d s : ℕ) :
    Avoids auxWire (NB.xorG (NB.ι2 a d) (NB.ι2 a s)) := by
  change auxWire ∉ ({NB.ι2 a d, NB.ι2 a s} : Finset Wr)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨Ne.symm (iota2_ne_auxWire ha), Ne.symm (iota2_ne_auxWire ha)⟩

theorem avoids_auxPre : ∀ i ∈ auxPre, Avoids auxWire i := by
  intro i hi
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hi
  exact avoids_edge1 (by decide) (by norm_num [wEnt]) _

theorem avoids_auxTail1 : ∀ i ∈ auxTail1, Avoids auxWire i := by
  intro i hi
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hi
  obtain ⟨k, hk, hwk⟩ := List.mem_range'.1 hw
  apply avoids_edge1 (by decide)
  intro h
  have hwe := h.2
  omega

theorem avoids_blk1_of_ne_zero {b : ℕ} (hb : b < v) (hb0 : b ≠ 0) :
    ∀ i ∈ blk1 ch0R b, Avoids auxWire i := by
  intro i hi
  rcases List.mem_append.1 hi with hi | hi
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hi
    exact avoids_edge1 hb (fun h => hb0 h.1) _
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hi
    exact avoids_edge1 hb (fun h => hb0 h.1) _

theorem avoids_blk2 {a : ℕ} (ha : a < v) : ∀ i ∈ blk2 ch0R a, Avoids auxWire i := by
  intro i hi
  rcases List.mem_append.1 hi with hi | hi
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hi
    exact avoids_edge2 ha _
  rcases List.mem_append.1 hi with hi | hi
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hi
    exact avoids_edge2 ha _
  obtain ⟨s, hs, hi⟩ := List.mem_flatMap.1 hi
  rcases List.mem_cons.1 hi with rfl | hi
  · exact avoids_xor2 ha _ _
  rcases List.mem_cons.1 hi with rfl | hi
  · exact avoids_edge2 ha _
  rcases List.mem_cons.1 hi with rfl | hi
  · exact avoids_xor2 ha _ _
  · exact absurd hi List.not_mem_nil

theorem avoids_auxPost : ∀ i ∈ auxPost, Avoids auxWire i := by
  intro i hi
  rcases List.mem_append.1 hi with hi | hi
  · exact avoids_auxTail1 i hi
  rcases List.mem_append.1 hi with hi | hi
  · obtain ⟨b, hb, hi⟩ := List.mem_flatMap.1 hi
    obtain ⟨k, hk, hbk⟩ := List.mem_range'.1 hb
    have hv : 0 < v := by decide
    exact avoids_blk1_of_ne_zero (by omega) (by omega) i hi
  · obtain ⟨a, ha, hi⟩ := List.mem_flatMap.1 hi
    exact avoids_blk2 (List.mem_range.1 ha) i hi

theorem lmulF_single {R : Type*} [CommRing R] {U : Type*} {m M : ℕ}
    (L : FMat m M) (F : FMat m M) (u : U) (c : R) :
    lmulF (R := R) L (Finsupp.single (F, u) c) = Finsupp.single (L * F, u) c := by
  simp [lmulF, Finsupp.lmapDomain]

/-- Formal evaluation of the entire repaired program on the selected aux wire. -/
theorem repaired_fold_aux (M : ℕ) :
    (repairedNet.prog.foldl (fStep M) (QHNet.fInit M)) auxWire =
      lmulF (edgeMat M (oneEdge (auxWidth 0)))
        (Finsupp.single ((1 : FMat 529 M), auxRole) 1) := by
  rw [repaired_prog_split]
  change (List.foldl (fStep M) (QHNet.fInit M) (auxPre ++ auxInstr :: auxPost)) auxWire = _
  rw [List.foldl_append, List.foldl_cons]
  rw [foldl_avoids M auxWire _ auxPost avoids_auxPost]
  have hw : NB.ι1 0 wEnt = auxWire := (iota1_eq_auxWire_iff (by decide)).2 ⟨rfl, rfl⟩
  simp only [auxInstr, fStep, hw, Function.update_self]
  rw [foldl_avoids M auxWire _ auxPre avoids_auxPre]
  simp [QHNet.fInit, auxWire, ch0R]

/-- If the repaired net were formally correct, its unique aux edge would have to
be the full chunk interchange. -/
theorem edgeMat_aux_of_formalOK {M : ℕ} (h : repairedNet.FormalOK M) :
    edgeMat M (oneEdge (auxWidth 0)) = AModel.swapMat := by
  have hh := h auxRole
  change (repairedNet.prog.foldl (fStep M) (QHNet.fInit M)) (.inl (NB.ρ auxRole)) = _ at hh
  rw [auxRole_merge] at hh
  change (repairedNet.prog.foldl (fStep M) (QHNet.fInit M)) auxWire = _ at hh
  rw [repaired_fold_aux, lmulF_single, Matrix.mul_one] at hh
  have hp := (Finsupp.single_left_injective (b := (1 : ZMod 2)) (by decide)) hh
  exact congrArg Prod.fst hp

theorem redQ_zero_repaired (M : ℕ) : AModelFac.redQ M 0 = 0 := by
  have hd : Nat.Coprime ((0 : ℚ).den) M := by
    rw [Rat.den_zero]
    exact Nat.coprime_one_left M
  unfold AModelFac.redQ AModelFac.toGood
  rw [dif_pos hd]
  show AModelFac.redHom M (⟨(0 : ℚ), hd⟩ : AModelFac.goodSub M) = 0
  exact (AModelFac.redHom M).map_zero

theorem redM_one_repaired (M : ℕ) : redM M (1 : QMat2 529) = 1 := by
  ext i j
  simp only [redM, Matrix.map_apply]
  by_cases h : i = j
  · subst h
    simp [Matrix.one_apply_eq, redQ_one]
  · simp [Matrix.one_apply_ne h, redQ_zero_repaired]

theorem oneEdge_edgeMat (M : ℕ) (w : ℕ) :
    edgeMat M (oneEdge w) =
      (((oneEdge w).runs.flatMap (runPiv 529)).map fun p => Equiv.swap p.1 p.2).prod.permMatrix
        (ZMod M) := by
  unfold edgeMat
  rw [show (oneEdge w).E₁ = 1 from rfl, show (oneEdge w).E₂ = 1 from rfl,
    redM_one_repaired, one_mul, mul_one]

theorem swapMat_castAdd_diag (M w : ℕ) (hw : w < 529) :
    (AModel.swapMat (Q := M) (Fin.castAdd 529 ⟨w, hw⟩) (Fin.castAdd 529 ⟨w, hw⟩)) = 0 := by
  simp only [AModel.swapMat, AModel.blk, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₁₁]
  rfl

theorem permMatrix_diag_of_fix {M : ℕ} {σ : Equiv.Perm (Fin (529 + 529))}
    {x : Fin (529 + 529)} (h : σ x = x) : σ.permMatrix (ZMod M) x x = 1 := by
  have hmem : x ∈ Equiv.toPEquiv σ x := by
    rw [Equiv.toPEquiv_apply]
    simpa using h
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, if_pos hmem]

theorem prod_swaps_fix {m : ℕ} (x : Fin (m + m))
    (ps : List (Fin (m + m) × Fin (m + m)))
    (h : ∀ p ∈ ps, Equiv.swap p.1 p.2 x = x) :
    (ps.map fun p => Equiv.swap p.1 p.2).prod x = x := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      simp only [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply]
      rw [ih (fun q hq => h q (by simp [hq]))]
      exact h p (by simp)

theorem oneRun_pivots_fix {w : ℕ} (hw : w < 529) :
    ∀ p ∈ runPiv 529 (oneRun w),
      Equiv.swap p.1 p.2 (Fin.castAdd 529 ⟨w, hw⟩) = Fin.castAdd 529 ⟨w, hw⟩ := by
  intro p hp
  obtain ⟨k, hk, hpk⟩ := List.mem_filterMap.1 hp
  simp only [oneRun] at hk
  by_cases hb : (oneRun w).1 + k < 529 ∧ (oneRun w).2.1 + k < 529
  · rw [dif_pos hb] at hpk
    cases hpk
    apply Equiv.swap_apply_of_ne_of_ne
    · intro heq
      have hv : w = 0 + k := congrArg Fin.val heq
      have hk' := List.mem_range.1 hk
      omega
    · intro heq
      have hv : w = 529 + (529 - w + k) := congrArg Fin.val heq
      omega
  · rw [dif_neg hb] at hpk
    contradiction

theorem oneEdge_prod_fix {w : ℕ} (hw : w < 529) :
    (((oneEdge w).runs.flatMap (runPiv 529)).map fun p => Equiv.swap p.1 p.2).prod
      (Fin.castAdd 529 ⟨w, hw⟩) = Fin.castAdd 529 ⟨w, hw⟩ := by
  apply prod_swaps_fix
  intro p hp
  apply oneRun_pivots_fix hw p
  simpa [oneEdge] using hp

/-- A one-run edge of width below `529` is never the full chunk interchange. -/
theorem oneEdge_ne_swapMat (M w : ℕ) (hM : 1 < M) (hw : w < 529) :
    edgeMat M (oneEdge w) ≠ AModel.swapMat := by
  letI : Fact (1 < M) := ⟨hM⟩
  intro h
  rw [oneEdge_edgeMat] at h
  have he := congrArg (fun A : FMat 529 M =>
    A (Fin.castAdd 529 ⟨w, hw⟩) (Fin.castAdd 529 ⟨w, hw⟩)) h
  rw [permMatrix_diag_of_fix (oneEdge_prod_fix hw), swapMat_castAdd_diag] at he
  exact one_ne_zero he

/-- The repaired net is not formally correct at any prime modulus. -/
theorem repairedNet_not_FormalOK_prime {q : ℕ} (hq : q.Prime) :
    ¬ repairedNet.FormalOK q := by
  intro h
  have he := edgeMat_aux_of_formalOK h
  have hw := auxWidth_valid 0 (by norm_num [NR])
  exact oneEdge_ne_swapMat q (auxWidth 0) hq.one_lt hw.2 he

/-- The proposed large-prime certificate is false for the repaired witness. -/
theorem not_RepairedFormalOKLarge : ¬ RepairedFormalOKLarge := by
  intro h
  obtain ⟨q₀, hq₀⟩ := h
  obtain ⟨q, hqge, hq⟩ := Nat.exists_infinite_primes (q₀ + 1)
  have hqgt : q₀ < q := by omega
  have hf := hq₀ q hq hqgt 1
  exact repairedNet_not_FormalOK_prime hq (by simpa using hf)

end IntMul.Kappa.R8.Bit.Oppbank.Repaired
