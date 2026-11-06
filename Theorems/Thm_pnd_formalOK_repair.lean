import Theorems.Thm_pnd_obstruction
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

/-!
# The idempotence-only `idxD` repair loses program moves

The pair `(1773,1774)` is not an artificial member of the published `idxD`:
stage two executes it, and stage one executes its reverse.  Both published
`Dm`s are non-idempotent, so filtering `idxD` by idempotence removes moves that
the program actually requires.

The final definitions and certificates test the semantic raw-zero repair:
make dense node zero the empty, dimension-zero projector while leaving every
other code unchanged.  Then both directions become the rank-one idempotent
`Pc 1774`, as required.  In source data this means `densSupG[0] = 0` and
`DIMT[0] = 0`; merely hiding zero from `argRel` does not alter the defective
`Dm` and therefore cannot repair the required move.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.Net0Pnd

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG
open Matrix Module

/-- The old-code/new-code moves executed by one stage's chunks. -/
def chunkMoves (cs : List LChunk) : List (ℕ × ℕ) :=
  cs.flatMap fun ch => ch.2.1.map fun mv => (mv.2, ch.1)

/-- The moves used by the actual two-stage program, before the aux/correction edges. -/
def programMoves : List (ℕ × ℕ) := chunkMoves NB.cs1 ++ chunkMoves NB.cs2

theorem foldl_genStepF_acc : ∀ (W : List LInstr) (f : ℕ → ℕ) (acc : List LChunk),
    W.foldl genStepF (f, acc) =
      ((W.foldl genStepF (f, [])).1, (W.foldl genStepF (f, [])).2 ++ acc)
  | [], f, acc => rfl
  | i :: W, f, acc => by
    simp only [List.foldl_cons, genStepF]
    rw [foldl_genStepF_acc W _ ((i.1, _, i.2.2) :: acc),
      foldl_genStepF_acc W _ [(i.1, _, i.2.2)]]
    simp

theorem genF_append (f : ℕ → ℕ) (W W' : List LInstr) :
    genF f (W ++ W') =
      ((genF (genF f W).1 W').1,
        (genF f W).2 ++ (genF (genF f W).1 W').2) := by
  simp only [genF, List.foldl_append]
  rw [foldl_genStepF_acc W' _ (W.foldl genStepF (f, [])).2]
  simp

theorem chunkMoves_genF_append (f : ℕ → ℕ) (W W' : List LInstr) :
    chunkMoves (genF f (W ++ W')).2 =
      chunkMoves (genF f W).2 ++ chunkMoves (genF (genF f W).1 W').2 := by
  simp only [chunkMoves, genF_append, List.flatMap_append]

theorem mem_chunkMoves_genF_of_prefix {f : ℕ → ℕ} {W W' : List LInstr} {p : ℕ × ℕ}
    (h : p ∈ chunkMoves (genF f W).2) : p ∈ chunkMoves (genF f (W ++ W')).2 := by
  rw [chunkMoves_genF_append]
  exact List.mem_append.2 (Or.inl h)

theorem stage2_requires_1773_1774 : (1773, 1774) ∈ chunkMoves NB.cs2 := by
  rw [show NB.cs2 = (genF (Gen.codeOf GenData.SG2_0) NB.W2F).2 by unfold NB.cs2; rfl]
  rw [← List.take_append_drop 98005 NB.W2F]
  apply mem_chunkMoves_genF_of_prefix
  native_decide

theorem stage1_requires_1774_1773 : (1774, 1773) ∈ chunkMoves NB.cs1 := by
  rw [show NB.cs1 = (genF (Gen.codeOf Gen.SG1_0) NB.W1F).2 by unfold NB.cs1; rfl]
  rw [← List.take_append_drop 113894 NB.W1F]
  apply mem_chunkMoves_genF_of_prefix
  native_decide

theorem program_requires_1773_1774 : (1773, 1774) ∈ programMoves := by
  exact List.mem_append.2 (Or.inr stage2_requires_1773_1774)

theorem program_requires_1774_1773 : (1774, 1773) ∈ programMoves := by
  exact List.mem_append.2 (Or.inl stage1_requires_1774_1773)

/-- The published move at the defective pair is not idempotent. -/
theorem Dm_1773_1774_not_idem :
    Dm 1773 1774 * Dm 1773 1774 ≠ Dm 1773 1774 := by
  intro hid
  rw [Dm_1773_1774] at hid
  have ht := pnd_rank_idem hid
  rw [Matrix.trace_sub, ← pnd_rank_idem Pc1774_idem, ← pnd_rank_idem Pc1773_idem,
    Pc1773_rank, Pc1774_rank] at ht
  norm_num at ht
  have hr : (Pc 1774 - Pc 1773).rank = 0 := by exact_mod_cast ht
  exact Pc1774_ne_Pc1773 (eq_of_sub_rank_zero hr)

theorem Dm_1774_1773 : Dm 1774 1773 = Pc 1773 - Pc 1774 := by
  have hd : dimCF 1774 = dimCF 1773 := by decide +kernel
  rw [Dm, if_pos (Nat.le_of_eq hd)]

/-- The reverse move executed by stage one is not idempotent either. -/
theorem Dm_1774_1773_not_idem :
    Dm 1774 1773 * Dm 1774 1773 ≠ Dm 1774 1773 := by
  intro hid
  rw [Dm_1774_1773] at hid
  have ht := pnd_rank_idem hid
  rw [Matrix.trace_sub, ← pnd_rank_idem Pc1773_idem, ← pnd_rank_idem Pc1774_idem,
    Pc1773_rank, Pc1774_rank] at ht
  norm_num at ht
  have hr : (Pc 1773 - Pc 1774).rank = 0 := by exact_mod_cast ht
  exact Pc1774_ne_Pc1773 (eq_of_sub_rank_zero hr).symm

open Classical in
/-- The proposed repair: retain only genuinely idempotent published moves. -/
noncomputable def idxDIdem : Finset (ℕ × ℕ) :=
  Pnd.idxD.filter fun p => Dm p.1 p.2 * Dm p.1 p.2 = Dm p.1 p.2

theorem mem_idxDIdem (p : ℕ × ℕ) :
    p ∈ idxDIdem ↔ p ∈ Pnd.idxD ∧ Dm p.1 p.2 * Dm p.1 p.2 = Dm p.1 p.2 := by
  classical
  rw [idxDIdem, Finset.mem_filter]

theorem forward_not_mem_idxDIdem : (1773, 1774) ∉ idxDIdem := by
  rw [mem_idxDIdem]
  exact fun h => Dm_1773_1774_not_idem h.2

theorem reverse_not_mem_idxDIdem : (1774, 1773) ∉ idxDIdem := by
  rw [mem_idxDIdem]
  exact fun h => Dm_1774_1773_not_idem h.2

/-- Hence the idempotence filter is not a coverage-preserving repair of the program. -/
theorem idem_filter_loses_required_moves :
    (1773, 1774) ∈ programMoves ∧ (1773, 1774) ∉ idxDIdem ∧
      (1774, 1773) ∈ programMoves ∧ (1774, 1773) ∉ idxDIdem :=
  ⟨program_requires_1773_1774, forward_not_mem_idxDIdem,
    program_requires_1774_1773, reverse_not_mem_idxDIdem⟩

/-- The raw-zero projector correction used below: dense node zero is the empty
projector, and its recorded dimension is zero. Every other code is unchanged. -/
noncomputable def PcRawZero (c : ℕ) : M23 := if c = 1773 then 0 else Pc c

def dimCFRawZero (c : ℕ) : ℕ := if c = 1773 then 0 else dimCF c

noncomputable def DmRawZero (o c : ℕ) : M23 :=
  if dimCFRawZero o ≤ dimCFRawZero c then PcRawZero c - PcRawZero o
  else PcRawZero o - PcRawZero c

def rkCRawZero (a b : ℕ) : ℕ :=
  let a1 := dimCFRawZero a
  let b1 := dimCFRawZero b
  if a1 < b1 then b1 - a1 else a1 - b1

theorem DmRawZero_1773_1774 : DmRawZero 1773 1774 = Pc 1774 := by
  rw [DmRawZero, if_pos (show dimCFRawZero 1773 ≤ dimCFRawZero 1774 by decide +kernel)]
  simp [PcRawZero]

theorem DmRawZero_1774_1773 : DmRawZero 1774 1773 = Pc 1774 := by
  rw [DmRawZero, if_neg (show ¬dimCFRawZero 1774 ≤ dimCFRawZero 1773 by decide +kernel)]
  simp [PcRawZero]

theorem DmRawZero_1773_1774_idem :
    DmRawZero 1773 1774 * DmRawZero 1773 1774 = DmRawZero 1773 1774 := by
  rw [DmRawZero_1773_1774]
  exact Pc1774_idem

theorem DmRawZero_1774_1773_idem :
    DmRawZero 1774 1773 * DmRawZero 1774 1773 = DmRawZero 1774 1773 := by
  rw [DmRawZero_1774_1773]
  exact Pc1774_idem

theorem rkCRawZero_1773_1774 : rkCRawZero 1773 1774 = 1 := by decide +kernel
theorem rkCRawZero_1774_1773 : rkCRawZero 1774 1773 = 1 := by decide +kernel

theorem DmRawZero_1773_1774_rank :
    (DmRawZero 1773 1774).rank = rkCRawZero 1773 1774 := by
  rw [DmRawZero_1773_1774, Pc1774_rank, rkCRawZero_1773_1774]

theorem DmRawZero_1774_1773_rank :
    (DmRawZero 1774 1773).rank = rkCRawZero 1774 1773 := by
  rw [DmRawZero_1774_1773, Pc1774_rank, rkCRawZero_1774_1773]

end IntMul.Kappa.R8.Bit.Oppbank.Net0Pnd
