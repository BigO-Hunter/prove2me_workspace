import Theorems.Thm_oneRunNB_masks_cert

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000

/-!
# Unconditional whole-program scalar semantics for the genuine R8 network

All four certificate inputs of `prog_sc_of_gates` are discharged: the chunk
gate bounds by the word-builder analysis (`cs1_gates_ok`/`cs2_gates_ok`), the
stage word effects by influence-mask reflection (`hS1`/`hS2`).  No structural
decomposition of the word is used.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.OneRunNB

open IntMul.Kappa IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank IntMul.Kappa.R8.Bit.Oppbank.NB

/-- **The whole-program scalar semantics, unconditional.** -/
theorem prog_sc {ch : Repaired.Ch} {N : ℕ} {fd : FrameData} :
    (∀ a < v, ∀ s < v,
      (prog ch).foldl scalarStepM (φ0 fd ch N) (NB.ι2 a (wY s)) = φ0 fd ch N (NB.ι2 a (wX s)) ∧
      (prog ch).foldl scalarStepM (φ0 fd ch N) (NB.ι2 a (wX s)) = φ0 fd ch N (NB.ι2 a (wY s))) ∧
    (∀ b < v, ∀ q < NR,
      (prog ch).foldl scalarStepM (φ0 fd ch N) (NB.ι1 b (wS q)) = φ0 fd ch N (NB.ι1 b (wS q))) ∧
    ∀ a < v, ∀ q < NR,
      (prog ch).foldl scalarStepM (φ0 fd ch N) (NB.ι2 a (wS q)) = φ0 fd ch N (NB.ι2 a (wS q)) :=
  prog_sc_of_gates cs1_gates_ok cs2_gates_ok (fun _ hb => hS1 hb) (fun _ ha => hS2 ha)

end IntMul.Kappa.R8.Bit.Oppbank.OneRunNB
