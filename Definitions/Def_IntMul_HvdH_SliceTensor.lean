import Mathlib

/-! Tensor products of maps acting slice by slice (Harvey–van der Hoeven §2.7, Lemma 2.11).
A `d`-dimensional array is a function `(Fin d → ℕ) → ℂ`; a one-dimensional map is any function
`(ℕ → ℂ) → (ℕ → ℂ)`. -/

namespace IntMul.HvdH

/-- Apply a one-dimensional map `A` to every `i`-slice of a `d`-dimensional array. -/
def sliceMap {d : ℕ} (i : Fin d) (A : (ℕ → ℂ) → (ℕ → ℂ)) (x : (Fin d → ℕ) → ℂ) :
    (Fin d → ℕ) → ℂ :=
  fun j => A (fun k => x (Function.update j i k)) (j i)

/-- Apply the maps `A i` slice by slice, for the axes listed in `l`, first axis first. -/
def sliceComp {d : ℕ} (A : Fin d → (ℕ → ℂ) → (ℕ → ℂ)) :
    List (Fin d) → ((Fin d → ℕ) → ℂ) → ((Fin d → ℕ) → ℂ)
  | [] => id
  | i :: l => sliceComp A l ∘ sliceMap i (A i)

/-- The tensor product `⊗ᵢ Aᵢ = B_d ⋯ B₁` with `Bᵢ` acting on `i`-slices. -/
def tensorMap {d : ℕ} (A : Fin d → (ℕ → ℂ) → (ℕ → ℂ)) :
    ((Fin d → ℕ) → ℂ) → ((Fin d → ℕ) → ℂ) :=
  sliceComp A (List.finRange d)

end IntMul.HvdH
