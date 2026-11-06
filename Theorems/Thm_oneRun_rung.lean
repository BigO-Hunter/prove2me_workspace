import Theorems.Thm_oneRun_transport
import Theorems.Thm_bitNetR7plain_mom_rebalanced
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-!
# Final assembly for a formally correct opposite-bank one-run network

`RunShapes` supplies the exact bitR8 moment.  The remaining gate package is
exactly run validity through `EdgeQ`, large-prime edge admissibility, and
large-prime formal correctness.  No histogram or frame premise about the old
identity-frame `repairedNet` occurs here.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.OneRun

open IntMul.Kappa IntMul.Kappa.R6.Bit IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Repaired

/-- The complete gate input needed after the one-run shape certificate. -/
structure GateOK (ch : Ch) (q₀ : ℕ) : Prop where
  edgeQ : ∀ e ∈ (net ch).edges, ∃ q, EdgeQ e q
  edgesOK : ∀ q, q.Prime → q₀ < q → ∀ f, (net ch).EdgesOK (q ^ f)
  formalOK : ∀ q, q.Prime → q₀ < q → ∀ f, (net ch).FormalOK (q ^ f)

/-- The three independent gate hypotheses plus the run shapes assemble the full
round-seven plain moment rung. -/
theorem bitNetR7plain_mom_of_oneRun
    {ch : Ch} {q₀ : ℕ} (hs : RunShapes ch)
    (hEdgeQ : ∀ e ∈ (net ch).edges, ∃ q, EdgeQ e q)
    (hEdgesOK : ∀ q, q.Prime → q₀ < q → ∀ f, (net ch).EdgesOK (q ^ f))
    (hFormalOK : ∀ q, q.Prime → q₀ < q → ∀ f, (net ch).FormalOK (q ^ f)) :
    BitNetMomStmtG 104719230 529 IntMul.Kappa.Jain.bitR7plain := by
  exact IntMul.Kappa.R8.bitNetR7plain_mom_of_formalOK (q₀ := q₀) (net ch)
    (net_RunsOK_of_edgeQ (ch := ch) hs hEdgeQ) hEdgesOK hFormalOK
    (net_mom_eq_of_shapes (ch := ch) hs)

/-- Gate + shape assembles the full round-seven plain moment rung. -/
theorem bitNetR7plain_mom_of_gate
    {ch : Ch} {q₀ : ℕ} (hs : RunShapes ch) (hg : GateOK ch q₀) :
    BitNetMomStmtG 104719230 529 IntMul.Kappa.Jain.bitR7plain := by
  exact bitNetR7plain_mom_of_oneRun hs hg.edgeQ hg.edgesOK hg.formalOK

end IntMul.Kappa.R8.Bit.Oppbank.OneRun
