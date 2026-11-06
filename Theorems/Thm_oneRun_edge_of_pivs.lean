import Theorems.Thm_IntMul_Kappa_R6_Bit_NB_edge_of_pivs
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-!
# One-run edges from pivot certificates

`edge_of_pivs` assembles an edge whenever every run pair is a pivot.  For one
reversed run, that is exactly the leading-minor certificate checked by the C
gate.  The four family theorems below are the `hEdgeQ` discharge shape.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.OneRun

open IntMul.Kappa IntMul.Kappa.R6.Bit IntMul.Kappa.R6.Bit.NB

/-- Exact-run form of `edge_of_pivs`: no singleton tail remains when the run's
pivot count already equals the rank. -/
theorem edge_exact {m : ℕ} (hm : 1 < m) (q : Matrix (Fin m) (Fin m) ℚ) (hq : q * q = q)
    (rs : List (ℕ × ℕ × ℕ)) (hok : ∀ ρ ∈ rs, RunOK m ρ) (hnd : (runPairs rs).Nodup)
    (hp : ∀ x ∈ runPairs rs, IsPiv q x.1 x.2) (hlen : (runPairs rs).length = q.rank) :
    ∃ e : Edge m, EdgeQ e q ∧ e.runs = rs := by
  obtain ⟨e, ⟨rs', h1, h2, h3⟩, h4, h5, h6, h7, h8, h9⟩ :=
    IntMul.Kappa.R6.Bit.NB.edge_of_pivs_sol_aux hm q hq rs hok hnd hp
  have hr : rs' = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst hr
  exact ⟨e, ⟨h4, h5, h6, h7, h8, h9⟩, by simpa using h1⟩

lemma runPairs_single (a b r : ℕ) :
    runPairs [(a, b, r)] = (List.range r).map fun k => (a + k, b + k) := by
  simp [runPairs]

lemma nodup_single (a b r : ℕ) : (runPairs [(a, b, r)]).Nodup := by
  rw [runPairs_single]
  exact (List.nodup_range).map fun k k' he => by simpa using congrArg Prod.fst he

/-- A one reversed-bank run from its pivot certificate. -/
theorem edge_of_oneRun {m w : ℕ} (hm : 1 < m) (hw0 : 0 < w) (hwm : w < m)
    (q : Matrix (Fin m) (Fin m) ℚ) (hq : q * q = q) (hrank : q.rank = w)
    (hp : ∀ k < w, IsPiv q k (m - w + k)) :
    ∃ e : Edge m, EdgeQ e q ∧ e.runs = [(0, m - w, w)] := by
  apply edge_exact hm q hq _ ?_ (nodup_single 0 (m - w) w) ?_ ?_
  · intro ρ hρ
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hρ
    subst hρ
    change 0 < w ∧ w < m ∧ 0 + w ≤ m ∧ (m - w) + w ≤ m
    exact ⟨hw0, hwm, by omega, by omega⟩
  · intro x hx
    rw [runPairs_single] at hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    simpa using hp k (List.mem_range.1 hk)
  · rw [runPairs_single, List.length_map, List.length_range, hrank]

/-- Side-family `PEOne` from the rank-`r` pivot certificate. -/
theorem side_of_oneRun {r : ℕ} (hr0 : 0 < r) (hr : r < 529)
    (q : Matrix (Fin 529) (Fin 529) ℚ) (hq : q * q = q) (hrank : q.rank = r)
    (hp : ∀ k < r, IsPiv q k (529 - r + k)) :
    ∃ e, PEOne q (SideR r) e := by
  obtain ⟨e, he, hrs⟩ := edge_of_oneRun (by omega) hr0 hr q hq hrank hp
  exact ⟨e, he, hrs⟩

/-- Slot-aux `PEOne` from the merged corner's pivot certificate. -/
theorem aux_of_oneRun (s : ℕ)
    (q : Matrix (Fin 529) (Fin 529) ℚ) (hq : q * q = q)
    (hrank : q.rank = 529 - auxCorner s) (hw0 : 0 < 529 - auxCorner s)
    (hwm : 529 - auxCorner s < 529)
    (hp : ∀ k < 529 - auxCorner s, IsPiv q k (auxCorner s + k)) :
    ∃ e, PEOne q (AuxR s) e := by
  have hc : auxCorner s ≤ 23 := by simp [auxCorner]
  have heq : 529 - (529 - auxCorner s) = auxCorner s := by omega
  obtain ⟨e, he, hrs⟩ := edge_of_oneRun (by omega) hw0 hwm q hq hrank (by
    intro k hk
    rw [heq]
    exact hp k hk)
  rw [heq] at hrs
  exact ⟨e, he, hrs⟩

/-- Data-entrance `PEOne` from the width-484 pivot certificate. -/
theorem data_of_oneRun
    (q : Matrix (Fin 529) (Fin 529) ℚ) (hq : q * q = q) (hrank : q.rank = 484)
    (hp : ∀ k < 484, IsPiv q k (529 - 484 + k)) :
    ∃ e, PEOne q DataR e := by
  obtain ⟨e, he, hrs⟩ := edge_of_oneRun (by norm_num) (by norm_num) (by norm_num) q hq hrank hp
  exact ⟨e, he, hrs⟩

/-- Copy-correction `PEOne` from the width-one pivot certificate. -/
theorem copy_of_oneRun
    (q : Matrix (Fin 529) (Fin 529) ℚ) (hq : q * q = q) (hrank : q.rank = 1)
    (hp : ∀ k < 1, IsPiv q k (529 - 1 + k)) :
    ∃ e, PEOne q CopyR e := by
  obtain ⟨e, he, hrs⟩ := edge_of_oneRun (by norm_num) (by norm_num) (by norm_num) q hq hrank hp
  exact ⟨e, he, hrs⟩

end IntMul.Kappa.R8.Bit.Oppbank.OneRun
