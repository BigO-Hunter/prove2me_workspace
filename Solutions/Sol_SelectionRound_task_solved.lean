import Definitions.Def_SelectionRound_Machine

open Light
open Light.DenseCanonicalSelectionRound

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The canonical greedy selection round solves its task

Top-level solution for `Light.DenseCanonicalSelectionRound.task_solved`: the proof
is the one from Joshua Wharton's DenseCanonicalSelectionRound.lean, reassembled at
top level.  It instantiates the closed `Solves` contract with the fixed
six-procedure program and its procedure index 5, and reduces to the execution
lemma `Light.DenseCanonicalSelectionRound.ends` and the shape bound
`time_le_taskTime`.
-/

theorem solution : Solves task program 5 taskTime need := by
  refine ⟨body 3 4, rfl, ?_⟩
  intro R lim d x μ fr hpre hok
  have hfr : fr ≤ lim.space := by simpa only [need, add_zero] using hok.cells
  have hn : x.length ≤ instanceSize x := by unfold instanceSize; omega
  have hheight : x.height ≤ (instanceSize x+1)*(x.height+1)+1 := by nlinarith
  have hsum : x.length*x.height+1 ≤ (instanceSize x+1)*(x.height+1)+1 := by
    nlinarith
  have hone : 1 ≤ (instanceSize x+1)*(x.height+1)+1 := by omega
  have hw := hok.word
  change (((instanceSize x+1)*(x.height+1)+1 : ℕ) : ℤ) ≤ lim.word at hw
  have h1 : 1 ≤ lim.word :=
    (by exact_mod_cast hone : (1 : ℤ) ≤ ((instanceSize x+1)*(x.height+1)+1 : ℕ)).trans hw
  have hh : (x.height : ℤ) ≤ lim.word :=
    (by exact_mod_cast hheight : (x.height : ℤ) ≤
      ((instanceSize x+1)*(x.height+1)+1 : ℕ)).trans hw
  have hs : ((x.length*x.height+1 : ℕ) : ℤ) ≤ lim.word :=
    (by exact_mod_cast hsum : ((x.length*x.height+1 : ℕ) : ℤ) ≤
      ((instanceSize x+1)*(x.height+1)+1 : ℕ)).trans hw
  have hd : d+3 ≤ lim.depth := hok.depth
  have hlayout : InOrder lim.space [(x.activeBase,x.length),
      (x.rowsBase,x.candidates*x.length),(x.scoresBase,x.candidates),
      (x.baseBase,x.length),(x.remainingBase,x.candidates)] := by
    rcases hpre.layout with ⟨h₁,h₂,h₃,h₄,h₅⟩
    exact ⟨h₁,h₂,h₃,h₄,h₅.trans hfr⟩
  change Ends lim (program++R) d (body 3 4)
    ⟨frame [x.candidates,x.length,x.height,x.activeBase,x.rowsBase,
      x.scoresBase,x.remainingBase,x.baseBase,fr], μ⟩
    (taskTime (instanceSize x) x.height) _
  exact (ends
    (getElem?_append_of_eq_some (show program[3]? = some (DenseScoreTablePass.Selection.body 1 2) from rfl) R)
    (getElem?_append_of_eq_some (show program[1]? = some (DenseScoreTablePass.body 0) from rfl) R)
    (getElem?_append_of_eq_some (show program[0]? = some DenseScorePass.body from rfl) R)
    (getElem?_append_of_eq_some (show program[2]? = some DenseArgminPass.body from rfl) R)
    (getElem?_append_of_eq_some (show program[4]? = some copyBody from rfl) R)
    hpre.active_read hpre.rows_read hpre.rows_bound hpre.remaining_read
    hpre.nonempty hok.space h1 hh hs hlayout hfr hd).mono
    (time_le_taskTime x) (fun _ h => h)
