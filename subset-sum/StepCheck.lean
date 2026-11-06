import Submission.Prog2
import Submission.Bench

/-! Lane-1 step-semantics cross-check (R2125607749): the minimal fuel F with
`(execMem prog2 … F …).2.isSome` IS the executed step count (halting step
counted, per the statement's `run … T` convention).  Bisection here vs the
Python simulator's counter.  `lake env lean StepCheck.lean` -/

open BigOSpeedrun.SubsetSum SubsetSum.MITM SubsetSum.MITM.Bench

theorem allPos_imp (l : List Nat) (h : (l.all (fun v => decide (0 < v))) = true) :
    ∀ v ∈ l, 0 < v := by
  have := List.all_eq_true.mp h
  intro v hv
  exact of_decide_eq_true (this v hv)

theorem getD_pos (l : List Nat) (hl : ∀ v ∈ l, 0 < v) (i : Nat) :
    0 < l.getD i 1 := by
  induction i generalizing l with
  | zero =>
    cases l with
    | nil => exact Nat.zero_lt_one
    | cons v _ => exact hl v (List.Mem.head ..)
  | succ k ih =>
    cases l with
    | nil => exact Nat.zero_lt_one
    | cons _ tl => exact ih tl (fun w hw => hl w (List.Mem.tail _ hw))

def mkInst (n : Nat) (vals : List Nat) (t : Nat)
    (hpos : ∀ v ∈ vals, 0 < v) : Instance n where
  a := fun i => vals.getD i.val 1
  t := t
  pos := fun i => getD_pos vals hpos i.val

def verdictAtX {n : Nat} (x : Instance n) (F : Nat) : Option Bool :=
  let w := wordLength n x.bits
  (execMem prog2 (fun _ => 0) F 0 0 (loadWords w x.input)).2

partial def binSearch (lo hi : Nat) (p : Nat → Bool) : Nat :=
  if lo + 1 >= hi then hi
  else
    let mid := (lo + hi) / 2
    if p mid then binSearch lo mid p else binSearch mid hi p

#eval show IO Unit from do
  let x4 := mkInst 4 [3,4,5,6] 6 (allPos_imp _ (by decide))
  let f4 := binSearch 0 4000 (fun F => (verdictAtX x4 F).isSome)
  IO.println s!"STEPS n=4 vals=[3,4,5,6] t=6: leanMinFuel={f4} python=480 match={f4 == 480}"
  let x6 := mkInst 6 [2^40+7, 2^40+9, 2^41+3, 5, 2^40+7, 11] (2^42) (allPos_imp _ (by decide))
  let f6 := binSearch 0 8000 (fun F => (verdictAtX x6 F).isSome)
  IO.println s!"STEPS n=6 hugeb t=2^42: leanMinFuel={f6}"
  let x8 := mkInst 8 [5,5,5,5,5,5,5,5] 41 (allPos_imp _ (by decide))
  let f8 := binSearch 0 8000 (fun F => (verdictAtX x8 F).isSome)
  IO.println s!"STEPS n=8 dup5s t=41: leanMinFuel={f8}"
