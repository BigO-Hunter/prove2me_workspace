import Submission.Prog2
import Submission.Bench

/-! Lane-1 diagnostics (R2125607749): pc map + instruction dump + smoke.
Run: `lake env lean Prog2Bench.lean > prog2_dump.txt` -/

open BigOSpeedrun.SubsetSum SubsetSum.MITM SubsetSum.MITM.Bench

/-- Number of emitted instructions before the mark `l`. -/
def emittedBefore : List Line → Nat → Nat
  | [], _ => 0
  | .mark l' :: rest, l => if l' = l then 0 else emittedBefore rest l
  | .raw _ :: rest, l => 1 + emittedBefore rest l
  | .jblt _ _ _ :: rest, l => 1 + emittedBefore rest l

def instrToString : Instr → String
  | .one i => s!"one {i}"
  | .add i j k => s!"add {i} {j} {k}"
  | .sub i j k => s!"sub {i} {j} {k}"
  | .mul i j k => s!"mul {i} {j} {k}"
  | .div i j k => s!"div {i} {j} {k}"
  | .rem i j k => s!"rem {i} {j} {k}"
  | .and i j k => s!"and {i} {j} {k}"
  | .or i j k => s!"or {i} {j} {k}"
  | .xor i j k => s!"xor {i} {j} {k}"
  | .shl i j k => s!"shl {i} {j} {k}"
  | .shr i j k => s!"shr {i} {j} {k}"
  | .load i j => s!"load {i} {j}"
  | .store i j => s!"store {i} {j}"
  | .rand i => s!"rand {i}"
  | .blt i j l => s!"blt {i} {j} {l}"
  | .accept => "accept"
  | .reject => "reject"

/-- Uniform positivity for literal value lists (decided at eval time). -/
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

/-- Fuel ceiling for the Lane-1 battery: analytic over-estimate of
prologue (227+6n) + phaseA (44·2^h+24h) + canon (6·2^h+11) + phaseA2
(44·2^m+25m) + scan (10·(2^h+2^m)+20). -/
def fuel2 (n : Nat) : Nat := 500 + 8 * n + 220 * 2 ^ (n - n / 2)

def runVerdict (n : Nat) (vals : List Nat) (t : Nat) (hpos : ∀ v ∈ vals, 0 < v) :
    Option Bool :=
  let x := mkInst n vals t hpos
  let w := wordLength n x.bits
  (execMem prog2 (fun _ => 0) (fuel2 n) 0 0 (loadWords w x.input)).2

#eval show IO Unit from do
  IO.println s!"# prog2 length: {prog2.length}"
  let labels : List (String × Nat) :=
    [("LCOPY",LCOPY),("LCOPY2",LCOPY2),("LSMALL",LSMALL),
     ("LROUND",LROUND),("LMERGE",LMERGE),("LHAVEJ",LHAVEJ),("LBOTH",LBOTH),
     ("LTAKEJ",LTAKEJ),("LTAKEL",LTAKEL),("LSTEP",LSTEP),("LDRAINI",LDRAINI),
     ("LDILOOP",LDILOOP),("LDRAINJ",LDRAINJ),("LDJLOOP",LDJLOOP),("LSWAP",LSWAP),
     ("LCANCH",LCANCH),("LCANLOOP",LCANLOOP),("LPHASEA2",LPHASEA2),
     ("LROUND2",LROUND2),("LMERGE2",LMERGE2),("LHAVEJ2",LHAVEJ2),("LBOTH2",LBOTH2),
     ("LTAKEJ2",LTAKEJ2),("LTAKEL2",LTAKEL2),("LSTEP2",LSTEP2),("LDRAINI2",LDRAINI2),
     ("LDILOOP2",LDILOOP2),("LDRAINJ2",LDRAINJ2),("LDJLOOP2",LDJLOOP2),("LSWAP2",LSWAP2),
     ("LSCAN",LSCAN),("LSCANLESS",LSCANLESS),("LSCANGTR",LSCANGTR),("LSCANDEC",LSCANDEC)]
  for (nm, l) in labels do
    IO.println s!"# label {nm}={emittedBefore prog2Lines l}"
  for ⟨pc, ins⟩ in (List.range prog2.length).zip prog2 do
    IO.println s!"{pc} {instrToString ins}"

#eval show IO Unit from do
  -- smoke A: n=4 (h=2: phaseA ends bd=ARR1, canon copy skipped)
  for t in [6, 2, 0, 18, 7, 19] do
    let v := runVerdict 4 [3,4,5,6] t (allPos_imp _ (by decide))
    IO.println s!"SMOKE n=4 [3,4,5,6] t={t} verdict={v}"
  -- smoke B: n=6 (h=3 odd: phaseA ends bd=ARR2, canon COPY path fires)
  for t in [0, 2, 7, 28, 29, 11, 12] do
    let v := runVerdict 6 [2,9,4,7,1,5] t (allPos_imp _ (by decide))
    IO.println s!"SMOKE n=6 [2,9,4,7,1,5] t={t} verdict={v}"
  -- smoke C: post-run memory layout at n=4 (S₁ canonical at ARR1=37, S₂ at B2 or B3)
  let x := mkInst 4 [3,4,5,6] 6 (allPos_imp _ (by decide))
  let w := wordLength 4 x.bits
  let (mem, _) := execMem prog2 (fun _ => 0) (fuel2 4) 0 0 (loadWords w x.input)
  IO.println s!"LAYOUT n=4 ARR1=37 S1 mem[37..40]={(List.range 4).map fun i => (mem (37+i)).toNat} (expect [0,3,4,7])"
  IO.println s!"LAYOUT n=4 regs [4]={(mem 4).toNat} [5]={(mem 5).toNat} [9]={(mem 9).toNat} [11]={(mem 11).toNat} [18]={(mem 18).toNat} [22]={(mem 22).toNat}"
  IO.println s!"LAYOUT n=4 S2 at [18]={(mem 18).toNat}: next4={(List.range 4).map fun i => (mem ((mem 18).toNat+i)).toNat} (expect sorted sums of 5,6 = [0,5,6,11])"
