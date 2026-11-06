import Submission.Bench
import Submission.Prog2
set_option autoImplicit true

/-!
# Bench2C — rock battery + step measurement for prog2 **v2** (R2125607749, Lane-1C)

Separate-file harness per the Lane-1B deconfliction (14:40 rider): `Bench2.lean`
(v1-era, references the dead radix names `full2`/`LPA2END`) and `Prog2.lean`
(Lane-1A's) are NOT edited here.  This file is self-contained against v2:
`prog2 = prologue ++ phaseA ++ canon ++ phaseA2 ++ scanB ++ smallN`.

Run:
    cd ~/prove2me_workspace/subset-sum
    lake build Submission && lake env lean Bench2C.lean

Sections:
  §1 pc map + reproducibility pins (the filed `prog` re-resolves byte-identical)
  §2 rock battery vs brute-force oracle: 15 targeted edges, 8 dup-heavy n=8,
     20 LCG pseudorandom (seed 20261031, n∈2..7), n≥12 oracle spots, and the
     width-blindness adversarial set (huge a_i ≫ 2^n at even AND odd n,
     t = Σa exact, empty-subset-only) — prog2 AND prog vs oracle; ALL must match
  §3 step-count measurement at n = 12,16,20,24 on exhaustive-NO instances
     (t = Σa+1: scan/binary-search run to exhaustion — full worst case):
     prog2 decomposed prologue/merge1/canon+merge2/scan, prog decomposed
     prologue/merge1/phaseB; per-2^(n/2) constants, growth ratios n→n+4
     (Θ(2^(n/2)) ⟹ ~4.000), and the S₁/S₂ sorted-array cross-checks
     (prog2's S₁ at scan entry == prog's bd array at pc 148 == the Lean-side
     merge of the generated multiset; S₂ likewise vs the second half).

`execMarks` mirrors the statement's `exec` case-for-case (like Bench.execMem),
tail-recursive with a step accumulator and three pc marks — phase costs are
measured, not guessed.  TEST-ONLY; the statement's `exec` stays the authority
(ExecEq.lean's equivalence covers the mirror).
-/

namespace Bench2C

open BigOSpeedrun.SubsetSum SubsetSum.MITM SubsetSum.MITM.Bench

/-! ## §0 helpers -/

/-- Number of emitted instructions before the mark `l` (mirrors BenchPrologue). -/
def emittedBefore : List Line → Nat → Nat
  | [], _ => 0
  | .mark l' :: rest, l => if l' = l then 0 else emittedBefore rest l
  | .raw _ :: rest, l => 1 + emittedBefore rest l
  | .jblt _ _ _ :: rest, l => 1 + emittedBefore rest l

def full1 : List Line := prologue ++ phaseA ++ phaseB ++ smallN

/-- pc map of prog (filed): phaseA entry 86, phaseB entry 148. -/
def pcPA : Nat := 86
def pcPB1 : Nat := 86 + (resolve phaseA).length

/-- pc map of prog2 (v2): phaseA entry 86, canon entry = phaseB's old 148,
scanB entry = 148 + |canon| + |phaseA2|. -/
def pcCan : Nat := pcPB1
def pcScan : Nat := pcPB1 + (resolve canon).length + (resolve phaseA2).length

def bitsOf (as : List Nat) (t : Nat) : Nat := Nat.log2 (as.foldl max t) + 1
def wOf (n : Nat) (as : List Nat) (t : Nat) : Nat := wordLength n (bitsOf as t)

/-- Generous fuel; a correct run halts far below it (only a hang pays fuel). -/
def fuelOf (n : Nat) : Nat :=
  400 * 2 ^ (n / 2) + (40 * n + 200) * 2 ^ (n - n / 2) + 5000

/-- Brute-force oracle: some subset of `as` sums to `t`. -/
def oracle (as : List Nat) (t : Nat) : Bool :=
  let n := as.length
  (List.range (2 ^ n)).any fun idx =>
    ((List.range n).map fun j =>
      if (idx >>> j) &&& 1 = 1 then as.getD j 0 else 0).sum = t

def runV (P : List Instr) (n : Nat) (as : List Nat) (t : Nat) : Option Bool :=
  (execMem P (fun _ => 0) (fuelOf n) 0 0
    (loadWords (wOf n as t) (n :: as ++ [t]))).2

/-- Tail-recursive step counter with three pc marks.  Returns
`(totalSteps, stepsAtA, stepsAtB, stepsAtC, verdict)`; an unreached mark
reports 0.  The halting instruction counts as a step (matches `exec` fuel
semantics). -/
def execMarks {w : Nat} (P : List Instr) (ρ : Nat → BitVec w) (mA mB mC : Nat) :
    (t pc r s sa sb sc : Nat) → (m : Nat → BitVec w) →
    Option (Nat × Nat × Nat × Nat × Bool)
  | 0, _, _, _, _, _, _, _ => none
  | t + 1, pc, r, s, sa, sb, sc, m =>
    let sa' := if pc = mA ∧ sa = 0 then s else sa
    let sb' := if pc = mB ∧ sb = 0 then s else sb
    let sc' := if pc = mC ∧ sc = 0 then s else sc
    let write (i : Nat) (v : BitVec w) := fun x => if x = i then v else m x
    match P.getD pc .reject with
    | .one i => execMarks P ρ mA mB mC t (pc + 1) r (s + 1) sa' sb' sc' (write i 1)
    | .add i j k => execMarks P ρ mA mB mC t (pc + 1) r (s + 1) sa' sb' sc' (write i (m j + m k))
    | .sub i j k => execMarks P ρ mA mB mC t (pc + 1) r (s + 1) sa' sb' sc' (write i (m j - m k))
    | .mul i j k => execMarks P ρ mA mB mC t (pc + 1) r (s + 1) sa' sb' sc' (write i (m j * m k))
    | .div i j k => execMarks P ρ mA mB mC t (pc + 1) r (s + 1) sa' sb' sc' (write i (m j / m k))
    | .rem i j k => execMarks P ρ mA mB mC t (pc + 1) r (s + 1) sa' sb' sc' (write i (m j % m k))
    | .and i j k => execMarks P ρ mA mB mC t (pc + 1) r (s + 1) sa' sb' sc' (write i (m j &&& m k))
    | .or i j k => execMarks P ρ mA mB mC t (pc + 1) r (s + 1) sa' sb' sc' (write i (m j ||| m k))
    | .xor i j k => execMarks P ρ mA mB mC t (pc + 1) r (s + 1) sa' sb' sc' (write i (m j ^^^ m k))
    | .shl i j k => execMarks P ρ mA mB mC t (pc + 1) r (s + 1) sa' sb' sc' (write i (m j <<< m k))
    | .shr i j k => execMarks P ρ mA mB mC t (pc + 1) r (s + 1) sa' sb' sc' (write i (m j >>> m k))
    | .load i j => execMarks P ρ mA mB mC t (pc + 1) r (s + 1) sa' sb' sc' (write i (m (m j).toNat))
    | .store i j => execMarks P ρ mA mB mC t (pc + 1) r (s + 1) sa' sb' sc'
        (fun x => if x = (m i).toNat then m j else m x)
    | .rand i => execMarks P ρ mA mB mC t (pc + 1) (r + 1) (s + 1) sa' sb' sc'
        (fun x => if x = i then ρ r else m x)
    | .blt i j l => execMarks P ρ mA mB mC t (if m i < m j then l else pc + 1) r (s + 1) sa' sb' sc' m
    | .accept => some (s + 1, sa', sb', sc', true)
    | .reject => some (s + 1, sa', sb', sc', false)

def runMarks (P : List Instr) (mA mB mC n : Nat) (as : List Nat) (t : Nat) :
    Option (Nat × Nat × Nat × Nat × Bool) :=
  execMarks P (fun _ => 0) mA mB mC (fuelOf n) 0 0 0 0 0 0
    (loadWords (wOf n as t) (n :: as ++ [t]))

/-- Memory snapshot after exactly `steps` steps. -/
def memAtSteps (P : List Instr) (steps n : Nat) (as : List Nat) (t : Nat) :
    Nat → BitVec (wOf n as t) :=
  (execMem P (fun _ => 0) steps 0 0
    (loadWords (wOf n as t) (n :: as ++ [t]))).1

def arrAt (mem : Nat → BitVec w) (bd len : Nat) : List Nat :=
  (List.range len).map fun i => (mem (bd + i)).toNat

def sortedAsc (l : List Nat) : Bool :=
  (l.zip (l.drop 1)).all fun p => p.1 ≤ p.2

/-- Structural `Instr` equality (the pinned statement defines no BEq and must
not be edited) — TEST-ONLY. -/
def instrEq : Instr → Instr → Bool
  | .one i, .one j => i == j
  | .add i j k, .add i' j' k' => i == i' && j == j' && k == k'
  | .sub i j k, .sub i' j' k' => i == i' && j == j' && k == k'
  | .mul i j k, .mul i' j' k' => i == i' && j == j' && k == k'
  | .div i j k, .div i' j' k' => i == i' && j == j' && k == k'
  | .rem i j k, .rem i' j' k' => i == i' && j == j' && k == k'
  | .and i j k, .and i' j' k' => i == i' && j == j' && k == k'
  | .or i j k, .or i' j' k' => i == i' && j == j' && k == k'
  | .xor i j k, .xor i' j' k' => i == i' && j == j' && k == k'
  | .shl i j k, .shl i' j' k' => i == i' && j == j' && k == k'
  | .shr i j k, .shr i' j' k' => i == i' && j == j' && k == k'
  | .load i j, .load i' j' => i == i' && j == j'
  | .store i j, .store i' j' => i == i' && j == j'
  | .rand i, .rand j => i == j
  | .blt i j l, .blt i' j' l' => i == i' && j == j' && l == l'
  | .accept, .accept => true
  | .reject, .reject => true
  | _, _ => false

def progEq (l1 l2 : List Instr) : Bool :=
  l1.length == l2.length && (l1.zip l2).all fun p => instrEq p.1 p.2

/-! ## Lean-side reference: generated half-sum multiset, mmerge-sorted -/

/-- Unsorted doubling generation — the multiset `halfSums` builds. -/
def genSums : List Nat → List Nat
  | [] => [0]
  | a :: as' => let l := genSums as'; l ++ l.map fun x => x + a

/-- Spec-exact merge (Sort.lean's `mmerge`: take right only when strictly
smaller) + mergesort — the unique sorted form of the multiset. -/
def mergeNat : List Nat → List Nat → List Nat
  | [], r => r
  | l, [] => l
  | a :: l', b :: r' =>
    if b < a then b :: mergeNat (a :: l') r' else a :: mergeNat l' (b :: r')

/-- Merge sort with an explicit fuel argument — structural on the fuel, no
termination tactic needed; `msortF len l` is the true sort for any `l`
(recursion depth ≤ log₂(len)+1 ≤ len). -/
def msortF : (fuel : Nat) → List Nat → List Nat
  | 0, l => l
  | fuel + 1, l =>
    if l.length ≤ 1 then l else
    let half := l.length / 2
    mergeNat (msortF fuel (l.take half)) (msortF fuel (l.drop half))

def msort (l : List Nat) : List Nat := msortF l.length l

/-! ## §1 pc map + reproducibility pins -/

#eval (resolve full1).length                    -- 249 (filed prog)
#eval progEq (resolve full1) prog               -- true: filed prog reproducible
#eval (resolve canon).length                    -- 13
#eval (resolve phaseA2).length                  -- 63
#eval (resolve scanB).length                    -- 20
#eval pcScan                                    -- 224 = 148 + 13 + 63
#eval (resolve prog2Lines).length               -- 301
#eval progEq (resolve prog2Lines) prog2         -- true
#eval prog2.all fun q => !isRandInstr q       -- true: no rand (Det applies)

/-! ## §2 rock battery -/

structure Case where
  name : String
  n : Nat
  as : List Nat
  t : Nat

def edgeCases : List Case :=
  [ { name := "e01 n2 empty",        n := 2, as := [3,5], t := 0 }
  , { name := "e02 n2 single1",      n := 2, as := [3,5], t := 3 }
  , { name := "e03 n2 single2",      n := 2, as := [3,5], t := 5 }
  , { name := "e04 n2 all",          n := 2, as := [3,5], t := 8 }
  , { name := "e05 n2 gap",          n := 2, as := [3,5], t := 4 }
  , { name := "e06 n2 over",         n := 2, as := [3,5], t := 9 }
  , { name := "e07 n2 hugeT",        n := 2, as := [3,5], t := 2^40 }
  , { name := "e08 n3 empty",        n := 3, as := [2,4,6], t := 0 }
  , { name := "e09 n3 single3",      n := 3, as := [2,4,6], t := 6 }
  , { name := "e10 n3 all",          n := 3, as := [2,4,6], t := 12 }
  , { name := "e11 n3 gap",          n := 3, as := [2,4,6], t := 11 }
  , { name := "e12 n4 hugeElem",     n := 4, as := [1,2,2^20,4], t := 8 }
  , { name := "e13 n7 dupmin yes",   n := 7, as := [1,1,1,1,1,1,1], t := 3 }
  , { name := "e14 n7 dupmin no",    n := 7, as := [1,1,1,1,1,1,1], t := 8 }
  , { name := "e15 n8 dupmin no",    n := 8, as := [2,2,2,2,2,2,2,2], t := 9 } ]

def dupCases : List Case :=
  [1, 3, 5, 10, 21, 30, 40, 41].map fun tv =>
    { name := s!"dup8 t={tv}", n := 8, as := [5,5,5,5,5,5,5,5], t := tv }

def lcg (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

def drawVals : Nat → Nat → (List Nat × Nat)
  | s, 0 => ([], s)
  | s, k + 1 =>
    let s1 := lcg s
    let (rest, s2) := drawVals s1 k
    ((s1 % 16 + 1) :: rest, s2)

/-- 20 pseudorandom instances, LCG seed 20261031, n ∈ 2..7, t ∈ [0, Σa+10]. -/
def randCases : List Case :=
  let rec go : Nat → Nat → List Case → List Case
    | _, 0, acc => acc.reverse
    | s, i + 1, acc =>
      let s1 := lcg s
      let n := 2 + s1 % 6
      let (as, s2) := drawVals s1 n
      let s3 := lcg s2
      let t := s3 % (as.sum + 11)
      go s3 i ({ name := s!"rand{20 - i} n={n} t={t}", n := n, as := as, t := t } :: acc)
  go 20261031 20 []

def spotCases : List Case :=
  [ { name := "spot n12 t=61",  n := 12,
      as := (List.range 12).map fun i => i + 7, t := 61 }
  , { name := "spot n12 t=151", n := 12,
      as := (List.range 12).map fun i => i + 7, t := 151 }
  , { name := "spot n16 yes",   n := 16,
      as := (List.range 16).map fun i => 1000 + 7 * i, t := 1000 + 1007 + 1014 }
  , { name := "spot n20 yes",   n := 20,
      as := (List.range 20).map fun i => 5000 + 13 * i,
      t := 5000 + 5013 + 5026 + 5039 } ]

/-- Width-blindness adversarial set (Lane-1B's list): values ≫ 2^n, odd n,
t = Σa exact, empty-only — the cases that KILL any fixed-pass radix and that
the b-independent merge+scan must pass. -/
def widthBlindCases : List Case :=
  [ { name := "wb n8 a~2^20 yes", n := 8,
      as := [2^20, 2^20+1, 2^20+2, 2^20+3, 5, 7, 9, 11], t := 2^20 + 9 }
  , { name := "wb n8 a~2^20 no",  n := 8,
      as := [2^20, 2^20+1, 2^20+2, 2^20+3, 1, 1, 1, 1], t := 2^19 }
  , { name := "wb n7 odd a~2^22", n := 7,
      as := [2^22, 1, 2, 4, 8, 16, 32], t := 2^22 + 42 }
  , { name := "wb n7 odd no",     n := 7,
      as := [2^22, 1, 2, 4, 8, 16, 32], t := 2^22 + 64 }
  , { name := "wb n5 empty-only", n := 5, as := [7,11,13,17,19], t := 0 }
  , { name := "wb n9 t=Σa",       n := 9,
      as := [3,5,7,9,11,13,15,17,19], t := 99 }
  , { name := "wb n6 all-equal huge", n := 6,
      as := [2^25, 2^25, 2^25, 2^25, 2^25, 2^25], t := 3 * 2^25 }
  , { name := "wb n6 all-equal huge no", n := 6,
      as := [2^25, 2^25, 2^25, 2^25, 2^25, 2^25], t := 3 * 2^25 + 1 } ]

def battery : List Case :=
  edgeCases ++ dupCases ++ randCases ++ spotCases ++ widthBlindCases

def checkCase (c : Case) : IO Bool := do
  let exp := oracle c.as c.t
  let got2 := runV prog2 c.n c.as c.t
  let got1 := runV prog c.n c.as c.t
  let ok := got2 == some exp && got1 == some exp
  unless ok do
    IO.println s!"  FAIL {c.name}: oracle={exp} prog2={got2} prog={got1}"
  return ok

/-! ## §3/§4 driver -/

def measInst (n : Nat) : List Nat × Nat :=
  let as := (List.range n).map fun i => i + 7
  (as, as.sum + 1)

#eval show IO Unit from do
  IO.println "== §2 rock battery (prog2 AND prog vs oracle) =="
  let mut npass := 0
  for c in battery do
    if ← checkCase c then
      npass := npass + 1
  IO.println s!"BATTERY: {npass}/{battery.length} pass"

  IO.println "== §3 step counts (exhaustive-NO: a_i = i+7, t = Σa+1) =="
  let mut prevTot2 := 0; let mut prevScan := 0; let mut prevM2 := 0
  let mut prevN := 0
  for n in [12, 16, 20, 24] do
    let (as, t) := measInst n
    let r2 := runMarks prog2 pcPA pcCan pcScan n as t
    -- prog control only at n = 12,16 (the poly is already pinned by 1B's
    -- 144→184 series; the n≥20 control runs are the heaviest in this file)
    let r1 := if n ≤ 16 then runMarks prog pcPA pcPB1 999999 n as t else none
    match r2 with
    | some (tot2, sa2, sb2, sc2, v2) =>
      let h := n / 2
      let m := n - h
      let merge1 := sb2 - sa2          -- phaseA in prog2 == in prog (same code)
      let canM2 := sc2 - sb2           -- canon + second-half merge
      let scan := tot2 - sc2
      IO.println s!"n={n} prog2 verdict={v2} (expect false: t>Σa)"
      IO.println s!"  prog2: prologue={sa2} merge1={merge1} canon+merge2={canM2} scan={scan} TOTAL={tot2}"
      match r1 with
      | some (tot1, sa1, sb1, _, v1) =>
        IO.println s!"  prog : prologue={sa1} merge1={sb1 - sa1} phaseB={tot1 - sb1} TOTAL={tot1} verdict={v1} agree={v1 == v2}"
      | none => pure ()
      IO.println s!"  C-fit ×1000 (total/2^(n/2)): prog2={1000 * tot2 / 2 ^ h}"
      IO.println s!"  per-2^(n/2) ×1000: scan={1000 * scan / 2 ^ h} canon+merge2={1000 * canM2 / 2 ^ h}"
      if prevN ≠ 0 then
        IO.println s!"  growth {prevN}→{n} ×1000 (Θ(2^(n/2)) ⟹ 4000): prog2total={1000 * tot2 / prevTot2.max 1} scan={1000 * scan / prevScan.max 1} merge2={1000 * canM2 / prevM2.max 1}"
      prevTot2 := tot2; prevScan := scan; prevM2 := canM2; prevN := n
      -- cross-checks at scanB entry: S₁ canonical at ARR1, S₂ at [18]
      let mem2 := memAtSteps prog2 sc2 n as t
      let arr1Base := (mem2 22).toNat
      let s1 := arrAt mem2 arr1Base (2 ^ h)
      let s2Base := (mem2 18).toNat
      let s2 := arrAt mem2 s2Base (2 ^ m)
      let expS1 := msort (genSums ((List.range h).map fun i => i + 7))
      let expS2 := msort (genSums ((List.range m).map fun i => h + i + 7))
      IO.println s!"  xcheck S₁: base={arr1Base} (expect {3 * n + 25}) ==lean={s1 == expS1} sorted={sortedAsc s1}"
      IO.println s!"  xcheck S₂: base={s2Base} sorted={sortedAsc s2} ==lean={s2 == expS2} m=[4]→{(mem2 4).toNat} H=[5]→{(mem2 5).toNat}"
      match r1 with
      | some (_, _, sb1, _, _) =>
        let mem1 := memAtSteps prog sb1 n as t
        let bd1 := (mem1 18).toNat
        let s1prog := arrAt mem1 bd1 (2 ^ h)
        IO.println s!"  xcheck S₁==prog-bd-array: {s1 == s1prog} (bd1={bd1})"
      | none => pure ()
    | none =>
      IO.println s!"n={n}: FUEL EXHAUSTED or mark missed — investigate"

  IO.println "== §4 scale verdicts without oracle (mathematical ground truth) =="
  for n in [22, 24] do
    let as := (List.range n).map fun i => i + 7
    let yesV := runV prog2 n as as.sum          -- t = Σa: full subset ⟹ YES
    let noV := runV prog2 n as (as.sum + 1)     -- t > Σa ⟹ NO
    IO.println s!"  n={n}: prog2 Σa={yesV} (expect true) Σa+1={noV} (expect false)"

end Bench2C
