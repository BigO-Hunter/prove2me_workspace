import Submission.Bench
import Submission.Prog2
set_option autoImplicit true

/-!
# Bench2 — rock battery + step-count measurement for prog2 (R2125607749, Lane 1)

TEST-ONLY harness (root-level like BenchPrologue.lean, not part of the
Submission lib's theorem surface).  Run:

    cd ~/prove2me_workspace/subset-sum
    lake build Submission && lake env lean Bench2.lean

Sections:
  §1 pc map (resolve check — jumps land, lengths match the Prog2.lean claims)
  §2 rock battery: 15 targeted edges + 8 dup-heavy n=8 + 20 LCG pseudorandom
     (seed 20261031, n∈2..7) + n≥12 oracle spot checks — prog2 AND prog vs
     brute-force oracle; ALL must match.
  §3 step-count measurement at n = 12,16,20,24 on exhaustive-NO instances
     (phaseB runs to exhaustion): prologue/radix/phaseB decomposition for
     prog2, prologue/merge/phaseB for prog, per-2^(n/2) constants + growth
     factors, plus the sorted-array cross-check (prog2's ARR1 at its phaseB
     entry == prog's array at pc 148, elementwise).
  §4 correctness-boundary diagnostic (§E of the lane report): in-envelope vs
     out-of-envelope instances — NOT part of the pass/fail battery; documents
     the half-sums < 2^(2h+2) boundary where 2-pass radix mis-sorts.

`execMarks` mirrors the statement's `exec` case-for-case (like Bench.execMem)
but is tail-recursive with a step accumulator and records the step count at
the first arrival at two pc marks — so phase costs are measured, not guessed.
-/

namespace Bench2

open BigOSpeedrun.SubsetSum SubsetSum.MITM SubsetSum.MITM.Bench

/-! ## §0 helpers -/

/-- Number of emitted instructions before the mark `l` (mirrors BenchPrologue). -/
def emittedBefore : List Line → Nat → Nat
  | [], _ => 0
  | .mark l' :: rest, l => if l' = l then 0 else emittedBefore rest l
  | .raw _ :: rest, l => 1 + emittedBefore rest l
  | .jblt _ _ _ :: rest, l => 1 + emittedBefore rest l

def full1 : List Line := prologue ++ phaseA ++ phaseB ++ smallN

/-- phaseB entry pc in `prog` (86-instr prologue + 62-instr merge phaseA). -/
def pcPB1 : Nat := 86 + (resolve phaseA).length

/-- phaseB entry pc in `prog2`. -/
def pcPB2 : Nat := emittedBefore full2 LPA2END

/-- `Instance.bits` mirrored without the proof-carrying structure. -/
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

/-- Verdict of `P` on the raw instance `(n, as, t)`. -/
def runV (P : List Instr) (n : Nat) (as : List Nat) (t : Nat) : Option Bool :=
  (execMem P (fun _ => 0) (fuelOf n) 0 0
    (loadWords (wOf n as t) (n :: as ++ [t]))).2

/-- Tail-recursive step counter with two pc marks.  Returns
`(totalSteps, stepsAtFirstMarkA, stepsAtFirstMarkB, verdict)`;
a mark never reached reports 0.  The halting instruction counts as a step
(matches `exec`'s fuel semantics). -/
def execMarks {w : Nat} (P : List Instr) (ρ : Nat → BitVec w) (mA mB : Nat) :
    (t pc r s sa sb : Nat) → (m : Nat → BitVec w) →
    Option (Nat × Nat × Nat × Bool)
  | 0, _, _, _, _, _, _ => none
  | t + 1, pc, r, s, sa, sb, m =>
    let sa' := if pc = mA ∧ sa = 0 then s else sa
    let sb' := if pc = mB ∧ sb = 0 then s else sb
    let write (i : Nat) (v : BitVec w) := fun x => if x = i then v else m x
    match P.getD pc .reject with
    | .one i => execMarks P ρ mA mB t (pc + 1) r (s + 1) sa' sb' (write i 1)
    | .add i j k => execMarks P ρ mA mB t (pc + 1) r (s + 1) sa' sb' (write i (m j + m k))
    | .sub i j k => execMarks P ρ mA mB t (pc + 1) r (s + 1) sa' sb' (write i (m j - m k))
    | .mul i j k => execMarks P ρ mA mB t (pc + 1) r (s + 1) sa' sb' (write i (m j * m k))
    | .div i j k => execMarks P ρ mA mB t (pc + 1) r (s + 1) sa' sb' (write i (m j / m k))
    | .rem i j k => execMarks P ρ mA mB t (pc + 1) r (s + 1) sa' sb' (write i (m j % m k))
    | .and i j k => execMarks P ρ mA mB t (pc + 1) r (s + 1) sa' sb' (write i (m j &&& m k))
    | .or i j k => execMarks P ρ mA mB t (pc + 1) r (s + 1) sa' sb' (write i (m j ||| m k))
    | .xor i j k => execMarks P ρ mA mB t (pc + 1) r (s + 1) sa' sb' (write i (m j ^^^ m k))
    | .shl i j k => execMarks P ρ mA mB t (pc + 1) r (s + 1) sa' sb' (write i (m j <<< m k))
    | .shr i j k => execMarks P ρ mA mB t (pc + 1) r (s + 1) sa' sb' (write i (m j >>> m k))
    | .load i j => execMarks P ρ mA mB t (pc + 1) r (s + 1) sa' sb' (write i (m (m j).toNat))
    | .store i j => execMarks P ρ mA mB t (pc + 1) r (s + 1) sa' sb'
        (fun x => if x = (m i).toNat then m j else m x)
    | .rand i => execMarks P ρ mA mB t (pc + 1) (r + 1) (s + 1) sa' sb'
        (fun x => if x = i then ρ r else m x)
    | .blt i j l => execMarks P ρ mA mB t (if m i < m j then l else pc + 1) r (s + 1) sa' sb' m
    | .accept => some (s + 1, sa', sb', true)
    | .reject => some (s + 1, sa', sb', false)

def runMarks (P : List Instr) (mA mB n : Nat) (as : List Nat) (t : Nat) :
    Option (Nat × Nat × Nat × Bool) :=
  execMarks P (fun _ => 0) mA mB (fuelOf n) 0 0 0 0 0
    (loadWords (wOf n as t) (n :: as ++ [t]))

/-- Memory snapshot after exactly `steps` steps: `(bd, array at [18])`. -/
def arrAtSteps (P : List Instr) (steps n : Nat) (as : List Nat) (t : Nat) :
    Nat × List Nat :=
  let (mem, _) := execMem P (fun _ => 0) steps 0 0
    (loadWords (wOf n as t) (n :: as ++ [t]))
  let bd := (mem 18).toNat
  (bd, (List.range (2 ^ (n / 2))).map fun i => (mem (bd + i)).toNat)

def sortedAsc (l : List Nat) : Bool :=
  (l.zip (l.drop 1)).all fun p => p.1 ≤ p.2

/-- Structural `Instr` equality (the statement defines no BEq/DecidableEq and
must not be edited) — TEST-ONLY. -/
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

/-! ## §1 pc map -/

#eval (resolve full1).length              -- 249 (unchanged prog)
#eval (resolve phaseA2).length            -- 78
#eval pcPB2                               -- 164 = 86 + 78
#eval pcPB1                               -- 148
#eval (resolve full2).length              -- 265 = 86 + 78 + 101
#eval progEq (resolve full1) prog         -- true: the filed prog, reproducible
#eval progEq (resolve full2) prog2        -- true

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
  , { name := "e12 n4 wrapNO",       n := 4, as := [1,2,2^20,4], t := 8 }
  , { name := "e13 n7 dupmin yes",   n := 7, as := [1,1,1,1,1,1,1], t := 3 }
  , { name := "e14 n7 dupmin no",    n := 7, as := [1,1,1,1,1,1,1], t := 8 }
  , { name := "e15 n8 dupmin no",    n := 8, as := [2,2,2,2,2,2,2,2], t := 9 } ]

def dupCases : List Case :=
  [1, 3, 5, 10, 21, 30, 40, 41].map fun tv =>
    { name := s!"dup8 t={tv}", n := 8, as := [5,5,5,5,5,5,5,5], t := tv }

def lcg (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

/-- Draw `k` values in 1..16 (keeps half-sums ≤ 3·16 = 48 < 2^(2h+2) for
every n ∈ 4..7 — INSIDE the radix envelope; n = 2,3 take the smallN path). -/
def drawVals : Nat → Nat → (List Nat × Nat)
  | s, 0 => ([], s)
  | s, k + 1 =>
    let s1 := lcg s
    let (rest, s2) := drawVals s1 k
    ((s1 % 16 + 1) :: rest, s2)

/-- 20 pseudorandom instances, LCG seed 20261031, n ∈ 2..7, t ∈ [0, Σa+10]
(the +10 margin produces NO verdicts past the max sum). -/
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

/-- n ≥ 12 full-pipeline spot checks (oracle-comparable; witness subsets keep
the early-exit oracle cheap).  All inside the envelope: n16 half-sums ≤ 8840
< 2^18, n20 ≤ 52470 < 2^22. -/
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

def battery : List Case := edgeCases ++ dupCases ++ randCases ++ spotCases

def checkCase (c : Case) : IO Bool := do
  let exp := oracle c.as c.t
  let got2 := runV prog2 c.n c.as c.t
  let got1 := runV prog c.n c.as c.t
  let ok := got2 == some exp && got1 == some exp
  unless ok do
    IO.println s!"  FAIL {c.name}: oracle={exp} prog2={got2} prog={got1}"
  return ok

/-! ## §3/§4 driver -/

/-- Exhaustive-NO measurement instance: a_i = i+7, t = Σa + 1 > every subset
sum ⟹ phaseB scans all 2^(n−h) candidates (full-pipeline worst case). -/
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

  IO.println "== §3 step counts (exhaustive-NO instances, a_i = i+7, t = Σa+1) =="
  let mut prevRadix := 0
  let mut prevMerge := 0
  let mut prevPB2 := 0
  let mut prevPB1 := 0
  let mut prevN := 0
  for n in [12, 16, 20, 24] do
    let (as, t) := measInst n
    let r2 := runMarks prog2 86 pcPB2 n as t
    let r1 := runMarks prog 86 pcPB1 n as t
    match r2, r1 with
    | some (tot2, sa2, sb2, v2), some (tot1, sa1, sb1, v1) =>
      let h := n / 2
      let m2 := n - h
      let radix := sb2 - sa2
      let merge := sb1 - sa1
      let pb2 := tot2 - sb2
      let pb1 := tot1 - sb1
      IO.println s!"n={n} verdicts prog={v1} prog2={v2} agree={v1 == v2} (expect false=NO)"
      IO.println s!"  prog2: prologue={sa2} radix={radix} phaseB={pb2} total={tot2}"
      IO.println s!"  prog : prologue={sa1} merge={merge} phaseB={pb1} total={tot1}"
      IO.println s!"  C-fit (×1000): radix/2^(n/2)={1000 * radix / 2 ^ h} merge/2^(n/2)={1000 * merge / 2 ^ h}"
      IO.println s!"  phaseB/2^(n-h): prog2={pb2 / 2 ^ m2} prog={pb1 / 2 ^ m2}  (linear in n ⟹ the poly source)"
      if prevN ≠ 0 then
        IO.println s!"  growth n={prevN}→{n} (×1000, expect ~4000 for Θ(2^(n/2))): radix={1000 * radix / prevRadix.max 1} merge={1000 * merge / prevMerge.max 1} phaseB2={1000 * pb2 / prevPB2.max 1} phaseB1={1000 * pb1 / prevPB1.max 1}"
      prevRadix := radix; prevMerge := merge; prevPB2 := pb2; prevPB1 := pb1; prevN := n
      -- sorted-array cross-check at the phaseB entry: prog2's ARR1 vs prog's bd
      let (bd2, arr2) := arrAtSteps prog2 sb2 n as t
      let (bd1, arr1) := arrAtSteps prog sb1 n as t
      IO.println s!"  xcheck: bd2={bd2} (expect {3 * n + 25}) bd1={bd1} equal={arr1 == arr2} sorted2={sortedAsc arr2} len={arr2.length} (expect {2 ^ h})"
    | _, _ =>
      IO.println s!"n={n}: FUEL EXHAUSTED or mark missed — investigate"

  IO.println "== §4 correctness boundary (half-sums vs 2^(2h+2)) — diagnostic, NOT battery =="
  let diag : List (String × Nat × List Nat × Nat) :=
    [ ("in-env  n8 Σhalf=1020<1024", 8, [255,255,255,255,255,255,255,255], 1020)
    , ("in-env  n8 Σhalf=1020 t=510", 8, [255,255,255,255,255,255,255,255], 510)
    , ("OUT-env n8 Σhalf=1606>1024", 8, [400,401,402,403,3,3,3,3], 1203)
    , ("OUT-env n8 same t=807", 8, [400,401,402,403,3,3,3,3], 807)
    , ("OUT-env n8 same t=6", 8, [400,401,402,403,3,3,3,3], 6) ]
  for (nm, n, as, t) in diag do
    let exp := oracle as t
    let got2 := runV prog2 n as t
    let got1 := runV prog n as t
    IO.println s!"  {nm}: oracle={exp} prog={got1} prog2={got2} prog2OK={got2 == some exp}"

end Bench2
