import Submission.Bench
import Submission.Prog2
set_option autoImplicit true

/-!
# Rock2b — Lane-1B independent rock battery + step measurement (R2125607749)

TEST-ONLY, Lane-1B file (Lane-1A owns Prog2.lean/Bench2.lean — this only READS
their defs; deconfliction per AGENTS.md rule 9).  Run:

    cd ~/prove2me_workspace/subset-sum
    lake build Submission && lake env lean Rock2b.lean

Charter coverage (corrected architecture — parent's two-pointer directive):
  §1 battery: 15 targeted edges + 8 dup-heavy n=8 all-equal + 20 LCG
     pseudorandom (seed 20261031, n ∈ 2..7) + 3 full-pipeline n=12/16/20
     + width-blindness cases (huge a_i — a fixed-pass radix would mis-sort
     these; merge must not care) + ODD-n envelope stress (n=9/11/13:
     m = h+1 so B2/B3 span 2·2^h cells, beyond the OLD haddr envelope).
     Three-way agreement: independent recursive oracle vs prog2 vs prog
     (prog skipped above n=12 — its binary-search phaseB is the slow lane).
  §2 steps: end-to-end pc-86→verdict decomposition at n=12,16,20 on
     exhaustive-NO instances (a_i = i+7, t = Σa+1 — worst case: the sweep
     runs to exhaustion).  prog2 marks: pc 86 (prologue end) and pc 224
     (scanB entry — MEASURED in Check2b §B2, not the stale 164 in Bench2's
     comments).  prog control at n=12,16 with marks 86/148.  Fit report:
     per-2^(n/2) constants and growth factors — prog2 must track C·2^(n/2),
     prog's phaseB must show the n·2^(n/2) drift.
-/

namespace Rock2b

open BigOSpeedrun.SubsetSum SubsetSum.MITM SubsetSum.MITM.Bench

/-! ## §0 instrument -/

/-- Independent oracle: recursive include/exclude — different algorithmic
shape from both programs' machinery (no arrays, no masks). -/
def orc2 : List Nat → Nat → Bool
  | [], t => t == 0
  | a :: rest, t => orc2 rest t || (a ≤ t && orc2 rest (t - a))

def bitsOf (as : List Nat) (t : Nat) : Nat := Nat.log2 (as.foldl max t) + 1
def wOf (n : Nat) (as : List Nat) (t : Nat) : Nat := wordLength n (bitsOf as t)

/-- Generous fuel; a correct run halts far below (only a hang pays fuel). -/
def fuelOf (n : Nat) : Nat :=
  400 * 2 ^ (n / 2) + (40 * n + 200) * 2 ^ (n - n / 2) + 5000

/-- Tail-recursive step counter with two pc marks (Lane-1B's own copy — same
semantics as Bench.execMem plus marks; halting instruction counts as a step,
matching `exec`'s fuel semantics).  Returns
`(totalSteps, stepsAtFirstMarkA, stepsAtFirstMarkB, verdict)`; an unreached
mark reports 0. -/
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

def runV (P : List Instr) (n : Nat) (as : List Nat) (t : Nat) : Option Bool :=
  match runMarks P 999999999 999999998 n as t with
  | some (_, _, _, v) => some v
  | none => none

/-! ## §1 the battery -/

structure Case where
  name : String
  n : Nat
  as : List Nat
  t : Nat
  runProg : Bool   -- also cross-check the filed prog (false for big n)

def edgeCases : List Case :=
  [ { name := "e01 n2 empty",     n := 2, as := [4,7], t := 0, runProg := true }
  , { name := "e02 n2 single1",   n := 2, as := [4,7], t := 4, runProg := true }
  , { name := "e03 n2 single2",   n := 2, as := [4,7], t := 7, runProg := true }
  , { name := "e04 n2 all",       n := 2, as := [4,7], t := 11, runProg := true }
  , { name := "e05 n2 gap",       n := 2, as := [4,7], t := 5, runProg := true }
  , { name := "e06 n2 over",      n := 2, as := [4,7], t := 12, runProg := true }
  , { name := "e07 n2 hugeT",     n := 2, as := [4,7], t := 2^40, runProg := true }
  , { name := "e08 n3 empty",     n := 3, as := [3,5,9], t := 0, runProg := true }
  , { name := "e09 n3 single",    n := 3, as := [3,5,9], t := 9, runProg := true }
  , { name := "e10 n3 all",       n := 3, as := [3,5,9], t := 17, runProg := true }
  , { name := "e11 n3 gap",       n := 3, as := [3,5,9], t := 16, runProg := true }
  , { name := "e12 n3 hugeT",     n := 3, as := [3,5,9], t := 2^40, runProg := true }
  , { name := "e13 n4 wrapNO",    n := 4, as := [1,2,2^20,4], t := 8, runProg := true }
  , { name := "e14 n7 dupmin y",  n := 7, as := [1,1,1,1,1,1,1], t := 3, runProg := true }
  , { name := "e15 n8 dupmin n",  n := 8, as := [2,2,2,2,2,2,2,2], t := 9, runProg := true } ]

/-- 8 duplicate-heavy t at n=8, all elements equal (bucket pile-up stress). -/
def dupCases : List Case :=
  [1, 3, 5, 10, 21, 30, 40, 41].map fun tv =>
    { name := s!"dup8 t={tv}", n := 8, as := [5,5,5,5,5,5,5,5], t := tv, runProg := true }

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
      go s3 i ({ name := s!"rand{20 - i} n={n} t={t}", n := n, as := as, t := t,
                 runProg := true } :: acc)
  go 20261031 20 []

/-- Full-pipeline n = 12/16/20: constructed-certain verdicts (empty subset,
single element, all elements, Σa+1 overshoot) — no oracle trust needed, but
the oracle runs anyway. -/
def pipelineCases : List Case :=
  ([12, 16, 20] : List Nat).flatMap fun n =>
    let as := (List.range n).map fun i => 2 * i + 3
    let S := as.sum
    [ { name := s!"pipe n={n} t=0", n := n, as := as, t := 0, runProg := n ≤ 12 }
    , { name := s!"pipe n={n} t=Σ", n := n, as := as, t := S, runProg := n ≤ 12 }
    , { name := s!"pipe n={n} t=Σ+1", n := n, as := as, t := S + 1, runProg := n ≤ 12 }
    , { name := s!"pipe n={n} t=a7+a3", n := n, as := as,
        t := (2 * 7 + 3) + (2 * 3 + 3), runProg := n ≤ 12 } ]

/-- Width-blindness: half-sums far beyond 2^(2h+2) — a fixed-pass radix
mis-sorts here (300 vs 44 collide mod 2^8); merge compares are 1 step for
any w, so prog2 MUST pass. This is the b-independence proof by execution. -/
def widthCases : List Case :=
  [ { name := "wide n8 1203", n := 8, as := [400,401,402,403,3,3,3,3], t := 1203, runProg := true }
  , { name := "wide n8 807",  n := 8, as := [400,401,402,403,3,3,3,3], t := 807, runProg := true }
  , { name := "wide n8 799",  n := 8, as := [400,401,402,403,3,3,3,3], t := 799, runProg := true }
  , { name := "wide n4 2^20hit", n := 4, as := [1,2,2^20,4], t := 2^20+4, runProg := true }
  , { name := "wide n7 hugevals", n := 7, as := [2^18,2^19,5,6,7,8,9], t := 2^18+2^19+7, runProg := true }
  , { name := "wide n7 hugeNO", n := 7, as := [2^18,2^19,5,6,7,8,9], t := 2^18+2^19+4, runProg := true } ]

/-- ODD-n envelope stress: m = h+1, so S₂ has 2·2^h elements and B2/B3 run
PAST the old envelope 3n+26+2·2^(n/2) — the layout extension Lane-1A
documented (3n+27+2^(n/2)+2·2^(n−n/2)) gets exercised for real. -/
def oddCases : List Case :=
  [ { name := "odd n9 half",  n := 9,  as := (List.range 9).map fun i => i + 2,
      t := ((List.range 9).map fun i => i + 2).sum / 2, runProg := true }
  , { name := "odd n9 over",  n := 9,  as := (List.range 9).map fun i => i + 2,
      t := ((List.range 9).map fun i => i + 2).sum + 1, runProg := true }
  , { name := "odd n11 mix",  n := 11, as := [9,1,40,7,7,3,100,2,2,15,6],
      t := 133, runProg := true }
  , { name := "odd n11 miss", n := 11, as := [9,1,40,7,7,3,100,2,2,15,6],
      t := 191, runProg := true }
  , { name := "odd n13 rand", n := 13, as := (List.range 13).map fun i => (lcg (i + 7)) % 30 + 1,
      t := 97, runProg := true } ]

def battery : List Case :=
  edgeCases ++ dupCases ++ randCases ++ pipelineCases ++ widthCases ++ oddCases

def checkCase (c : Case) : IO Bool := do
  let exp := orc2 c.as c.t
  let got2 := runV prog2 c.n c.as c.t
  let ok2 := got2 == some exp
  let ok1 := !c.runProg || runV prog c.n c.as c.t == some exp
  unless (ok2 && ok1) do
    IO.println (s!"  FAIL {c.name}: oracle={exp} prog2={got2}" ++
      (if c.runProg then s!" prog={runV prog c.n c.as c.t}" else ""))
  return ok2 && ok1

/-! ## §2 step measurement -/

/-- Exhaustive-NO measurement instance (worst case: sweep runs to exhaustion).
Same shape as Lane-1A's measInst so the numbers cross-check. -/
def measInst (n : Nat) : List Nat × Nat :=
  let as := (List.range n).map fun i => i + 7
  (as, as.sum + 1)

-- MEASURED pc boundaries (Check2b §B2): prog2: 86 prologue end, 148 canon,
-- 161 phaseA2, 224 scanB, 244 smallN, 301 total.  prog: 86/148/249.
def pcA2 : Nat := 86
def pcSCAN : Nat := 224
def pcPB1 : Nat := 148

#eval show IO Unit from do
  IO.println "== §1 rock battery (independent oracle vs prog2 [vs prog]) =="
  let mut npass := 0
  for c in battery do
    if ← checkCase c then
      npass := npass + 1
  IO.println s!"BATTERY: {npass}/{battery.length} pass"

  IO.println "== §2 steps, exhaustive-NO (a_i = i+7, t = Σa+1) =="
  let mut prevGen := 0
  let mut prevTot := 0
  let mut prevN := 0
  for n in [12, 16, 20] do
    let (as, t) := measInst n
    IO.println s!"-- n={n} (oracle NO: {orc2 as t == false}) --"
    match runMarks prog2 pcA2 pcSCAN n as t with
    | some (tot, sa, sb, v) =>
      let h := n / 2
      let gen := sb - sa          -- phaseA + canon + phaseA2 (both halves)
      let scan := tot - sb        -- scanB (+ verdict)
      IO.println s!"  prog2: prologue={sa} gen+sort(both halves)={gen} scan={scan} total={tot} verdict={v}"
      IO.println s!"    C-fit ×1000: gen/2^h={1000 * gen / 2 ^ h} scan/2^h={1000 * scan / 2 ^ h} (total-prologue)/2^h={1000 * (tot - sa) / 2 ^ h}"
      if prevN ≠ 0 then
        IO.println s!"    growth ×1000 (Θ(2^(n/2)) ⇒ ~4000): gen={1000 * gen / prevGen.max 1} total={1000 * tot / prevTot.max 1}"
      prevGen := gen; prevTot := tot; prevN := n
    | none => IO.println s!"  prog2 n={n}: FUEL EXHAUSTED — investigate"
    if n ≤ 16 then
      match runMarks prog pcA2 pcPB1 n as t with
      | some (tot1, sa1, sb1, v1) =>
        IO.println s!"  prog : prologue={sa1} merge={sb1 - sa1} phaseB={tot1 - sb1} total={tot1} verdict={v1}"
        IO.println s!"    phaseB/2^(n-h)={ (tot1 - sb1) / 2 ^ (n - n / 2)} (grows with n ⟹ the poly source)"
      | none => IO.println s!"  prog n={n}: FUEL EXHAUSTED"

end Rock2b
