import Submission.Bench
import Submission.Prog2
set_option autoImplicit true

/-!
# Check2b — Lane-1B independent verification (R2125607749)

TEST-ONLY, separate file by design: Lane-1A owns Prog2.lean/Bench2.lean; this
file only READS their defs (deconfliction, AGENTS.md rule 9).  Run:

    cd ~/prove2me_workspace/subset-sum
    lake build Submission && lake env lean Check2b.lean

Checks:
  §A prog frozen: resolve (prologue ++ phaseA ++ phaseB ++ smallN) == prog
     elementwise (structural Instr eq — the statement defines no BEq).
  §B label lint: every jblt label in prog2Lines has a mark (the LSMALL
     defined-but-unmarked class, which silently resolved to pc 0 twice before).
  §C quick verdicts on prog2 incl. the width-blindness cases a fixed-pass
     radix would MIS-SORT (half-sums >= 2^(2h+2)): n=8 [400..403,3,3,3,3]
     and n=4 with a 2^20 element. Merge compares are 1 step for any b, so
     prog2 must pass these — this is the b-independence proof by execution.
-/

namespace Check2b

open BigOSpeedrun.SubsetSum SubsetSum.MITM SubsetSum.MITM.Bench

/-! ## §A structural equality (mirror of Bench2's instrEq — independent copy
so a bug in theirs can't hide a bug in mine) -/

partial def iEq : Instr → Instr → Bool
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

def listEq (l1 l2 : List Instr) : Bool :=
  l1.length == l2.length && (l1.zip l2).all fun p => iEq p.1 p.2

#eval listEq (resolve (prologue ++ phaseA ++ phaseB ++ smallN)) prog  -- expect true
#eval listEq (resolve prog2Lines) prog2                               -- expect true
#eval (prog.length, prog2.length)                                     -- (249, 265) per Lane-1A's map

/-! ## §B label lint: no jblt may reference an unmarked label (would resolve
to pc 0 = re-run the prologue on live memory — the historical wild-base bug) -/

partial def marksOf : List Line → List Nat
  | [] => []
  | .mark l :: rest => l :: marksOf rest
  | _ :: rest => marksOf rest

partial def jumpsOf : List Line → List Nat
  | [] => []
  | .jblt _ _ l :: rest => l :: jumpsOf rest
  | _ :: rest => jumpsOf rest

#eval (jumpsOf prog2Lines).all fun l => l ∈ marksOf prog2Lines   -- expect true
#eval (jumpsOf prog2Lines).length                                  -- jump count
#eval (marksOf prog2Lines).all fun l => (marksOf prog2Lines).count l == 1
    -- expect true: marks unique (duplicate marks silently shadow via find?)

/-! ## §B2 exact pc boundaries in prog2 (for the step-measurement lane —
Bench2's hard-coded 86+78=164 is STALE; prog2 resolves to 301 instrs) -/

partial def emittedBefore : List Line → Nat → Nat
  | [], _ => 0
  | .mark l' :: rest, l => if l' = l then 0 else emittedBefore rest l
  | .raw _ :: rest, l => 1 + emittedBefore rest l
  | .jblt _ _ _ :: rest, l => 1 + emittedBefore rest l

#eval (emittedBefore prog2Lines LPHASEA2,   -- canon end = phaseA2 entry
       emittedBefore prog2Lines LSCAN,      -- scanB entry
       emittedBefore prog2Lines LSMALL,     -- smallN entry
       (resolve phaseA).length, (resolve canon).length,
       (resolve phaseA2).length, (resolve scanB).length)

/-! ## §C quick verdicts -/

def bitsOf (as : List Nat) (t : Nat) : Nat := Nat.log2 (as.foldl max t) + 1

def runV2 (n : Nat) (as : List Nat) (t : Nat) (fuel : Nat) : Option Bool :=
  (execMem prog2 (fun _ => 0) fuel 0 0
    (loadWords (wordLength n (bitsOf as t)) (n :: as ++ [t]))).2

def runV1 (n : Nat) (as : List Nat) (t : Nat) (fuel : Nat) : Option Bool :=
  (execMem prog (fun _ => 0) fuel 0 0
    (loadWords (wordLength n (bitsOf as t)) (n :: as ++ [t]))).2

/-- Independent oracle (List.any over all 2^n masks). -/
def orc (as : List Nat) (t : Nat) : Bool :=
  let n := as.length
  (List.range (2 ^ n)).any fun idx =>
    ((List.range n).map fun j =>
      if (idx >>> j) &&& 1 = 1 then as.getD j 0 else 0).sum = t

#eval show IO Unit from do
  let cases : List (String × Nat × List Nat × Nat × Bool) :=
    [ -- small-n path (shared smallN section)
      ("n2 t=0",      2, [3,5], 0, true)
    , ("n2 t=8",      2, [3,5], 8, true)
    , ("n2 t=4",      2, [3,5], 4, false)
    , ("n3 t=11",     3, [2,4,6], 11, false)
    , ("n3 t=12",     3, [2,4,6], 12, true)
      -- general path, small
    , ("n4 t=6",      4, [3,4,5,6], 6, true)
    , ("n4 t=1",      4, [3,4,5,6], 1, false)
    , ("n5 t=9",      5, [1,3,5,7,9], 9, true)     -- odd h=2
    , ("n5 t=24",     5, [1,3,5,7,9], 24, true)     -- 3+5+7+9
    , ("n5 t=25",     5, [1,3,5,7,9], 25, true)     -- all
      -- WIDTH-BLINDNESS: half-sums beyond 2^(2h+2) — fixed-pass radix
      -- would mis-sort these; merge must not care (1-step w-bit compares)
    , ("n8 hugevals 1203", 8, [400,401,402,403,3,3,3,3], 1203, true)   -- 400+401+402
    , ("n8 hugevals 6",    8, [400,401,402,403,3,3,3,3], 6, true)      -- 3+3
    , ("n8 hugevals 807",  8, [400,401,402,403,3,3,3,3], 807, true)   -- 400+401+3+3
    , ("n8 hugevals 799",  8, [400,401,402,403,3,3,3,3], 799, false)  -- no subset reaches
    , ("n4 2^20 elem t=8", 4, [1,2,2^20,4], 8, false)                  -- wrap-NO
    , ("n4 2^20 elem hit", 4, [1,2,2^20,4], 2^20+4, true)
    , ("n7 dupmin t=3",  7, [1,1,1,1,1,1,1], 3, true)
    , ("n7 dupmin t=8",  7, [1,1,1,1,1,1,1], 8, false)
    , ("n8 all5 t=9",    8, [5,5,5,5,5,5,5,5], 9, false)
    , ("n8 all5 t=40",   8, [5,5,5,5,5,5,5,5], 40, true)
    , ("n8 all5 t=41",   8, [5,5,5,5,5,5,5,5], 41, false)
      -- huge t (wrap complements; t > Σa)
    , ("n6 hugeT",     6, [2,4,6,8,10,12], 2^40, false)
    ]
  let mut bad := 0
  for (nm, n, as, t, exp) in cases do
    let o := orc as t
    let v2 := runV2 n as t 400000
    let v1 := runV1 n as t 400000
    let ok := (o == exp) && (v2 == some exp) && (v1 == some exp)
    unless ok do
      bad := bad + 1
      IO.println s!"  FAIL {nm}: oracle={o} expected={exp} prog2={v2} prog={v1}"
  IO.println s!"QUICK-BATTERY: {cases.length - bad}/{cases.length} pass (oracle, prog2, prog all agree)"

end Check2b
