import Submission.Prog2
import Submission.Bench

/-! Lane-1 rock battery (R2125607749): prog2's verdict vs brute-force oracle.
15 targeted edges + 8 dup-heavy n=8 + 20 LCG (seed 20261031) + 3 huge-b +
3 full-pipeline n=12.  Run: `lake env lean Prog2Rocks.lean` -/

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

def fuel2 (n : Nat) : Nat := 500 + 8 * n + 220 * 2 ^ (n - n / 2)

def runVerdict (n : Nat) (vals : List Nat) (t : Nat) (hpos : ∀ v ∈ vals, 0 < v) :
    Option Bool :=
  let x := mkInst n vals t hpos
  let w := wordLength n x.bits
  (execMem prog2 (fun _ => 0) (fuel2 n) 0 0 (loadWords w x.input)).2

/-- Brute-force oracle: all subset sums. -/
def sumsOf : List Nat → List Nat
  | [] => [0]
  | v :: rest => let r := sumsOf rest; r ++ r.map (· + v)

def oracle (vals : List Nat) (t : Nat) : Bool := t ∈ sumsOf vals

/-- LCG identical to the Python sim: s' = (1103515245·s + 12345) mod 2^31. -/
def lcg (s : Nat) : Nat := (1103515245 * s + 12345) % 2147483648

def lcgTake : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, s => let s1 := lcg s; s1 :: lcgTake k s1

def lcgCases : Nat → Nat → List (Nat × List Nat × Nat)
  | 0, _ => []
  | k + 1, s =>
    let s1 := lcg s
    let n := 2 + s1 % 6
    let draws := lcgTake (n + 1) s1
    let vals := (draws.take n).map (· % 1000 + 1)
    let t := (draws.getD n 0) % (vals.sum + 2)
    (n, vals, t) :: lcgCases k (draws.getD n 0)

/-- Parity supplement: the low bits of an LCG are weak (the 20-case stream
above only produced even n); this stream forces n ∈ 3..7 from `s % 5`. -/
def lcgCasesOdd : Nat → Nat → List (Nat × List Nat × Nat)
  | 0, _ => []
  | k + 1, s =>
    let s1 := lcg s
    let n := 3 + s1 % 5
    let draws := lcgTake (n + 1) s1
    let vals := (draws.take n).map (· % 1000 + 1)
    let t := (draws.getD n 0) % (vals.sum + 2)
    (n, vals, t) :: lcgCasesOdd k (draws.getD n 0)

def checkCase (tag : String) (n : Nat) (vals : List Nat) (t : Nat) : IO Bool := do
  if h : (vals.all (fun v => decide (0 < v))) = true then
    if vals.length == n then
      let v := runVerdict n vals t (allPos_imp vals h)
      let want := oracle vals t
      let ok := v == some want
      IO.println s!"{if ok then "PASS" else "FAIL"} {tag} n={n} t={t} got={v} want={want}"
      return ok
    else
      IO.println s!"FAIL {tag}: length {vals.length} ≠ n {n}"
      return false
  else
    IO.println s!"FAIL {tag}: nonpositive vals {vals}"
    return false

#eval show IO Unit from do
  let twelve := (List.range 12).map (· + 7)
  let edges : List (String × Nat × List Nat × Nat) :=
    [ ("E01-empty-n2", 2, [3,5], 0)
    , ("E02-single-n2", 2, [3,5], 3)
    , ("E03-all-n2", 2, [3,5], 8)
    , ("E04-gap-n2", 2, [3,5], 4)
    , ("E05-gap-n3", 3, [2,4,7], 5)
    , ("E06-part-n3", 3, [2,4,7], 6)
    , ("E07-all-n3", 3, [2,4,7], 13)
    , ("E08-huget-n4", 4, [3,4,5,6], 2^60)
    , ("E09-hit-n4", 4, [3,4,5,6], 6)
    , ("E10-dupmin-n7", 7, [1,1,1,1,1,1,1], 3)
    , ("E11-dupmin-over-n7", 7, [1,1,1,1,1,1,1], 8)
    , ("E12-dupmin-n8", 8, [1,1,1,1,1,1,1,1], 5)
    , ("E13-dupmin-empty-n8", 8, [1,1,1,1,1,1,1,1], 0)
    , ("E14-dup-gap-n8", 8, [2,2,2,2,2,2,2,2], 7)
    , ("E15-dup-all-n8", 8, [2,2,2,2,2,2,2,2], 16)
    , ("D1-dup8-t0", 8, [5,5,5,5,5,5,5,5], 0)
    , ("D2-dup8-t5", 8, [5,5,5,5,5,5,5,5], 5)
    , ("D3-dup8-t15", 8, [5,5,5,5,5,5,5,5], 15)
    , ("D4-dup8-t20", 8, [5,5,5,5,5,5,5,5], 20)
    , ("D5-dup8-t25", 8, [5,5,5,5,5,5,5,5], 25)
    , ("D6-dup8-t35", 8, [5,5,5,5,5,5,5,5], 35)
    , ("D7-dup8-t40", 8, [5,5,5,5,5,5,5,5], 40)
    , ("D8-dup8-t41-miss", 8, [5,5,5,5,5,5,5,5], 41)
    , ("HB1-hugeb-hit-n6", 6, [2^40+7, 2^40+9, 2^41+3, 5, 2^40+7, 11], (2^40+7)+(2^41+3)+5)
    , ("HB2-hugeb-miss-n6", 6, [2^40+7, 2^40+9, 2^41+3, 5, 2^40+7, 11], 2^42)
    , ("HB3-hugeb-hit-n4", 4, [2^59+1, 2^59+2, 2^59+3, 2^59+4], 2^60+3)
    , ("P12a-hit", 12, twelve, 24)
    , ("P12b-all", 12, twelve, 150)
    , ("P12c-miss", 12, twelve, 151)
    , ("O01-n5-empty", 5, [2,3,5,7,11], 0)
    , ("O02-n5-single", 5, [2,3,5,7,11], 5)
    , ("O03-n5-gap", 5, [2,3,5,7,11], 4)
    , ("O04-n5-pair", 5, [2,3,5,7,11], 13)
    , ("O05-n5-all", 5, [2,3,5,7,11], 28)
    , ("O06-n5-over", 5, [2,3,5,7,11], 29)
    , ("O07-n6-empty", 6, [2,9,4,7,1,5], 0)
    , ("O08-n6-hit", 6, [2,9,4,7,1,5], 7)
    , ("O09-n6-all", 6, [2,9,4,7,1,5], 28)
    , ("O10-n6-over", 6, [2,9,4,7,1,5], 29)
    ]
  let lcgL := ((List.range 20).zip (lcgCases 20 20261031)).map
    (fun p => (s!"L{p.1+1}-lcg", p.2.1, p.2.2.1, p.2.2.2))
  let lcgO := ((List.range 10).zip (lcgCasesOdd 10 999983)).map
    (fun p => (s!"O{p.1+11}-lcgodd", p.2.1, p.2.2.1, p.2.2.2))
  let all := edges ++ lcgL ++ lcgO
  let results ← all.mapM fun (tag, n, vals, t) => checkCase tag n vals t
  IO.println s!"ROCKS TOTAL: pass={results.count true} fail={results.count false} of {all.length}"
