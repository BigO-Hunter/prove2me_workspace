import Submission.Bench
import Submission.Prog2
set_option autoImplicit true

/-!
# Rock2d — Lane-1B worst-case scan + small-n constant sweep (R2125607749)

Rock2b/c measured exhaustive-NO instances — but that only exercises the scan's
i-sweep.  scanB's true worst case moves BOTH pointers: j sweeps 2^m−1 → 0 and
then i sweeps 0 → H−1, accepting on the LAST comparison.  That happens at
t = maxA = Σ(first half): witness = all-first-half + empty-second-half, found
only after the full j descent and full i ascent.  Iterations ≈ 2^m + 2^h
(vs 2^h for exhaustive-NO) — for odd n the scan constant TRIPLES (8→24 per
2^(n/2)).  SolvedInTime quantifies over ALL instances, so L4's C must survive
this t.  Small n (4..11) also matters: the constant C·2^(n/2) has to absorb
the 233-step prologue at 2^(n/2) = 4..32.

Three scan shapes per n ∈ {4..11, 15}, prog2 only (a_i = i+7):
  (a) t = Σa+1   — exhaustive NO: i-sweep only, 2^h iterations
  (b) t = maxA   — YES at the last comparison: full j-sweep + full i-sweep
  (c) t = 0      — empty subset: j-sweep only, 2^m iterations
-/

namespace Rock2d

open BigOSpeedrun.SubsetSum SubsetSum.MITM SubsetSum.MITM.Bench

def bitsOf (as : List Nat) (t : Nat) : Nat := Nat.log2 (as.foldl max t) + 1
def wOf (n : Nat) (as : List Nat) (t : Nat) : Nat := wordLength n (bitsOf as t)
def fuelOf (n : Nat) : Nat :=
  400 * 2 ^ (n / 2) + (40 * n + 200) * 2 ^ (n - n / 2) + 5000

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

def pcA2 : Nat := 86
def pcSCAN : Nat := 224

def asOf (n : Nat) : List Nat := (List.range n).map fun i => i + 7
def maxA (n : Nat) : Nat := (asOf n |>.take (n / 2)).sum

#eval show IO Unit from do
  IO.println "== worst-case scan shapes + small-n constants (prog2, a_i = i+7) =="
  IO.println "   shapes: NO=Sigma+1 (i-sweep) | LASTYES=maxA (j-sweep THEN i-sweep, accept at last cmp) | ZERO=0 (j-sweep)"
  for n in [4, 5, 6, 7, 8, 9, 10, 11, 15] do
    let as := asOf n
    let h := n / 2
    let shapes : List (String × Nat × Bool) :=
      [("NO", as.sum + 1, false), ("LASTYES", maxA n, true), ("ZERO", 0, true)]
    for (nm, t, expV) in shapes do
      match runMarks prog2 pcA2 pcSCAN n as t with
      | some (tot, sa, sb, v) =>
        let gen := sb - sa
        let scan := tot - sb
        let flag := if v == expV then "" else "  <-- VERDICT MISMATCH"
        IO.println s!"n={n} h={h} {nm}: prologue={sa} gen+sort={gen} scan={scan} total={tot} v={v}{flag}"
        IO.println s!"    per-2^(n/2) ×1000: gen={1000 * gen / 2 ^ h} scan={1000 * scan / 2 ^ h} machine={1000 * (tot - sa) / 2 ^ h} all-in={1000 * tot / 2 ^ h}"
      | none => IO.println s!"n={n} {nm}: FUEL EXHAUSTED"

end Rock2d
