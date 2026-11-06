import Submission.Bench
import Submission.Prog2
set_option autoImplicit true

/-!
# Rock2c — Lane-1B ODD-n step measurement (R2125607749)

Rock2b's step table is even-n only (12/16/20).  For ODD n the second half has
m = h+1 elements → S₂ has 2·2^h entries → gen+sort and scan constants differ
by parity.  L4's stepBound' = C·2^(n/2) must cover BOTH.  This file measures
prog2 on exhaustive-NO instances at n = 13, 15, 21 (h = 6, 7, 10; m = 7, 8, 11
— n=21 also stress-tests the B2/B3 envelope at maximal asymmetry) plus the
prog control at n = 13, 15.

Same instrument as Rock2b (own copy — root files can't import each other).
-/

namespace Rock2c

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

def measInst (n : Nat) : List Nat × Nat :=
  let as := (List.range n).map fun i => i + 7
  (as, as.sum + 1)

def pcA2 : Nat := 86     -- prologue end (both programs)
def pcSCAN : Nat := 224  -- prog2 scanB entry
def pcPB1 : Nat := 148   -- prog phaseB entry

#eval show IO Unit from do
  IO.println "== odd-n steps, exhaustive-NO (a_i = i+7, t = Σa+1) =="
  for n in [13, 15, 21] do
    let (as, t) := measInst n
    let h := n / 2
    match runMarks prog2 pcA2 pcSCAN n as t with
    | some (tot, sa, sb, v) =>
      let gen := sb - sa
      let scan := tot - sb
      IO.println s!"n={n} (h={h}, m={n - h}, 2^h={2 ^ h}, 2^m={2 ^ (n - h)})"
      IO.println s!"  prog2: prologue={sa} gen+sort={gen} scan={scan} total={tot} verdict={v} (expect false)"
      IO.println s!"    per-2^h ×1000: gen={1000 * gen / 2 ^ h} scan={1000 * scan / 2 ^ h} machine={1000 * (tot - sa) / 2 ^ h}"
      IO.println s!"    per-2^m ×1000: gen={1000 * gen / 2 ^ (n - h)} scan={1000 * scan / 2 ^ (n - h)}"
    | none => IO.println s!"n={n}: FUEL EXHAUSTED"
    if n ≤ 15 then
      match runMarks prog pcA2 pcPB1 n as t with
      | some (tot1, sa1, sb1, v1) =>
        IO.println s!"  prog : prologue={sa1} merge={sb1 - sa1} phaseB={tot1 - sb1} total={tot1} verdict={v1}"
        IO.println s!"    phaseB/2^(n-h)={(tot1 - sb1) / 2 ^ (n - n / 2)} (even-n was 144@12, 184@16)"
      | none => IO.println s!"  prog n={n}: FUEL EXHAUSTED"

end Rock2c
