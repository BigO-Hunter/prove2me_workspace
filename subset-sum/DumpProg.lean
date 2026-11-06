import Submission.Program

/-! Lane-1: dump the OLD prog (pc + instruction per line) for the Python sim
(step-count comparison evidence).  `lake env lean DumpProg.lean > prog_dump.txt` -/

open BigOSpeedrun.SubsetSum SubsetSum.MITM

def istr : Instr → String
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

#eval show IO Unit from do
  for ⟨pc, ins⟩ in (List.range prog.length).zip prog do
    IO.println s!"{pc} {istr ins}"
