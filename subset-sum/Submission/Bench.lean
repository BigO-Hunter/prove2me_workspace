import Submission.Program
set_option autoImplicit true

/-!
# Test bench (R2125607414): run the emitted program on concrete instances.

`execMem` mirrors the statement's `exec` case-for-case but threads the final
memory out — TEST-ONLY diagnostics; the statement's `exec` stays the
authority (equivalence of the boolean parts is a later lemma, not assumed
here).

Checks on `n = 4`, `a = [3, 4, 5, 6]`, `t = 6` (so `h = 2`, `RELOC = 2n+23 = 31`,
`ARR1 = RELOC+n+2 = 37`, result of Phase A lands in `ARR1` since `h` is even):
- registers: `[7] = n = 4`, `[8] = RELOC = 31`, `[1] = 1`, `[2] = 0`
- relocated input: `mem[32..35] = [3, 4, 5, 6]`, `mem[36] = t = 6`
- Phase A: `mem[37..40] = [0, 3, 4, 7]` — the sorted sums of `{3, 4}`
-/

namespace SubsetSum.MITM.Bench

open BigOSpeedrun.SubsetSum SubsetSum.MITM

def execMem {w : Nat} (P : List Instr) (ρ : Nat → BitVec w) :
    (t pc r : Nat) → (m : Nat → BitVec w) → (Nat → BitVec w) × Option Bool
  | 0, _, _, m => (m, none)
  | t + 1, pc, r, m =>
    let write (i : Nat) (v : BitVec w) := fun x => if x = i then v else m x
    match P.getD pc .reject with
    | .one i => execMem P ρ t (pc + 1) r (write i 1)
    | .add i j k => execMem P ρ t (pc + 1) r (write i (m j + m k))
    | .sub i j k => execMem P ρ t (pc + 1) r (write i (m j - m k))
    | .mul i j k => execMem P ρ t (pc + 1) r (write i (m j * m k))
    | .div i j k => execMem P ρ t (pc + 1) r (write i (m j / m k))
    | .rem i j k => execMem P ρ t (pc + 1) r (write i (m j % m k))
    | .and i j k => execMem P ρ t (pc + 1) r (write i (m j &&& m k))
    | .or i j k => execMem P ρ t (pc + 1) r (write i (m j ||| m k))
    | .xor i j k => execMem P ρ t (pc + 1) r (write i (m j ^^^ m k))
    | .shl i j k => execMem P ρ t (pc + 1) r (write i (m j <<< m k))
    | .shr i j k => execMem P ρ t (pc + 1) r (write i (m j >>> m k))
    | .load i j => execMem P ρ t (pc + 1) r (write i (m (m j).toNat))
    | .store i j => execMem P ρ t (pc + 1) r (fun x => if x = (m i).toNat then m j else m x)
    | .rand i => execMem P ρ t (pc + 1) (r + 1) (fun x => if x = i then ρ r else m x)
    | .blt i j l => execMem P ρ t (if m i < m j then l else pc + 1) r m
    | .accept => (m, some true)
    | .reject => (m, some false)

def inst4 : Instance 4 where
  a := fun i => i.val + 3          -- [3, 4, 5, 6]; positivity trivial
  t := 6
  pos := fun _ => Nat.succ_pos _

#eval show IO Unit from do
  let w := wordLength 4 inst4.bits
  let mem0 := loadWords w inst4.input
  let (mem, verdict) := execMem progPA (fun _ => 0) 4000 0 0 mem0
  IO.println s!"verdict: {verdict} (none expected — no halt yet)"
  IO.println s!"regs: [1]={mem 1} [2]={mem 2} [7]={mem 7} [8]={mem 8}"
  IO.println s!"relocated input mem[32..36]: {(List.range 5).map fun i => (mem (32 + i)).toNat}"
  IO.println s!"ARR1 = 37, mem[37..40]: {(List.range 4).map fun i => (mem (37 + i)).toNat}"
  IO.println s!"expect: regs [1]=1 [2]=0 [7]=4 [8]=31; input [3,4,5,6,6]; sums [0,3,4,7]"

end SubsetSum.MITM.Bench
