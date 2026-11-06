import Submission.Bench

/-! Diagnostics for the exec walk: pc layout + prologue contract on many n. -/

open BigOSpeedrun.SubsetSum SubsetSum.MITM Bench

/-- Number of emitted instructions before the mark `l`. -/
def emittedBefore : List Line → Nat → Nat
  | [], _ => 0
  | .mark l' :: rest, l => if l' = l then 0 else emittedBefore rest l
  | .raw _ :: rest, l => 1 + emittedBefore rest l
  | .jblt _ _ _ :: rest, l => 1 + emittedBefore rest l

def full : List Line := prologue ++ phaseA ++ phaseB ++ smallN

#eval (resolve full).length          -- 249
#eval (resolve prologue).length      -- 86
#eval emittedBefore full LROUND      -- 86 : Phase A entry pc
#eval emittedBefore prologue LCOPY   -- 65
#eval emittedBefore prologue LCOPY2  -- 77
#eval emittedBefore full LSMALL      -- 192

/-- Analytic prologue step count (LOOP1 = 22x7, LOOP2 = 6 per iteration). -/
def cSteps (n : Nat) : Nat := 227 + 6 * (if n ≤ 20 then 1 else n - 20)

def mkInst (n : Nat) : Instance n :=
  ⟨fun i => i.val + 7, 2 * n, fun _ => Nat.succ_pos _⟩

#eval show IO Unit from do
  for n in [4, 5, 6, 19, 20, 21, 22, 23, 30] do
    let x : Instance n := mkInst n
    let w := wordLength n x.bits
    let mem0 := loadWords w x.input
    let P := resolve full
    let reloc := 2 * n + 23
    -- exact horizon
    let (mem, _) := execMem P (fun _ => 0) (cSteps n) 0 0 mem0
    let block := (List.range (n + 1)).map fun i => (mem (reloc + 1 + i)).toNat
    let want := (List.range (n + 1)).map fun i => (x.input.getD (1 + i) 0)
    -- one step short of post: [8] not yet RELOC (post's last instr sets [8])
    let (mem1, _) := execMem P (fun _ => 0) (cSteps n - 1) 0 0 mem0
    let ok8 := (mem1 8).toNat ≠ reloc
    IO.println s!"n={n} C={cSteps n} regs=({(mem 1).toNat},{(mem 2).toNat},{(mem 7).toNat},{(mem 8).toNat}) blockOK={block == want} pinsC={ok8 && (mem 1).toNat == 1 && (mem 7).toNat == n}"
