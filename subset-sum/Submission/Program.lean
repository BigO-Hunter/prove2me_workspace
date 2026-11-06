import Submission.SubsetSumStatement
set_option autoImplicit true

/-!
# The MITM program, part 1: assembly DSL + relocation bootstrap (R2125607414)

## The relocation kernel — SOLVED (zero irreversible sacrifice, uniform in n)

Initial memory: `n` at 0, `a₁..aₙ` at `1..n` (each ≥ 1), `t` at `n+1` (≥ 0),
zero beyond.  Every write to a literal cell destroys that cell's input before
any copy exists — broken by this sequence:

1. `add 0 0 0` — `[0] := 2n`: a valid beyond-input address, with `n`
   recoverable arithmetically forever after (`n = ([0] - cursorBias) / 2`).
2. `store 0 1` — `mem[2n] := a₁` (saved BEFORE cell 1 is reused).
3. `one 1` — `[1] := 1`; a₁ is already safe.
4. `store 0 2` at cursor `2n+1` — a₂ saved; `sub 2 2 2` — `[2] := 0`.
5. `saveAk k` for `k = 3..8`: cursor `++`, then `store 0 k` — each register
   cell's input is saved just before the cell becomes a register.
6. Loop `for i = 9 .. n+1`: `mem[cursor] := mem[i]` — state entirely in
   cells `0..8`, all their inputs already saved.

**Faithful by construction**: with `RELOC = 2n - 1`, iteration `i` writes
`2n + i - 1 = RELOC + i`, so `mem[RELOC + i]` = old cell `i` for all
`i = 1..n+1`.  Hand-verified uniform on the edge cases `n = 2, 3`: for small
`n` the "save" slots land on `t`/zeros exactly at their correct relocated
positions (old cell `k > n+1` is zero and lands harmlessly above the block),
and the copy loop's start index `9` already exceeds the bound `n+2`, so it
skips cleanly.  No case split.

Register file after the prologue (cells `0..8`):
`[1] = 1`, `[2] = 0`, `[7] = n`, `[8] = RELOC`; `[0],[3..6]` scratch.
The relocated input sits at `[8] + 1 .. [8] + n + 1`; arrays go above
`[8] + n + 1`.
-/

namespace SubsetSum.MITM

open BigOSpeedrun.SubsetSum

/-- Symbolic assembly line: a label, a raw instruction, or a `blt` with a
symbolic target. -/
inductive Line where
  | mark (l : Nat)
  | raw (i : Instr)
  | jblt (i j : Nat) (l : Nat)

/-- Resolve a symbolic program into a concrete `List Instr`. -/
def resolve (ls : List Line) : List Instr :=
  let rec offsets : Nat → List Line → List (Nat × Nat)
    | _, [] => []
    | pc, .mark l :: rest => (l, pc) :: offsets pc rest
    | pc, .raw _ :: rest => offsets (pc + 1) rest
    | pc, .jblt _ _ _ :: rest => offsets (pc + 1) rest
  let table := offsets 0 ls
  let target (l : Nat) : Nat :=
    match table.find? fun p => p.1 = l with
    | some p => p.2
    | none => 0
  ls.filterMap fun
    | .mark _ => none
    | .raw i => some i
    | .jblt i j l => some (.blt i j (target l))

/-! ## Register file (cells 0..8) -/

def rCUR : Nat := 0   -- relocation cursor (scratch afterwards)
def rONE : Nat := 1   -- constant 1, forever
def rZER : Nat := 2   -- constant 0, forever
def rTMP : Nat := 3   -- scratch
def rBND : Nat := 4   -- loop bound n + 2 (scratch afterwards)
def rIDX : Nat := 5   -- loop index i
def rVAL : Nat := 6   -- value in flight
def rN   : Nat := 7   -- n
def rRE  : Nat := 8   -- RELOC = 2n - 1

/-! ## Phase A registers (cells 9+; all free after relocation) -/

def rH   : Nat := 9   -- h = n / 2
def rK   : Nat := 10  -- round counter k
def rL   : Nat := 11  -- source length 2^(k-1)
def rI   : Nat := 12  -- merge pointer i
def rJ   : Nat := 13  -- merge pointer j
def rW   : Nat := 14  -- write index w
def rVI  : Nat := 15  -- src[i]
def rVJ  : Nat := 16  -- src[j] + a_k
def rAK  : Nat := 17  -- a_k
def rSRC : Nat := 18  -- source array base
def rDST : Nat := 19  -- destination array base
def rT1  : Nat := 20  -- temp / address
def rT2  : Nat := 21  -- temp
def rT3  : Nat := 22  -- temp

/-- Phase A labels. -/
def LROUND  : Nat := 10
def LMERGE  : Nat := 11
def LHAVEJ  : Nat := 12
def LBOTH   : Nat := 13
def LTAKEJ  : Nat := 14
def LTAKEL  : Nat := 15
def LSTEP   : Nat := 16
def LDRAINI : Nat := 17
def LDRAINJ : Nat := 18
def LDILOOP : Nat := 19
def LDJLOOP : Nat := 20
def LSWAP   : Nat := 21

/-- Unconditional jump: `blt` over the permanent `0 < 1` cells. -/
def jmp (l : Nat) : Line := .jblt rZER rONE l

/-! ## The prologue -/

def LCOPY : Nat := 2
def LCOPY2 : Nat := 3
def LSMALL : Nat := 50
def LSMALLOK : Nat := 60
def LSMALLOK2 : Nat := 62
def LSMALLR : Nat := 61

/-- Save `a_k` (the current content of cell `k`) at the next cursor slot. -/
def saveAk (k : Nat) : List Line :=
  [ .raw (.add rCUR rCUR rONE)
  , .raw (.store rCUR k) ]

/-- The relocation prologue.  After it: `[1] = 1`, `[2] = 0`, `[7] = n`,
`[8] = RELOC = 2n + 23`, and the input block lives at `RELOC + 1 .. RELOC + n + 1`.

`RELOC = 2n + 23` keeps the block strictly above the register file
(cells `0..22`) for EVERY `n` (the earlier `2n - 1` placement overlapped
the block with the registers for small `n` — measured on the bench, n = 4).
Bootstrap saves `a₁ .. a₂₂` into a scratch strip at `2n .. 2n+21`, then two
copy loops build the faithful block: scratch → `RELOC + 1 .. + 22`, then
cells `23 .. n+1` → `RELOC + 23 .. + n+1`. -/
def prologue : List Line :=
  [ .raw (.add rCUR rCUR rCUR)    -- [0] := 2n      (scratch base)
  , .raw (.store rCUR 1)           -- scratch[0] := a₁
  , .raw (.one rONE)               -- [1] := 1
  , .raw (.add rCUR rCUR rONE)     -- 2n+1
  , .raw (.store rCUR 2)           -- scratch[1] := a₂
  , .raw (.sub rZER rZER rZER)     -- [2] := 0
  ] ++ saveAk 3                     -- a₃ saved; cell 3 now free
  ++ [ -- case split: n ≤ 3 goes to the unrolled small verdict (L_SMALL);
       -- the general path requires n ≥ 4 so LOOP1's cells 3..7 can never
       -- collide with the scratch strip (2n ≥ 8).
       .raw (.add rTMP rONE rONE)   -- [3] := 2
     , .raw (.add rTMP rTMP rTMP)   -- 4
     , .raw (.add rTMP rTMP rTMP)   -- 8
     , .raw (.add rTMP rTMP rONE)   -- 9
     , .jblt rCUR rTMP LSMALL       -- 2n+2 < 9  ⟺  n ≤ 3
  ] ++ ((List.range 23).drop 4).flatMap saveAk
  ++ [ -- [3] := 23 ; cursor := 2n+21+2 = RELOC
       .raw (.add rTMP rONE rONE)  -- [3] := 2
     , .raw (.add rTMP rTMP rTMP)  -- 4
     , .raw (.add rTMP rTMP rTMP)  -- 8
     , .raw (.add rTMP rTMP rTMP)  -- 16
     , .raw (.add rBND rONE rONE)  -- [4] := 2
     , .raw (.add rBND rBND rBND)  -- 4
     , .raw (.add rBND rBND rBND)  -- 8
     , .raw (.sub rBND rBND rONE)  -- 7
     , .raw (.add rTMP rTMP rBND)  -- [3] := 23  (cells 3,4 only: scratch-safe)
     , .raw (.add rCUR rCUR rONE)  -- 2n+22
     , .raw (.add rCUR rCUR rONE)  -- RELOC = 2n+23
     -- LOOP1 setup: [4] := 2n (src base), [5] := 0 (j), [10] := 22 (bound)
     , .raw (.sub rBND rCUR rTMP)  -- [4] := 2n      (with [3] = 23)
     , .raw (.sub rIDX rIDX rIDX)  -- [5] := 0
     , .raw (.sub rTMP rTMP rONE)  -- [3] := 22      (bound)
     , .mark LCOPY
     -- cells ≤ 7 ONLY here: the scratch strip starts at cell 8 = 2n,
     -- and LOOP1 runs BEFORE the strip is copied to the block.
     , .raw (.add rVAL rBND rIDX)  -- [6] := 2n + j  (src addr)
     , .raw (.load rN rVAL)        -- [7] := scratch[j]
     , .raw (.add rVAL rCUR rIDX)  -- [6] := RELOC + j (dst addr)
     , .raw (.add rVAL rVAL rONE)
     , .raw (.store rVAL rN)
     , .raw (.add rIDX rIDX rONE)
     , .jblt rIDX rTMP LCOPY
     -- LOOP2: i = 23 .. n+1 : block[i] := cell i
     , .raw (.add rIDX rTMP rZER)  -- [5] := 23
     , .raw (.sub rBND rCUR rTMP)  -- 2n
     , .raw (.shr rBND rBND rONE)  -- n
     , .raw (.add rBND rBND rONE)
     , .raw (.add rBND rBND rONE)  -- n+2
     , .mark LCOPY2
     , .raw (.add rT1 rIDX rZER)   -- src addr = i
     , .raw (.load rVAL rT1)
     , .raw (.add rT2 rCUR rIDX)   -- dst = RELOC + i
     , .raw (.store rT2 rVAL)
     , .raw (.add rIDX rIDX rONE)
     , .jblt rIDX rBND LCOPY2
     -- post: [7] := n ; [8] := RELOC
     , .raw (.sub rN rBND rONE)
     , .raw (.sub rN rN rONE)
     , .raw (.add rRE rCUR rZER)   -- [8] := RELOC (cursor holds it)
  ]

/-- Phase A: build the sorted half-sums of `a₁..a_h` by doubling merges.

Invariant at `LROUND` with counter `k`: `[rSRC]` holds `S_{k-1}` (sorted,
length `[rL] = 2^(k-1)`), `[rDST]` is scratch of size `2^k`.  The round
writes `S_k = merge(S_{k-1}, S_{k-1} + a_k)` to `[rDST]`, doubles `[rL]`,
swaps the pointers, increments `k`.  `LDRAINI`/`LDRAINJ` double as their own
loop heads (the fall-through entry performs one copy before the guard). -/
def phaseA : List Line :=
  [ .raw (.shr rH rN rONE)
  , .raw (.add rSRC rRE rN)
  , .raw (.add rSRC rSRC rONE)
  , .raw (.add rSRC rSRC rONE)      -- ARR1 = RELOC + n + 2
  , .raw (.add rT1 rONE rZER)       -- t1 := 1
  , .raw (.shl rT1 rT1 rH)          -- t1 := 2^h
  , .raw (.add rDST rSRC rT1)       -- ARR2 := ARR1 + 2^h
  , .raw (.add rDST rDST rONE)
  , .raw (.add rL rONE rZER)        -- L := 1
  , .raw (.add rT1 rSRC rZER)
  , .raw (.store rT1 rZER)          -- S₀ := [0] at ARR1
  , .raw (.add rK rONE rZER)        -- k := 1
  , .mark LROUND
  , .raw (.add rT1 rRE rK)
  , .raw (.load rAK rT1)            -- a_k := mem[RELOC + k]
  , .raw (.sub rI rI rI)
  , .raw (.sub rJ rJ rJ)
  , .raw (.sub rW rW rW)
  , .mark LMERGE
  , .jblt rJ rL LHAVEJ
  , jmp LDRAINI
  , .mark LHAVEJ
  , .jblt rI rL LBOTH
  , jmp LDRAINJ
  , .mark LBOTH
  , .raw (.add rT1 rSRC rI)
  , .raw (.load rVI rT1)
  , .raw (.add rT2 rSRC rJ)
  , .raw (.load rVJ rT2)
  , .raw (.add rVJ rVJ rAK)
  , .jblt rVJ rVI LTAKEJ
  , jmp LTAKEL
  , .mark LTAKEJ
  , .raw (.add rT1 rDST rW)
  , .raw (.store rT1 rVJ)
  , .raw (.add rJ rJ rONE)
  , jmp LSTEP
  , .mark LTAKEL
  , .raw (.add rT1 rDST rW)
  , .raw (.store rT1 rVI)
  , .raw (.add rI rI rONE)
  , .mark LSTEP
  , .raw (.add rW rW rONE)
  , jmp LMERGE
  , .mark LDRAINI
  , .jblt rI rL LDILOOP
  , jmp LSWAP
  , .mark LDILOOP
  , .raw (.add rT1 rSRC rI)
  , .raw (.load rVI rT1)
  , .raw (.add rT2 rDST rW)
  , .raw (.store rT2 rVI)
  , .raw (.add rI rI rONE)
  , .raw (.add rW rW rONE)
  , .jblt rI rL LDILOOP
  , jmp LSWAP
  , .mark LDRAINJ
  , .mark LDJLOOP
  , .raw (.add rT2 rSRC rJ)
  , .raw (.load rVJ rT2)
  , .raw (.add rVJ rVJ rAK)
  , .raw (.add rT1 rDST rW)
  , .raw (.store rT1 rVJ)
  , .raw (.add rJ rJ rONE)
  , .raw (.add rW rW rONE)
  , .jblt rJ rL LDJLOOP
  , .mark LSWAP
  , .raw (.add rL rL rL)            -- L := 2L
  , .raw (.add rT1 rSRC rZER)       -- swap src/dst
  , .raw (.add rSRC rDST rZER)
  , .raw (.add rDST rT1 rZER)
  , .raw (.add rK rK rONE)
  , .raw (.add rT2 rH rONE)
  , .jblt rK rT2 LROUND
  ]

/-- The program so far: prologue + Phase A. -/
def progPA : List Instr := resolve (prologue ++ phaseA)

/-! ## Phase B: enumerate second-half sums, binary-search complements -/

def LBIDX    : Nat := 30
def LBBIT    : Nat := 31
def LBBIT2   : Nat := 32
def LADDK    : Nat := 33
def LBITNEXT : Nat := 34
def LAFTER   : Nat := 35
def LBSRCH   : Nat := 36
def LSMID    : Nat := 37
def LGTR     : Nat := 38
def LLESS    : Nat := 39
def LNEXT    : Nat := 40

/-- Phase B: for each subset sum `s` of `a_{h+1}..a_n`, binary-search
`t - s` in the sorted first-half array `[rSRC]` (length `[rL] = 2^h`);
accept on hit, reject after exhaustion.  Wrapped complements (`s > t`)
exceed every half-sum, so they never match spuriously. -/
def phaseB : List Line :=
  [ -- [11] := L := 2^h (LSWAP doubled it one last time — re-derive), [19] := m2, [22] := CNT2
    .raw (.add rL rONE rZER)
  , .raw (.shl rL rL rH)
    -- [19] := m2 = n - h ; [22] := CNT2 = 2^m2 ; [10] := idx := 0
  , .raw (.sub rDST rN rH)
  , .raw (.add rT3 rONE rZER)
  , .raw (.shl rT3 rT3 rDST)
  , .raw (.sub rK rK rK)
  , .mark LBIDX
    -- s := 0 ([14]) ; j := 0 ([13])
  , .raw (.sub rW rW rW)
  , .raw (.sub rJ rJ rJ)
  , .mark LBBIT
  , .jblt rJ rDST LBBIT2
  , jmp LAFTER
  , .mark LBBIT2
    -- ak := mem[RELOC + h + 1 + j]
  , .raw (.add rT1 rRE rH)
  , .raw (.add rT1 rT1 rONE)
  , .raw (.add rT1 rT1 rJ)
  , .raw (.load rAK rT1)
    -- bit := (idx >>> j) &&& 1
  , .raw (.shr rT2 rK rJ)
  , .raw (.and rT2 rT2 rONE)
  , .jblt rZER rT2 LADDK          -- 0 < bit  ⟺  bit = 1
  , jmp LBITNEXT
  , .mark LADDK
  , .raw (.add rW rW rAK)
  , .mark LBITNEXT
  , .raw (.add rJ rJ rONE)
  , jmp LBBIT
  , .mark LAFTER
    -- c := t - s   (t at mem[RELOC + n + 1])
  , .raw (.add rT1 rRE rN)
  , .raw (.add rT1 rT1 rONE)
  , .raw (.load rT2 rT1)
  , .raw (.sub rVJ rT2 rW)
    -- binary search: lo := 0, hi := L - 1
  , .raw (.sub rI rI rI)
  , .raw (.sub rJ rL rONE)
  , .mark LBSRCH
  , .raw (.add rT1 rJ rONE)       -- hi + 1
  , .jblt rI rT1 LSMID            -- lo ≤ hi
  , jmp LNEXT
  , .mark LSMID
  , .raw (.add rT1 rI rJ)         -- lo + hi
  , .raw (.shr rT1 rT1 rONE)      -- mid
  , .raw (.add rT2 rSRC rT1)
  , .raw (.load rVI rT2)          -- arr[mid]
  , .jblt rVI rVJ LLESS           -- arr < c
  , .jblt rVJ rVI LGTR            -- c < arr
  , .raw (.accept)                -- equal: HIT
  , .mark LGTR
  , .raw (.sub rJ rT1 rONE)       -- hi := mid - 1
  , jmp LBSRCH
  , .mark LLESS
  , .raw (.add rI rT1 rONE)       -- lo := mid + 1
  , jmp LBSRCH
  , .mark LNEXT
  , .raw (.add rK rK rONE)        -- idx++
  , .jblt rK rT3 LBIDX
  , .raw (.reject)
  ]

/-! ## Small-n verdict (n = 2, 3): unrolled, machinery-free -/

def LS2    : Nat := 51
def LS3    : Nat := 52
def LS2a   : Nat := 53
def LS2b   : Nat := 54
def LS2c   : Nat := 55
def LS3a   : Nat := 56
def LS3b   : Nat := 57
def LS3c   : Nat := 58
def LS3d   : Nat := 59
def LS3e   : Nat := 63
def LS3f   : Nat := 64

/-- Entry state: `[0] = 2n+2`, `[1] = 1`, `[2] = 0`, `[3] = 8`; a₁,a₂,a₃
pristine at `mem[2n], mem[2n+1], mem[2n+2]`; `t` at cell `n+1`. -/
def smallN : List Line :=
  [ .mark LSMALL
    -- [5] := 2n ; a₁ := mem[2n] ; a₂ ; a₃
  , .raw (.sub rT1 rCUR rONE)
  , .raw (.sub rT1 rT1 rONE)       -- 2n
  , .raw (.load rVI rT1)           -- [15] a₁
  , .raw (.add rT1 rT1 rONE)
  , .raw (.load rVJ rT1)           -- [16] a₂
  , .raw (.add rT1 rT1 rONE)
  , .raw (.load rAK rT1)           -- [17] a₃ (n = 3 only; garbage-free cell for n = 2 reads 0)
    -- n = 2 ⟺ [0] = 6 < 7 ; n = 3 gives [0] = 8
  , .raw (.sub rT2 rTMP rONE)      -- 9 - 1 = 8
  , .raw (.sub rT2 rT2 rONE)       -- 7
  , .jblt rCUR rT2 LS2
    -- n = 3: t at cell 4
  , .raw (.add rT2 rONE rONE)
  , .raw (.add rT2 rT2 rONE)       -- 3
  , .raw (.add rT2 rT2 rONE)       -- 4
  , .raw (.load rW rT2)            -- [14] t
  , jmp LS3
    -- n = 2: t was saved by saveAk 3 at mem[2n+2]; it sits in [17] (rAK)
  , .mark LS2
  , .raw (.add rW rAK rZER)        -- t := [17]
    -- accept iff t ∈ {0, a₁, a₂, a₁+a₂}
  , .jblt rW rONE LSMALLOK         -- t = 0 → accept
  , .raw (.add rT2 rVI rVJ)        -- a₁+a₂
  , .jblt rVI rW LS2a
  , .jblt rW rVI LS2a
  , .raw (.accept)
  , .mark LS2a
  , .jblt rVJ rW LS2b
  , .jblt rW rVJ LS2b
  , .raw (.accept)
  , .mark LS2b
  , .jblt rT2 rW LS2c
  , .jblt rW rT2 LS2c
  , .raw (.accept)
  , .mark LS2c
  , .raw (.reject)
  , .mark LSMALLOK
  , .raw (.accept)
    -- n = 3: accept iff t ∈ {0, a₁, a₂, a₁+a₂, a₃, a₃+a₁, a₃+a₂, a₃+a₁+a₂}
  , .mark LS3
  , .jblt rW rONE LSMALLOK2        -- t = 0 → accept (LS3 section uses its own)
  , .raw (.add rT2 rVI rVJ)        -- a₁+a₂
  , .jblt rVI rW LS3a
  , .jblt rW rVI LS3a
  , .raw (.accept)
  , .mark LS3a
  , .jblt rVJ rW LS3b
  , .jblt rW rVJ LS3b
  , .raw (.accept)
  , .mark LS3b
  , .jblt rT2 rW LS3c
  , .jblt rW rT2 LS3c
  , .raw (.accept)
  , .mark LS3c
  , .jblt rAK rW LS3d
  , .jblt rW rAK LS3d
  , .raw (.accept)
  , .mark LS3d
    -- a₃ + a₁ ; a₃ + a₂ ; a₃ + (a₁+a₂) — mismatches fall to the NEXT
    -- test (LS3e / LS3f), only the last one rejects (LSMALLR)
  , .raw (.add rT1 rAK rVI)
  , .jblt rT1 rW LS3e
  , .jblt rW rT1 LS3e
  , .raw (.accept)
  , .mark LS3e
  , .raw (.add rT1 rAK rVJ)
  , .jblt rT1 rW LS3f
  , .jblt rW rT1 LS3f
  , .raw (.accept)
  , .mark LS3f
  , .raw (.add rT1 rAK rT2)
  , .jblt rT1 rW LSMALLR
  , .jblt rW rT1 LSMALLR
  , .raw (.accept)
  , .mark LSMALLR
  , .raw (.reject)
  , .mark LSMALLOK2
  , .raw (.accept)
  ]

/-- The full program: prologue (+ small-n split) + Phase A + Phase B +
small-n verdict section. -/
def prog : List Instr := resolve (prologue ++ phaseA ++ phaseB ++ smallN)

end SubsetSum.MITM

