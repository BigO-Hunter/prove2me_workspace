import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R7_Consts
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-!
# R7 staircase `QHNet` carrier and program wiring (staircase ②, carrier half)

**Construction: S. Jain**, *integer-mult-kappa* round seven — ported and verified
here.  This module is the retarget of the r8 opp-bank carrier
(`Def_IntMul_Kappa_R8_Data_BitOppbankQHNet.lean`, inlined verbatim because that
module's SupDense import chain is not buildable from git — wound R2125609307)
at the staircase boundaries `IntMul.Kappa.R7.Stair`:
`W = 108516254`, `NR = 28866`, `wEnt = 3542`, `wAuxEnd = 32408`, `NL = 32431`.

What is here:

* the wire layout (`wX/wY/wS/wT/wU`), the `gw/ι1/ι2` point coercions through
  the M1 `g1/g2` layout, the XOR gate, the chunk machinery (`LChunk`,
  `chunkInstrs`, `chunkProg`) — all byte-faithful retargets of the r8 shapes;
* the `Ch` edge-family carrier (Defs52 `Ch`: `S, Si, e1, e2, ex, en, ei, ec`)
  with the zero flag-basis carrier `S0/Si0` — **carrier, not certificate**:
  the schedule-derived edge inhabitant (`ch_cert`) and its `cs1/cs2` chunk
  lists land with the run-profile/honest-`Pc` modules (staircase ③ and the
  second half of ②), per the r8 lesson (`Net0Pnd` header): stub edges pass
  trivially but `FormalOK` needs honest projectors;
* the program wiring, **parameterized over the chunk lists** (no empty-list
  stub is claimed to be the schedule): `blk1` = chunks + aux exits on
  `List.range' wEnt NR` (NR = 28866 — the slot growth vs r8 lands here),
  `entI` = entrance edges on `List.range wAuxEnd`, `corrI` = the XOR-combined
  copy-correction triple (the −759/centre gate sharing), `blk2` = entrance ++
  chunks ++ corrections, `prog = blk1 ∘ range v ++ blk2 ∘ range v`,
  `net ch := ⟨prog ch, R7.Stair.ρ⟩`;
* structural size receipts (kernel list-arithmetic, sorry-free) pinning the
  program shape: per-block instruction counts and the full program length;
* the densified node bound keystone: upstream `node_dims` has **64,042**
  nodes, so `codeBound = 1773 + nNodes = 65815` (r8: 64,251; the +1,072-slot
  retarget grows it; derived from the schedule via
  `Solutions/gen_stair_r7.py`, not reused from r8).
-/

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R7.Stair

namespace IntMul.Kappa.R7.Stair.NB

abbrev Wr := Fin W ⊕ Fin Tmp
abbrev NI := Instr Wr (ZMod 2) 529

def gw (g : ℕ) : Wr :=
  if h : g < W then .inl ⟨g, h⟩
  else .inr ⟨(g - W) % Tmp, Nat.mod_lt _ (by decide : 0 < Tmp)⟩

def ι1 (b w : ℕ) : Wr := gw (g1 b w)
def ι2 (a w : ℕ) : Wr := gw (g2 a w)

/-! ## Wire layout (r8 `WireLayout` formulas at the staircase boundaries) -/

def wX (t : ℕ) : ℕ := t
def wY (T : ℕ) : ℕ := v + T
def wS (q : ℕ) : ℕ := wEnt + q
def wT (c : ℕ) : ℕ := wAuxEnd + c
def wU (s : ℕ) : ℕ := NL + s

/-- Densified node ids: `0 .. nNodes - 1` (upstream `node_dims` length), codes
from `1773` (r8 convention: `cLOW/cHIGH/cPT` below, `cND` at and above). -/
def nNodes : ℕ := 64042

def cLOW : ℕ := 0
def cHIGH : ℕ := 1
def cPT (T : ℕ) : ℕ := Nat.add 2 T
def cND (n : ℕ) : ℕ := Nat.add 1773 n

def codeBound : ℕ := 65815

theorem codeBound_eq : codeBound = 1773 + nNodes := by decide

/-! ## Instructions (Defs51/52 shapes, verbatim) -/

/-- XOR gate `x_d ← x_d + x_s` (Defs51). -/
def xorG (d s : Wr) : Instr Wr (ZMod 2) 529 :=
  Instr.gate (fun x y => if x = y then 1 else if x = d ∧ y = s then 1 else 0) {d, s}

/-- One schedule chunk: moves (one chunk edge each) then XOR pairs. -/
abbrev LChunk := ℕ × List (ℕ × ℕ) × List (ℕ × ℕ)

def chunkInstrs (ι : ℕ → Wr) (E : ℕ → ℕ → Edge 529) (ch : LChunk) : List NI :=
  ch.2.1.map (fun mv => Instr.edge (ι mv.1) (E mv.2 ch.1)) ++
    ch.2.2.map fun p => xorG (ι p.1) (ι p.2)

def chunkProg (ι : ℕ → Wr) (E : ℕ → ℕ → Edge 529) (cs : List LChunk) : List NI :=
  cs.flatMap (chunkInstrs ι E)

/-! ## Chosen edges (Defs52 `Ch` / `ch0`), codeBound = 65815 -/

structure Ch where
  S : Matrix (Fin 529) (Fin 23 × Fin 23) ℚ
  Si : Matrix (Fin 23 × Fin 23) (Fin 529) ℚ
  e1 : ℕ → ℕ → ℕ → Edge 529
  e2 : ℕ → ℕ → ℕ → Edge 529
  ex : ℕ → Edge 529
  en : ℕ → ℕ → Edge 529
  ei : ℕ → Edge 529
  ec : ℕ → ℕ → Edge 529

/-- Flag-basis carrier matrices (Defs52 uses `Classical.epsilon` + `FB0`; the
staircase-corner witness replaces these with the honest carrier in the `Pc`
module). -/
def S0 : Matrix (Fin 529) (Fin 23 × Fin 23) ℚ := 0
def Si0 : Matrix (Fin 23 × Fin 23) (Fin 529) ℚ := 0

/-- Carrier `ch0` at the staircase boundaries: program wiring is complete; the
edge families are the neutral `dfltE` until the certificate inhabitant lands
(docstring honesty: this is the r8 `ch0` shape, NOT the schedule witness). -/
def dfltE : Edge 529 := ⟨1, [], 1⟩

def ch0 : Ch where
  S := S0
  Si := Si0
  e1 b o c := dfltE
  e2 a o c := dfltE
  ex b := dfltE
  en a t := dfltE
  ei a := dfltE
  ec a s := dfltE

def entE (ch : Ch) (a w : ℕ) : Edge 529 :=
  if w < v then ch.en a w else if w < wEnt then ch.en a (w - v) else ch.ei a

/-! ## Program wiring (r8 shapes, parameterized over the chunk lists) -/

/-- Stage-one block: chunks then aux exits on slots `wEnt .. wAuxEnd`. -/
def blk1 (ch : Ch) (cs1 : List LChunk) (b : ℕ) : List NI :=
  chunkProg (ι1 b) (ch.e1 b) cs1 ++
    (List.range' wEnt NR).map fun w => Instr.edge (ι1 b w) (ch.ex b)

def corrI (ch : Ch) (a s : ℕ) : List NI :=
  [xorG (ι2 a (wU s)) (ι2 a (wY s)), Instr.edge (ι2 a (wU s)) (ch.ec a s),
    xorG (ι2 a (wX s)) (ι2 a (wU s))]

/-- Entrance edges on local wires `0 .. wAuxEnd` (R6 used `43619`; r8 `wAuxEnd
= 31336`; staircase `wAuxEnd = 32408`). -/
def entI (ch : Ch) (a : ℕ) : List NI :=
  (List.range wAuxEnd).map fun w => Instr.edge (ι2 a w) (entE ch a w)

def blk2 (ch : Ch) (cs2 : List LChunk) (a : ℕ) : List NI :=
  entI ch a ++ (chunkProg (ι2 a) (ch.e2 a) cs2 ++ (List.range v).flatMap (corrI ch a))

/-- The full side program: stage one over all centres, then stage two. -/
def prog (ch : Ch) (cs1 cs2 : List LChunk) : List NI :=
  (List.range v).flatMap (blk1 ch cs1) ++ (List.range v).flatMap (blk2 ch cs2)

/-- The named staircase network for a given certificate. -/
def net (ch : Ch) (cs1 cs2 : List LChunk) : QHNet (ZMod 2) W Tmp 529 :=
  ⟨prog ch cs1 cs2, ρ⟩

/-! ## Structural size receipts (kernel list arithmetic) -/

private theorem sum_const_range (k n : ℕ) :
    ((List.range n).map fun _ => k).sum = n * k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_singleton, List.sum_singleton]
    ring

theorem chunkInstrs_length (ι : ℕ → Wr) (E : ℕ → ℕ → Edge 529) (c : LChunk) :
    (chunkInstrs ι E c).length = c.2.1.length + c.2.2.length := by
  simp [chunkInstrs]

/-- The chunk program of a stage, sized: one edge per move, one gate per pair. -/
theorem chunkProg_length (ι : ℕ → Wr) (E : ℕ → ℕ → Edge 529) (cs : List LChunk) :
    (chunkProg ι E cs).length =
      (cs.map (fun c => c.2.1.length + c.2.2.length)).sum := by
  simp [chunkProg, chunkInstrs_length]

/-- Stage-one block: the chunk program plus one aux exit per side slot
(`NR = 28866` — the slot growth vs r8 is exactly here). -/
theorem blk1_length (ch : Ch) (cs1 : List LChunk) (b : ℕ) :
    (blk1 ch cs1 b).length =
      (cs1.map (fun c => c.2.1.length + c.2.2.length)).sum + NR := by
  simp [blk1, chunkProg_length]

theorem corrI_length (ch : Ch) (a s : ℕ) : (corrI ch a s).length = 3 := rfl

theorem entI_length (ch : Ch) (a : ℕ) : (entI ch a).length = wAuxEnd := by
  simp [entI]

/-- Stage-two block: entrance on all local wires, chunks, then three
instructions per correction slot (`v` of them — the gate sharing). -/
theorem blk2_length (ch : Ch) (cs2 : List LChunk) (a : ℕ) :
    (blk2 ch cs2 a).length =
      wAuxEnd + (cs2.map (fun c => c.2.1.length + c.2.2.length)).sum + 3 * v := by
  simp only [blk2, List.length_append, List.length_flatMap, entI_length, corrI_length,
    chunkProg_length]
  rw [sum_const_range]
  ring

/-- Full program length: `v` stage-one blocks then `v` stage-two blocks. -/
theorem prog_length (ch : Ch) (cs1 cs2 : List LChunk) :
    (prog ch cs1 cs2).length =
      v * ((cs1.map (fun c => c.2.1.length + c.2.2.length)).sum + NR) +
      v * (wAuxEnd + (cs2.map (fun c => c.2.1.length + c.2.2.length)).sum + 3 * v) := by
  simp only [prog, List.length_append, List.length_flatMap, blk1_length, blk2_length,
    sum_const_range]

/-- The wire-level slot identity of the aux-exit bank: stage one emits exactly
`v * NR` aux-exit edges, one per centre per side slot. -/
theorem aux_exit_edge_count (ch : Ch) :
    ((List.range v).flatMap fun b => (List.range' wEnt NR).map fun _ => (ch.ex b)).length
      = v * NR := by
  simp only [List.length_flatMap, List.length_map, List.length_range']
  rw [sum_const_range]

end IntMul.Kappa.R7.Stair.NB
