import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankProjB

open IntMul.Kappa.R8.Bit.Oppbank.NB
open IntMul.Kappa.R8.Bit.Oppbank.ProjB
open IntMul.Kappa.R8.Bit.Oppbank.LocGrecDense

/-! Ground-truth eval: sizes and rank histograms of cs1 / cs2 (computable copies). -/

def dimCF' (c : ℕ) : ℕ :=
  cond (Nat.beq c 0) 0
    (cond (Nat.beq c 1) 23
      (cond (Nat.blt c 1773) 22 (dimF (Nat.sub c 1773))))

def rkC' (a b : ℕ) : ℕ :=
  let a1 := dimCF' a; let b1 := dimCF' b
  cond (Nat.blt a1 b1) (Nat.sub b1 a1) (Nat.sub a1 b1)

def mvR8 (cs : List LChunk) : List ℕ :=
  cs.flatMap fun chk => chk.2.1.map fun mv => rkC' mv.2 chk.1

#eval nNodes
#eval (recs).length
#eval (mvR8 cs1).length
#eval (List.range 26).map fun r => (mvR8 cs1).count r
#eval (mvR8 cs2).length
#eval (List.range 26).map fun r => (mvR8 cs2).count r
#eval cs1.length
#eval cs2.length
