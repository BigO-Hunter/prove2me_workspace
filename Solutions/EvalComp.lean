import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
open IntMul.Kappa.R8.Bit.Oppbank.NB

def touchLen (l : List (ℕ × ℕ)) : ℕ := (touch l).length

#eval (recs).length
#eval (mixF (fun _ => cLOW)).length
#eval ((mixF (fun _ => cLOW)).map fun i => (touchLen i.2.2)).sum
#eval ((mixI (fun _ => cLOW)).map fun i => (touchLen i.2.2)).sum
#eval ((scat rdS (fun _ => cLOW)).map fun i => (touchLen i.2.2)).sum
#eval ((injo (fun _ => cLOW)).map fun i => (touchLen i.2.2)).sum
#eval ((copyo (fun t => cND (t + 1))).map fun i => (touchLen i.2.2)).sum
#eval ((mixFB 0 12 cND).map fun i => (touchLen i.2.2)).sum
#eval ((mixFB 12 24 cND).map fun i => (touchLen i.2.2)).sum
#eval ((tcopy).map fun i => (touchLen i.2.2)).sum
#eval ((injo cPT).map fun i => (touchLen i.2.2)).sum
#eval ((sweepR 0 20000 cHIGH).map fun i => (touchLen i.2.1)).sum
#eval (recEl (0, 1, 1, []) |>.length)
#eval (recEl (0, 1, 0, []) |>.length)
#eval ((recs.map fun r => (recEl r).length).sum)
