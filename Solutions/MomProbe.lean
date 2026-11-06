import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNet0P

open IntMul.Kappa
open IntMul.Kappa.R8.Bit.Oppbank.Net0P

#check @histMoment
#check net0P.hist
#eval net0P.hist.length
#eval (net0P.hist.map (·.2)).sum
