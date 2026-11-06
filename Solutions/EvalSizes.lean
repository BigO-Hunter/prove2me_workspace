import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
open IntMul.Kappa.R8.Bit.Oppbank.NB

#eval cs1.length
#eval cs2.length
#eval (cs1.flatMap fun chk => chk.2.1).length
#eval (cs2.flatMap fun chk => chk.2.1).length
