import Submission.SubsetSumStatement

#eval ((75/100 : Rat)).num
#eval ((75/100 : Rat)).den
#eval (((75/100 : Rat)).num).toNat

example : ((75/100 : Rat)).den = 4 := by decide
example : (((75/100 : Rat)).num).toNat = 3 := by decide
example : ((75/100 : Rat)).den = 100 := by decide
