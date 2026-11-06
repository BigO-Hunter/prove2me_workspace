import math
cxR6 = [(1,184811440),(2,107199136),(3,50583808),(4,53478128),(5,33031680),(6,27611408),
 (7,14767104),(8,20195472),(9,6217728),(10,14119424),(11,5051904),(12,13742960),
 (13,4663296),(14,14864256),(15,4849504),(16,13014320),(17,10196912),(18,33371712),
 (19,13601280),(20,22774048),(22,44038192),(23,16479408),(24,4048),(529,8193152),
 (552,199193984)]
S = sum(n for w,n in cxR6); wmax = max(w for w,n in cxR6); rankSum = sum(w*n for w,n in cxR6)
mc = 576; Wc = 207387136
print("S (sum n_w) =", S); print("wmax =", wmax); print("rankSum =", rankSum)
# hnum: 2*S*(2*wmax+1)^e <= (2*mc)^e  <=>  2*S <= ((2*mc)/(2*wmax+1))^e
base = (2*mc)/(2*wmax+1)
print("ratio (2mc)/(2wmax+1) =", base)
e_need = math.log(2*S)/math.log(base)
print("min e satisfying hnum =", e_need, "-> p0 must be >=", math.ceil(e_need))
# hp0: p0 <= 2 + mc*log(rankSum)
bound = 2 + mc*math.log(rankSum)
print("hz0 upper bound 2+mc*ln(rankSum) =", bound)
print("feasible window:", math.ceil(e_need), "<=", "p0", "<=", int(bound))