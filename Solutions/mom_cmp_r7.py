#!/usr/bin/env python3
"""Compare histMoment at m=529 for Jain.bitR7 / bitR7plain / bitR8.

Decides whether a padding or reduction route could yield BitNetMomStmtG at
(W=108516254, m=529, bitR7). histMoment h m tau = sum n_w * (w/m)^tau.
The tau -> 0+ limit is the total child-call count sum n_w, which no choice of
tau can escape: a candidate network's histogram must have sum n_w <= bitR7's.
"""
from decimal import Decimal, getcontext

getcontext().prec = 60

bitR7 = [(1,1690297301),(3,1356586),(5,354200),(7,3580962),(9,1526602),(11,5093396),
 (13,2164162),(15,7948248),(17,8476006),(18,6272882),(19,1639946),(21,6906900),
 (23,61280142),(439,6272882),(483,61280142),(485,545468),(487,173558),(489,293986),
 (491,580888),(493,14168),(495,322322),(497,17710),(499,1129898),(501,127512),
 (503,410872),(505,99176),(507,1186570),(509,340032),(511,322322),(513,106260),
 (515,1583274),(517,626934),(519,2854852),(521,13711082),(523,4629394),
 (525,5653032),(527,6233920)]

bitR7plain = [(1,1792923209),(3,1438052),(5,842996),(7,3357816),(9,4200812),(11,2160620),
 (13,570262),(15,13622532),(17,1009470),(19,1944558),(21,6843144),(23,59760624),
 (439,6272882),(483,59760624),(485,453376),(487,173558),(489,421498),(491,233772),
 (493,205436),(495,226688),(497,340032),(499,602140),(501,173558),(503,357742),
 (505,283360),(507,690690),(509,389620),(511,102718),(513,184184),(515,584430),
 (517,350658),(519,3021326),(521,13448974),(523,4558554),(525,5649490),(527,6233920)]

bitR8 = [(1,221936407),(2,259926128),(3,38728228),(4,49343602),(5,24609816),(6,8068676),
 (7,3818276),(8,4785242),(9,2992990),(10,1211364),(11,1445136),(12,1331792),
 (13,1080310),(14,669438),(15,2755676),(16,3860780),(17,1933932),(18,364826),
 (19,13388760),(20,587972),(21,1771000),(22,116886),(484,6272882),(506,59760624),
 (507,453376),(508,173558),(509,421498),(510,233772),(511,205436),(512,226688),
 (513,340032),(514,602140),(515,173558),(516,357742),(517,283360),(518,690690),
 (519,389620),(520,102718),(521,184184),(522,584430),(523,350658),(524,3021326),
 (525,13448974),(526,4558554),(527,5649490),(528,6233920)]

m = 529


def moment(h, tau):
    t = Decimal(str(tau))
    return sum(Decimal(n) * (Decimal(w) / m) ** t for w, n in h)


print(f"{'tau':>9} {'bitR7':>22} {'bitR7plain':>22} {'bitR8':>22}  plain<=r7 r8<=r7")
for tau in [0, 0.001, 0.01, 0.1, 0.25, 0.5, 0.75, 0.9, 0.99, 0.999, 1]:
    a, b, c = moment(bitR7, tau), moment(bitR7plain, tau), moment(bitR8, tau)
    print(f"{tau:>9} {a:>22.3f} {b:>22.3f} {c:>22.3f}  "
          f"{str(b <= a):>9} {str(c <= a):>6}")

# crossing points, if any
for name, h in (("bitR7plain", bitR7plain), ("bitR8", bitR8)):
    lo, hi = 0.0, 1.0
    if moment(h, 0) <= moment(bitR7, 0):
        print(f"\n{name}: dominates bitR7 at tau=0 too")
        continue
    if moment(h, 1) <= moment(bitR7, 1):
        for _ in range(90):
            mid = (lo + hi) / 2
            if moment(h, mid) <= moment(bitR7, mid):
                hi = mid
            else:
                lo = mid
        print(f"\n{name}: crosses bitR7 at tau ~ {hi:.9f} "
              f"(dominates only for tau >= that)")
    else:
        print(f"\n{name}: does NOT dominate bitR7 anywhere in (0,1] "
              f"(fails at both tau->0+ and tau=1)")

print("\nsum n_w  :", {k: sum(n for _, n in v)
                       for k, v in (("bitR7", bitR7), ("bitR7plain", bitR7plain),
                                    ("bitR8", bitR8))})
print("rankSum  :", {k: sum(w * n for w, n in v)
                     for k, v in (("bitR7", bitR7), ("bitR7plain", bitR7plain),
                                  ("bitR8", bitR8))})
