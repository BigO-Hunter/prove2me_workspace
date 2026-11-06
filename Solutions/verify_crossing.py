#!/usr/bin/env python3
"""High-precision verification via Decimal (ln/exp), 50 significant digits."""
from decimal import Decimal as D, getcontext
getcontext().prec = 50

DC = {0:13016, 1:25510, 2:25258, 3:2987, 4:10042, 5:3871, 6:2463, 7:2257,
      8:1427, 9:5371, 10:1114, 11:1660, 12:941, 13:482, 14:715, 15:296,
      16:331, 17:347, 18:851, 19:512, 20:7, 21:4915, 22:4184, 23:10705}
v = 1771
net = {}
def add(w, c): net[w] = net.get(w, 0) + c
nData = 3542 * v; nAux = 2 * 27794 * v; nEc = v * v
add(439, nData); add(21, nData); add(1, 24 * nData)
add(23, nAux); add(483, nAux); add(1, nEc)
for r in range(1, 24):
    tot = 2 * DC[r] * v
    if r <= 11: add(1, r * tot)
    else:
        add(2 * r - 23, tot); add(1, (23 - r) * tot)

bitR7plain = [(1, 1456218305), (3, 4381934), (5, 354200), (7, 3580962), (9, 1526602), (11, 5093396), (13, 2164162), (15, 7948248), (17, 8476006), (18, 6272882), (19, 1639946), (21, 6906900), (23, 61280142), (439, 6272882), (483, 61280142), (485, 545468), (487, 173558), (489, 293986), (491, 580888), (493, 14168), (495, 322322), (497, 17710), (499, 1129898), (501, 127512), (503, 410872), (505, 99176), (507, 1186570), (509, 340032), (511, 322322), (513, 106260), (515, 1583274), (517, 626934), (519, 2854852), (521, 13711082), (523, 4629394), (525, 5653032), (527, 6233920)]

LN529 = D(529).ln()
def mom(h, tau):
    s = D(0)
    for w, c in dict(h).items():
        # (w/529)^tau = exp(tau*(ln w - ln 529))
        s += D(c) * (D(w).ln() - LN529).exp() if False else D(c) * (tau * (D(w).ln() - LN529)).exp()
    return s

def diff(tau): return mom(net.items(), tau) - mom(bitR7plain, tau)

print("== net0P vs bitR7plain (Decimal, 50 digits) ==")
for lbl, tau in [("0.2", D("0.2")), ("0.3", D("0.3")), ("1/3", D(1)/D(3)),
                 ("0.35", D("0.35")), ("0.4", D("0.4")), ("0.5", D("0.5")),
                 ("0.7", D("0.7")), ("0.9", D("0.9")), ("0.99", D("0.99"))]:
    d = diff(tau)
    print(f"tau={lbl:>5}: net-R7plain = {d:.10E}  {'NET EXCEEDS' if d > 0 else 'net<=tgt'}")

# crossings on (0,1)
d001 = diff(D("0.001"))
print("tau=0.001:", f"{d001:.6E}", "EXCEEDS" if d001 > 0 else "below")
# bisection for the down-crossing
lo, hi = D("0.3"), D("0.45")
print("bracket:", f"{diff(lo):.4E}", f"{diff(hi):.4E}")
for _ in range(100):
    mid = (lo + hi) / 2
    if diff(mid) > 0: lo = mid
    else: hi = mid
print("net0P falls below bitR7plain at tau ~", hi)
# peak excess near 0.33
best = max(((D(i)/D(1000), diff(D(i)/D(1000))) for i in range(250, 400)), key=lambda x: x[1])
print("peak excess:", f"{best[1]:.6E}", "at tau ~", best[0])
