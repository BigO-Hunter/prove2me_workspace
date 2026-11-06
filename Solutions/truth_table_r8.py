#!/usr/bin/env python3
"""Domination truth table: net0P.hist vs bitR8 / bitR7plain.

net0P = NB.net (toNB ProjB.ch0P), W=104719230, v=1771, wEnt=3542, wAuxEnd=31336, NR=27794.
Edge families (per a-side / per b-side, from ProjB ch0P):
  en a t (DataR)   : per a, 3542 edges   -> widths [439, 21] + 24*[1]
  ei a   (AuxR)    : per a, 27794 edges  -> widths [23, 483]
  ex b   (AuxR)    : per b, 27794 edges  -> widths [23, 483]
  ec a s (SideR 1) : per a, 1771 edges   -> widths [1]
  e1/e2   (SideR r): chunk moves, rank r = rkC o c; DC1(r) per b-pass (stage1), DC2(r) per a-pass (stage2)
                     r = 0        : no runs
                     1 <= r <= 11 : r * [1]
                     12 <= r <= 23: [2r-23] + (23-r)*[1]
                     r > 23       : UNSAT -> pickE -> dfltE -> no runs
"""
import json

def cn_field(P, i):
    return (P >> (32 * i)) & 0xFFFFFFFF

CN1 = [0,
       7606387081216,
       55808805046126,
       168901881785973771409367274299306216702056534074276018869729942912263215568780089525678354751052489266655318970768602727151327515054601651852028596763777167919079645955958324625422683806,
       31937084640975886314307985140717147638313451778475849278494628151054563607017791006608655722746875743030490749445621121099625533144021590448500117257710457103757693296658642433648961798503667036,
       118623462721834333714207366003601528855833786467865295191229796848093924537016547775352697881052842576171863267545352866474883348364481122439214589093587145981163039901667590095405293446595876603,
       155952509220275631690979608803871153591432212772412147050782886605793958666005062649227720027558801326061842498726927707600856739398979021939930863746274570398700167516414791867446129000049300536876544402747086077965,
       2824194695642645963992122392163592482489722342619352801782484697079381884648382156959914452253096300385992117250287667530996850421154532588919701815682940710988194207051075321585466367820088066625644736642799310782036122271744,
       0,
       149051210906274711701180689321291325867034428652797454482743287669355594324162082175412854971961746353967789405508665977116118632241208266265589759341191695764331217945095606134358984243410168516599365581185101070336,
       0]

CN2 = [0, 0,
       152922670929814314602510057875091100564879478747675310443334022414014181189724733660488513542662051454070848870586813145352900934377343545908851844573244653678055589041537845882633620361418665223368113419332391801611,
       34873586608168428075601575474895176540990581766560104878509736736975954424164215012497417073714394497276066715495244400539726338652898251629000087185248346761900468004762689282,
       87838130361782749065758054070503072742611023643379367882967853488540380725720741828222153297518727462212694945983582288589207818143853371191280125420046067330785534886256617848544409724932486982363637610691287344468797165667,
       2736356565434879994134870168333554894821614297320262737160435580184046875035599582566919045724369781992165858897928163497300810584550902232269264970842261502900394762629980612487420205774681302602155491153894768094086839664640,
       0, 0, 0, 0]

MAXR = 40  # decode generously
DC1 = [sum(cn_field(P, r) for P in CN1) for r in range(MAXR)]
DC2 = [sum(cn_field(P, r) for P in CN2) for r in range(MAXR)]

print("== decoded rank histograms (per pass) ==")
print("DC1:", [(r, DC1[r]) for r in range(MAXR) if DC1[r]])
print("DC2:", [(r, DC2[r]) for r in range(MAXR) if DC2[r]])
print("DC1 total:", sum(DC1), " DC2 total:", sum(DC2))
print("DC1 runs total:", sum(r * DC1[r] for r in range(MAXR)))
print("DC2 runs total:", sum(r * DC2[r] for r in range(MAXR)))

v = 1771
nData = 3542 * v      # en edges total (DataR)
nAux = 2 * 27794 * v  # ei + ex edges total (AuxR)
nEc = v * v           # ec edges total (SideR 1)

# build net0P width multiset counts
net = {}
def add(w, c):
    net[w] = net.get(w, 0) + c

add(439, nData)
add(21, nData)
add(1, 24 * nData)
add(23, nAux)
add(483, nAux)
add(1, nEc)
for r in range(1, MAXR):
    tot = (DC1[r] + DC2[r]) * v
    if tot == 0:
        continue
    if r <= 11:
        add(1, r * tot)
    elif r <= 23:
        add(2 * r - 23, tot)
        add(1, (23 - r) * tot)
    else:
        print(f"  !! rank {r} > 23 present: DC1+DC2 = {DC1[r]+DC2[r]} -> UNSAT, contributes NOTHING (dfltE)")

netwidths = sorted(net)
print("\n== net0P.hist counts ==")
for w in netwidths:
    print(f"  ({w}, {net[w]})")
total_children = sum(net.values())
rank_sum = sum(w * net[w] for w in netwidths)
print("net0P total children:", total_children)
print("net0P rank sum      :", rank_sum)

bitR8 = [(1, 221936407), (2, 259926128), (3, 38728228), (4, 49343602), (5, 24609816), (6, 8068676), (7, 3818276), (8, 4785242), (9, 2992990), (10, 1211364), (11, 1445136), (12, 1331792), (13, 1080310), (14, 669438), (15, 2755676), (16, 3860780), (17, 1933932), (18, 364826), (19, 13388760), (20, 587972), (21, 1771000), (22, 116886), (484, 6272882), (506, 59760624), (507, 453376), (508, 173558), (509, 421498), (510, 233772), (511, 205436), (512, 226688), (513, 340032), (514, 602140), (515, 173558), (516, 357742), (517, 283360), (518, 690690), (519, 389620), (520, 102718), (521, 184184), (522, 584430), (523, 350658), (524, 3021326), (525, 13448974), (526, 4558554), (527, 5649490), (528, 6233920)]

# bitR7plain from Def_IntMul_KappaJainData
import re
src = open("/Users/dmitri.arkhipov/prove2me_workspace/Definitions/Def_IntMul_KappaJainData.lean").read()
m = re.search(r"def bitR7plain : List \(ℕ × ℕ\) :=\s*\n\s*\[(.*?)\]", src, re.S)
bitR7plain = eval("[" + m.group(1) + "]")

def moment(h, tau):
    return sum(c * (w / 529.0) ** tau for (w, c) in h)

def rank_sum(h):
    return sum(w * c for (w, c) in h)

def total(h):
    return sum(c for (w, c) in h)

for name, tgt in [("bitR8", bitR8), ("bitR7plain", bitR7plain)]:
    print(f"\n===== net0P vs {name} =====")
    print(f"{name}: total={total(tgt)} rankSum={rank_sum(tgt)}")
    print(f"net0P : total={total_children} rankSum={rank_sum}")
    print(f"count  arm: net0P <= {name}: {total_children <= total(tgt)}   (diff {total(tgt)-total_children})")
    print(f"rank   arm: net0P rankSum <= {name} rankSum: {rank_sum <= rank_sum(tgt)}  (diff {rank_sum(tgt)-rank_sum})")
    # moment at tau=1 exact
    print(f"tau=1  : net {rank_sum/529} vs tgt {rank_sum(tgt)/529}  net<=tgt: {rank_sum <= rank_sum(tgt)}")
    # sample tau in (0,1)
    import math
    diffs = []
    for i in range(1, 200):
        tau = i / 200
        d = moment(net.items(), tau) - moment(tgt, tau)
        diffs.append((tau, d))
    pos = [x for x in diffs if x[1] > 0]
    print(f"sampled 200 tau in (0,1): net-tgt max={max(diffs,key=lambda x:x[1])[1]:.6f} at tau={max(diffs,key=lambda x:x[1])[0]}, min={min(diffs,key=lambda x:x[1])[1]:.6f}")
    if pos:
        print(f"  !! net0P EXCEEDS {name} at {len(pos)} sampled taus, first at tau={pos[0][0]}, diff={pos[0][1]:.6f}")
    else:
        print(f"  net0P <= {name} at ALL sampled taus in (0,1)")

# cumMass comparison (moment_dom sufficient condition)
def cum_mass(h, x):
    return sum(w * c for (w, c) in h if w <= x)

print("\n== cumMass (net0P vs bitR8) — moment_dom sufficient condition ==")
allx = sorted(set([w for w, _ in net.items()] + [w for w, _ in bitR8]))
viol = [(x, cum_mass(net.items(), x), cum_mass(bitR8, x)) for x in allx if cum_mass(net.items(), x) > cum_mass(bitR8, x)]
print("violations:", len(viol))
for x, a, b in viol[:10]:
    print(f"  x={x}: net={a} > bitR8={b} (by {a-b})")

print("\n== cumMass (net0P vs bitR7plain) ==")
allx2 = sorted(set([w for w, _ in net.items()] + [w for w, _ in bitR7plain]))
viol2 = [(x, cum_mass(net.items(), x), cum_mass(bitR7plain, x)) for x in allx2 if cum_mass(net.items(), x) > cum_mass(bitR7plain, x)]
print("violations:", len(viol2))
for x, a, b in viol2[:10]:
    print(f"  x={x}: net={a} > bitR7plain={b} (by {a-b})")
