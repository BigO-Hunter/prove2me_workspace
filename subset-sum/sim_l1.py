#!/usr/bin/env python3
"""Lane-1 simulator + battery + step measurement (R2125607749).

Simulates the EXACT resolved instruction stream dumped from Lean
(prog2_dump.txt / prog_dump.txt), mirroring SubsetSumStatement.lean's `exec`
semantics instruction-for-instruction (w-bit masking, div/rem-by-zero
conventions, shifts >= w -> 0, blt unsigned, getD-past-end -> reject).
One instruction = one step, halting instruction counted (matches
`run P x rho T` halting within T steps).

Usage:
  python3 sim_l1.py battery   # full battery vs oracle + Lean cross-check
  python3 sim_l1.py steps     # step counts prog2 vs prog, fit C
  python3 sim_l1.py radixdemo # why the 2-pass n/2-digit radix fails
"""
import sys

MASK_CACHE = {}


def log2_floor(x):
    return 0 if x <= 1 else x.bit_length() - 1


def word_length(n, b):
    return 4 * (n + b) + log2_floor((n + 2) ** 4 - 1) + 1


class Mem(dict):
    def __missing__(self, k):
        return 0


def load_dump(path):
    """Parse 'pc instr args' lines; return list indexed by pc."""
    import re
    pat = re.compile(r"^(\d+) (one|add|sub|mul|div|rem|and|or|xor|shl|shr|load|store|rand|blt|accept|reject)( .*)?$")
    prog = []
    for line in open(path):
        line = line.strip()
        m = pat.match(line)
        if not m:
            continue
        pc = int(m.group(1))
        assert pc == len(prog), f"pc gap at {pc}"
        rest = (m.group(3) or "").split()
        prog.append((m.group(2), [int(x) for x in rest]))
    return prog


def simulate(prog, n, vals, t, fuel_cap=200_000_000, pc_ranges=None):
    """Run prog on Instance(n, vals, t). Returns (verdict, steps, segsteps).

    verdict: True/False, or None if fuel_cap exceeded.
    segsteps: {name: count} when pc_ranges given as [(name, lo, hi), ...].
    """
    assert len(vals) == n and all(v >= 1 for v in vals) and t >= 0
    maxv = max([t] + list(vals))
    b = log2_floor(maxv) + 1
    w = word_length(n, b)
    mask = (1 << w) - 1
    mem = Mem()
    mem[0] = n & mask
    for i, v in enumerate(vals):
        mem[1 + i] = v & mask
    mem[n + 1] = t & mask
    pc = 0
    steps = 0
    seg = {name: 0 for name, _, _ in pc_ranges} if pc_ranges else None
    while True:
        if steps >= fuel_cap:
            return None, steps, seg
        if pc < len(prog):
            op, a = prog[pc]
        else:
            op, a = "reject", []
        if seg is not None:
            for name, lo, hi in pc_ranges:
                if lo <= pc < hi:
                    seg[name] += 1
                    break
        steps += 1
        npc = pc + 1
        if op == "one":
            mem[a[0]] = 1
        elif op == "add":
            mem[a[0]] = (mem[a[1]] + mem[a[2]]) & mask
        elif op == "sub":
            mem[a[0]] = (mem[a[1]] - mem[a[2]]) & mask
        elif op == "mul":
            mem[a[0]] = (mem[a[1]] * mem[a[2]]) & mask
        elif op == "div":
            mem[a[0]] = 0 if mem[a[2]] == 0 else (mem[a[1]] // mem[a[2]]) & mask
        elif op == "rem":
            mem[a[0]] = mem[a[1]] if mem[a[2]] == 0 else mem[a[1]] % mem[a[2]]
        elif op == "and":
            mem[a[0]] = mem[a[1]] & mem[a[2]]
        elif op == "or":
            mem[a[0]] = mem[a[1]] | mem[a[2]]
        elif op == "xor":
            mem[a[0]] = mem[a[1]] ^ mem[a[2]]
        elif op == "shl":
            s = mem[a[2]]
            mem[a[0]] = 0 if s >= w else (mem[a[1]] << s) & mask
        elif op == "shr":
            s = mem[a[2]]
            mem[a[0]] = 0 if s >= w else mem[a[1]] >> s
        elif op == "load":
            mem[a[0]] = mem[mem[a[1]]]
        elif op == "store":
            mem[mem[a[0]]] = mem[a[1]]
        elif op == "rand":
            raise RuntimeError("rand executed -- prog2 must be rand-free")
        elif op == "blt":
            if mem[a[0]] < mem[a[1]]:
                npc = a[2]
        elif op == "accept":
            return True, steps, seg
        elif op == "reject":
            return False, steps, seg
        else:
            raise RuntimeError(f"bad op {op}")
        pc = npc


def oracle(vals, t):
    sums = {0}
    for v in vals:
        sums |= {s + v for s in sums}
    return t in sums


def lcg(s):
    return (1103515245 * s + 12345) % 2147483648


def lcg_cases(k, seed):
    cases = []
    s = seed
    for _ in range(k):
        s1 = lcg(s)
        n = 2 + s1 % 6
        draws = []
        cur = s1
        for _ in range(n + 1):
            cur = lcg(cur)
            draws.append(cur)
        vals = [d % 1000 + 1 for d in draws[:n]]
        t = draws[n] % (sum(vals) + 2)
        cases.append((n, vals, t))
        s = draws[n]
    return cases


def lcg_cases_odd(k, seed):
    """Parity supplement: low LCG bits are weak (the 20-case stream only
    produced even n); force n in 3..7 via s % 5."""
    cases = []
    s = seed
    for _ in range(k):
        s1 = lcg(s)
        n = 3 + s1 % 5
        draws = []
        cur = s1
        for _ in range(n + 1):
            cur = lcg(cur)
            draws.append(cur)
        vals = [d % 1000 + 1 for d in draws[:n]]
        t = draws[n] % (sum(vals) + 2)
        cases.append((n, vals, t))
        s = draws[n]
    return cases


def edges():
    twelve = [i + 7 for i in range(12)]
    e = [
        ("E01-empty-n2", 2, [3, 5], 0),
        ("E02-single-n2", 2, [3, 5], 3),
        ("E03-all-n2", 2, [3, 5], 8),
        ("E04-gap-n2", 2, [3, 5], 4),
        ("E05-gap-n3", 3, [2, 4, 7], 5),
        ("E06-part-n3", 3, [2, 4, 7], 6),
        ("E07-all-n3", 3, [2, 4, 7], 13),
        ("E08-huget-n4", 4, [3, 4, 5, 6], 2**60),
        ("E09-hit-n4", 4, [3, 4, 5, 6], 6),
        ("E10-dupmin-n7", 7, [1] * 7, 3),
        ("E11-dupmin-over-n7", 7, [1] * 7, 8),
        ("E12-dupmin-n8", 8, [1] * 8, 5),
        ("E13-dupmin-empty-n8", 8, [1] * 8, 0),
        ("E14-dup-gap-n8", 8, [2] * 8, 7),
        ("E15-dup-all-n8", 8, [2] * 8, 16),
    ]
    for i, t in enumerate([0, 5, 15, 20, 25, 35, 40, 41]):
        e.append((f"D{i+1}-dup8-t{t}" + ("-miss" if t == 41 else ""), 8, [5] * 8, t))
    hb = [2**40 + 7, 2**40 + 9, 2**41 + 3, 5, 2**40 + 7, 11]
    e.append(("HB1-hugeb-hit-n6", 6, hb, (2**40 + 7) + (2**41 + 3) + 5))
    e.append(("HB2-hugeb-miss-n6", 6, hb, 2**42))
    e.append(("HB3-hugeb-hit-n4", 4, [2**59 + 1, 2**59 + 2, 2**59 + 3, 2**59 + 4], 2**60 + 3))
    e.append(("P12a-hit", 12, twelve, 24))
    e.append(("P12b-all", 12, twelve, 150))
    e.append(("P12c-miss", 12, twelve, 151))
    o5 = [2, 3, 5, 7, 11]
    for tag, t in (("O01-n5-empty", 0), ("O02-n5-single", 5), ("O03-n5-gap", 4),
                   ("O04-n5-pair", 13), ("O05-n5-all", 28), ("O06-n5-over", 29)):
        e.append((tag, 5, o5, t))
    o6 = [2, 9, 4, 7, 1, 5]
    for tag, t in (("O07-n6-empty", 0), ("O08-n6-hit", 7), ("O09-n6-all", 28),
                   ("O10-n6-over", 29)):
        e.append((tag, 6, o6, t))
    for i, (n, vals, t) in enumerate(lcg_cases(20, 20261031)):
        e.append((f"L{i+1}-lcg", n, vals, t))
    for i, (n, vals, t) in enumerate(lcg_cases_odd(10, 999983)):
        e.append((f"O{i+11}-lcgodd", n, vals, t))
    return e


def parse_lean_rocks(path):
    """(tag, t) -> (got, want) from Lean's PASS/FAIL lines."""
    import re
    out = {}
    for line in open(path):
        m = re.match(r"(?:PASS|FAIL) (\S+) n=(\d+) t=(\d+) got=\(some (\w+)\) want=(\w+)", line)
        if m:
            out[(m.group(1), int(m.group(3)))] = (m.group(4), m.group(5))
    return out


def cmd_battery():
    prog2 = load_dump("prog2_dump.txt")
    lean = parse_lean_rocks("rocks_out.txt")
    npass = nfail = 0
    for tag, n, vals, t in edges():
        got, steps, _ = simulate(prog2, n, vals, t)
        want = oracle(vals, t)
        ok = got == want
        # cross-check against the Lean-side run
        lgot, lwant = lean.get((tag, t), ("?", "?"))
        lean_ok = (str(got).lower() == lgot) and (str(want).lower() == lwant)
        if ok and lean_ok:
            npass += 1
        else:
            nfail += 1
        print(f"{'PASS' if ok and lean_ok else 'FAIL'} {tag} n={n} t={t} "
              f"py_got={got} py_want={want} lean=({lgot},{lwant}) steps={steps}")
    # full pipeline n=16/20 (python only)
    for n in (16, 20):
        vals = [i + 7 for i in range(n)]
        s = sum(vals)
        for tag, t in ((f"P{n}a-hit", 24), (f"P{n}b-all", s), (f"P{n}c-miss", s + 1),
                       (f"P{n}d-half", s // 2)):
            got, steps, _ = simulate(prog2, n, vals, t)
            want = oracle(vals, t)
            ok = got == want
            npass += ok
            nfail += not ok
            print(f"{'PASS' if ok else 'FAIL'} {tag} n={n} t={t} got={got} want={want} steps={steps}")
    print(f"PY ROCKS TOTAL: pass={npass} fail={nfail} of {npass+nfail}")
    return 1 if nfail else 0


def cmd_steps():
    prog2 = load_dump("prog2_dump.txt")
    prog1 = load_dump("prog_dump.txt")
    # prog2 segment pc ranges (from the Lean label map)
    segs = [("prologue", 0, 86), ("phaseA", 86, 148), ("canon", 148, 161),
            ("phaseA2", 161, 224), ("scanB", 224, 244), ("smallN", 244, 301)]
    print("n | prog2 miss-steps  C2=steps/2^(n//2) | seg: phaseA canon phaseA2 scanB "
          "| prog(old) miss-steps  C1=steps/2^(n//2)  C1/n")
    rows = []
    for n in (8, 10, 12, 14, 16, 18, 20, 22, 24):
        vals = [i + 7 for i in range(n)]
        s = sum(vals)
        half = 1 << (n // 2)
        got2, st2, seg = simulate(prog2, n, vals, s + 1, pc_ranges=segs)
        assert got2 is False, (n, got2)
        got1, st1, _ = simulate(prog1, n, vals, s + 1)
        assert got1 is False, (n, got1)
        rows.append((n, st2, st1, seg))
        print(f"{n:2d} | {st2:12d} {st2/half:10.2f} | "
              f"{seg['phaseA']:7d} {seg['canon']:6d} {seg['phaseA2']:7d} {seg['scanB']:7d} | "
              f"{st1:12d} {st1/half:10.2f} {st1/half/n:8.3f}")
    # hit-early and hit-all step counts for prog2 at the three report n
    print()
    print("report points (prog2): n, miss / all-hit / early-hit steps")
    for n in (12, 16, 20):
        vals = [i + 7 for i in range(n)]
        s = sum(vals)
        _, st_miss, _ = simulate(prog2, n, vals, s + 1)
        _, st_all, _ = simulate(prog2, n, vals, s)
        _, st_hit, _ = simulate(prog2, n, vals, 24)
        half = 1 << (n // 2)
        print(f"n={n}: miss={st_miss} all={st_all} earlyhit={st_hit}  "
              f"C(miss)={st_miss/half:.2f} C(all)={st_all/half:.2f} C(hit)={st_hit/half:.2f}")
    cmax = max(st2 / (1 << (n // 2)) for n, st2, _, _ in rows)
    print(f"\nFIT: max_n steps(prog2)/2^(floor(n/2)) = {cmax:.2f} over n=8..24 (worst-case miss path)")
    print("propose T(n) = ceil(Cmax)*2^(n/2) + D*n with Cmax >= above, D covering the O(n) prologue;")
    print("growth check: prog2 ratio flat (2^(n/2)), old prog ratio grows ~linearly in n (n*2^(n/2)).")


def cmd_radixdemo():
    # The charter's 2-pass LSD radix with n/2-bit digits, run on values >= 2^n:
    n = 8
    d = n // 2  # digit bits
    m = 1 << d  # buckets
    vals = [300, 44, 700, 128, 256 + 44, 5, 699, 1024]
    a = list(vals)
    for shift in (0, d):  # exactly two passes: low digit, high digit
        cnt = [0] * m
        for v in a:
            cnt[(v >> shift) & (m - 1)] += 1
        for i in range(1, m):
            cnt[i] += cnt[i - 1]
        out = [0] * len(a)
        for v in reversed(a):
            cnt[(v >> shift) & (m - 1)] -= 1
            out[cnt[(v >> shift) & (m - 1)]] = v
        a = out
    print(f"n={n}, digit={d} bits, 2-pass LSD radix on values >= 2^n={1<<n}:")
    print(f"  input : {vals}")
    print(f"  output: {a}")
    print(f"  sorted? {a == sorted(a)}  <-- 2^(n/2)-bucket 2-pass radix only sorts mod 2^n;")
    print(f"  300 vs 44: 300 % 256 = 44 -> digit-equal, full-value order NOT established.")
    print("  Covering w = 4(n+b+log2(n+2)) bits needs ceil(w/d) = Theta(b/n) passes ->")
    print("  Theta((b/n)*2^(n/2)) steps, b-dependent: WORSE than the merge for alpha=1/2.")


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "battery"
    if cmd == "battery":
        sys.exit(cmd_battery())
    elif cmd == "steps":
        cmd_steps()
    elif cmd == "radixdemo":
        cmd_radixdemo()
    else:
        raise SystemExit(f"unknown cmd {cmd}")
