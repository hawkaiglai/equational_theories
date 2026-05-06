#!/usr/bin/env python3
"""
Gauss + Tao simplification attack on Φ_x bijectivity.

Gauss's insight: write the sequence two ways, find a constant.
Tao's method: start with simplest cases (p=2,3,4), extend.

Key object: the sequence d_k = c_k ◇ x (orbit elements applied to x).

From E677 with b = x, a = c_k:
  c_k = x ◇ (c_k ◇ ((x ◇ c_k) ◇ x))
      = L_x(c_k ◇ (c_{k+1} ◇ x))
      = L_x(c_k ◇ d_{k+1})    ... wait, this gives:
  L_x^{-1}(c_k) = c_k ◇ d_{k+1}
  c_{k-1} = c_k ◇ d_{k+1}

RECURRENCE: c_k ◇ d_{k+1} = c_{k-1}  (indices mod p)

With:
  d_0 = x ◇ x = c_1
  d_1 = c_1 ◇ x = c_{p-2} (proven: from k=0 recurrence)

E255 ⟺ d_{p-2} = x (since θ(x) = c_{p-2}, E255 = c_{p-2}◇x = x)

Questions:
  1. Which orbit periods p are possible in finite E677 magmas?
  2. For each possible p, what does the d_k chain look like?
  3. Is there a "Gauss pairing" d_k + d_{p-1-k} = constant?
"""

import sys
import time
from z3 import *


def check_e677_table(mul, n):
    for a in range(n):
        for b in range(n):
            if mul[b][mul[a][mul[mul[b][a]][b]]] != a:
                return False
    return True


def orbit_of(mul, z, n):
    orbit = [z]
    cur = z
    for _ in range(n):
        cur = mul[z][cur]
        if cur == orbit[0]:
            break
        orbit.append(cur)
    return orbit


def enumerate_e677(n, max_count=500, timeout_ms=300000):
    s = Solver()
    s.set("timeout", timeout_ms)
    m = [[Int(f'm_{i}_{j}') for j in range(n)] for i in range(n)]
    for i in range(n):
        for j in range(n):
            s.add(m[i][j] >= 0, m[i][j] < n)
    for i in range(n):
        s.add(Distinct([m[i][j] for j in range(n)]))
    for a in range(n):
        for b in range(n):
            t1 = m[b][a]
            t2 = Int(f'e1_{a}_{b}')
            s.add(t2 >= 0, t2 < n)
            for v in range(n):
                s.add(Implies(t1 == v, t2 == m[v][b]))
            t3 = Int(f'e2_{a}_{b}')
            s.add(t3 >= 0, t3 < n)
            for v in range(n):
                s.add(Implies(t2 == v, t3 == m[a][v]))
            t4 = Int(f'e3_{a}_{b}')
            s.add(t4 >= 0, t4 < n)
            for v in range(n):
                s.add(Implies(t3 == v, t4 == m[b][v]))
            s.add(t4 == a)
    magmas = []
    start = time.time()
    while len(magmas) < max_count:
        result = s.check()
        if result != sat:
            break
        model = s.model()
        table = [[model.eval(m[i][j]).as_long() for j in range(n)] for i in range(n)]
        assert check_e677_table(table, n)
        magmas.append(table)
        s.add(Or([m[i][j] != table[i][j] for i in range(n) for j in range(n)]))
    elapsed = time.time() - start
    print(f"  {len(magmas)} E677 magmas of size {n} ({elapsed:.1f}s)")
    return magmas


def analyze_dk_sequence(mul, n, z):
    """
    Compute the d_k = c_k ◇ x sequence for element z and analyze it.
    """
    orb = orbit_of(mul, z, n)
    p = len(orb)

    # c_k = orb[k]
    # d_k = c_k ◇ x = mul[orb[k]][z]
    d = [mul[orb[k]][z] for k in range(p)]

    # Check: d_0 = c_1?
    assert d[0] == orb[1 % p], f"d_0 = {d[0]} ≠ c_1 = {orb[1 % p]}"

    # Check: d_1 = c_{p-2}?
    if p >= 3:
        assert d[1] == orb[p - 2], f"d_1 = {d[1]} ≠ c_{{p-2}} = {orb[p-2]}"

    # Check recurrence: c_k ◇ d_{k+1} = c_{k-1}
    recurrence_ok = True
    for k in range(p):
        lhs = mul[orb[k]][d[(k + 1) % p]]
        rhs = orb[(k - 1) % p]
        if lhs != rhs:
            recurrence_ok = False

    # Check E255: d_{p-2} = x?
    e255 = d[p - 2] == z if p >= 2 else (z == z)

    # Which d_k are orbit elements vs outsiders?
    orb_set = set(orb)
    orb_idx = {orb[k]: k for k in range(p)}
    d_positions = []
    for k in range(p):
        if d[k] in orb_set:
            d_positions.append(orb_idx[d[k]])
        else:
            d_positions.append(f"out({d[k]})")

    # Gauss pairing: do d_k and d_{p-1-k} orbit indices sum to a constant?
    gauss_sums = []
    for k in range(p // 2):
        j = p - 1 - k
        if isinstance(d_positions[k], int) and isinstance(d_positions[j], int):
            gauss_sums.append((d_positions[k] + d_positions[j]) % p)
        else:
            gauss_sums.append("N/A")

    # Self-squaring chain: which c_i ◇ c_i = c_j hold?
    self_sq = {}
    for k in range(p):
        sq = mul[orb[k]][orb[k]]
        if sq in orb_set:
            self_sq[k] = orb_idx[sq]
        else:
            self_sq[k] = f"out({sq})"

    return {
        'z': z,
        'p': p,
        'orbit': orb,
        'd': d,
        'd_positions': d_positions,
        'recurrence_ok': recurrence_ok,
        'e255': e255,
        'gauss_sums': gauss_sums,
        'self_sq': self_sq,
    }


def test_impossible_periods(max_n=8, timeout_ms=120000):
    """
    For each candidate period p, try to find an E677 magma with
    an element of that period. UNSAT = period is impossible.
    """
    print("\n" + "=" * 60)
    print("  Testing which orbit periods are POSSIBLE")
    print("=" * 60)

    for n in range(2, max_n + 1):
        for p in range(2, n + 1):
            s_simple = Solver()
            s_simple.set("timeout", timeout_ms)

            m3 = [[Int(f'm_{i}_{j}') for j in range(n)] for i in range(n)]
            for i in range(n):
                for j in range(n):
                    s_simple.add(m3[i][j] >= 0, m3[i][j] < n)
            for i in range(n):
                s_simple.add(Distinct([m3[i][j] for j in range(n)]))

            # E677
            for a in range(n):
                for b in range(n):
                    t1 = m3[b][a]
                    t2 = Int(f'g1_{a}_{b}')
                    s_simple.add(t2 >= 0, t2 < n)
                    for v in range(n):
                        s_simple.add(Implies(t1 == v, t2 == m3[v][b]))
                    t3 = Int(f'g2_{a}_{b}')
                    s_simple.add(t3 >= 0, t3 < n)
                    for v in range(n):
                        s_simple.add(Implies(t2 == v, t3 == m3[a][v]))
                    t4 = Int(f'g3_{a}_{b}')
                    s_simple.add(t4 >= 0, t4 < n)
                    for v in range(n):
                        s_simple.add(Implies(t3 == v, t4 == m3[b][v]))
                    s_simple.add(t4 == a)

            # Orbit of element 0 under L_0 has period exactly p
            # c_0 = 0, c_{k+1} = m3[0][c_k]
            c_vals = [0]
            cur = 0
            # Build chain: c_{k+1} = m3[0][c_k]
            # Since c_k are concrete for k=0 but symbolic after...
            # Just use concrete orbit: m3[0][0], m3[0][m3[0][0]], etc.
            # This is hard with Z3 nested lookups. Let me use aux vars.

            c_aux = [Int(f'co_{k}') for k in range(p + 1)]
            s_simple.add(c_aux[0] == 0)
            for k in range(p):
                s_simple.add(c_aux[k + 1] >= 0, c_aux[k + 1] < n)
                for v in range(n):
                    s_simple.add(Implies(c_aux[k] == v,
                                         c_aux[k + 1] == m3[0][v]))

            # Period exactly p: c_p = c_0 = 0
            s_simple.add(c_aux[p] == 0)
            # And c_k ≠ 0 for 1 ≤ k < p
            for k in range(1, p):
                s_simple.add(c_aux[k] != 0)

            start = time.time()
            result = s_simple.check()
            elapsed = time.time() - start

            if result == sat:
                status = "POSSIBLE"
            elif result == unsat:
                status = "IMPOSSIBLE"
            else:
                status = f"timeout ({elapsed:.0f}s)"

            print(f"  n={n}, p={p}: {status}")


def main():
    # Part 1: Which periods are possible? (skip — too slow for large n)
    test_impossible_periods(max_n=7, timeout_ms=30000)

    # Part 2: Analyze d_k sequences in known magmas
    print("\n" + "=" * 60)
    print("  d_k sequence analysis")
    print("=" * 60)

    for n in [5, 7]:
        print(f"\n--- Size {n} ---")
        magmas = enumerate_e677(n, max_count=20)

        seen_periods = set()
        for idx, mul in enumerate(magmas):
            for z in range(n):
                orb = orbit_of(mul, z, n)
                p = len(orb)
                if p <= 1:
                    continue
                if p in seen_periods:
                    continue
                seen_periods.add(p)

                r = analyze_dk_sequence(mul, n, z)
                print(f"\n  Magma #{idx+1}, z={z}, period p={p}:")
                print(f"    orbit:       {r['orbit']}")
                print(f"    d_k:         {r['d']}")
                print(f"    d_positions: {r['d_positions']}")
                print(f"    recurrence:  {'✓' if r['recurrence_ok'] else '✗'}")
                print(f"    E255:        {'✓' if r['e255'] else '✗'}")
                print(f"    Gauss sums:  {r['gauss_sums']}")
                print(f"    self-sq c_i²: {r['self_sq']}")

    # Part 3: Analyze the n=35 example
    print("\n--- n=35 example ---")
    TABLE_35 = [
        [23,22,21,24,0,2,28,1,14,13,25,15,29,18,19,17,34,33,30,32,27,11,9,8,10,16,3,12,20,31,5,26,4,7,6],
        [20,21,24,23,3,1,0,28,12,15,14,25,19,29,16,18,32,34,33,31,8,9,27,10,11,17,2,13,22,30,26,4,6,5,7],
        [24,20,22,21,28,3,1,2,25,12,15,13,18,17,29,16,33,30,31,34,9,10,11,27,8,19,0,14,23,32,7,5,26,6,4],
        [22,24,23,20,2,28,3,0,13,25,12,14,16,19,17,29,31,32,34,30,10,27,8,11,9,18,1,15,21,33,4,6,7,26,5],
        [19,17,18,29,14,13,25,15,4,7,26,5,28,1,0,2,24,21,22,23,34,30,33,32,31,3,12,6,16,20,9,27,8,11,10],
        [16,18,29,19,12,15,14,25,6,5,4,26,0,28,3,1,23,24,21,20,32,33,34,31,30,2,13,7,17,22,27,8,10,9,11],
        [17,29,19,16,13,25,12,14,7,26,6,4,3,0,2,28,20,23,24,22,31,34,32,30,33,1,15,5,18,21,8,10,11,27,9],
        [29,16,17,18,25,12,15,13,26,6,5,7,1,2,28,3,21,22,20,24,33,31,30,34,32,0,14,4,19,23,11,9,27,10,8],
        [8,11,9,27,23,22,24,21,19,17,29,18,34,33,32,30,26,5,7,4,25,13,15,14,12,31,20,16,10,6,1,28,0,2,3],
        [10,9,27,8,20,21,23,24,16,18,19,29,32,34,31,33,4,26,5,6,14,15,25,12,13,30,22,17,11,7,28,0,3,1,2],
        [11,27,8,10,22,24,20,23,17,29,16,19,31,32,30,34,6,4,26,7,12,25,14,13,15,33,21,18,9,5,0,3,2,28,1],
        [27,10,11,9,24,20,21,22,29,16,18,17,33,30,34,31,5,7,6,26,15,12,13,25,14,32,23,19,8,4,2,1,28,3,0],
        [7,26,4,6,30,34,31,32,22,24,20,23,10,8,11,27,12,14,25,13,3,28,0,2,1,9,33,21,5,15,19,16,17,29,18],
        [26,6,7,5,34,31,33,30,24,20,21,22,9,11,27,10,15,13,12,25,1,3,2,28,0,8,32,23,4,14,17,18,29,16,19],
        [4,7,5,26,32,30,34,33,23,22,24,21,27,9,8,11,25,15,13,14,28,2,1,0,3,10,31,20,6,12,18,29,19,17,16],
        [6,5,26,4,31,33,32,34,20,21,23,24,8,27,10,9,14,25,15,12,0,1,28,3,2,11,30,22,7,13,29,19,16,18,17],
        [13,25,14,12,11,27,10,8,30,34,31,32,6,4,7,26,3,0,28,2,16,29,19,17,18,5,9,33,15,1,23,20,22,24,21],
        [25,12,13,15,27,10,9,11,34,31,33,30,5,7,26,6,1,2,3,28,18,16,17,29,19,4,8,32,14,0,22,21,24,20,23],
        [12,15,25,14,10,9,8,27,31,33,32,34,4,26,6,5,0,28,1,3,19,18,29,16,17,7,11,30,13,2,24,23,20,21,22],
        [14,13,15,25,8,11,27,9,32,30,34,33,26,5,4,7,28,1,2,0,29,17,18,19,16,6,10,31,12,3,21,24,23,22,20],
        [30,34,32,31,17,29,16,19,2,28,3,0,20,23,22,24,10,8,27,11,6,26,4,7,5,21,18,1,33,9,14,12,13,25,15],
        [31,33,34,32,16,18,19,29,3,1,0,28,23,24,20,21,8,27,9,10,4,5,26,6,7,22,17,2,30,11,25,14,12,15,13],
        [34,31,30,33,29,16,18,17,28,3,1,2,21,22,24,20,9,11,10,27,5,6,7,26,4,23,19,0,32,8,13,15,25,12,14],
        [32,30,33,34,19,17,29,18,0,2,28,1,24,21,23,22,27,9,11,8,26,7,5,4,6,20,16,3,31,10,15,25,14,13,12],
        [33,32,31,30,18,19,17,16,1,0,2,3,22,20,21,23,11,10,8,9,7,4,6,5,26,24,29,28,34,27,12,13,15,14,25],
        [5,4,6,7,33,32,30,31,21,23,22,20,11,10,9,8,13,12,14,15,2,0,3,1,28,27,34,24,26,25,16,17,18,19,29],
        [18,19,16,17,15,14,13,12,5,4,7,6,2,3,1,0,22,20,23,21,30,32,31,33,34,28,25,26,29,24,10,11,9,8,27],
        [9,8,10,11,21,23,22,20,18,19,17,16,30,31,33,32,7,6,4,5,13,14,12,15,25,34,24,29,27,26,3,2,1,0,28],
        [21,23,20,22,1,0,2,3,15,14,13,12,17,16,18,19,30,31,32,33,11,8,10,9,27,29,28,25,24,34,6,7,5,4,26],
        [15,14,12,13,9,8,11,10,33,32,30,31,7,6,5,4,2,3,0,1,17,19,16,18,29,26,27,34,25,28,20,22,21,23,24],
        [28,3,2,1,26,6,5,7,27,10,9,11,15,13,25,12,18,17,16,29,21,20,22,24,23,14,4,8,0,19,30,33,34,31,32],
        [2,28,0,3,7,26,6,4,11,27,10,8,12,14,13,25,16,19,29,17,20,24,23,22,21,15,5,9,1,18,32,31,30,34,33],
        [0,2,1,28,4,7,26,5,8,11,27,9,25,15,14,13,29,18,17,19,24,22,21,23,20,12,6,10,3,16,33,34,32,30,31],
        [3,1,28,0,6,5,4,26,10,9,8,27,14,25,12,15,19,29,18,16,23,21,24,20,22,13,7,11,2,17,34,32,31,33,30],
        [1,0,3,2,5,4,7,6,9,8,11,10,13,12,15,14,17,16,19,18,22,23,20,21,24,25,26,27,28,29,31,30,33,32,34],
    ]
    for z in [0, 1, 4]:
        r = analyze_dk_sequence(TABLE_35, 35, z)
        p = r['p']
        if p > 1:
            print(f"\n  z={z}, period p={p}:")
            print(f"    orbit:       {r['orbit']}")
            print(f"    d_k:         {r['d']}")
            print(f"    d_positions: {r['d_positions']}")
            print(f"    recurrence:  {'✓' if r['recurrence_ok'] else '✗'}")
            print(f"    E255:        {'✓' if r['e255'] else '✗'}")
            print(f"    Gauss sums:  {r['gauss_sums']}")
            print(f"    self-sq c_i²: {r['self_sq']}")


if __name__ == '__main__':
    main()
