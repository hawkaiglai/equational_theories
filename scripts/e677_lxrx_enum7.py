#!/usr/bin/env python3
"""
Test L_x∘R_x "exactly 1 fixed point" conjecture on ALL size-7 E677 magmas.
Also test R_x∘L_x. These are independent of R_x bijectivity.
"""

import time
from collections import Counter
from z3 import Solver, Int, Implies, Distinct, Or, sat

def check_e677(mul, n):
    for x in range(n):
        for y in range(n):
            if mul[y][mul[x][mul[mul[y][x]][y]]] != x:
                return False
    return True

def analyze_model(mul, n):
    """Return (lxrx_fp_dist, rxlx_fp_dist, rx_bij, fixer_dist)."""
    lxrx_fps = []
    rxlx_fps = []
    for x in range(n):
        # L_x∘R_x
        lxrx_fp = sum(1 for z in range(n) if mul[x][mul[z][x]] == z)
        lxrx_fps.append(lxrx_fp)
        # R_x∘L_x
        rxlx_fp = sum(1 for z in range(n) if mul[mul[x][z]][x] == z)
        rxlx_fps.append(rxlx_fp)

    rx_bij = all(len(set(mul[y][x] for y in range(n))) == n for x in range(n))

    fixer_counts = [sum(1 for y in range(n) if mul[y][x] == x) for x in range(n)]

    return Counter(lxrx_fps), Counter(rxlx_fps), rx_bij, Counter(fixer_counts)

def enumerate_and_test(n, max_count=500):
    print(f"Enumerating E677 magmas of size {n}...")
    s = Solver()
    s.set("timeout", 600000)

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

    count = 0
    all_lxrx_exactly_1 = True
    all_rxlx_exactly_1 = True
    all_rx_bij = True
    all_fixer_exactly_1 = True
    counterexamples = []

    start = time.time()
    while count < max_count:
        result = s.check()
        if result != sat:
            break
        model = s.model()
        table = [[model.eval(m[i][j]).as_long() for j in range(n)] for i in range(n)]
        assert check_e677(table, n)
        count += 1

        lxrx_dist, rxlx_dist, rx_bij, fixer_dist = analyze_model(table, n)

        if set(lxrx_dist.keys()) != {1}:
            all_lxrx_exactly_1 = False
            counterexamples.append(('lxrx', count, lxrx_dist, table))
        if set(rxlx_dist.keys()) != {1}:
            all_rxlx_exactly_1 = False
            counterexamples.append(('rxlx', count, rxlx_dist, table))
        if not rx_bij:
            all_rx_bij = False
        if set(fixer_dist.keys()) != {1}:
            all_fixer_exactly_1 = False

        s.add(Or([m[i][j] != table[i][j] for i in range(n) for j in range(n)]))

        if count % 50 == 0:
            print(f"  {count} models ({time.time()-start:.1f}s)... "
                  f"LxRx=1: {all_lxrx_exactly_1}, RxLx=1: {all_rxlx_exactly_1}")

    elapsed = time.time() - start
    print(f"\nSize {n}: {count} models enumerated ({elapsed:.1f}s)")
    print(f"  L_x∘R_x exactly 1 FP in ALL: {'✓' if all_lxrx_exactly_1 else '✗'}")
    print(f"  R_x∘L_x exactly 1 FP in ALL: {'✓' if all_rxlx_exactly_1 else '✗'}")
    print(f"  R_x bijective in ALL:         {'✓' if all_rx_bij else '✗'}")
    print(f"  Exactly 1 fixer in ALL:       {'✓' if all_fixer_exactly_1 else '✗'}")

    if counterexamples:
        print(f"\n  COUNTEREXAMPLES to exactly-1-FP:")
        for kind, idx, dist, table in counterexamples[:3]:
            print(f"    Model #{idx}, {kind}: FP distribution = {dict(dist)}")
            for row in table:
                print(f"      {row}")

    return count, all_lxrx_exactly_1, all_rxlx_exactly_1, counterexamples

if __name__ == '__main__':
    for n in [5, 7]:
        print("=" * 60)
        enumerate_and_test(n, max_count=500)
        print()
