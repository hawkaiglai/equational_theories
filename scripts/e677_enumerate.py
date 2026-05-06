#!/usr/bin/env python3
"""
Enumerate ALL E677 magmas of a given size using Z3's model enumeration.
For each one found, check E255 and report structural properties.
"""

import sys
import time
from z3 import *


def check_e677(mul, n):
    for x in range(n):
        for y in range(n):
            if mul[y][mul[x][mul[mul[y][x]][y]]] != x:
                return False
    return True


def check_e255_all(mul, n):
    for x in range(n):
        if mul[mul[mul[x][x]][x]][x] != x:
            return False, x
    return True, None


def enumerate_e677(n, max_count=1000, timeout_ms=300000):
    """Find all E677 magmas of size n (up to max_count)."""
    print(f"Enumerating E677 magmas of size {n} (max {max_count})...")

    s = Solver()
    s.set("timeout", timeout_ms)

    m = [[Int(f'm_{i}_{j}') for j in range(n)] for i in range(n)]
    for i in range(n):
        for j in range(n):
            s.add(m[i][j] >= 0, m[i][j] < n)

    # Row permutation
    for i in range(n):
        s.add(Distinct([m[i][j] for j in range(n)]))

    # E677 with auxiliary variables (flat encoding)
    for x in range(n):
        for y in range(n):
            t1 = m[y][x]
            s2 = Int(f's2_{x}_{y}')
            s.add(s2 >= 0, s2 < n)
            for v in range(n):
                s.add(Implies(t1 == v, s2 == m[v][y]))

            s3 = Int(f's3_{x}_{y}')
            s.add(s3 >= 0, s3 < n)
            for v in range(n):
                s.add(Implies(s2 == v, s3 == m[x][v]))

            s4 = Int(f's4_{x}_{y}')
            s.add(s4 >= 0, s4 < n)
            for v in range(n):
                s.add(Implies(s3 == v, s4 == m[y][v]))

            s.add(s4 == x)

    magmas = []
    start = time.time()

    while len(magmas) < max_count:
        result = s.check()
        if result != sat:
            break

        model = s.model()
        table = [[model.eval(m[i][j]).as_long() for j in range(n)] for i in range(n)]

        # Verify
        assert check_e677(table, n), "E677 verification failed!"
        magmas.append(table)

        # Block this solution
        block = Or([m[i][j] != table[i][j] for i in range(n) for j in range(n)])
        s.add(block)

        if len(magmas) % 10 == 0:
            elapsed = time.time() - start
            print(f"  Found {len(magmas)} so far ({elapsed:.1f}s)...")

    elapsed = time.time() - start
    print(f"  Total: {len(magmas)} E677 magmas of size {n} ({elapsed:.1f}s)")
    return magmas


def analyze_magma(mul, n, idx):
    """Analyze a single E677 magma."""
    ok, witness = check_e255_all(mul, n)
    e255_status = "E255 ✓" if ok else f"E255 ✗ (at x={witness})"

    # Idempotents
    idem = [x for x in range(n) if mul[x][x] == x]

    # R_x surjectivity
    r_surj = all(len(set(mul[y][x] for y in range(n))) == n for x in range(n))

    # Is it a quasigroup? (all rows AND columns are permutations)
    is_qg = r_surj  # rows already guaranteed by construction

    # Squaring map
    sq_map = [mul[x][x] for x in range(n)]

    print(f"  Magma #{idx+1}: {e255_status}, "
          f"idempotents={idem}, R_x_surj={r_surj}, "
          f"quasigroup={is_qg}, S={sq_map}")

    if not ok:
        print(f"    *** COUNTEREXAMPLE! ***")
        for row in mul:
            print(f"      {row}")

    return ok


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    max_count = int(sys.argv[2]) if len(sys.argv) > 2 else 100

    magmas = enumerate_e677(n, max_count=max_count, timeout_ms=600000)

    if not magmas:
        print(f"No E677 magmas of size {n} exist.")
        return 0

    print(f"\nAnalysis of {len(magmas)} E677 magmas of size {n}:")
    print("-" * 60)

    all_e255 = True
    for i, mul in enumerate(magmas):
        ok = analyze_magma(mul, n, i)
        if not ok:
            all_e255 = False

    print("-" * 60)
    if all_e255:
        print(f"ALL {len(magmas)} E677 magmas of size {n} satisfy E255 ✓")
    else:
        print(f"FOUND E677 magma(s) of size {n} that VIOLATE E255 ✗")

    return 0


if __name__ == '__main__':
    sys.exit(main())
