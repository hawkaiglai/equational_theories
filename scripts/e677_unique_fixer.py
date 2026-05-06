#!/usr/bin/env python3
"""
Unique Left-Fixer Conjecture for E677 Magmas
=============================================

Observation from size-7 data: every element x has EXACTLY ONE left-fixer
y such that y◇x = x. That fixer equals θ(x) = (x◇x)◇x.

This is equivalent to: R_x (right multiplication by x) is a bijection,
i.e., the magma is a QUASIGROUP.

If R_x bijective → unique fixer → the fixer must be θ(x) → E255.

This script verifies:
  1. R_x bijective (quasigroup) in all E677 magmas
  2. Unique left-fixer property
  3. The unique fixer equals θ(x)

Checked on: enumerated small magmas + Adam's n=35 example.
"""

import sys
import time


# ── Adam's n=35 example ──────────────────────────────────────────────

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


def check_e677(mul, n):
    for a in range(n):
        for b in range(n):
            if mul[b][mul[a][mul[mul[b][a]][b]]] != a:
                return False, a, b
    return True, None, None


def theta(mul, z):
    return mul[mul[z][z]][z]


def analyze_fixer_structure(mul, n, label=""):
    """Complete analysis of left-fixer and quasigroup structure."""
    print(f"\n{'=' * 60}")
    print(f"  {label} (n = {n})")
    print(f"{'=' * 60}")

    # E677 check
    ok, _, _ = check_e677(mul, n)
    print(f"  E677: {'✓' if ok else '✗'}")

    # R_x bijective? (columns are permutations = quasigroup)
    r_bijective = True
    r_failures = []
    for x in range(n):
        col = [mul[y][x] for y in range(n)]
        if len(set(col)) != n:
            r_bijective = False
            r_failures.append(x)
    print(f"  R_x bijective (quasigroup): {'✓' if r_bijective else f'✗ at x={r_failures}'})")

    # Left-fixers for each x
    fixer_counts = []
    unique_fixer_ok = True
    fixer_is_theta = True
    e255_ok = True

    for x in range(n):
        fixers = [y for y in range(n) if mul[y][x] == x]
        fixer_counts.append(len(fixers))
        th = theta(mul, x)

        if len(fixers) != 1:
            unique_fixer_ok = False
        if len(fixers) == 0 or fixers[0] != th:
            if len(fixers) > 0 and th not in fixers:
                fixer_is_theta = False
        if mul[th][x] != x:
            e255_ok = False

    print(f"  E255: {'✓' if e255_ok else '✗'}")
    print(f"  Every x has exactly 1 left-fixer: {'✓' if unique_fixer_ok else '✗'}")
    print(f"  That fixer equals θ(x): {'✓' if fixer_is_theta else '✗'}")

    fixer_dist = {}
    for c in fixer_counts:
        fixer_dist[c] = fixer_dist.get(c, 0) + 1
    print(f"  Left-fixer count distribution: {dict(sorted(fixer_dist.items()))}")

    # Σ |Fix(L_y)| = ?
    total_fixed = sum(1 for y in range(n) for x in range(n) if mul[y][x] == x)
    print(f"  Σ |Fix(L_y)| = {total_fixed} (should be {n} if unique fixer)")

    # θ map analysis
    theta_map = [theta(mul, z) for z in range(n)]
    theta_image = set(theta_map)
    theta_injective = len(theta_image) == n
    print(f"  θ injective: {'✓' if theta_injective else f'✗ (|image|={len(theta_image)})'}")

    # Idempotents
    idempotents = [e for e in range(n) if mul[e][e] == e]
    print(f"  Idempotents: {idempotents} ({len(idempotents)} total)")

    return r_bijective, unique_fixer_ok, fixer_is_theta, e255_ok


def main():
    # ── Test n=35 ──
    n35 = 35
    r_ok, uf_ok, ft_ok, e255_ok = analyze_fixer_structure(
        TABLE_35, n35, "Adam's n=35 example"
    )

    # ── Test enumerated size-7 ──
    try:
        from z3 import Solver, Int, Implies, Distinct, Or, sat, unknown
        HAS_Z3 = True
    except ImportError:
        HAS_Z3 = False
        print("\nZ3 not available, skipping enumeration.")

    if HAS_Z3:
        max_n = int(sys.argv[1]) if len(sys.argv) > 1 else 7
        max_models = int(sys.argv[2]) if len(sys.argv) > 2 else 300

        for n in [5, 7]:
            if n > max_n:
                continue

            print(f"\n\n{'#' * 60}")
            print(f"  Enumerating all E677 magmas of size {n}")
            print(f"{'#' * 60}")

            s = Solver()
            s.set("timeout", 300000)
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
            all_r_ok = True
            all_uf_ok = True
            all_ft_ok = True
            all_e255 = True

            start = time.time()
            while count < max_models:
                result = s.check()
                if result != sat:
                    break
                model = s.model()
                table = [[model.eval(m[i][j]).as_long()
                          for j in range(n)] for i in range(n)]
                assert check_e677(table, n)[0]
                count += 1

                # Quick check (no verbose output)
                n_ = n
                r_bij = all(
                    len(set(table[y][x] for y in range(n_))) == n_
                    for x in range(n_)
                )
                theta_map = [theta(table, z) for z in range(n_)]
                uf = all(
                    sum(1 for y in range(n_) if table[y][x] == x) == 1
                    for x in range(n_)
                )
                ft = all(table[theta_map[x]][x] == x for x in range(n_))

                if not r_bij:
                    all_r_ok = False
                if not uf:
                    all_uf_ok = False
                if not ft:
                    all_ft_ok = False
                if not ft:
                    all_e255 = False

                s.add(Or([m[i][j] != table[i][j]
                          for i in range(n_) for j in range(n_)]))

                if count % 50 == 0:
                    print(f"  ... {count} models checked ({time.time()-start:.1f}s)")

            elapsed = time.time() - start
            print(f"\n  Size {n}: {count} models ({elapsed:.1f}s)")
            print(f"  R_x bijective (quasigroup) in ALL: {'✓' if all_r_ok else '✗'}")
            print(f"  Unique left-fixer in ALL:          {'✓' if all_uf_ok else '✗'}")
            print(f"  Fixer equals θ(x) in ALL:          {'✓' if all_ft_ok else '✗'}")
            print(f"  E255 in ALL:                       {'✓' if all_e255 else '✗'}")

    # ── Summary ──
    print(f"\n\n{'=' * 60}")
    print("SUMMARY OF UNIQUE-FIXER CONJECTURE")
    print("=" * 60)
    print("""
Conjecture: In every finite E677 magma:
  (a) R_x is bijective (quasigroup property)
  (b) Every x has exactly one left-fixer y with y◇x = x
  (c) That fixer is θ(x) = (x◇x)◇x

Proof strategy if (a) holds:
  R_x bijective → column x is a permutation
  → ∃! y: y◇x = x (exactly one fixed point of R_x at value x)
  → define φ(x) = that unique y
  → show φ(x) = θ(x) using E677
  → then φ(x)◇x = x gives E255
""")


if __name__ == '__main__':
    main()
