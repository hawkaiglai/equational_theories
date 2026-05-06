#!/usr/bin/env python3
"""
Deep structural analysis of ALL size-7 E677 magmas.

The block decomposition conjecture failed. This script digs into what
structural properties DO hold universally, looking for the real mechanism
that forces E255.

Key question: WHY does θ(x)◇x = x hold in every finite E677 magma?
θ(x) = (x◇x)◇x = c_{p-2} in the L_x orbit.
E255 says c_{p-2}◇x = x, i.e., L_{c_{p-2}}(x) = x.
"""

import sys
import time
from z3 import *
from collections import Counter


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


def enumerate_e677_z3(n, max_count=500, timeout_ms=300000):
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
        block = Or([m[i][j] != table[i][j] for i in range(n) for j in range(n)])
        s.add(block)
    elapsed = time.time() - start
    print(f"Found {len(magmas)} E677 magmas of size {n} ({elapsed:.1f}s)")
    return magmas


def deep_analyze(mul, n, idx):
    """Deep structural analysis of one E677 magma."""

    # Basic
    idempotents = [e for e in range(n) if mul[e][e] == e]
    orbits = {z: orbit_of(mul, z, n) for z in range(n)}
    periods = {z: len(orbits[z]) for z in range(n)}

    # θ map
    theta = {z: mul[mul[z][z]][z] for z in range(n)}

    # E255 check
    e255 = all(mul[theta[z]][z] == z for z in range(n))

    # Classify: which type?
    # Type A: idempotent only fixes itself
    # Type B: idempotent is global left identity
    fix_counts = {}
    for e in idempotents:
        fix_e = [x for x in range(n) if mul[e][x] == x]
        fix_counts[e] = len(fix_e)

    # Left-fixers for each element: who left-fixes x?
    left_fixers = {x: [y for y in range(n) if mul[y][x] == x] for x in range(n)}

    # For non-idempotent x: is θ(x) the unique left-fixer?
    unique_fixer = True
    for x in range(n):
        if x in idempotents:
            continue
        if len(left_fixers[x]) != 1 or left_fixers[x][0] != theta[x]:
            unique_fixer = False

    # Orbit multiplication table: for z with period p,
    # what does L_{c_i}(c_j) look like?
    # Focus on first non-idempotent element
    non_idem = [x for x in range(n) if x not in idempotents]

    # Key structural question: for orbit c_0=x, c_1, ..., c_{p-1}:
    # What is c_i ◇ c_j in terms of orbit positions?
    orbit_closed = True
    orbit_mult_pattern = None
    if non_idem:
        z = non_idem[0]
        orb = orbits[z]
        p = len(orb)
        # Build the orbit multiplication table
        orb_set = set(orb)
        orb_idx = {orb[k]: k for k in range(p)}

        # Check if orbit is closed under ◇
        closed = True
        omt = [[None]*p for _ in range(p)]
        for i in range(p):
            for j in range(p):
                prod = mul[orb[i]][orb[j]]
                if prod in orb_set:
                    omt[i][j] = orb_idx[prod]
                else:
                    closed = False
                    omt[i][j] = f"out({prod})"

        orbit_closed = closed

        if closed:
            # Check if pattern is (i,j) -> (α*i + β*j + γ) mod p
            # for some α, β, γ
            # From row 0: L_{c_0}(c_j) = c_{omt[0][j]}
            # We know L_x(c_j) = c_{j+1}, so omt[0][j] should be j+1 mod p
            row0 = [omt[0][j] for j in range(p)]

            # Check if each row i acts as shift:
            # L_{c_i}(c_j) = c_{f(i,j)} where f(i,j) = ?
            # Hypothesis: f(i,j) = (β*i + j + 1) mod p for some β
            # (since L_x = shift by 1, and L_{c_k} might shift by β*k+1)

            # Find β from omt[1][0]: L_{c_1}(c_0) = c_{omt[1][0]}
            # This should be β*1 + 0 + 1 mod p → omt[1][0] = β + 1
            if p > 1:
                beta_candidate = (omt[1][0] - 1) % p
                linear = True
                for i in range(p):
                    for j in range(p):
                        expected = (beta_candidate * i + j + 1) % p
                        if omt[i][j] != expected:
                            linear = False
                            break
                    if not linear:
                        break

                # Try more general: f(i,j) = (α*i + β*j + γ) mod p
                if not linear:
                    # Use 3 data points to solve for α, β, γ
                    # (0,0) -> omt[0][0], (0,1) -> omt[0][1], (1,0) -> omt[1][0]
                    gamma = omt[0][0]
                    beta2 = (omt[0][1] - gamma) % p
                    alpha2 = (omt[1][0] - gamma) % p
                    general_linear = True
                    for i in range(p):
                        for j in range(p):
                            expected = (alpha2 * i + beta2 * j + gamma) % p
                            if omt[i][j] != expected:
                                general_linear = False
                                break
                        if not general_linear:
                            break
                    if general_linear:
                        orbit_mult_pattern = f"c_i◇c_j = c_{{({alpha2}i+{beta2}j+{gamma}) mod {p}}}"
                    else:
                        orbit_mult_pattern = "non-linear"
                else:
                    orbit_mult_pattern = f"c_i◇c_j = c_{{({beta_candidate}i+j+1) mod {p}}}"
            else:
                orbit_mult_pattern = "trivial (p=1)"

    # Check: is the L_x inverse formula consistent?
    # L_b^{-1}(a) = a ◇ ((b◇a)◇b)
    # For orbit: L_x^{-1}(c_k) = c_{k-1 mod p}
    # So c_k ◇ ((x◇c_k)◇x) = c_{k-1}
    # = c_k ◇ (c_{k+1} ◇ x) ... and c_{k+1}◇x should be something

    return {
        'idx': idx,
        'n': n,
        'e255': e255,
        'idempotents': idempotents,
        'num_idem': len(idempotents),
        'periods': dict(Counter(periods.values())),
        'theta': theta,
        'fix_counts': fix_counts,
        'left_fixers': left_fixers,
        'unique_fixer': unique_fixer,
        'orbit_closed': orbit_closed,
        'orbit_mult_pattern': orbit_mult_pattern,
    }


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    max_count = int(sys.argv[2]) if len(sys.argv) > 2 else 500

    print(f"Deep structural analysis of size-{n} E677 magmas")
    print("=" * 60)

    magmas = enumerate_e677_z3(n, max_count=max_count)
    if not magmas:
        print("No magmas found.")
        return

    # Classify
    type_counts = Counter()
    pattern_counts = Counter()
    all_unique_fixer = True
    all_orbit_closed = True
    all_e255 = True

    fixer_stats = Counter()  # how many left-fixers per non-idempotent element

    for idx, mul in enumerate(magmas):
        r = deep_analyze(mul, n, idx)

        if not r['e255']:
            all_e255 = False
            print(f"\n*** E255 FAILS in magma #{idx+1} ***")

        if not r['unique_fixer']:
            all_unique_fixer = False
        if not r['orbit_closed']:
            all_orbit_closed = False

        # Classify type
        fix_vals = list(r['fix_counts'].values())
        if fix_vals == [n]:
            type_counts['global_left_id'] += 1
        elif fix_vals == [1]:
            type_counts['self_only'] += 1
        else:
            type_counts[f'other_{fix_vals}'] += 1

        if r['orbit_mult_pattern']:
            pattern_counts[r['orbit_mult_pattern']] += 1

        # Left-fixer count for non-idempotents
        for x in range(n):
            if mul[x][x] != x:
                fixer_stats[len(r['left_fixers'][x])] += 1

    print(f"\nType distribution:")
    for t, c in type_counts.most_common():
        print(f"  {t}: {c}")

    print(f"\nOrbit multiplication patterns:")
    for p, c in pattern_counts.most_common():
        print(f"  {p}: {c}")

    print(f"\nUniversal properties:")
    print(f"  E255 holds in all:                {'✓' if all_e255 else '✗'}")
    print(f"  θ(x) is UNIQUE left-fixer in all: {'✓' if all_unique_fixer else '✗'}")
    print(f"  Orbit closed under ◇ in all:      {'✓' if all_orbit_closed else '✗'}")

    print(f"\nLeft-fixer count distribution (non-idempotent elements):")
    for k, c in sorted(fixer_stats.items()):
        print(f"  {k} left-fixer(s): {c} elements")

    # Detailed look at first magma of each type
    print(f"\n{'=' * 60}")
    print("Detailed examples:")
    shown_types = set()
    for idx, mul in enumerate(magmas):
        r = deep_analyze(mul, n, idx)
        fix_vals = tuple(r['fix_counts'].values())
        if fix_vals in shown_types:
            continue
        shown_types.add(fix_vals)

        print(f"\n--- Magma #{idx+1} (fix pattern {fix_vals}) ---")
        print(f"  Idempotents: {r['idempotents']}")
        print(f"  Periods: {r['periods']}")
        print(f"  θ map: {r['theta']}")
        print(f"  Orbit closed: {r['orbit_closed']}")
        print(f"  Orbit pattern: {r['orbit_mult_pattern']}")
        print(f"  Unique fixer: {r['unique_fixer']}")

        # Print left-fixers
        print(f"  Left-fixers:")
        for x in range(n):
            lf = r['left_fixers'][x]
            is_idem = x in r['idempotents']
            th = r['theta'][x]
            print(f"    x={x}: fixers={lf}, θ(x)={th}, "
                  f"{'IDEMPOTENT' if is_idem else ''}")

        # Print multiplication table
        print(f"  Table:")
        for i in range(n):
            print(f"    {mul[i]}")


if __name__ == '__main__':
    main()
