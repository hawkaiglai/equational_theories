#!/usr/bin/env python3
"""
The θ-injectivity reduction was WRONG.

Z3 found: E677 magma of size 7 where θ(z) = 4 for all z (constant, non-injective).
Linear analysis found: F_7 with a=4, b=1 has θ(z) = 0 for all z (also constant).

BOTH satisfy E255! So θ-injectivity is NOT necessary for E255.

The correct reduction is simply: E255 ⟺ ∀x, θ(x)◇x = x.
No injectivity needed.

This script:
1. Prints the Z3-found magma and verifies E255
2. Analyzes WHY E255 holds even when θ is constant
3. Searches for the actual counterexample: E677 + NOT E255
"""

import sys
import time


def check_e677(mul, n):
    for x in range(n):
        for y in range(n):
            if mul[y][mul[x][mul[mul[y][x]][y]]] != x:
                return False
    return True


def check_e255(mul, n):
    for x in range(n):
        if mul[mul[mul[x][x]][x]][x] != x:
            return False, x
    return True, None


def theta(mul, z):
    return mul[mul[z][z]][z]


def print_table(mul, n):
    w = len(str(n-1))
    header = "  * | " + " ".join(f"{j:{w}}" for j in range(n))
    print(header)
    print("  " + "-" * (len(header) - 2))
    for i in range(n):
        row = " ".join(f"{mul[i][j]:{w}}" for j in range(n))
        print(f"  {i:{w}} | {row}")


def z3_find_theta_noninj_with_table(n, timeout_ms=300000):
    """Find E677 magma with θ non-injective and print full table."""
    from z3 import Solver, Int, And, Or, Implies, Distinct, sat

    print(f"\nZ3: finding E677 magma of size {n} with θ non-injective...")
    s = Solver()
    s.set("timeout", timeout_ms)

    m = [[Int(f'm_{i}_{j}') for j in range(n)] for i in range(n)]
    for i in range(n):
        for j in range(n):
            s.add(m[i][j] >= 0, m[i][j] < n)
    for i in range(n):
        s.add(Distinct([m[i][j] for j in range(n)]))

    # E677
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

    # θ non-injective
    theta_vars = []
    for z in range(n):
        sz = m[z][z]
        tz = Int(f'th_{z}')
        s.add(tz >= 0, tz < n)
        for v in range(n):
            s.add(Implies(sz == v, tz == m[v][z]))
        theta_vars.append(tz)

    collision = []
    for z1 in range(n):
        for z2 in range(z1+1, n):
            collision.append(theta_vars[z1] == theta_vars[z2])
    s.add(Or(collision))

    start = time.time()
    result = s.check()
    elapsed = time.time() - start

    if result == sat:
        model = s.model()
        table = [[model.eval(m[i][j]).as_long() for j in range(n)]
                 for i in range(n)]

        assert check_e677(table, n), "E677 FAILED!"
        t_map = [theta(table, z) for z in range(n)]
        e255_ok, witness = check_e255(table, n)

        print(f"  FOUND in {elapsed:.1f}s!")
        print(f"\n  Multiplication table:")
        print_table(table, n)
        print(f"\n  θ map: {t_map}")
        print(f"  E677: ✓")
        print(f"  E255: {'✓ (all elements)' if e255_ok else f'✗ at x={witness}'}")

        if e255_ok:
            print(f"\n  E255 holds DESPITE θ being non-injective!")
            print(f"  θ is constant={t_map[0]}, and element {t_map[0]} is a "
                  f"left identity for all elements.")
            # Verify left identity
            lid = t_map[0]
            is_lid = all(table[lid][x] == x for x in range(n))
            print(f"  Element {lid} is left identity: {is_lid}")
        else:
            print(f"\n  *** E255 FAILS! THIS IS A COUNTEREXAMPLE! ***")

        return table
    else:
        print(f"  {'UNSAT' if str(result) == 'unsat' else 'TIMEOUT'} in {elapsed:.1f}s")
        return None


def z3_direct_e255_counterexample(n, timeout_ms=600000):
    """The original search: E677 + NOT E255."""
    from z3 import Solver, Int, And, Or, Implies, Distinct, sat

    print(f"\nZ3: searching for E677 + ¬E255 at size {n} (timeout {timeout_ms//1000}s)...")
    s = Solver()
    s.set("timeout", timeout_ms)

    m = [[Int(f'm_{i}_{j}') for j in range(n)] for i in range(n)]
    for i in range(n):
        for j in range(n):
            s.add(m[i][j] >= 0, m[i][j] < n)
    for i in range(n):
        s.add(Distinct([m[i][j] for j in range(n)]))

    # E677
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

    # NOT E255: ∃x, ((x◇x)◇x)◇x ≠ x
    e255_fail = []
    for x in range(n):
        s1 = m[x][x]  # x◇x
        s2x = Int(f'e2_{x}')
        s.add(s2x >= 0, s2x < n)
        for v in range(n):
            s.add(Implies(s1 == v, s2x == m[v][x]))
        s3x = Int(f'e3_{x}')
        s.add(s3x >= 0, s3x < n)
        for v in range(n):
            s.add(Implies(s2x == v, s3x == m[v][x]))
        e255_fail.append(s3x != x)
    s.add(Or(e255_fail))

    # Symmetry breaking
    for i in range(1, n):
        s.add(m[0][0] <= m[i][i])

    start = time.time()
    result = s.check()
    elapsed = time.time() - start

    if result == sat:
        model = s.model()
        table = [[model.eval(m[i][j]).as_long() for j in range(n)]
                 for i in range(n)]
        assert check_e677(table, n)
        e255_ok, witness = check_e255(table, n)
        assert not e255_ok

        print(f"\n  *** COUNTEREXAMPLE FOUND in {elapsed:.1f}s! ***")
        print_table(table, n)
        print(f"  E255 fails at x={witness}")
        return table
    else:
        status = "UNSAT" if str(result) == "unsat" else f"TIMEOUT/UNKNOWN ({result})"
        print(f"  {status} in {elapsed:.1f}s")
        return None


def analyze_why_e255_holds(mul, n):
    """For an E677 magma with θ constant, analyze the structure."""
    print(f"\n{'='*60}")
    print(f"WHY E255 HOLDS (θ-constant magma, size {n})")
    print(f"{'='*60}")

    t_map = [theta(mul, z) for z in range(n)]
    const = t_map[0]
    print(f"  θ is constant: θ(z) = {const} for all z")

    # Element const must be left identity
    row_const = mul[const]
    is_lid = all(row_const[x] == x for x in range(n))
    print(f"  Element {const} is left identity: {is_lid}")
    print(f"  Row {const}: {row_const}")

    # S map
    S_map = [mul[z][z] for z in range(n)]
    print(f"  S map: {S_map}")

    # θ = const means S(z)◇z = const for all z.
    # So L_{S(z)}(z) = const. In other words, applying S(z) as left-multiplier to z
    # always gives the same element const.

    # This is a strong constraint! Let's understand the orbit structure.
    print(f"\n  L_z orbit analysis:")
    for z in range(n):
        orbit = [z]
        cur = z
        for _ in range(n):
            cur = mul[z][cur]
            if cur == orbit[0]:
                break
            orbit.append(cur)
        period = len(orbit)
        # Position of const in orbit
        try:
            const_pos = orbit.index(const)
        except ValueError:
            const_pos = -1
        print(f"    z={z}: orbit = {orbit}, period = {period}, "
              f"const={const} at pos {const_pos}")
        # θ(z) = L_z^{-2}(z) = orbit[p-2]
        if period > 1:
            print(f"           orbit[p-2] = orbit[{period-2}] = {orbit[period-2]}, "
                  f"should = {const}: {'✓' if orbit[period-2] == const else '✗'}")

    # Check: what makes const a left identity?
    # E677 at (x, const): x = const ◇ (x ◇ ((const◇x)◇const))
    # Since const◇x = x (left identity): x = const ◇ (x ◇ (x◇const))
    # So const ◇ (x ◇ R_const(x)) = x, meaning L_const(x ◇ R_const(x)) = x
    # Since L_const = id: x ◇ R_const(x) = x, i.e., L_x(R_const(x)) = x
    # So R_const(x) = L_x^{-1}(x) for all x.

    print(f"\n  R_{const} analysis:")
    for x in range(n):
        r_const_x = mul[x][const]
        l_x_inv_x = mul[x][mul[mul[x][x]][x]]  # L_x^{-1}(x) = x ◇ θ(x) = x ◇ const
        print(f"    R_{const}({x}) = {r_const_x}, "
              f"x◇const = {mul[x][const]}, "
              f"L_x⁻¹(x) = {l_x_inv_x}")


def main():
    print("=" * 60)
    print("CORRECTING THE θ-INJECTIVITY ERROR")
    print("=" * 60)

    print("""
FINDING: θ-injectivity is NOT equivalent to E255.
The F_7 linear magma (a=4, b=1) has θ constant (= 0)
yet E255 holds because 0 is a universal left identity.

The correct reduction is: E255 ⟺ ∀x, θ(x)◇x = x.
This does NOT require θ to be injective.
    """)

    # Phase 1: Find and analyze the θ-non-injective E677 magma
    table = z3_find_theta_noninj_with_table(7)
    if table:
        analyze_why_e255_holds(table, 7)

    # Phase 2: Also check the known linear example
    print(f"\n{'='*60}")
    print(f"KNOWN LINEAR EXAMPLE: F_7, a=4, b=1")
    print(f"{'='*60}")
    mul = [[(4*x + y) % 7 for y in range(7)] for x in range(7)]
    assert check_e677(mul, 7)
    print_table(mul, 7)
    t_map = [theta(mul, z) for z in range(7)]
    print(f"θ map: {t_map}")
    e255_ok, _ = check_e255(mul, 7)
    print(f"E255: {'✓' if e255_ok else '✗'}")
    if e255_ok:
        analyze_why_e255_holds(mul, 7)

    # Phase 3: Direct search for E677 + NOT E255
    print(f"\n{'='*60}")
    print(f"DIRECT COUNTEREXAMPLE SEARCH: E677 + ¬E255")
    print(f"{'='*60}")
    for n in [7, 8]:
        result = z3_direct_e255_counterexample(n, timeout_ms=300000)
        if result:
            print(f"\n*** COUNTEREXAMPLE TO E677 ⊨_fin E255 FOUND AT SIZE {n}! ***")
            return 0

    print(f"\n{'='*60}")
    print(f"REVISED STRATEGY")
    print(f"{'='*60}")
    print("""
Since θ-injectivity ≠ E255, we need a different approach.

The direct question: does E677 + finiteness force θ(x)◇x = x?

Key structural fact: θ(x) = L_x⁻²(x), so E255 says the element
2 steps back in the L_x-orbit acts as a left identity for x.

In orbit notation: x_{p-2} ◇ x_0 = x_0 where x_k = L_x^k(x), period p.

New approach ideas:
1. Study the constraint L_{S(z)}(z) = θ(z) — this maps each z to its
   "left-identity candidate" and is always well-defined.
2. E255 says: the element that z maps to via this candidate-map also
   left-fixes z. This is a DYNAMICAL CONSTRAINT on the iteration structure.
3. Perhaps decompose by orbit period and handle each case.
    """)

    return 1


if __name__ == '__main__':
    sys.exit(main())
