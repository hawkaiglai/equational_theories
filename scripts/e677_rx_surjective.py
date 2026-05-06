#!/usr/bin/env python3
"""
Attempting to prove R_x surjective from E677.

E677: a = b ◇ (a ◇ ((b◇a)◇b))

Key algebraic identities derived from E677:
  L_b^{-1}(a) = a ◇ ((b◇a)◇b)                    ... (*)

Strategy: show that for any x, t ∈ M, ∃y: y◇x = t.

From (*) with b = x:
  L_x^{-1}(a) = a ◇ ((x◇a)◇x) = a ◇ R_x(L_x(a))

Let u = L_x(a), so a = L_x^{-1}(u):
  L_x^{-1}(L_x^{-1}(u)) = L_x^{-1}(u) ◇ R_x(u)
  L_x^{-2}(u) = R_{R_x(u)}(L_x^{-1}(u))

So: L_x^{-1}(u) ◇ R_x(u) = L_x^{-2}(u)

This means: R_{R_x(u)}(L_x^{-1}(u)) = L_x^{-2}(u)

As u varies over M: R_x(u) varies over image(R_x).

============================================================

Alternative approach: Use Z3 to try to find E677 model where
R_x is NOT bijective. If UNSAT, it's forced.
Then try to extract a proof from the UNSAT core.

Also: try Prover9 to prove R_x surjective from E677.
"""

import sys
import time
from z3 import *


def test_rx_not_bijective(n, timeout_ms=300000):
    """Try to find E677 magma of size n where some R_x is not bijective."""
    print(f"\nSearching for E677 magma of size {n} with R_x NOT bijective...")

    s = Solver()
    s.set("timeout", timeout_ms)

    m = [[Int(f'm_{i}_{j}') for j in range(n)] for i in range(n)]

    # Domain
    for i in range(n):
        for j in range(n):
            s.add(m[i][j] >= 0, m[i][j] < n)

    # L_x bijective (rows are permutations)
    for i in range(n):
        s.add(Distinct([m[i][j] for j in range(n)]))

    # E677
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

    # Assert: some column is NOT a permutation
    # i.e., ∃x: R_x not injective, i.e., ∃x,y1,y2: y1≠y2 ∧ y1◇x = y2◇x
    x = Int('rx_x')
    y1 = Int('rx_y1')
    y2 = Int('rx_y2')
    s.add(x >= 0, x < n)
    s.add(y1 >= 0, y1 < n)
    s.add(y2 >= 0, y2 < n)
    s.add(y1 != y2)

    # Skip the first solver and use the clean one below

    s_clean = Solver()
    s_clean.set("timeout", timeout_ms)

    m2 = [[Int(f'm_{i}_{j}') for j in range(n)] for i in range(n)]

    for i in range(n):
        for j in range(n):
            s_clean.add(m2[i][j] >= 0, m2[i][j] < n)
    for i in range(n):
        s_clean.add(Distinct([m2[i][j] for j in range(n)]))

    # E677
    for a in range(n):
        for b in range(n):
            t1 = m2[b][a]
            t2 = Int(f'f1_{a}_{b}')
            s_clean.add(t2 >= 0, t2 < n)
            for v in range(n):
                s_clean.add(Implies(t1 == v, t2 == m2[v][b]))
            t3 = Int(f'f2_{a}_{b}')
            s_clean.add(t3 >= 0, t3 < n)
            for v in range(n):
                s_clean.add(Implies(t2 == v, t3 == m2[a][v]))
            t4 = Int(f'f3_{a}_{b}')
            s_clean.add(t4 >= 0, t4 < n)
            for v in range(n):
                s_clean.add(Implies(t3 == v, t4 == m2[b][v]))
            s_clean.add(t4 == a)

    # NOT all columns are permutations
    col_not_perm = []
    for x in range(n):
        col_not_perm.append(Not(Distinct([m2[y][x] for y in range(n)])))
    s_clean.add(Or(col_not_perm))

    start = time.time()
    result = s_clean.check()
    elapsed = time.time() - start

    if result == sat:
        print(f"  SAT in {elapsed:.1f}s — R_x NOT always bijective!")
        model = s_clean.model()
        table = [[model.eval(m2[i][j]).as_long() for j in range(n)] for i in range(n)]
        print(f"  Table:")
        for row in table:
            print(f"    {row}")
        # Check which columns are not permutations
        for x in range(n):
            col = [table[y][x] for y in range(n)]
            if len(set(col)) != n:
                print(f"  Column {x} NOT a permutation: {col}")
        return True
    elif result == unsat:
        print(f"  UNSAT in {elapsed:.1f}s — R_x bijective is FORCED by E677 at size {n}!")
        return False
    else:
        print(f"  UNKNOWN/timeout after {elapsed:.1f}s")
        return None


def test_theta_fixer_direct(n, timeout_ms=300000):
    """
    Try to find E677 quasigroup where θ(x)◇x ≠ x for some x.
    If UNSAT, then E677 + quasigroup → E255.
    """
    print(f"\nSearching for E677 quasigroup of size {n} where θ(x)◇x ≠ x...")

    s = Solver()
    s.set("timeout", timeout_ms)

    m = [[Int(f'm_{i}_{j}') for j in range(n)] for i in range(n)]

    for i in range(n):
        for j in range(n):
            s.add(m[i][j] >= 0, m[i][j] < n)

    # Rows AND columns are permutations (quasigroup)
    for i in range(n):
        s.add(Distinct([m[i][j] for j in range(n)]))
    for j in range(n):
        s.add(Distinct([m[i][j] for i in range(n)]))

    # E677
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

    # ∃x: θ(x)◇x ≠ x, where θ(x) = (x◇x)◇x
    # θ(x) = m[m[x][x]][x]
    theta_neq = []
    for x in range(n):
        # xx = x◇x
        xx = m[x][x]
        # θ = xx◇x = m[xx][x] — but xx is a Z3 expression
        th = Int(f'theta_{x}')
        s.add(th >= 0, th < n)
        for v in range(n):
            s.add(Implies(xx == v, th == m[v][x]))
        # θ◇x = m[th][x]
        th_x = Int(f'thx_{x}')
        s.add(th_x >= 0, th_x < n)
        for v in range(n):
            s.add(Implies(th == v, th_x == m[v][x]))
        theta_neq.append(th_x != x)

    s.add(Or(theta_neq))

    start = time.time()
    result = s.check()
    elapsed = time.time() - start

    if result == sat:
        print(f"  SAT in {elapsed:.1f}s — E677 quasigroup with E255 failure!")
        model = s.model()
        table = [[model.eval(m[i][j]).as_long() for j in range(n)] for i in range(n)]
        print(f"  Table:")
        for row in table:
            print(f"    {row}")
        for x in range(n):
            th = table[table[x][x]][x]
            thx = table[th][x]
            if thx != x:
                print(f"  θ({x}) = {th}, θ({x})◇{x} = {thx} ≠ {x}")
    elif result == unsat:
        print(f"  UNSAT in {elapsed:.1f}s — E677 + quasigroup → E255 at size {n}!")
    else:
        print(f"  UNKNOWN/timeout after {elapsed:.1f}s")


def algebraic_exploration(mul, n):
    """
    For a single E677 magma, explore the algebraic identity
    that makes R_x surjective.

    From E677: L_b^{-1}(a) = a ◇ ((b◇a)◇b)
    Set b = x: L_x^{-1}(a) = a ◇ R_x(L_x(a))

    This gives: R_x(L_x(a)) = L_a^{-1}(L_x^{-1}(a))... no wait.

    Let me just verify: L_x^{-1}(a) = a ◇ R_x(L_x(a))
    i.e., L_x^{-1}(a) = a ◇ ((x◇a)◇x)
    """
    print(f"\nAlgebraic exploration (n={n}):")

    def L(y, z):
        return mul[y][z]

    def R(x, y):
        return mul[y][x]

    def L_inv(b, a):
        """L_b^{-1}(a) from E677: a ◇ ((b◇a)◇b)"""
        return mul[a][mul[mul[b][a]][b]]

    # Verify L_b^{-1} formula
    ok = True
    for b in range(n):
        for a in range(n):
            li = L_inv(b, a)
            if L(b, li) != a:
                print(f"  L_inv FAIL: L_{b}(L_{b}^-1({a})) = {L(b,li)} ≠ {a}")
                ok = False
    print(f"  L_inv formula verified: {'✓' if ok else '✗'}")

    # Key identity: L_x^{-1}(a) = a ◇ R_x(L_x(a))
    # i.e., L_x^{-1}(a) = R_{R_x(L_x(a))}(a)
    print(f"\n  Checking: L_x^{{-1}}(a) = a ◇ R_x(L_x(a)):")
    ok = True
    for x in range(n):
        for a in range(n):
            lhs = L_inv(x, a)
            rhs = mul[a][R(x, L(x, a))]
            if lhs != rhs:
                print(f"    FAIL: x={x}, a={a}: {lhs} ≠ {rhs}")
                ok = False
    print(f"  Verified: {'✓' if ok else '✗'}")

    # Define Φ_x(a) = R_x(L_x(a)) = (x◇a)◇x
    # Then: L_x^{-1}(a) = a ◇ Φ_x(a) = R_{Φ_x(a)}(a)
    # So Φ_x(a) = L_a^{-1}(L_x^{-1}(a))...
    # Actually: a ◇ Φ_x(a) = L_x^{-1}(a), so Φ_x(a) = L_a^{-1}(L_x^{-1}(a))

    print(f"\n  Φ_x(a) = R_x(L_x(a)) = (x◇a)◇x:")
    for x in range(min(n, 3)):
        phi = [R(x, L(x, a)) for a in range(n)]
        is_perm = len(set(phi)) == n
        print(f"    Φ_{x} = {phi}  perm={'✓' if is_perm else '✗'}")

    # If Φ_x is a bijection, then R_x ∘ L_x is a bijection,
    # so R_x must be surjective (since L_x is bijective,
    # R_x ∘ L_x = bijection → R_x is surjective).
    print(f"\n  Checking if Φ_x = R_x ∘ L_x is always a bijection:")
    all_perm = True
    for x in range(n):
        phi = [R(x, L(x, a)) for a in range(n)]
        if len(set(phi)) != n:
            all_perm = False
            print(f"    Φ_{x} NOT a permutation: {phi}")
    print(f"  All Φ_x bijective: {'✓' if all_perm else '✗'}")

    if all_perm:
        print(f"\n  *** KEY: Φ_x = R_x ∘ L_x is a bijection ***")
        print(f"  Since L_x is bijective, R_x must be SURJECTIVE.")
        print(f"  On finite set, R_x surjective → R_x bijective. QED.")


def main():
    # Test R_x non-bijective search
    for n in [5, 6, 7]:
        test_rx_not_bijective(n, timeout_ms=120000)

    # Test θ-fixer in quasigroup context
    for n in [5, 6, 7, 8]:
        test_theta_fixer_direct(n, timeout_ms=120000)

    # Algebraic exploration on known magmas
    # Use a size-7 E677 magma from enumeration
    print(f"\n{'=' * 60}")
    print("Algebraic exploration on size-7 example")
    print("=" * 60)

    # Quick enumeration to get one example
    from z3 import Solver, Int, Implies, Distinct, Or, sat
    s = Solver()
    s.set("timeout", 60000)
    n = 7
    m = [[Int(f'm_{i}_{j}') for j in range(n)] for i in range(n)]
    for i in range(n):
        for j in range(n):
            s.add(m[i][j] >= 0, m[i][j] < n)
    for i in range(n):
        s.add(Distinct([m[i][j] for j in range(n)]))
    for a in range(n):
        for b in range(n):
            t1 = m[b][a]
            t2 = Int(f'f1_{a}_{b}')
            s.add(t2 >= 0, t2 < n)
            for v in range(n):
                s.add(Implies(t1 == v, t2 == m[v][b]))
            t3 = Int(f'f2_{a}_{b}')
            s.add(t3 >= 0, t3 < n)
            for v in range(n):
                s.add(Implies(t2 == v, t3 == m[a][v]))
            t4 = Int(f'f3_{a}_{b}')
            s.add(t4 >= 0, t4 < n)
            for v in range(n):
                s.add(Implies(t3 == v, t4 == m[b][v]))
            s.add(t4 == a)

    if s.check() == sat:
        model = s.model()
        table = [[model.eval(m[i][j]).as_long() for j in range(n)] for i in range(n)]
        algebraic_exploration(table, n)

    # Also on n=35
    print(f"\n{'=' * 60}")
    print("Algebraic exploration on n=35 example")
    print("=" * 60)

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
    algebraic_exploration(TABLE_35, 35)


if __name__ == '__main__':
    main()
