#!/usr/bin/env python3
"""
Minimal criminal analysis for E677 -> E255.

If M is a smallest finite E677 magma failing E255 at some element x,
what structural constraints does this impose?

Key questions:
1. Sub-magma structure: which subsets of M are closed under ◇?
2. The d_k recurrence visits elements outside the orbit — do those
   elements, together with the orbit, generate a proper sub-magma?
3. If a proper sub-magma exists, does it satisfy E677? If so, does
   it satisfy E255 (by minimality)? Can we derive a contradiction?
4. What is the relationship between different L_x orbits?

We test on known models (size 7, Jihoon n=31, Adam n=35) and also
use SAT/Z3 to probe structural constraints on hypothetical criminals.
"""

import sys
from collections import defaultdict
from itertools import combinations


# ══════════════════════════════════════════════════════════════════════
# MODEL DEFINITIONS
# ══════════════════════════════════════════════════════════════════════

def jihoon_model():
    N = 31
    return [[(5*x + 27*y + 1) % N for y in range(N)] for x in range(N)], N

def adam_model():
    TABLE = [
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
    return TABLE, 35


# ══════════════════════════════════════════════════════════════════════
# CORE FUNCTIONS
# ══════════════════════════════════════════════════════════════════════

def check_e677(mul, n):
    for x in range(n):
        for y in range(n):
            if mul[y][mul[x][mul[mul[y][x]][y]]] != x:
                return False
    return True

def check_e255(mul, n):
    for x in range(n):
        if mul[mul[mul[x][x]][x]][x] != x:
            return False
    return True

def orbit_of(mul, x, n):
    """Return L_x orbit: [c_0=x, c_1=x◇x, c_2=L_x(c_1), ...]"""
    orbit = [x]
    cur = x
    for _ in range(n):
        cur = mul[x][cur]  # L_x(cur)
        if cur == orbit[0]:
            break
        orbit.append(cur)
    return orbit

def d_sequence(mul, x, orbit):
    """Compute d_k = c_k ◇ x for orbit elements c_k."""
    return [mul[c][x] for c in orbit]

def closure(mul, n, subset):
    """Compute the closure of a subset under ◇."""
    closed = set(subset)
    changed = True
    while changed:
        changed = False
        new = set()
        for a in closed:
            for b in closed:
                v = mul[a][b]
                if v not in closed:
                    new.add(v)
                    changed = True
        closed |= new
    return closed

def all_sub_magmas(mul, n, min_size=2):
    """Find all sub-magmas (subsets closed under ◇) of size >= min_size."""
    subs = []
    # Try closures of all small subsets
    for size in range(1, min(5, n)):
        for combo in combinations(range(n), size):
            c = closure(mul, n, combo)
            if min_size <= len(c) < n:
                fc = frozenset(c)
                if fc not in [frozenset(s) for s in subs]:
                    subs.append(sorted(c))
    return subs

def is_e677_submagma(mul, subset):
    """Check if a subset closed under ◇ satisfies E677."""
    for x in subset:
        for y in subset:
            if mul[y][mul[x][mul[mul[y][x]][y]]] != x:
                return False
    return True


# ══════════════════════════════════════════════════════════════════════
# ANALYSIS 1: Sub-magma structure of known models
# ══════════════════════════════════════════════════════════════════════

def analyze_submagmas(mul, n, name):
    print(f"\n{'='*60}")
    print(f"SUB-MAGMA ANALYSIS: {name} (size {n})")
    print(f"{'='*60}")

    # Find all sub-magmas
    subs = all_sub_magmas(mul, n)
    print(f"\nFound {len(subs)} proper sub-magmas (size 2 to {n-1}):")
    for s in subs:
        is_e677 = is_e677_submagma(mul, s)
        e255_ok = all(mul[mul[mul[x][x]][x]][x] == x for x in s)
        idem = all(mul[x][x] == x for x in s)
        print(f"  Size {len(s):3d}: elements={s[:10]}{'...' if len(s)>10 else ''}"
              f"  E677={'Y' if is_e677 else 'N'}  E255={'Y' if e255_ok else 'N'}"
              f"  all_idem={'Y' if idem else 'N'}")


# ══════════════════════════════════════════════════════════════════════
# ANALYSIS 2: Orbit + d_k closure
# ══════════════════════════════════════════════════════════════════════

def analyze_orbit_closure(mul, n, name):
    print(f"\n{'='*60}")
    print(f"ORBIT + d_k CLOSURE ANALYSIS: {name} (size {n})")
    print(f"{'='*60}")

    for x in range(min(n, 10)):  # Test first 10 elements
        orb = orbit_of(mul, x, n)
        p = len(orb)
        if p <= 1:
            continue  # Skip idempotents

        dk = d_sequence(mul, x, orb)
        orb_set = set(orb)
        dk_outside = [d for d in dk if d not in orb_set]

        # Closure of orbit alone
        orb_closure = closure(mul, n, orb)

        # Closure of orbit + d_k values
        all_dk = set(dk)
        orb_dk_closure = closure(mul, n, set(orb) | all_dk)

        # Which d_k are in orbit?
        dk_in_orbit = sum(1 for d in dk if d in orb_set)

        print(f"\n  x={x}, period={p}")
        print(f"    orbit = {orb}")
        print(f"    d_k   = {dk}")
        print(f"    d_k in orbit: {dk_in_orbit}/{p}")
        print(f"    d_k outside orbit: {dk_outside}")
        print(f"    closure(orbit)     = size {len(orb_closure)}"
              f" {'= M' if len(orb_closure)==n else '⊊ M'}")
        print(f"    closure(orbit∪d_k) = size {len(orb_dk_closure)}"
              f" {'= M' if len(orb_dk_closure)==n else '⊊ M'}")

        # Check single-point identity
        if p >= 5:
            sp_holds = (mul[orb[p-4]][orb[p-4]] == orb[p-5])
            print(f"    c_{{p-4}}^2 = c_{{p-5}}: {sp_holds}")

        # Check: is orbit closure an E677 sub-magma?
        if len(orb_closure) < n:
            is_e677_sub = is_e677_submagma(mul, sorted(orb_closure))
            print(f"    orbit closure is E677 sub-magma: {is_e677_sub}")


# ══════════════════════════════════════════════════════════════════════
# ANALYSIS 3: L_x orbit partition and cross-orbit structure
# ══════════════════════════════════════════════════════════════════════

def analyze_orbit_partition(mul, n, name):
    print(f"\n{'='*60}")
    print(f"ORBIT PARTITION ANALYSIS: {name} (size {n})")
    print(f"{'='*60}")

    # For each element, compute its L_x orbit
    # Note: different x give different L_x, so different partitions
    # But L_x orbits for a FIXED x partition M.

    for x in range(min(n, 5)):
        orb_x = orbit_of(mul, x, n)
        p = len(orb_x)
        if p <= 1:
            continue

        # L_x orbits partition M
        visited = set()
        orbits = []
        for start in range(n):
            if start in visited:
                continue
            orb = []
            cur = start
            for _ in range(n + 1):
                if cur in visited:
                    break
                visited.add(cur)
                orb.append(cur)
                cur = mul[x][cur]  # L_x(cur)
            orbits.append(orb)

        print(f"\n  x={x}: L_x orbits partition M into {len(orbits)} orbits")
        for i, orb in enumerate(orbits):
            print(f"    orbit {i}: size {len(orb)}, elements={orb[:15]}{'...' if len(orb)>15 else ''}")

        # Key question: do all L_x orbits have the same period?
        periods = [len(o) for o in orbits]
        print(f"    periods: {sorted(periods)}")

        # For each L_x orbit, check if E255 holds at its elements
        for orb in orbits:
            e255_status = [mul[mul[mul[z][z]][z]][z] == z for z in orb]
            all_ok = all(e255_status)
            print(f"    orbit starting {orb[0]}: E255 {'all pass' if all_ok else 'SOME FAIL'}")


# ══════════════════════════════════════════════════════════════════════
# ANALYSIS 4: Cross-orbit d_k interactions
# ══════════════════════════════════════════════════════════════════════

def analyze_dk_cross_orbit(mul, n, name):
    print(f"\n{'='*60}")
    print(f"d_k CROSS-ORBIT ANALYSIS: {name} (size {n})")
    print(f"{'='*60}")

    for x in range(min(n, 5)):
        orb_x = orbit_of(mul, x, n)
        p = len(orb_x)
        if p <= 2:
            continue

        orb_set = set(orb_x)
        dk = d_sequence(mul, x, orb_x)

        print(f"\n  x={x}, period={p}, orbit={orb_x}")

        # For each d_k outside the orbit, what L_x orbit does it belong to?
        for k, d in enumerate(dk):
            if d not in orb_set:
                # Find which L_x orbit d belongs to
                d_orb = orbit_of(mul, x, n)  # wrong — need L_x orbit of d
                cur = d
                d_lx_orbit = [cur]
                for _ in range(n):
                    cur = mul[x][cur]
                    if cur == d_lx_orbit[0]:
                        break
                    d_lx_orbit.append(cur)

                # What is d's own L_d orbit?
                d_own_orbit = orbit_of(mul, d, n)

                print(f"    d_{k} = {d} (outside orbit)")
                print(f"      L_x orbit of d_{k}: period {len(d_lx_orbit)}")
                print(f"      L_d orbit of d_{k}: period {len(d_own_orbit)}")

                # Key: what does E677(x, d_k) tell us?
                # E677: x = d_k ◇ (x ◇ ((d_k ◇ x) ◇ d_k))
                dk_x = mul[d][x]        # d_k ◇ x
                dk_x_dk = mul[dk_x][d]  # (d_k ◇ x) ◇ d_k
                x_term = mul[x][dk_x_dk] # x ◇ ((d_k ◇ x) ◇ d_k)
                result = mul[d][x_term]  # d_k ◇ (...)
                print(f"      E677(x, d_{k}): {d}◇(...)  = {result} (should be {x}): {'OK' if result==x else 'FAIL'}")

                # What about E677(d_k, x)?
                x_dk = mul[x][d]          # x ◇ d_k
                x_dk_x = mul[x_dk][x]     # (x ◇ d_k) ◇ x
                dk_term = mul[d][x_dk_x]  # d_k ◇ ((x ◇ d_k) ◇ x)
                result2 = mul[x][dk_term] # x ◇ (...)
                print(f"      E677(d_{k}, x): x◇(...)  = {result2} (should be {d}): {'OK' if result2==d else 'FAIL'}")


# ══════════════════════════════════════════════════════════════════════
# ANALYSIS 5: Generation structure — what generates M?
# ══════════════════════════════════════════════════════════════════════

def analyze_generation(mul, n, name):
    print(f"\n{'='*60}")
    print(f"GENERATION ANALYSIS: {name} (size {n})")
    print(f"{'='*60}")

    # For each element, what does {x} generate?
    gen_sizes = {}
    for x in range(n):
        c = closure(mul, n, [x])
        gen_sizes[x] = len(c)

    size_counts = defaultdict(list)
    for x, s in gen_sizes.items():
        size_counts[s].append(x)

    print(f"\n  Single-element generation:")
    for s in sorted(size_counts.keys()):
        elts = size_counts[s]
        print(f"    <x> has size {s}: {len(elts)} elements"
              f" (e.g., x={elts[:5]})")

    # For each pair, what does {x,y} generate?
    if n <= 35:
        pair_gens = {}
        for x in range(n):
            for y in range(x+1, n):
                c = closure(mul, n, [x, y])
                if len(c) == n:
                    pair_gens[(x,y)] = len(c)

        print(f"\n  2-element generation to full M: {len(pair_gens)} pairs generate M")
        if pair_gens:
            # Sample
            items = list(pair_gens.items())[:5]
            for (x,y), s in items:
                print(f"    <{x},{y}> generates M (size {s})")

    # Key for minimal criminal: if M is 2-generated and one generator
    # is in the orbit, what does that constrain?
    for x in range(min(n, 3)):
        orb = orbit_of(mul, x, n)
        if len(orb) <= 1:
            continue
        orb_closure = closure(mul, n, orb)
        if len(orb_closure) < n:
            # Orbit doesn't generate M. What's the smallest set that
            # extends the orbit to generate M?
            print(f"\n  x={x}: orbit (size {len(orb)}) generates {len(orb_closure)}/{n} elements")
            for y in range(n):
                if y in orb_closure:
                    continue
                ext = closure(mul, n, list(orb_closure) + [y])
                if len(ext) == n:
                    print(f"    orbit + {y} generates M")
                    break
        else:
            print(f"\n  x={x}: orbit (size {len(orb)}) already generates M")


# ══════════════════════════════════════════════════════════════════════
# ANALYSIS 6: Enumerate size-7 magmas and run all analyses
# ══════════════════════════════════════════════════════════════════════

def enumerate_size7():
    """Enumerate size-7 E677 magmas using Z3."""
    try:
        from z3 import Solver, Int, Distinct, Implies, Or, sat
    except ImportError:
        print("Z3 not available, skipping enumeration")
        return []

    n = 7
    s = Solver()
    s.set("timeout", 300000)
    m = [[Int(f'm_{i}_{j}') for j in range(n)] for i in range(n)]
    for i in range(n):
        for j in range(n):
            s.add(m[i][j] >= 0, m[i][j] < n)
    # L_y is a permutation (each row is a permutation)
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

    magmas = []
    while len(magmas) < 50:
        result = s.check()
        if result != sat:
            break
        model = s.model()
        table = [[model.eval(m[i][j]).as_long() for j in range(n)] for i in range(n)]
        magmas.append(table)
        s.add(Or([m[i][j] != table[i][j] for i in range(n) for j in range(n)]))

    print(f"\nEnumerated {len(magmas)} size-7 E677 magmas")
    return magmas


# ══════════════════════════════════════════════════════════════════════
# MAIN
# ══════════════════════════════════════════════════════════════════════

if __name__ == '__main__':
    # Test on Jihoon model
    mul_j, n_j = jihoon_model()
    assert check_e677(mul_j, n_j), "Jihoon model fails E677!"
    assert check_e255(mul_j, n_j), "Jihoon model fails E255!"

    analyze_orbit_closure(mul_j, n_j, "Jihoon (size 31)")
    analyze_orbit_partition(mul_j, n_j, "Jihoon (size 31)")
    analyze_dk_cross_orbit(mul_j, n_j, "Jihoon (size 31)")
    analyze_generation(mul_j, n_j, "Jihoon (size 31)")

    # Test on Adam model
    mul_a, n_a = adam_model()
    assert check_e677(mul_a, n_a), "Adam model fails E677!"
    assert check_e255(mul_a, n_a), "Adam model fails E255!"

    analyze_orbit_closure(mul_a, n_a, "Adam (size 35)")
    analyze_orbit_partition(mul_a, n_a, "Adam (size 35)")
    analyze_dk_cross_orbit(mul_a, n_a, "Adam (size 35)")
    analyze_generation(mul_a, n_a, "Adam (size 35)")

    # Enumerate and test size-7
    print(f"\n{'='*60}")
    print(f"SIZE-7 ANALYSIS")
    print(f"{'='*60}")
    magmas7 = enumerate_size7()
    if magmas7:
        # Run sub-magma analysis on first few
        for i, mul7 in enumerate(magmas7[:5]):
            analyze_submagmas(mul7, 7, f"Size-7 #{i}")
            analyze_orbit_closure(mul7, 7, f"Size-7 #{i}")
            analyze_generation(mul7, 7, f"Size-7 #{i}")

        # Aggregate statistics across all size-7 magmas
        print(f"\n{'='*60}")
        print(f"AGGREGATE SIZE-7 STATISTICS ({len(magmas7)} magmas)")
        print(f"{'='*60}")

        sub_magma_counts = []
        orbit_generates_m = 0
        total_non_idem = 0

        for mul7 in magmas7:
            subs = all_sub_magmas(mul7, 7)
            sub_magma_counts.append(len(subs))

            for x in range(7):
                orb = orbit_of(mul7, x, 7)
                if len(orb) > 1:
                    total_non_idem += 1
                    c = closure(mul7, 7, orb)
                    if len(c) == 7:
                        orbit_generates_m += 1

        print(f"\n  Sub-magma counts: min={min(sub_magma_counts)}, "
              f"max={max(sub_magma_counts)}, "
              f"mean={sum(sub_magma_counts)/len(sub_magma_counts):.1f}")
        print(f"  Non-idempotent orbits generating M: "
              f"{orbit_generates_m}/{total_non_idem}")
