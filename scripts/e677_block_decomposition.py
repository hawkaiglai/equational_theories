#!/usr/bin/env python3
"""
Block Decomposition Conjecture for E677 Magmas
================================================

Conjecture: Every finite E677 magma (M, ◇) satisfies:
  1. M has at least one idempotent (e◇e = e)
  2. For each idempotent e, Fix(L_e) = {x : e◇x = x} is a sub-block
  3. The Fix(L_e) blocks partition M
  4. Within each block, all elements have the same L_x orbit period
  5. E255 holds: ((x◇x)◇x)◇x = x for all x

This script enumerates E677 magmas up to a given size via Z3 and
verifies all five conjecture properties. A single failure is a
counterexample that kills the structural proof approach.

Usage: python e677_block_decomposition.py [max_size] [max_models_per_size]
"""

import sys
import time
from z3 import *


# ── Core checks ───────────────────────────────────────────────────────

def check_e677_table(mul, n):
    """Verify E677: a = b ◇ (a ◇ ((b◇a)◇b)) for all a,b."""
    for a in range(n):
        for b in range(n):
            ba = mul[b][a]
            ba_b = mul[ba][b]
            a_ba_b = mul[a][ba_b]
            rhs = mul[b][a_ba_b]
            if rhs != a:
                return False
    return True


def check_e255(mul, x):
    """Check ((x◇x)◇x)◇x = x."""
    return mul[mul[mul[x][x]][x]][x] == x


def theta(mul, z):
    """θ(z) = (z◇z)◇z = L_z^{-2}(z)."""
    return mul[mul[z][z]][z]


def orbit_of(mul, z, n):
    """L_z-orbit of z: [z, z◇z, z◇(z◇z), ...]."""
    orbit = [z]
    cur = z
    for _ in range(n):
        cur = mul[z][cur]
        if cur == orbit[0]:
            break
        orbit.append(cur)
    return orbit


def analyze_block_decomposition(mul, n, verbose=False):
    """
    Analyze all five conjecture properties for a single E677 magma.

    Returns dict with:
      'e255_ok': bool
      'has_idempotent': bool
      'idempotents': list
      'partition_ok': bool
      'uniform_period': bool
      'blocks': dict mapping idempotent -> Fix(L_e)
      'block_periods': dict mapping idempotent -> set of periods in block
      'issues': list of strings
    """
    issues = []

    # Property 5: E255 for all elements
    e255_fails = [x for x in range(n) if not check_e255(mul, x)]
    e255_ok = len(e255_fails) == 0
    if not e255_ok:
        issues.append(f"E255 fails at {e255_fails}")

    # Property 1: idempotents exist
    idempotents = [e for e in range(n) if mul[e][e] == e]
    has_idempotent = len(idempotents) > 0
    if not has_idempotent:
        issues.append("NO IDEMPOTENTS")

    # Property 2 & 3: Fix(L_e) blocks partition M
    blocks = {}
    for e in idempotents:
        fix_e = [x for x in range(n) if mul[e][x] == x]
        blocks[e] = fix_e

    # Check partition: every element belongs to exactly one block
    element_to_blocks = {x: [] for x in range(n)}
    for e, fix in blocks.items():
        for x in fix:
            element_to_blocks[x].append(e)

    uncovered = [x for x in range(n) if len(element_to_blocks[x]) == 0]
    multi_covered = [x for x in range(n) if len(element_to_blocks[x]) > 1]
    partition_ok = len(uncovered) == 0 and len(multi_covered) == 0

    if uncovered:
        issues.append(f"Elements not in any Fix(L_e): {uncovered}")
    if multi_covered:
        issues.append(f"Elements in multiple blocks: {multi_covered} -> {[(x, element_to_blocks[x]) for x in multi_covered]}")

    # Property 4: uniform orbit period within each block
    orbits = {z: orbit_of(mul, z, n) for z in range(n)}
    periods = {z: len(orbits[z]) for z in range(n)}

    block_periods = {}
    uniform_period = True
    for e, fix in blocks.items():
        ps = set(periods[x] for x in fix)
        block_periods[e] = ps
        if len(ps) > 1:
            uniform_period = False
            issues.append(f"Block Fix(L_{e}) has mixed periods: {ps}")

    # Additional: θ(z)◇z = z for all z (equivalent to E255)
    theta_fix = all(mul[theta(mul, z)][z] == z for z in range(n))

    # Additional: block sizes
    block_sizes = {e: len(fix) for e, fix in blocks.items()}

    # Additional: are all blocks the same size?
    sizes = set(block_sizes.values())
    uniform_blocks = len(sizes) <= 1

    # Additional: does each idempotent belong to its own block?
    idem_in_own = all(e in blocks[e] for e in idempotents) if idempotents else True

    # Additional: is θ constant within each block?
    theta_map = {z: theta(mul, z) for z in range(n)}
    theta_image_per_block = {}
    for e, fix in blocks.items():
        theta_vals = set(theta_map[x] for x in fix)
        theta_image_per_block[e] = theta_vals

    return {
        'n': n,
        'e255_ok': e255_ok,
        'e255_fails': e255_fails,
        'has_idempotent': has_idempotent,
        'idempotents': idempotents,
        'num_idempotents': len(idempotents),
        'partition_ok': partition_ok,
        'uncovered': uncovered,
        'multi_covered': multi_covered,
        'uniform_period': uniform_period,
        'blocks': blocks,
        'block_sizes': block_sizes,
        'block_periods': block_periods,
        'uniform_blocks': uniform_blocks,
        'idem_in_own': idem_in_own,
        'theta_fix': theta_fix,
        'theta_image_per_block': theta_image_per_block,
        'periods': periods,
        'issues': issues,
    }


# ── Z3 enumeration ───────────────────────────────────────────────────

def enumerate_e677_z3(n, max_count=500, timeout_ms=300000):
    """Enumerate E677 magmas of size n using Z3."""
    s = Solver()
    s.set("timeout", timeout_ms)

    m = [[Int(f'm_{i}_{j}') for j in range(n)] for i in range(n)]

    # Domain constraints
    for i in range(n):
        for j in range(n):
            s.add(m[i][j] >= 0, m[i][j] < n)

    # L_x bijective (each row is a permutation)
    for i in range(n):
        s.add(Distinct([m[i][j] for j in range(n)]))

    # E677: a = b ◇ (a ◇ ((b◇a)◇b)) for all a,b
    # Using auxiliary variables for nested lookups
    for a in range(n):
        for b in range(n):
            # t1 = b◇a = m[b][a]
            t1 = m[b][a]
            # t2 = (b◇a)◇b = m[t1][b] — need aux var
            t2 = Int(f'e1_{a}_{b}')
            s.add(t2 >= 0, t2 < n)
            for v in range(n):
                s.add(Implies(t1 == v, t2 == m[v][b]))
            # t3 = a ◇ t2 = m[a][t2]
            t3 = Int(f'e2_{a}_{b}')
            s.add(t3 >= 0, t3 < n)
            for v in range(n):
                s.add(Implies(t2 == v, t3 == m[a][v]))
            # t4 = b ◇ t3 = m[b][t3]
            t4 = Int(f'e3_{a}_{b}')
            s.add(t4 >= 0, t4 < n)
            for v in range(n):
                s.add(Implies(t3 == v, t4 == m[b][v]))
            # Assert t4 == a
            s.add(t4 == a)

    magmas = []
    start = time.time()

    while len(magmas) < max_count:
        result = s.check()
        if result != sat:
            if result == unknown:
                print(f"    Z3 timeout after {len(magmas)} models")
            break

        model = s.model()
        table = [[model.eval(m[i][j]).as_long() for j in range(n)] for i in range(n)]

        assert check_e677_table(table, n), "E677 verification failed!"
        magmas.append(table)

        # Block this solution
        block = Or([m[i][j] != table[i][j] for i in range(n) for j in range(n)])
        s.add(block)

        if len(magmas) % 50 == 0:
            elapsed = time.time() - start
            print(f"    Found {len(magmas)} models ({elapsed:.1f}s)...")

    elapsed = time.time() - start
    print(f"    Size {n}: {len(magmas)} E677 magmas found ({elapsed:.1f}s)")
    return magmas


# ── Main ──────────────────────────────────────────────────────────────

def main():
    max_size = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    max_models = int(sys.argv[2]) if len(sys.argv) > 2 else 500

    print("=" * 70)
    print("E677 Block Decomposition Conjecture Verification")
    print("=" * 70)
    print(f"Testing sizes 2..{max_size}, up to {max_models} models per size\n")

    total_models = 0
    total_pass = 0
    total_fail = 0
    all_stats = []

    for n in range(2, max_size + 1):
        print(f"\n{'─' * 50}")
        print(f"  Size n = {n}")
        print(f"{'─' * 50}")

        magmas = enumerate_e677_z3(n, max_count=max_models)

        if not magmas:
            print(f"    No E677 magmas of size {n}")
            continue

        size_pass = 0
        size_fail = 0
        size_stats = {
            'n': n,
            'count': len(magmas),
            'all_e255': True,
            'all_idempotent': True,
            'all_partition': True,
            'all_uniform_period': True,
            'period_sets': set(),
            'block_size_sets': set(),
            'idem_counts': [],
        }

        for idx, mul in enumerate(magmas):
            result = analyze_block_decomposition(mul, n)
            total_models += 1

            ok = (result['e255_ok'] and result['has_idempotent'] and
                  result['partition_ok'] and result['uniform_period'])

            if ok:
                size_pass += 1
                total_pass += 1
            else:
                size_fail += 1
                total_fail += 1
                print(f"\n    *** CONJECTURE FAILURE in magma #{idx+1} ***")
                for issue in result['issues']:
                    print(f"    ISSUE: {issue}")
                print(f"    Idempotents: {result['idempotents']}")
                print(f"    Blocks: {result['blocks']}")
                print(f"    Block periods: {result['block_periods']}")
                if not result['e255_ok']:
                    print(f"    E255 fails at: {result['e255_fails']}")
                    print(f"    *** THIS IS A COUNTEREXAMPLE TO E677 ⊨_fin E255 ***")
                    print(f"    Table:")
                    for row in mul:
                        print(f"      {row}")

            if not result['e255_ok']:
                size_stats['all_e255'] = False
            if not result['has_idempotent']:
                size_stats['all_idempotent'] = False
            if not result['partition_ok']:
                size_stats['all_partition'] = False
            if not result['uniform_period']:
                size_stats['all_uniform_period'] = False

            # Collect stats
            for e, ps in result['block_periods'].items():
                size_stats['period_sets'].update(ps)
            for e, sz in result['block_sizes'].items():
                size_stats['block_size_sets'].add(sz)
            size_stats['idem_counts'].append(result['num_idempotents'])

        # Summary for this size
        print(f"\n    Size {n} summary: {size_pass}/{len(magmas)} pass all conjecture properties")
        print(f"      E255 holds universally:    {'✓' if size_stats['all_e255'] else '✗'}")
        print(f"      Idempotents always exist:  {'✓' if size_stats['all_idempotent'] else '✗'}")
        print(f"      Fix(L_e) partitions M:     {'✓' if size_stats['all_partition'] else '✗'}")
        print(f"      Uniform period per block:  {'✓' if size_stats['all_uniform_period'] else '✗'}")
        print(f"      Orbit periods seen:        {sorted(size_stats['period_sets'])}")
        print(f"      Block sizes seen:          {sorted(size_stats['block_size_sets'])}")
        idem_range = (min(size_stats['idem_counts']), max(size_stats['idem_counts']))
        print(f"      Idempotent count range:    {idem_range[0]}..{idem_range[1]}")

        all_stats.append(size_stats)

    # Grand summary
    print(f"\n{'=' * 70}")
    print(f"GRAND SUMMARY")
    print(f"{'=' * 70}")
    print(f"Total models tested: {total_models}")
    print(f"All properties pass: {total_pass}")
    print(f"Failures:            {total_fail}")

    if total_fail == 0:
        print(f"\n✓ CONJECTURE HOLDS for all {total_models} E677 magmas tested (sizes 2..{max_size})")
        print(f"\nStructural proof path remains viable:")
        print(f"  1. Every finite E677 magma has idempotents")
        print(f"  2. Fix(L_e) blocks partition M")
        print(f"  3. Uniform orbit period within each block")
        print(f"  4. E255 holds within each block")
    else:
        print(f"\n✗ CONJECTURE FAILS in {total_fail} models")
        print(f"  The block decomposition approach needs revision.")

    # Additional structural observations
    print(f"\nObserved patterns:")
    all_periods = set()
    all_block_sizes = set()
    for s in all_stats:
        all_periods.update(s['period_sets'])
        all_block_sizes.update(s['block_size_sets'])
    print(f"  All orbit periods:  {sorted(all_periods)}")
    print(f"  All block sizes:    {sorted(all_block_sizes)}")

    # Check: are block sizes always prime?
    from math import gcd
    def is_prime(n):
        if n < 2:
            return False
        for i in range(2, int(n**0.5) + 1):
            if n % i == 0:
                return False
        return True

    all_prime = all(is_prime(s) for s in all_block_sizes if s > 0)
    print(f"  Block sizes always prime: {'✓' if all_prime else '✗'}")

    # Check: block_size = orbit_period?
    print(f"\n  Checking block_size == orbit_period relationship:")
    for s in all_stats:
        if s['count'] > 0:
            print(f"    n={s['n']}: periods={sorted(s['period_sets'])}, "
                  f"block_sizes={sorted(s['block_size_sets'])}")


if __name__ == '__main__':
    main()
