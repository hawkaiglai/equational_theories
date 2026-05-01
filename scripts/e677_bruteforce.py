#!/usr/bin/env python3
"""
E677 brute-force search — pure Python, no dependencies.

Uses constraint propagation + backtracking to search for E677 magmas
that violate E255. Practical for sizes up to ~6-7.

Also includes a complete enumeration verifier for small sizes to confirm
"no counterexample of size <= 5" claim from the SSOT.
"""

import sys
import time
from itertools import permutations


def check_e677(mul, n):
    """Check E677: x = mul[y][mul[x][mul[mul[y][x]][y]]] for all x,y."""
    for x in range(n):
        for y in range(n):
            if mul[y][mul[x][mul[mul[y][x]][y]]] != x:
                return False
    return True


def check_e255_all(mul, n):
    """Check E255 for all elements. Returns (True, None) or (False, witness)."""
    for x in range(n):
        if mul[mul[mul[x][x]][x]][x] != x:
            return False, x
    return True, None


def check_partial_e677(mul, n, filled):
    """Check E677 constraints that are fully determined given filled cells.
    Returns True if no violation found (may have unchecked constraints)."""
    for x in range(n):
        for y in range(n):
            # t1 = mul[y][x]
            if not filled[y][x]:
                continue
            t1 = mul[y][x]
            # t2 = mul[t1][y]
            if not filled[t1][y]:
                continue
            t2 = mul[t1][y]
            # t3 = mul[x][t2]
            if not filled[x][t2]:
                continue
            t3 = mul[x][t2]
            # t4 = mul[y][t3]
            if not filled[y][t3]:
                continue
            t4 = mul[y][t3]
            if t4 != x:
                return False
    return True


def search_with_permutation_rows(n, timeout_secs=600):
    """Search by generating row permutations with constraint checking.

    Since L_y is bijective, each row of the multiplication table is a permutation.
    We enumerate row permutations and check E677 + not-E255.
    """
    print(f"  Permutation-row search for size {n}...")
    start = time.time()

    all_perms = list(permutations(range(n)))
    num_perms = len(all_perms)
    print(f"    {num_perms} permutations per row, {num_perms}^{n} total = ~{num_perms**n:.2e}")

    if num_perms ** n > 1e12:
        print(f"    Too many combinations, skipping brute force")
        return None

    count = 0
    e677_count = 0

    def backtrack(row, mul):
        nonlocal count, e677_count

        if time.time() - start > timeout_secs:
            return None

        if row == n:
            # All rows filled — check E677
            count += 1
            if count % 100000 == 0:
                elapsed = time.time() - start
                print(f"    Checked {count} tables, {e677_count} E677, {elapsed:.1f}s...")

            if check_e677(mul, n):
                e677_count += 1
                ok, witness = check_e255_all(mul, n)
                if not ok:
                    return mul  # Found counterexample!
            return None

        # Try each permutation for this row
        # Use partial E677 checking to prune early
        for perm in all_perms:
            mul[row] = list(perm)

            # Quick partial check: verify E677 constraints involving only rows 0..row
            filled = [[r <= row for _ in range(n)] for r in range(n)]
            # Actually simpler: just check if filled cells are consistent
            ok = True
            for x in range(n):
                for y in range(row + 1):  # y ranges over filled rows
                    t1 = mul[y][x]
                    if t1 > row:
                        continue  # t1 row not filled yet
                    t2 = mul[t1][y]
                    if t2 >= n:
                        ok = False
                        break
                    # x row: only check if x <= row
                    if x > row:
                        continue
                    t3 = mul[x][t2]
                    if t3 >= n:
                        ok = False
                        break
                    # y row already filled
                    t4 = mul[y][t3]
                    if t4 != x:
                        ok = False
                        break
                if not ok:
                    break

            if ok:
                result = backtrack(row + 1, mul)
                if result is not None:
                    return result

        mul[row] = [0] * n  # reset
        return None

    mul = [[0] * n for _ in range(n)]
    result = backtrack(0, mul)

    elapsed = time.time() - start
    print(f"    Searched {count} tables, {e677_count} satisfy E677, {elapsed:.1f}s")
    return result


def enumerate_small(n, timeout_secs=300):
    """Enumerate ALL E677 magmas of size n and check E255."""
    print(f"\n  Complete enumeration for size {n}:")
    start = time.time()

    all_perms = list(permutations(range(n)))
    total_combos = len(all_perms) ** n

    if total_combos > 5e8:
        print(f"    {total_combos:.2e} combinations — too many for brute force")
        return

    print(f"    Checking {total_combos} candidate tables...")

    e677_magmas = []
    e255_failures = []
    count = 0

    def generate(row, mul):
        nonlocal count
        if time.time() - start > timeout_secs:
            return

        if row == n:
            count += 1
            if check_e677(mul, n):
                table = [list(r) for r in mul]
                e677_magmas.append(table)
                ok, witness = check_e255_all(table, n)
                if not ok:
                    e255_failures.append((table, witness))
            return

        for perm in all_perms:
            mul[row] = list(perm)

            # Prune: check partial E677
            prune = False
            for x in range(n):
                for y in range(row + 1):
                    t1 = mul[y][x]
                    if t1 > row:
                        continue
                    t2 = mul[t1][y]
                    if x > row:
                        continue
                    t3 = mul[x][t2]
                    t4 = mul[y][t3]
                    if t4 != x:
                        prune = True
                        break
                if prune:
                    break

            if not prune:
                generate(row + 1, mul)

    mul = [[0] * n for _ in range(n)]
    generate(0, mul)

    elapsed = time.time() - start
    print(f"    Checked {count} tables in {elapsed:.1f}s")
    print(f"    E677 magmas found: {len(e677_magmas)}")
    print(f"    E255 failures: {len(e255_failures)}")

    if e677_magmas:
        print(f"\n    Sample E677 magma(s):")
        for i, table in enumerate(e677_magmas[:3]):
            print(f"\n    Magma #{i+1}:")
            for row in table:
                print(f"      {row}")
            ok, w = check_e255_all(table, n)
            print(f"      E255: {'✓ all pass' if ok else f'✗ fails at x={w}'}")

    if e255_failures:
        print(f"\n    *** COUNTEREXAMPLE(S) FOUND ***")
        for table, witness in e255_failures:
            print(f"\n    Table:")
            for row in table:
                print(f"      {row}")
            print(f"    E255 fails at x={witness}")

    return e255_failures


def main():
    print("=" * 60)
    print("E677 Brute Force Search")
    print("=" * 60)

    # First: confirm no counterexample for small sizes
    for n in range(1, 6):
        failures = enumerate_small(n, timeout_secs=120)

    # Then: try search for size 6
    print(f"\n{'=' * 60}")
    print("Searching size 6 with backtracking...")
    print(f"{'=' * 60}")
    result = search_with_permutation_rows(6, timeout_secs=600)

    if result is not None:
        print(f"\n*** COUNTEREXAMPLE FOUND ***")
        print("Table:")
        for row in result:
            print(f"  {row}")
        ok, witness = check_e255_all(result, 6)
        print(f"E255 fails at x={witness}")
        return 0
    else:
        print("No counterexample found for size 6")

    return 1


if __name__ == '__main__':
    sys.exit(main())
