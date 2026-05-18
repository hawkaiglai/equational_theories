#!/usr/bin/env python3
"""
Verify: the unique fixed point of L_x∘R_x is ALWAYS c_{p-3} (orbit position p-3).

If true, the FP condition R_x(c_{p-3}) = L_x^{-1}(c_{p-3}) = c_{p-4}
is exactly the single-point identity d_{p-3} = c_{p-4} from Theorem 3.1.

This connects the abstract "FP existence" question to the concrete orbit recurrence.
The question "why does L_x∘R_x have a FP?" becomes "why does d_{p-3} = c_{p-4}?"

Tests on: Jihoon (n=31), Adam (n=35), all enumerated size-7 E677 magmas.
"""

from collections import Counter
import time

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


def check_e677(mul, n):
    for x in range(n):
        for y in range(n):
            if mul[y][mul[x][mul[mul[y][x]][y]]] != x:
                return False
    return True


def get_orbit(mul, x, n):
    """Left orbit: c_0=x, c_{k+1}=x◇c_k. Return cycle portion."""
    c = [x]
    seen = {x: 0}
    cur = x
    while True:
        nxt = mul[x][cur]
        if nxt in seen:
            tail = seen[nxt]
            break
        seen[nxt] = len(c)
        c.append(nxt)
        cur = nxt
    period = len(c) - tail
    return c[tail:tail+period], period


def verify_fp_position(mul, n, label):
    """For every x, find the FP of L_x∘R_x and check it's c_{p-3}."""
    print(f"\n{'═' * 60}")
    print(f"  {label} (n={n})")
    print(f"{'═' * 60}")

    results = {'match': 0, 'mismatch': 0, 'no_fp': 0, 'fp_outside_orbit': 0,
               'idempotent': 0}
    position_dist = Counter()

    for x in range(n):
        cycle, period = get_orbit(mul, x, n)
        cycle_pos = {cycle[k]: k for k in range(period)}

        # Find FP: z such that x◇(z◇x) = z
        fp_z = None
        for z in range(n):
            if mul[x][mul[z][x]] == z:
                fp_z = z
                break

        if fp_z is None:
            results['no_fp'] += 1
            continue

        if period == 1:
            # Idempotent: x◇x=x, so FP is x itself at position 0
            results['idempotent'] += 1
            # For p=1, p-3 = -2 ≡ -2 mod 1 = 0. So c_{p-3} = c_0 = x. ✓
            if fp_z == x:
                results['match'] += 1
            else:
                results['mismatch'] += 1
            continue

        if fp_z not in cycle_pos:
            results['fp_outside_orbit'] += 1
            # Show details for first few
            if results['fp_outside_orbit'] <= 3:
                print(f"  x={x}: FP z={fp_z} is OUTSIDE orbit (period {period})")
                print(f"    orbit = {cycle}")
            continue

        fp_pos = cycle_pos[fp_z]
        target_pos = (period - 3) % period
        position_dist[fp_pos] += 1

        if fp_pos == target_pos:
            results['match'] += 1
        else:
            results['mismatch'] += 1
            if results['mismatch'] <= 3:
                print(f"  x={x}: FP at c_{fp_pos}, expected c_{target_pos} "
                      f"(period {period})")

    print(f"\n  Results:")
    print(f"    FP = c_{{p-3}}: {results['match']}")
    print(f"    FP ≠ c_{{p-3}}: {results['mismatch']}")
    print(f"    FP outside orbit: {results['fp_outside_orbit']}")
    print(f"    No FP: {results['no_fp']}")
    print(f"    Idempotent (trivial): {results['idempotent']}")
    print(f"    FP position distribution: {dict(sorted(position_dist.items()))}")

    if results['mismatch'] == 0 and results['no_fp'] == 0 and results['fp_outside_orbit'] == 0:
        print(f"  *** FP is ALWAYS c_{{p-3}} (or x for idempotents) ✓ ***")

    return results


def enumerate_size7_test(max_count=500):
    """Test on all enumerated size-7 E677 magmas."""
    from z3 import Solver, Int, Implies, Distinct, Or, sat

    n = 7
    print(f"\n{'═' * 60}")
    print(f"  Enumerated size-{n} E677 magmas")
    print(f"{'═' * 60}")

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
    total_match = 0
    total_mismatch = 0
    total_outside = 0
    total_nofp = 0

    start = time.time()
    while count < max_count:
        result = s.check()
        if result != sat:
            break
        model = s.model()
        table = [[model.eval(m[i][j]).as_long() for j in range(n)] for i in range(n)]
        assert check_e677(table, n)
        count += 1

        # Quick FP position check for all elements
        for x in range(n):
            cycle, period = get_orbit(table, x, n)
            cycle_pos = {cycle[k]: k for k in range(period)}

            fp_z = None
            for z in range(n):
                if table[x][table[z][x]] == z:
                    fp_z = z
                    break

            if fp_z is None:
                total_nofp += 1
                continue

            if period == 1:
                if fp_z == x:
                    total_match += 1
                else:
                    total_mismatch += 1
                continue

            if fp_z not in cycle_pos:
                total_outside += 1
                print(f"  Model #{count}, x={x}: FP z={fp_z} OUTSIDE orbit "
                      f"(period {period}, orbit={cycle})")
                continue

            fp_pos = cycle_pos[fp_z]
            target_pos = (period - 3) % period
            if fp_pos == target_pos:
                total_match += 1
            else:
                total_mismatch += 1
                print(f"  Model #{count}, x={x}: FP at c_{fp_pos}, "
                      f"expected c_{target_pos} (period {period})")

        s.add(Or([m[i][j] != table[i][j] for i in range(n) for j in range(n)]))

        if count % 100 == 0:
            print(f"  ... {count} models, {count*n} elements checked "
                  f"({time.time()-start:.1f}s)")

    elapsed = time.time() - start
    print(f"\n  {count} models, {count*n} total elements ({elapsed:.1f}s)")
    print(f"    FP = c_{{p-3}}: {total_match}")
    print(f"    FP ≠ c_{{p-3}}: {total_mismatch}")
    print(f"    FP outside orbit: {total_outside}")
    print(f"    No FP: {total_nofp}")

    if total_mismatch == 0 and total_nofp == 0 and total_outside == 0:
        print(f"  *** UNIVERSAL: FP is ALWAYS c_{{p-3}} across {count} models ✓ ***")


if __name__ == '__main__':
    print("Fixed Point Position Verification")
    print("=" * 60)
    print("Conjecture: the unique FP of L_x∘R_x is always c_{p-3}")
    print("This is equivalent to d_{p-3} = c_{p-4} (single-point identity)")

    # Named models
    mul31, n31 = jihoon_model()
    verify_fp_position(mul31, n31, "Jihoon (5x+27y+1)%31")

    mul35, n35 = adam_model()
    verify_fp_position(mul35, n35, "Adam n=35")

    # Enumerated size-7
    enumerate_size7_test(max_count=500)
