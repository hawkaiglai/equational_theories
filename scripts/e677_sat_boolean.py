#!/usr/bin/env python3
"""
Pure Boolean SAT encoding for E677 + NOT(single-point identity).
Uses python-sat with CaDiCaL backend for much better performance
than Z3's SMT encoding.

Encoding:
  Variable x_{i,j,k} means mul[i][j] = k.
  "At least one" + "at most one" for each cell.
  Row permutation: each row is a permutation (columns also distinct).
  L_0 fixed as cyclic.
  E677 via composition clauses.
  Negation of single-point identity.
"""

from pysat.solvers import Solver as SATSolver
from pysat.card import CardEnc, EncType
import time
import sys


def var(i, j, k, n):
    """Variable encoding: x_{i,j,k} means mul[i][j] = k."""
    return i * n * n + j * n + k + 1  # 1-indexed for DIMACS


def encode_and_solve(p, extra=0, timeout_s=600, solver_name='cadical195'):
    """
    Encode E677 magma of size n = p + extra, with element 0 having
    orbit period p, and the single-point identity negated.
    Return (result, elapsed, table_or_None).
    """
    n = p + extra
    print(f"\n{'─' * 60}")
    print(f"  p={p}, n={n} (orbit {'= whole magma' if extra == 0 else f'+ {extra} extra'})")
    print(f"  Variables: {n*n*n}, using {solver_name}")
    print(f"{'─' * 60}")

    clauses = []

    # Helper to add clause
    def add(*lits):
        clauses.append(list(lits))

    # 1. Each cell has exactly one value
    for i in range(n):
        for j in range(n):
            # At least one value
            add(*[var(i, j, k, n) for k in range(n)])
            # At most one value (pairwise)
            for k1 in range(n):
                for k2 in range(k1 + 1, n):
                    add(-var(i, j, k1, n), -var(i, j, k2, n))

    # 2. Each row is a permutation (L_y bijective):
    #    For each row i and value k, exactly one j has mul[i][j] = k
    for i in range(n):
        for k in range(n):
            # At least one column has value k
            add(*[var(i, j, k, n) for j in range(n)])
            # At most one column has value k (pairwise)
            for j1 in range(n):
                for j2 in range(j1 + 1, n):
                    add(-var(i, j1, k, n), -var(i, j2, k, n))

    # 3. Fix L_0 as cyclic: mul[0][k] = (k+1) mod p for k in orbit
    for k in range(p):
        val = (k + 1) % p
        add(var(0, k, val, n))

    # If extra > 0, L_0 maps extras to extras
    if extra > 0:
        for k in range(p, n):
            for val in range(p):
                add(-var(0, k, val, n))  # mul[0][k] != val for orbit values

    # 4. E677: for all a, b: a = mul[b][mul[a][mul[mul[b][a]][b]]]
    # This is the complex part. We need to encode composition.
    #
    # Let ba = mul[b][a], then ba_b = mul[ba][b], then a_bab = mul[a][ba_b],
    # then result = mul[b][a_bab]. Constraint: result = a.
    #
    # Encoding composition: if mul[b][a] = v1, and mul[v1][b] = v2,
    # and mul[a][v2] = v3, and mul[b][v3] = v4, then v4 = a.
    #
    # For each (a, b, v1, v2, v3):
    #   x_{b,a,v1} AND x_{v1,b,v2} AND x_{a,v2,v3} => mul[b][v3] = a
    #   i.e., x_{b,a,v1} AND x_{v1,b,v2} AND x_{a,v2,v3} => x_{b,v3,a}
    #
    # As CNF: NOT x_{b,a,v1} OR NOT x_{v1,b,v2} OR NOT x_{a,v2,v3} OR x_{b,v3,a}

    e677_count = 0
    for a in range(n):
        for b in range(n):
            for v1 in range(n):  # ba = mul[b][a] = v1
                for v2 in range(n):  # ba_b = mul[v1][b] = v2
                    for v3 in range(n):  # a_bab = mul[a][v2] = v3
                        # If all three hold, then mul[b][v3] must = a
                        add(
                            -var(b, a, v1, n),
                            -var(v1, b, v2, n),
                            -var(a, v2, v3, n),
                            var(b, v3, a, n)
                        )
                        e677_count += 1

    # 5. Negate single-point identity: mul[p-4][p-4] != (p-5) mod p
    target = (p - 5) % p
    add(-var(p - 4, p - 4, target, n))

    print(f"  Clauses: {len(clauses):,} (E677: {e677_count:,})")
    print(f"  Solving...", flush=True)

    start = time.time()

    with SATSolver(name=solver_name, bootstrap_with=clauses) as solver:
        # Set time limit via interrupt mechanism if supported
        result = solver.solve_limited(expect_interrupt=True)
        # Fallback: just solve with no time limit for now
        if result is None:
            result = solver.solve()

        elapsed = time.time() - start

        if result is False or result == False:
            print(f"  *** UNSAT in {elapsed:.1f}s ***")
            print(f"  → E255 PROVED for period {p}" +
                  (f" in magmas of size {n}" if extra > 0 else " (orbit = whole magma)"))
            return "UNSAT", elapsed, None
        elif result is True or result == True:
            model = solver.get_model()
            # Extract table
            model_set = set(model) if model else set()
            table = [[0] * n for _ in range(n)]
            for i in range(n):
                for j in range(n):
                    for k in range(n):
                        if var(i, j, k, n) in model_set:
                            table[i][j] = k
                            break

            print(f"  *** SAT in {elapsed:.1f}s — COUNTEREXAMPLE! ***")
            for i, row in enumerate(table):
                print(f"    {i}: {row}")

            # Verify E677
            e677_ok = all(
                table[b][table[a][table[table[b][a]][b]]] == a
                for a in range(n) for b in range(n)
            )
            sp = table[p-4][p-4]
            print(f"  E677: {'OK' if e677_ok else 'FAIL'}")
            print(f"  c_{{p-4}}^2 = {sp}, expected {target}")
            return "SAT", elapsed, table
        else:
            print(f"  UNKNOWN after {elapsed:.1f}s")
            return "UNKNOWN", elapsed, None


if __name__ == '__main__':
    print("=" * 60)
    print("E677 Pure Boolean SAT Encoding (CaDiCaL)")
    print("=" * 60)

    # Try available solvers
    available = []
    for s in ['cadical195', 'cadical153', 'glucose42', 'glucose41', 'minisat22']:
        try:
            with SATSolver(name=s) as solver:
                available.append(s)
        except Exception:
            pass
    print(f"Available solvers: {available}")
    solver_name = available[0] if available else 'minisat22'
    print(f"Using: {solver_name}")

    results = {}
    for p in [5, 6, 7, 8, 9, 10, 11]:
        if p < 5:
            continue
        r, t, tbl = encode_and_solve(p, extra=0, timeout_s=600,
                                      solver_name=solver_name)
        results[p] = (r, t)
        if r == "SAT":
            print(f"\n*** COUNTEREXAMPLE AT p={p}! ***")
            break
        if t > 300 and r == "UNKNOWN":
            print(f"\n  Skipping larger p (too slow)")
            break

    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)
    for p, (r, t) in sorted(results.items()):
        print(f"  p={p}: {r} ({t:.1f}s)")
