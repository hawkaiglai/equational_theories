#!/usr/bin/env python3
"""
Full magma SAT encoding v2. Fixed model extraction.
Uses glucose for model extraction (cadical has issues with get_model in python-sat).
"""

from pysat.solvers import Solver as SATSolver
import time
from collections import defaultdict


def var(i, j, k, n):
    return i * n * n + j * n + k + 1


def build_e677_clauses(n):
    """Build E677 + L_y bijective clauses for magma of size n."""
    clauses = []
    def add(*lits):
        clauses.append(list(lits))

    # Cell: each (i,j) has exactly one value
    for i in range(n):
        for j in range(n):
            add(*[var(i, j, k, n) for k in range(n)])
            for k1 in range(n):
                for k2 in range(k1 + 1, n):
                    add(-var(i, j, k1, n), -var(i, j, k2, n))

    # Row permutation: L_y bijective
    for i in range(n):
        for k in range(n):
            add(*[var(i, j, k, n) for j in range(n)])
            for j1 in range(n):
                for j2 in range(j1 + 1, n):
                    add(-var(i, j1, k, n), -var(i, j2, k, n))

    # E677
    for a in range(n):
        for b in range(n):
            for v1 in range(n):
                for v2 in range(n):
                    for v3 in range(n):
                        add(-var(b, a, v1, n), -var(v1, b, v2, n),
                            -var(a, v2, v3, n), var(b, v3, a, n))

    return clauses


def add_not_e255(clauses, n):
    """Add NOT E255 constraint using auxiliary variables."""
    max_var = n * n * n
    next_v = [max_var + 1]
    def new_var():
        v = next_v[0]
        next_v[0] += 1
        return v

    # For each x: chain x*x -> (x*x)*x -> ((x*x)*x)*x
    # NOT E255: at least one x has ((x*x)*x)*x != x

    # Approach: for each x, create a variable fail_x that's true iff E255 fails at x.
    # Then: at least one fail_x is true.

    # fail_x is true iff ((x*x)*x)*x != x
    # Equivalently: forall v1,v2,v3: if mul[x][x]=v1 and mul[v1][x]=v2 and mul[v2][x]=v3 then v3=x
    # Negation: exists v1,v2,v3: mul[x][x]=v1 and mul[v1][x]=v2 and mul[v2][x]=v3 and v3!=x

    # Simple encoding: for each x, NOT(E255 at x) iff
    # the chain mul[mul[mul[x][x]][x]][x] != x.
    # This means: for some v3 != x, mul[v2][x] = v3 where v2 is determined.

    # Actually, let's just encode: for each x, E255_holds_x.
    # e255_x = (the chain equals x)
    # We want: NOT(forall x: e255_x) = exists x: NOT e255_x = OR_x(NOT e255_x)

    # e255_x is encoded as: forall v1,v2: mul[x][x]=v1 AND mul[v1][x]=v2 => mul[v2][x]=x
    # = forall v1,v2: NOT(mul[x][x]=v1) OR NOT(mul[v1][x]=v2) OR mul[v2][x]=x

    # These are implied by E677 if E255 holds. To negate:
    # NOT e255_x = exists v1,v2: mul[x][x]=v1 AND mul[v1][x]=v2 AND mul[v2][x]!=x

    # Use indicator: f_x (fail at x) is TRUE iff E255 fails at x
    # f_x => exists v1,v2 s.t. chain leads to non-x
    # NOT f_x => chain leads to x

    # Actually, simplest approach: don't use indicators.
    # For each x, add clauses that BLOCK E255 at x, but only for at least one x.

    # Use a selector: s_x means "x is the witness where E255 fails"
    # Constraint: at least one s_x is true
    # If s_x is true, then ((x*x)*x)*x != x

    s_vars = [new_var() for x in range(n)]

    # At least one selector
    clauses.append(list(s_vars))

    # If s_x, then ((x*x)*x)*x != x
    # Chain: mul[x][x]=v1, mul[v1][x]=v2, mul[v2][x]=v3, need v3 != x
    # Contrapositive: if mul[x][x]=v1 and mul[v1][x]=v2 and mul[v2][x]=x then NOT s_x
    for x in range(n):
        for v1 in range(n):
            for v2 in range(n):
                # if s_x and mul[x][x]=v1 and mul[v1][x]=v2 then mul[v2][x] != x
                clauses.append([
                    -s_vars[x],
                    -var(x, x, v1, n),
                    -var(v1, x, v2, n),
                    -var(v2, x, x, n)
                ])

    return next_v[0]


def extract_table(solver, n):
    """Extract multiplication table from SAT model."""
    model = solver.get_model()
    if model is None:
        return None
    model_set = set(model)
    table = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            for k in range(n):
                if var(i, j, k, n) in model_set:
                    table[i][j] = k
                    break
    return table


def verify_e677(table, n):
    """Verify E677 holds in the table."""
    for a in range(n):
        for b in range(n):
            ba = table[b][a]
            ba_b = table[ba][b]
            a_bab = table[a][ba_b]
            result = table[b][a_bab]
            if result != a:
                return False
    return True


def check_e255(table, n):
    """Check if E255 holds at every element."""
    for x in range(n):
        chain = table[table[table[x][x]][x]][x]
        if chain != x:
            return False, x
    return True, None


def main():
    print("=" * 70)
    print("  FULL MAGMA SAT: E677 + NOT E255 (v2)")
    print("=" * 70)

    # Use glucose for reliable model extraction
    solver_name = 'glucose42'

    # 1. Existence check
    print(f"\n  STEP 1: Which sizes have E677 magmas?")
    print(f"  {'─' * 50}")

    sizes_with_magma = []
    for n in range(1, 13):
        clauses = build_e677_clauses(n)
        start = time.time()
        with SATSolver(name=solver_name, bootstrap_with=clauses) as solver:
            result = solver.solve()
            elapsed = time.time() - start

            if result:
                table = extract_table(solver, n)
                if table:
                    e677_ok = verify_e677(table, n)
                    e255_ok, fail_x = check_e255(table, n)
                    sizes_with_magma.append(n)
                    print(f"  n={n:2d}: EXISTS ({elapsed:.2f}s) E677={'✓' if e677_ok else '✗'} "
                          f"E255={'✓' if e255_ok else f'✗ at x={fail_x}'}")
                    if n <= 7:
                        for i in range(n):
                            print(f"         {i}: {table[i]}")
                else:
                    sizes_with_magma.append(n)
                    print(f"  n={n:2d}: EXISTS ({elapsed:.2f}s) [model extraction failed]")
            else:
                print(f"  n={n:2d}: NO E677 MAGMA ({elapsed:.2f}s)")

            if elapsed > 120:
                print(f"  ... stopping existence check (too slow)")
                break

    # 2. E255 check for sizes where magma exists
    print(f"\n\n  STEP 2: E677 + NOT E255 for sizes with existing magmas")
    print(f"  {'─' * 50}")

    for n in sizes_with_magma:
        clauses = build_e677_clauses(n)
        add_not_e255(clauses, n)

        print(f"  n={n:2d}: ", end="", flush=True)
        start = time.time()
        with SATSolver(name=solver_name, bootstrap_with=clauses) as solver:
            result = solver.solve()
            elapsed = time.time() - start

            if result:
                table = extract_table(solver, n)
                if table:
                    e677_ok = verify_e677(table, n)
                    e255_ok, fail_x = check_e255(table, n)
                    print(f"*** SAT ({elapsed:.1f}s) — COUNTEREXAMPLE! ***")
                    print(f"         E677={'✓' if e677_ok else '✗'}, "
                          f"E255={'✓' if e255_ok else f'✗ at x={fail_x}'}")
                    for i in range(n):
                        print(f"         {i}: {table[i]}")
                else:
                    print(f"SAT ({elapsed:.1f}s) [model extraction failed]")
            else:
                print(f"UNSAT ({elapsed:.1f}s) — E255 PROVED for all size-{n} E677 magmas")

    # 3. UNSAT core for smallest interesting size
    print(f"\n\n  STEP 3: UNSAT core for E677 + NOT E255")
    print(f"  {'─' * 50}")

    for n in sizes_with_magma[:3]:  # First few
        print(f"\n  n={n}: extracting UNSAT core...")
        clauses_base = build_e677_clauses(n)

        # Gate E677 instances
        max_base = n * n * n
        act_map = {}
        gated_clauses = []
        next_act = max_base + 1

        # Copy base clauses (cell + row perm)
        # Need to separate E677 from base
        # Rebuild with gating
        gated = []
        def add_g(*lits):
            gated.append(list(lits))

        # Cell + row perm (ungated)
        for i in range(n):
            for j in range(n):
                add_g(*[var(i, j, k, n) for k in range(n)])
                for k1 in range(n):
                    for k2 in range(k1 + 1, n):
                        add_g(-var(i, j, k1, n), -var(i, j, k2, n))

        for i in range(n):
            for k in range(n):
                add_g(*[var(i, j, k, n) for j in range(n)])
                for j1 in range(n):
                    for j2 in range(j1 + 1, n):
                        add_g(-var(i, j1, k, n), -var(i, j2, k, n))

        # NOT E255 (ungated)
        max_var_after_base = add_not_e255(gated, n)
        next_act = max_var_after_base

        # E677 (gated)
        for a in range(n):
            for b in range(n):
                act = next_act
                next_act += 1
                act_map[(a, b)] = act

                for v1 in range(n):
                    for v2 in range(n):
                        for v3 in range(n):
                            gated.append([
                                -act,
                                -var(b, a, v1, n),
                                -var(v1, b, v2, n),
                                -var(a, v2, v3, n),
                                var(b, v3, a, n)
                            ])

        assumptions = list(act_map.values())

        with SATSolver(name='minisat22', bootstrap_with=gated) as solver:
            result = solver.solve(assumptions=assumptions)

            if result:
                print(f"    SAT — unexpected!")
                continue

            print(f"    UNSAT")
            core = solver.get_core()
            if core is None:
                print(f"    Core extraction failed")
                continue

            inv_map = {v: k for k, v in act_map.items()}
            core_set = set(abs(v) for v in core)
            raw_pairs = sorted([inv_map[v] for v in core_set if v in inv_map])

            print(f"    Raw core: {len(raw_pairs)} / {n*n} E677 instances")

            # Minimize
            minimal = list(raw_pairs)
            removed = 0
            for pair in list(raw_pairs):
                if pair not in minimal:
                    continue
                test = [p2 for p2 in minimal if p2 != pair]
                test_assum = [act_map[p2] for p2 in test]
                r = solver.solve(assumptions=test_assum)
                if not r:
                    minimal = test
                    removed += 1

            print(f"    Minimal: {len(minimal)} pairs (removed {removed})")
            for a, b in sorted(minimal):
                print(f"      E677({a},{b})")


if __name__ == '__main__':
    main()
