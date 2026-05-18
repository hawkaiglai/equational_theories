#!/usr/bin/env python3
"""
Full magma SAT encoding for E677 + NOT E255.

NO orbit assumption. No fixing L_0. Just:
  - n x n multiplication table
  - E677 for all (a,b)
  - L_y bijective for all y (each row is a permutation)
  - NOT E255: exists x such that ((x*x)*x)*x != x

If UNSAT, ALL E677 magmas of size n satisfy E255.

This is the CORRECT encoding for studying E255. The orbit=M encoding
was vacuous for all p != 7.

Rudi/Bernardo cleared n<=11 (~20s). Let's reproduce and get UNSAT cores.
"""

from pysat.solvers import Solver as SATSolver
import time
from collections import defaultdict


def var(i, j, k, n):
    """Variable x_{i,j,k}: mul[i][j] = k. 1-indexed."""
    return i * n * n + j * n + k + 1


def build_full_encoding(n, gate_e677=False, with_not_e255=True):
    """
    Build full magma encoding.

    Returns (clauses, act_map, e255_neg_assumptions)
    """
    clauses = []
    max_table_var = n * n * n
    next_var = [max_table_var + 1]
    act_map = {}

    def new_var():
        v = next_var[0]
        next_var[0] += 1
        return v

    def add(*lits):
        clauses.append(list(lits))

    # 1. Each cell has exactly one value
    for i in range(n):
        for j in range(n):
            add(*[var(i, j, k, n) for k in range(n)])
            for k1 in range(n):
                for k2 in range(k1 + 1, n):
                    add(-var(i, j, k1, n), -var(i, j, k2, n))

    # 2. Row permutation: L_y bijective
    for i in range(n):
        for k in range(n):
            add(*[var(i, j, k, n) for j in range(n)])
            for j1 in range(n):
                for j2 in range(j1 + 1, n):
                    add(-var(i, j1, k, n), -var(i, j2, k, n))

    # 3. E677: for all a, b: a = mul[b][mul[a][mul[mul[b][a]][b]]]
    for a in range(n):
        for b in range(n):
            if gate_e677:
                act = new_var()
                act_map[(a, b)] = act

            for v1 in range(n):
                for v2 in range(n):
                    for v3 in range(n):
                        lits = [
                            -var(b, a, v1, n),
                            -var(v1, b, v2, n),
                            -var(a, v2, v3, n),
                            var(b, v3, a, n)
                        ]
                        if gate_e677:
                            lits.insert(0, -act_map[(a, b)])
                        add(*lits)

    # 4. NOT E255: exists x such that ((x*x)*x)*x != x
    # I.e., for at least one x: mul[mul[mul[x][x]][x]][x] != x
    #
    # For each x, define e255_holds_x = (mul[mul[mul[x][x]][x]][x] == x)
    # NOT E255 means: NOT all x satisfy E255
    # = exists x: NOT e255_holds_x
    #
    # Encoding: for each x, the condition ((x*x)*x)*x = x can be written as:
    # for all v1, v2, v3:
    #   if mul[x][x]=v1 and mul[v1][x]=v2 and mul[v2][x]=v3, then v3=x
    #
    # The NEGATION for a specific x:
    #   exists v1, v2, v3: mul[x][x]=v1 and mul[v1][x]=v2 and mul[v2][x]=v3 and v3!=x
    #
    # This is hard to encode directly as CNF. Instead, use auxiliary variables.

    e255_neg_assumptions = []

    if with_not_e255:
        # For each x, create an indicator variable w_x that is TRUE iff E255 fails at x
        # w_x = exists v3 != x such that mul[chain(x)][x] = v3
        #
        # Actually simpler: for each x, define the chain:
        #   s_x = mul[x][x]  (squaring)
        #   t_x = mul[s_x][x]  (= (x*x)*x)
        #   u_x = mul[t_x][x]  (= ((x*x)*x)*x)
        #   E255 holds at x iff u_x = x
        #
        # We need auxiliary variables for the compositions.
        # s_{x,v}: mul[x][x] = v (already have var(x,x,v))
        # t_{x,v}: (x*x)*x = v. This is: exists s: mul[x][x]=s AND mul[s][x]=v
        # u_{x,v}: ((x*x)*x)*x = v. This is: exists t: t_x = t AND mul[t][x]=v

        # For each x, introduce:
        #   t_{x,v}: auxiliary for (x*x)*x = v
        t_vars = {}
        for x in range(n):
            for v in range(n):
                t_vars[(x, v)] = new_var()

        # t_{x,v} is true iff exists s: mul[x][x]=s AND mul[s][x]=v
        # Encoding:
        #   (1) mul[x][x]=s AND mul[s][x]=v => t_{x,v}
        #   (2) t_{x,v} => exists s: mul[x][x]=s AND mul[s][x]=v (optional, not needed for UNSAT)
        for x in range(n):
            for s in range(n):
                for v in range(n):
                    # if mul[x][x]=s and mul[s][x]=v then t_{x,v}
                    add(-var(x, x, s, n), -var(s, x, v, n), t_vars[(x, v)])

            # At least one t value
            add(*[t_vars[(x, v)] for v in range(n)])
            # At most one t value (since mul[x][x] is unique, chain is deterministic)
            for v1 in range(n):
                for v2 in range(v1 + 1, n):
                    add(-t_vars[(x, v1)], -t_vars[(x, v2)])

        # u_{x,v}: ((x*x)*x)*x = v
        u_vars = {}
        for x in range(n):
            for v in range(n):
                u_vars[(x, v)] = new_var()

        for x in range(n):
            for t in range(n):
                for v in range(n):
                    # if t_{x,t} and mul[t][x]=v then u_{x,v}
                    add(-t_vars[(x, t)], -var(t, x, v, n), u_vars[(x, v)])

            add(*[u_vars[(x, v)] for v in range(n)])
            for v1 in range(n):
                for v2 in range(v1 + 1, n):
                    add(-u_vars[(x, v1)], -u_vars[(x, v2)])

        # NOT E255: exists x: u_{x,x} is FALSE, i.e., exists x: NOT u_{x,v=x}
        # = OR over x: NOT u_{x,x}
        # = at least one x where E255 fails
        add(*[-u_vars[(x, x)] for x in range(n)])

    return clauses, act_map, next_var[0]


def solve_full(n, solver_name='cadical195', timeout_s=600):
    """Check if E677 + NOT E255 is satisfiable for size n."""
    print(f"\n{'─' * 60}")
    print(f"  n={n}: E677 + L_y bijective + NOT E255")
    print(f"{'─' * 60}")

    clauses, _, _ = build_full_encoding(n, gate_e677=False, with_not_e255=True)
    print(f"  Variables: ~{n**3 + 2*n**2}, Clauses: {len(clauses):,}")

    start = time.time()
    with SATSolver(name=solver_name, bootstrap_with=clauses) as solver:
        result = solver.solve()
        elapsed = time.time() - start

    if result:
        print(f"  *** SAT in {elapsed:.1f}s — COUNTEREXAMPLE! ***")
        return "SAT", elapsed
    else:
        print(f"  *** UNSAT in {elapsed:.1f}s — E255 PROVED for all size-{n} E677 magmas ***")
        return "UNSAT", elapsed


def solve_just_e677(n, solver_name='cadical195'):
    """Check if E677 (no E255 constraint) is satisfiable for size n."""
    print(f"  n={n}: E677 + L_y bijective (no E255 constraint):", end=" ", flush=True)

    clauses, _, _ = build_full_encoding(n, gate_e677=False, with_not_e255=False)

    start = time.time()
    with SATSolver(name=solver_name, bootstrap_with=clauses) as solver:
        result = solver.solve()
        elapsed = time.time() - start

    if result:
        model = solver.get_model()
        if model is None:
            print(f"SAT ({elapsed:.1f}s) but model extraction failed")
            return "SAT", elapsed, None
        model_set = set(model)
        table = [[0] * n for _ in range(n)]
        for i in range(n):
            for j in range(n):
                for k in range(n):
                    if var(i, j, k, n) in model_set:
                        table[i][j] = k

        # Check E255
        e255_ok = True
        for x in range(n):
            chain = table[table[table[x][x]][x]][x]
            if chain != x:
                e255_ok = False
                break

        print(f"SAT ({elapsed:.1f}s), E255={'holds' if e255_ok else 'FAILS'}")
        return "SAT", elapsed, table
    else:
        print(f"UNSAT ({elapsed:.1f}s) — no E677 magma of size {n} exists!")
        return "UNSAT", elapsed, None


def extract_core_full(n, solver_name='minisat22'):
    """Extract UNSAT core for full encoding at size n."""
    print(f"\n{'─' * 60}")
    print(f"  UNSAT CORE: n={n}, full encoding")
    print(f"{'─' * 60}")

    clauses, act_map, _ = build_full_encoding(n, gate_e677=True, with_not_e255=True)
    assumptions = list(act_map.values())

    print(f"  Clauses: {len(clauses):,}, Assumptions: {len(assumptions)}")

    start = time.time()
    with SATSolver(name=solver_name, bootstrap_with=clauses) as solver:
        result = solver.solve(assumptions=assumptions)
        elapsed = time.time() - start

        if result:
            print(f"  SAT — unexpected!")
            return None

        print(f"  UNSAT in {elapsed:.1f}s")

        core = solver.get_core()
        if core is None:
            print(f"  Core extraction failed")
            return None

        inv_map = {v: k for k, v in act_map.items()}
        core_set = set(abs(v) for v in core)
        raw_pairs = sorted([inv_map[v] for v in core_set if v in inv_map])

        print(f"  Raw core: {len(raw_pairs)} / {n*n} E677 instances")

        # Categorize
        by_a = defaultdict(list)
        by_b = defaultdict(list)
        for a, b in raw_pairs:
            by_a[a].append(b)
            by_b[b].append(a)

        print(f"\n  By first arg (a):")
        for a in sorted(by_a):
            print(f"    a={a}: b in {sorted(by_a[a])} ({len(by_a[a])} values)")

        print(f"\n  By second arg (b):")
        for b in sorted(by_b):
            print(f"    b={b}: a in {sorted(by_b[b])} ({len(by_b[b])} values)")

        # Try minimization (may be slow)
        if n <= 5 and len(raw_pairs) > 0:
            print(f"\n  Minimizing...")
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

            print(f"  Minimized: {len(minimal)} pairs (removed {removed})")
            print(f"  Minimal core:")
            for a, b in sorted(minimal):
                print(f"    E677({a},{b})")
            return minimal

        return raw_pairs


if __name__ == '__main__':
    print("=" * 70)
    print("  FULL MAGMA SAT: E677 + NOT E255")
    print("  (no orbit assumption — this is the CORRECT encoding)")
    print("=" * 70)

    # First check: does E677 magma of size n exist at all?
    print(f"\n  E677 existence check (no E255 constraint):")
    for n in range(2, 9):
        solve_just_e677(n)

    # Main: check E677 + NOT E255
    print(f"\n\n  E677 + NOT E255 check:")
    results = {}
    for n in range(2, 13):
        r, t = solve_full(n)
        results[n] = (r, t)
        if r == "SAT":
            print(f"\n  *** COUNTEREXAMPLE AT n={n}! ***")
            break
        if t > 300:
            print(f"\n  Stopping (too slow)")
            break

    print(f"\n{'=' * 70}")
    print(f"  SUMMARY")
    print(f"{'=' * 70}")
    for n, (r, t) in sorted(results.items()):
        print(f"  n={n:2d}: {r} ({t:.1f}s)")

    # UNSAT core extraction for small n
    print(f"\n\n{'=' * 70}")
    print(f"  UNSAT CORE EXTRACTION (full encoding)")
    print(f"{'=' * 70}")

    for n in [3, 4, 5]:
        core = extract_core_full(n)
