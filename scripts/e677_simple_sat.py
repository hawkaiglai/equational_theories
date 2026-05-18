#!/usr/bin/env python3
"""
SAT test: can a "simple" finite E677 magma (no proper E677 sub-magma)
fail E255?

The minimal criminal approach says: if E677 ⊨_fin E255 fails, there's
a smallest counterexample. That counterexample has no proper E677
sub-magma (otherwise restricting to the sub-magma gives a smaller one).

We test: for each size n, is "E677 + NOT E255" UNSAT? And separately,
can we get UNSAT faster by adding "every element generates M" (which
holds in all known simple E677 magmas)?

Also test: in known magmas, verify that "generates M" = "no proper
E677 sub-magma containing the element."
"""

from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
import time
import sys


def var(i, j, k, n):
    """Variable x_{i,j,k}: mul[i][j] = k. 1-indexed."""
    return 1 + i * n * n + j * n + k


def encode_e677_sat(n, add_not_e255=True, add_quasigroup_cols=False,
                    fix_lx_cyclic=False, cyclic_element=0):
    """
    Encode E677 for a magma of size n.

    If fix_lx_cyclic: fix L_{cyclic_element} to be the cyclic shift
    (0->1->2->...->n-1->0). This means the orbit of cyclic_element
    under L_{cyclic_element} is the whole magma with period n.
    """
    clauses = []
    num_vars = n * n * n  # x_{i,j,k} variables

    # Each cell has at least one value
    for i in range(n):
        for j in range(n):
            clauses.append([var(i, j, k, n) for k in range(n)])

    # Each cell has at most one value (pairwise exclusion)
    for i in range(n):
        for j in range(n):
            for k1 in range(n):
                for k2 in range(k1 + 1, n):
                    clauses.append([-var(i, j, k1, n), -var(i, j, k2, n)])

    # Row permutations: L_i is a bijection (each row is a permutation)
    for i in range(n):
        for k in range(n):
            # k appears at least once in row i
            clauses.append([var(i, j, k, n) for j in range(n)])
            # k appears at most once in row i
            for j1 in range(n):
                for j2 in range(j1 + 1, n):
                    clauses.append([-var(i, j1, k, n), -var(i, j2, k, n)])

    # Optional: column permutations (R_x bijective)
    if add_quasigroup_cols:
        for j in range(n):
            for k in range(n):
                clauses.append([var(i, j, k, n) for i in range(n)])
                for i1 in range(n):
                    for i2 in range(i1 + 1, n):
                        clauses.append([-var(i1, j, k, n), -var(i2, j, k, n)])

    # Fix L_x as cyclic shift: mul[x][j] = (j+1) mod n
    if fix_lx_cyclic:
        x = cyclic_element
        for j in range(n):
            val = (j + 1) % n
            clauses.append([var(x, j, val, n)])

    # E677: for all a, b: a = b ◇ (a ◇ ((b ◇ a) ◇ b))
    # This requires auxiliary variables for intermediate values
    aux_count = [num_vars]

    def new_aux():
        aux_count[0] += 1
        return aux_count[0]

    for a in range(n):
        for b in range(n):
            # Step 1: t1 = b ◇ a = mul[b][a]
            # Step 2: t2 = t1 ◇ b = mul[t1][b]
            # Step 3: t3 = a ◇ t2 = mul[a][t2]
            # Step 4: t4 = b ◇ t3 = mul[b][t3]
            # Assert: t4 = a

            # For each possible value of mul[b][a] = v1:
            for v1 in range(n):
                # If mul[b][a] = v1, then we need mul[v1][b] = v2
                for v2 in range(n):
                    # If mul[v1][b] = v2, then we need mul[a][v2] = v3
                    for v3 in range(n):
                        # If mul[a][v2] = v3, then mul[b][v3] must = a
                        # Clause: NOT(mul[b][a]=v1) OR NOT(mul[v1][b]=v2)
                        #         OR NOT(mul[a][v2]=v3) OR mul[b][v3]=a
                        clauses.append([
                            -var(b, a, v1, n),
                            -var(v1, b, v2, n),
                            -var(a, v2, v3, n),
                            var(b, v3, a, n)
                        ])

    # NOT E255: exists x such that ((x◇x)◇x)◇x ≠ x
    if add_not_e255:
        # For element 0 (WLOG by symmetry when L_0 is cyclic):
        # NOT E255 at 0: mul[mul[mul[0][0]][0]][0] ≠ 0
        x = 0
        if fix_lx_cyclic and cyclic_element == 0:
            # mul[0][0] = 1 (cyclic), so c_1 = 1
            # mul[1][0] = 2 (cyclic), so c_2 = 2 = θ(0) = (0◇0)◇0
            # Wait no: θ(x) = (x◇x)◇x. If x=0: θ(0) = mul[mul[0][0]][0] = mul[1][0] = 2
            # E255 at 0: θ(0)◇0 = mul[2][0] = 0 (since cyclic: mul[0][j]=(j+1)%n)
            # Wait: mul[0][j] = (j+1) mod n. So mul[0][0]=1, mul[0][1]=2, etc.
            # But θ(0) = (0◇0)◇0 = mul[mul[0][0]][0] = mul[1][0].
            # mul[1][0] is NOT fixed by the cyclic constraint (that only fixes row 0).
            # E255 at 0: ((0◇0)◇0)◇0 = mul[mul[mul[0][0]][0]][0]
            #          = mul[mul[1][0]][0]
            # So we need mul[mul[1][0]][0] ≠ 0.
            # Since mul[0][0] = 1 is fixed, we need:
            # for each possible v = mul[1][0]: mul[v][0] ≠ 0
            not_e255_clauses = []
            for v in range(n):
                # If mul[1][0] = v, then mul[v][0] ≠ 0
                # i.e., NOT(mul[1][0]=v) OR NOT(mul[v][0]=0)
                clauses.append([-var(1, 0, v, n), -var(v, 0, 0, n)])
            # Actually that's wrong — that says for ALL v, not EXISTS.
            # We want: mul[mul[mul[0][0]][0]][0] ≠ 0
            # Since mul[0][0] = 1 (fixed), this is: mul[mul[1][0]][0] ≠ 0
            # For each v: if mul[1][0] = v then mul[v][0] ≠ 0
            # This IS correct: for each v, the implication must hold.
            pass  # clauses already added above
        else:
            # General NOT E255: there exists x with ((x◇x)◇x)◇x ≠ x
            # Try x = 0
            # mul[mul[mul[0][0]][0]][0] ≠ 0
            for v1 in range(n):
                for v2 in range(n):
                    # If mul[0][0]=v1 and mul[v1][0]=v2, then mul[v2][0] ≠ 0
                    clauses.append([-var(0, 0, v1, n), -var(v1, 0, v2, n),
                                    -var(v2, 0, 0, n)])

    return clauses, aux_count[0]


def run_sat(n, fix_cyclic=True, quasigroup=False):
    """Run SAT for size n. Return 'SAT' or 'UNSAT' with timing."""
    print(f"\n  n={n}, cyclic={'Y' if fix_cyclic else 'N'}, "
          f"quasigroup={'Y' if quasigroup else 'N'}", end='', flush=True)

    t0 = time.time()
    clauses, num_vars = encode_e677_sat(
        n, add_not_e255=True,
        add_quasigroup_cols=quasigroup,
        fix_lx_cyclic=fix_cyclic, cyclic_element=0
    )
    t_encode = time.time() - t0

    solver = Cadical153()
    for c in clauses:
        solver.add_clause(c)

    t0 = time.time()
    result = solver.solve()
    t_solve = time.time() - t0

    status = "SAT" if result else "UNSAT"
    print(f"  => {status}  (encode: {t_encode:.2f}s, solve: {t_solve:.2f}s, "
          f"clauses: {len(clauses)}, vars: {num_vars})")

    if result:
        # Extract model
        model = solver.get_model()
        model_set = set(model)
        mul = [[0]*n for _ in range(n)]
        for i in range(n):
            for j in range(n):
                for k in range(n):
                    if var(i, j, k, n) in model_set:
                        mul[i][j] = k
        # Verify
        e677_ok = True
        for a in range(n):
            for b in range(n):
                if mul[b][mul[a][mul[mul[b][a]][b]]] != a:
                    e677_ok = False
                    break
            if not e677_ok:
                break
        e255_ok = all(mul[mul[mul[x][x]][x]][x] == x for x in range(n))
        print(f"    Verification: E677={'OK' if e677_ok else 'FAIL'}, "
              f"E255={'holds' if e255_ok else 'FAILS'}")
        if not e255_ok:
            for x in range(n):
                v = mul[mul[mul[x][x]][x]][x]
                if v != x:
                    print(f"    E255 fails at x={x}: ((x◇x)◇x)◇x = {v} ≠ {x}")
            print(f"    Multiplication table:")
            for i in range(n):
                print(f"      {mul[i]}")

    solver.delete()
    return status, t_solve


if __name__ == '__main__':
    print("=" * 60)
    print("E677 + NOT E255 SAT SEARCH")
    print("Testing with L_0 = cyclic (orbit of 0 = whole magma)")
    print("=" * 60)

    # Test with cyclic L_0 (orbit = whole magma, period = n)
    for n in range(5, 14):
        status, t = run_sat(n, fix_cyclic=True, quasigroup=False)
        if t > 300:
            print(f"  Stopping at n={n} (timeout)")
            break

    print("\n" + "=" * 60)
    print("Same but with quasigroup (R_x also bijective)")
    print("=" * 60)

    for n in range(5, 35):
        status, t = run_sat(n, fix_cyclic=True, quasigroup=True)
        if t > 300:
            print(f"  Stopping at n={n} (timeout)")
            break
