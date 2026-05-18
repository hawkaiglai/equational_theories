#!/usr/bin/env python3
"""
Algebraic analysis of the d-sequence in E677 magmas.

The d-sequence: d_k = mul[k][0] (= c_k ◇ x where x = c_0).

Known:
  d_0 = 1 (from L_0 cyclic)
  d_1 = p-2 (from E677(0,0))
  Identity iii: mul[k][d_{k+1}] = k-1 (mod p) for all k

Question: what ADDITIONAL constraints does E677 impose on the d-sequence?

Strategy: Apply E677(a,b) for all pairs and see which constraints involve
only d-sequence values and L-inverse lookups (which are determined by the
row structure).

Key E677 instances to analyze:
  E677(k, 0): gives identity iii (already known)
  E677(0, k): involves mul[d_k][k], links d-values across rows
  E677(a, b): general case
"""

from itertools import product


def analyze_e677_constraints(p):
    """
    For the orbit=whole-magma case (n=p), analyze what E677(a,b)
    tells us about the multiplication table, expressed in terms of
    d-values and row structure.

    We represent the table symbolically:
    - Row 0 is fixed: mul[0][j] = (j+1) mod p
    - d_k = mul[k][0] for k=0..p-1 (column 0)
    - Identity iii: mul[k][d_{k+1}] = k-1 mod p

    For each E677(a,b), express the constraint and check if it
    involves only d-values or if it requires other table entries.
    """
    print(f"\n{'='*60}")
    print(f"  E677 constraint analysis for p={p}")
    print(f"{'='*60}")

    # Track which cells are used in E677 chains
    # E677(a,b): chain is mul[b][a], mul[ba][b], mul[a][ba_b], mul[b][a_bab]=a

    # For each (a,b), list the 4 cells accessed
    for a in range(p):
        for b in range(p):
            cell1 = (b, a)  # mul[b][a]
            # cell2 depends on val of cell1
            # cell3 depends on val of cell2
            # cell4 depends on val of cell3, and must equal a

            # Check if cell1 is a known cell
            if b == 0:
                ba = (a + 1) % p
            elif a == 0:
                ba = f"d_{b}"  # = mul[b][0] = d_b
            else:
                ba = f"T[{b}][{a}]"

            # Only print interesting cases
            if isinstance(ba, int) or 'd_' in str(ba):
                pass  # Could trace further


def enumerate_all_e677_identities(p):
    """
    Enumerate ALL E677(a,b) identities where a,b are orbit elements,
    and express them purely in terms of:
    - Known values (row 0, d_1)
    - d-sequence values d_k
    - The constraint mul[k][d_{k+1}] = k-1

    Classify each identity by how many "unknown" table lookups it needs.
    """
    print(f"\n{'='*60}")
    print(f"  E677 identities classified by unknown count (p={p})")
    print(f"{'='*60}")

    # Known cells:
    # (0, j) -> (j+1)%p for all j  [row 0]
    # (k, 0) -> d_k for all k  [column 0, symbolic]
    # (k, d_{k+1}) -> k-1 for all k  [identity iii, but d_{k+1} may be unknown]

    known_cells = set()
    for j in range(p):
        known_cells.add((0, j))

    # d-values: (k, 0) for all k. These are "d-symbolic" — known if d is known.
    d_cells = set()
    for k in range(p):
        d_cells.add((k, 0))

    # Identity iii cells: (k, d_{k+1}) — position depends on d-values
    iii_cells = set()
    for k in range(p):
        iii_cells.add(k)  # Just mark that row k has an identity iii entry

    by_class = {0: [], 1: [], 2: [], 3: [], 4: []}

    for a in range(p):
        for b in range(p):
            # Trace the E677 chain symbolically
            # Step 1: ba = mul[b][a]
            if b == 0:
                ba = (a + 1) % p
                step1_known = True
            else:
                step1_known = (a == 0)  # mul[b][0] = d_b
                ba = f"d_{b}" if a == 0 else None

            # Step 2: ba_b = mul[ba][b]
            if step1_known and isinstance(ba, int):
                if ba == 0:
                    ba_b = (b + 1) % p
                    step2_known = True
                else:
                    step2_known = (b == 0)
                    ba_b = f"d_{ba}" if b == 0 else None
            else:
                step2_known = False
                ba_b = None

            # Step 3: a_bab = mul[a][ba_b]
            if step2_known and isinstance(ba_b, int):
                if a == 0:
                    a_bab = (ba_b + 1) % p
                    step3_known = True
                else:
                    step3_known = (ba_b == 0)
                    a_bab = f"d_{a}" if ba_b == 0 else None
            else:
                step3_known = False
                a_bab = None

            # Step 4: mul[b][a_bab] = a
            if step3_known and isinstance(a_bab, int):
                if b == 0:
                    # mul[0][a_bab] = (a_bab+1)%p = a
                    # This gives a_bab = (a-1)%p
                    step4_constrained = True
                else:
                    step4_constrained = (a_bab == 0)  # mul[b][0] = d_b = a => d_b = a
            else:
                step4_constrained = False

            unknowns = sum(1 for s in [step1_known, step2_known, step3_known]
                          if not s)

            # Special: if step1 gives d_b, step2 uses mul[d_b][b], etc.
            # Count symbolic d-lookups
            desc_parts = []
            if b == 0:
                desc_parts.append(f"ba=L_0({a})={(a+1)%p}")
            elif a == 0:
                desc_parts.append(f"ba=d_{b}")
            else:
                desc_parts.append(f"ba=T[{b}][{a}]")

            # Only output low-unknown cases
            if unknowns <= 1 or (a == 0 or b == 0):
                pass  # Will print below

    # Now do a more structured analysis: what does E677(a, b) give
    # when b=0 and when a=0?

    print(f"\n  --- E677(a, 0) for all a (gives identity iii) ---")
    for a in range(p):
        # ba = mul[0][a] = a+1
        ba = (a + 1) % p
        # ba_b = mul[a+1][0] = d_{a+1}
        # a_bab = mul[a][d_{a+1}] = a-1 (by identity iii)
        # result = mul[0][a-1] = a
        print(f"  E677({a},0): L_0(a)={ba}, d_{{ba}}=d_{ba}, "
              f"mul[{a}][d_{ba}]={a}-1={((a-1)%p)}, L_0({(a-1)%p})={a} ✓ (identity iii)")

    print(f"\n  --- E677(0, b) for all b ---")
    for b in range(p):
        # ba = mul[b][0] = d_b
        # ba_b = mul[d_b][b] = UNKNOWN (call it u_b)
        # a_bab = mul[0][u_b] = u_b + 1
        # result = mul[b][u_b + 1] = 0
        print(f"  E677(0,{b}): ba=d_{b}, ba_b=T[d_{b}][{b}]=u, "
              f"a_bab=L_0(u)=u+1, constraint: L_{b}(u+1)=0, "
              f"i.e., T[{b}][u+1]=0")
        # So: mul[b][(mul[d_b][b] + 1) % p] = 0
        # This means L_b^{-1}(0) = (mul[d_b][b] + 1) % p
        # Or equivalently: mul[d_b][b] = L_b^{-1}(0) - 1 mod p

    print(f"\n  --- E677(a, a) for all a (diagonal) ---")
    for a in range(p):
        # ba = mul[a][a] = S(a) (squaring)
        # ba_b = mul[S(a)][a] = UNKNOWN
        # a_bab = mul[a][ba_b] = UNKNOWN
        # result = mul[a][a_bab] = a
        # So: a_bab = L_a^{-1}(a)
        print(f"  E677({a},{a}): ba=S_{a}=T[{a}][{a}], "
              f"ba_b=T[S_{a}][{a}], a_bab=T[{a}][ba_b], "
              f"constraint: T[{a}][a_bab]={a}, i.e., a_bab=L_{a}^{{-1}}({a})")

    print(f"\n  --- E677(a, p-1) for all a (last row/col interactions) ---")
    for a in range(p):
        # ba = mul[p-1][a]
        print(f"  E677({a},{p-1}): ba=T[{p-1}][{a}], ...")


def find_d_constraints_from_e677(p):
    """
    Use E677 at specific (a,b) to derive constraints purely on d-values.

    Key approach: if we can chain E677 instances to get constraints
    that only involve mul[k][0] = d_k values, we get a system of
    equations on the d-vector.

    Actually: let's be smarter. The d_k recurrence says:
      d_{k+1} = L_k^{-1}(k-1)
    Each d_{k+1} is determined by the INVERSE of L_k at point k-1.

    And E677 constrains the L_k permutations. So E677 relates
    different rows of the table, and through the d-recurrence,
    this constrains the d-sequence.

    But we can't evaluate L_k^{-1} without knowing the full row.

    ALTERNATIVE: look for E677 identities that, when evaluated with
    what we know about the table, give equations on d-values.
    """
    print(f"\n{'='*60}")
    print(f"  D-sequence constraints from E677 (p={p})")
    print(f"{'='*60}")

    # Look for E677(a,b) where the chain simplifies.
    # E677(a,b): a = L_b(L_a(L_{L_b(a)}(b)))  NO, this isn't right.
    # Let me re-derive:
    # a = b ◇ (a ◇ ((b ◇ a) ◇ b))
    # Let u = b ◇ a = L_b(a)
    # Let v = u ◇ b = L_u(b) = L_{L_b(a)}(b)
    # Let w = a ◇ v = L_a(v) = L_a(L_{L_b(a)}(b))
    # Then: a = b ◇ w = L_b(w) = L_b(L_a(L_{L_b(a)}(b)))
    #
    # So E677: a = L_b(L_a(L_{L_b(a)}(b))) ... but this uses
    # the fact that u ◇ b = L_u(b), not R_b(u). Let me double-check.
    #
    # (b ◇ a) ◇ b: this is (L_b(a)) ◇ b. Using ◇, that's
    # L_{L_b(a)}(b). Wait, x ◇ y = L_x(y). So (b◇a) ◇ b = L_{b◇a}(b) = L_{L_b(a)}(b). ✓
    #
    # a ◇ ((b◇a)◇b) = L_a(L_{L_b(a)}(b)). ✓
    #
    # b ◇ (a ◇ ((b◇a)◇b)) = L_b(L_a(L_{L_b(a)}(b))). ✓
    #
    # So E677: a = L_b(L_a(L_{L_b(a)}(b)))
    #
    # This is ENTIRELY in terms of L operators!

    print(f"\n  E677 rewritten: a = L_b(L_a(L_{{L_b(a)}}(b)))")
    print(f"  This is PURELY a constraint on the L-permutations!")
    print()

    # Now: L_0(k) = (k+1) mod p.
    # For other rows, L_k is an unknown permutation.
    #
    # E677(a, 0): a = L_0(L_a(L_{L_0(a)}(0)))
    #   = L_0(L_a(L_{a+1}(0)))
    #   = L_0(L_a(d_{a+1}))      [since L_{a+1}(0) = mul[a+1][0] = d_{a+1}]
    #   = L_a(d_{a+1}) + 1
    # So: L_a(d_{a+1}) = a - 1.  [identity iii] ✓
    #
    # E677(0, b): 0 = L_b(L_0(L_{L_b(0)}(b)))
    #   = L_b(L_0(L_{d_b}(b)))
    #   = L_b((L_{d_b}(b) + 1) mod p)
    #   = L_b(mul[d_b][b] + 1)
    # So: L_b(mul[d_b][b] + 1) = 0, i.e., mul[d_b][b] + 1 = L_b^{-1}(0)
    #   i.e., mul[d_b][b] = L_b^{-1}(0) - 1 mod p
    #
    # This gives: T[d_b][b] = L_b^{-1}(0) - 1
    # But L_b^{-1}(0) is not a d-value. It's the element j such that
    # L_b(j) = 0, i.e., mul[b][j] = 0. Call this j = L_b^{-1}(0).
    #
    # From d-sequence: d_{k+1} = L_k^{-1}(k-1).
    # At k=b, j: d_{b+1}... no. d_{k+1} = L_k^{-1}(k-1), not L_k^{-1}(0).
    #
    # L_b^{-1}(0) is actually the element j such that b ◇ j = 0.
    # We can relate this to the d-sequence:
    # L_b(j) = 0 means j is mapped to 0 by L_b.
    # From identity iii: L_b(d_{b+1}) = b-1.
    # So L_b maps d_{b+1} to b-1, and maps j to 0.
    # These are different (unless b-1 = 0, i.e., b = 1).

    print(f"  E677(0, b): T[d_b][b] = L_b^{{-1}}(0) - 1 (mod p)")
    print(f"  This links column b (T[d_b][b]) to L_b^{{-1}}(0).")
    print()

    # E677(a, b) in general: a = L_b(L_a(L_{L_b(a)}(b)))
    #
    # This constrains the L-permutations. For fixed a, as b varies,
    # each E677(a,b) links L_b, L_a, and L_{L_b(a)} together.
    #
    # Can we get constraints on d-values by using E677 instances
    # that chain through column 0?

    # Strategy: use E677(a, b) where:
    # - L_b(a) hits 0 somehow, bringing d-values into play
    # - Or a = 0 or b = 0 (already analyzed)

    # E677(a, b) where L_b(a) = 0, i.e., mul[b][a] = 0.
    # This means a = L_b^{-1}(0). Denote this as a = z_b.
    # Then E677(z_b, b): z_b = L_b(L_{z_b}(L_0(b)))
    #   = L_b(L_{z_b}((b+1) mod p))
    #   = L_b(T[z_b][(b+1)%p])
    # So: z_b = L_b(T[z_b][(b+1)%p])
    # i.e., T[z_b][(b+1)%p] = L_b^{-1}(z_b) = L_b^{-1}(L_b^{-1}(0))

    print(f"  E677 where L_b(a) = 0:")
    print(f"  Let z_b = L_b^{{-1}}(0). Then E677(z_b, b):")
    print(f"  z_b = L_b(L_{{z_b}}(b+1)), so T[z_b][b+1] = L_b^{{-1}}(z_b)")
    print()

    # What about E677(a, b) where some intermediate hits column 0?
    # E677(a, b): chain is
    #   step1: u = L_b(a) = mul[b][a]
    #   step2: v = L_u(b) = mul[u][b]
    #   step3: w = L_a(v) = mul[a][v]
    #   step4: L_b(w) = a, so w = L_b^{-1}(a)
    #
    # If a = 0: u = L_b(0) = d_b [column 0 → d-value]
    #   v = L_{d_b}(b) = T[d_b][b]
    #   w = L_0(v) = v + 1
    #   L_b(w) = 0, so w = z_b = L_b^{-1}(0)
    #   Therefore: v + 1 = z_b, i.e., T[d_b][b] = z_b - 1

    # If b = 0: u = L_0(a) = a+1
    #   v = L_{a+1}(0) = d_{a+1}
    #   w = L_a(d_{a+1}) = a-1 [identity iii]
    #   L_0(w) = a, i.e., w+1 = a, i.e., w = a-1 ✓

    # Can we combine? Use E677(0, b) to get T[d_b][b] = z_b - 1.
    # Then use E677 involving T[d_b][b] in a chain.

    # E677(b, d_b): Let's see what this gives.
    # a=b, B=d_b (using capital to avoid confusion with the index).
    # u = L_{d_b}(b) = T[d_b][b] = z_b - 1  [from E677(0,b)]
    # v = L_{z_b - 1}(d_b) = T[z_b - 1][d_b]
    # w = L_b(v) = T[b][v]
    # constraint: L_{d_b}(w) = b, i.e., w = L_{d_b}^{-1}(b)
    # So T[b][T[z_b-1][d_b]] = L_{d_b}^{-1}(b)

    print(f"  Chaining E677(0,b) with E677(b, d_b):")
    print(f"  From E677(0,b): T[d_b][b] = z_b - 1")
    print(f"  In E677(b, d_b): u = T[d_b][b] = z_b - 1")
    print(f"  v = T[z_b - 1][d_b]")
    print(f"  constraint: T[b][v] = L_{{d_b}}^{{-1}}(b)")
    print()

    # This is getting complex. Let me try NUMERICAL evaluation for p=5.
    print(f"\n  === NUMERICAL CHECK for p=5 ===")
    # The known size-5 E677 magmas all have the same orbit structure.
    # Let me use one to verify and extract the d-sequence.

    # From the SAT solver: for p=5, all E677 magmas with orbit=M
    # have mul[1][1] = 0 (single-point identity). Let me enumerate
    # a few solutions to see the full table.

    from pysat.solvers import Solver as SATSolver

    for pp in [5, 6, 7]:
        print(f"\n  === Enumerating E677 tables for p={pp} (orbit=M, WITH E255) ===")
        n = pp
        clauses = []

        def var(i, j, k, n=n):
            return i * n * n + j * n + k + 1

        def add(*lits):
            clauses.append(list(lits))

        # Cell constraints
        for i in range(n):
            for j in range(n):
                add(*[var(i, j, k) for k in range(n)])
                for k1 in range(n):
                    for k2 in range(k1 + 1, n):
                        add(-var(i, j, k1), -var(i, j, k2))

        # Row permutation
        for i in range(n):
            for k in range(n):
                add(*[var(i, j, k) for j in range(n)])
                for j1 in range(n):
                    for j2 in range(j1 + 1, n):
                        add(-var(i, j1, k), -var(i, j2, k))

        # L_0 cyclic
        for k in range(n):
            add(var(0, k, (k + 1) % n))

        # E677
        for a in range(n):
            for b in range(n):
                for v1 in range(n):
                    for v2 in range(n):
                        for v3 in range(n):
                            add(-var(b, a, v1), -var(v1, b, v2),
                                -var(a, v2, v3), var(b, v3, a))

        # DO include single-point identity (we want solutions)
        target = (pp - 5) % pp
        add(var(pp - 4, pp - 4, target))

        solutions = []
        with SATSolver(name='cadical195', bootstrap_with=clauses) as solver:
            while solver.solve() and len(solutions) < 20:
                model_set = set(solver.get_model())
                table = [[0] * n for _ in range(n)]
                for i in range(n):
                    for j in range(n):
                        for k in range(n):
                            if var(i, j, k) in model_set:
                                table[i][j] = k

                solutions.append(table)

                # Block this solution
                block = []
                for i in range(n):
                    for j in range(n):
                        block.append(-var(i, j, table[i][j]))
                solver.add_clause(block)

        print(f"  Found {len(solutions)} solutions")

        # Analyze d-sequences and key properties
        d_seqs = set()
        z_seqs = set()  # z_b = L_b^{-1}(0) sequences
        for idx, t in enumerate(solutions):
            d = tuple(t[k][0] for k in range(n))
            d_seqs.add(d)

            # z_b = L_b^{-1}(0)
            z = []
            for b in range(n):
                for j in range(n):
                    if t[b][j] == 0:
                        z.append(j)
                        break
            z_seqs.add(tuple(z))

        print(f"  Distinct d-sequences: {len(d_seqs)}")
        for d in sorted(d_seqs):
            print(f"    d = {d}")

        print(f"  Distinct z-sequences (L_b^{{-1}}(0)):")
        for z in sorted(z_seqs):
            print(f"    z = {z}")

        # Check T[d_b][b] = z_b - 1 from E677(0,b)
        print(f"\n  Verifying T[d_b][b] = z_b - 1 (mod {pp}):")
        for idx, t in enumerate(solutions[:3]):
            d = [t[k][0] for k in range(n)]
            z = []
            for b in range(n):
                for j in range(n):
                    if t[b][j] == 0:
                        z.append(j)
                        break

            ok = True
            for b in range(n):
                lhs = t[d[b]][b]
                rhs = (z[b] - 1) % n
                if lhs != rhs:
                    ok = False
                    print(f"    sol {idx}, b={b}: T[d_{b}={d[b]}][{b}]={lhs}, z_{b}={z[b]}, z_b-1={rhs} {'✓' if lhs==rhs else '✗'}")
            if ok:
                print(f"    Solution {idx}: all checks pass ✓")

        # Look for d-sequence patterns
        print(f"\n  D-sequence analysis:")
        for d in sorted(d_seqs):
            print(f"    d = {d}")
            # Check d_{p-3} = p-4 (single-point identity)
            print(f"      d_{{p-3}} = d_{pp-3} = {d[pp-3]}, need {pp-4}: {'✓' if d[pp-3]==pp-4 else '✗'}")
            # Check d_{p-2} = 0 (E255)
            print(f"      d_{{p-2}} = d_{pp-2} = {d[pp-2]}, need 0: {'✓' if d[pp-2]==0 else '✗'}")
            # Check d_0 = 1, d_1 = p-2
            print(f"      d_0={d[0]} (need 1): {'✓' if d[0]==1 else '✗'}")
            print(f"      d_1={d[1]} (need {pp-2}): {'✓' if d[1]==pp-2 else '✗'}")
            # Which d values are in {0,...,p-1}?
            from collections import Counter
            counts = Counter(d)
            print(f"      Value frequencies: {dict(counts)}")
            # Is d a permutation?
            print(f"      d is permutation: {len(set(d)) == pp}")

        # Print a few full tables
        if solutions:
            print(f"\n  First solution table:")
            t = solutions[0]
            for i in range(n):
                print(f"    {i}: {t[i]}")

            # Compute all L_k as permutations
            print(f"\n  L_k permutations:")
            for k in range(n):
                perm = t[k]
                # Express as cycle notation
                visited = [False] * n
                cycles = []
                for start in range(n):
                    if visited[start]:
                        continue
                    cycle = []
                    j = start
                    while not visited[j]:
                        visited[j] = True
                        cycle.append(j)
                        j = perm[j]
                    if len(cycle) > 1:
                        cycles.append(tuple(cycle))
                    elif len(cycle) == 1 and cycle[0] != perm[cycle[0]]:
                        cycles.append(tuple(cycle))
                cycle_str = " ".join(str(c) for c in cycles) if cycles else "(identity)"
                print(f"    L_{k}: {perm}  cycles: {cycle_str}")


def check_d_functional_equation(p):
    """
    Check whether the d-sequence satisfies d_{d_k} = d_{k+1} or
    some other functional equation.
    """
    print(f"\n{'='*60}")
    print(f"  D-sequence functional equations check (p={p})")
    print(f"{'='*60}")

    from pysat.solvers import Solver as SATSolver

    n = p
    clauses = []

    def var(i, j, k, n=n):
        return i * n * n + j * n + k + 1

    def add(*lits):
        clauses.append(list(lits))

    for i in range(n):
        for j in range(n):
            add(*[var(i, j, k) for k in range(n)])
            for k1 in range(n):
                for k2 in range(k1 + 1, n):
                    add(-var(i, j, k1), -var(i, j, k2))

    for i in range(n):
        for k in range(n):
            add(*[var(i, j, k) for j in range(n)])
            for j1 in range(n):
                for j2 in range(j1 + 1, n):
                    add(-var(i, j1, k), -var(i, j2, k))

    for k in range(n):
        add(var(0, k, (k + 1) % n))

    for a in range(n):
        for b in range(n):
            for v1 in range(n):
                for v2 in range(n):
                    for v3 in range(n):
                        add(-var(b, a, v1), -var(v1, b, v2),
                            -var(a, v2, v3), var(b, v3, a))

    # Include E255
    target = (p - 5) % p
    add(var(p - 4, p - 4, target))

    # Enumerate and check functional equations
    with SATSolver(name='cadical195', bootstrap_with=clauses) as solver:
        count = 0
        equations_hold = {
            'd_{d_k} = d_{k+1}': True,
            'd_{d_k} = d_{k+1} (shifted)': True,
        }

        while solver.solve() and count < 50:
            model_set = set(solver.get_model())
            table = [[0] * n for _ in range(n)]
            for i in range(n):
                for j in range(n):
                    for k in range(n):
                        if var(i, j, k) in model_set:
                            table[i][j] = k

            d = [table[k][0] for k in range(n)]

            # Check d_{d_k} = d_{k+1}
            for k in range(n):
                if d[d[k]] != d[(k + 1) % n]:
                    equations_hold['d_{d_k} = d_{k+1}'] = False
                    if count == 0:
                        print(f"  d_{d_k} ≠ d_{{k+1}} at k={k}: "
                              f"d[d[{k}]] = d[{d[k]}] = {d[d[k]]}, "
                              f"d[{(k+1)%n}] = {d[(k+1)%n]}")
                        print(f"  d = {d}")

            count += 1
            block = []
            for i in range(n):
                for j in range(n):
                    block.append(-var(i, j, table[i][j]))
            solver.add_clause(block)

        print(f"\n  Checked {count} solutions for p={p}")
        for eq, holds in equations_hold.items():
            print(f"    {eq}: {'HOLDS' if holds else 'FAILS'}")


if __name__ == '__main__':
    # Run E677 identity analysis
    enumerate_all_e677_identities(5)

    # Find d-sequence constraints numerically
    find_d_constraints_from_e677(5)

    # Check functional equations
    for p in [5, 6, 7]:
        check_d_functional_equation(p)
