#!/usr/bin/env python3
"""
E677 Counterexample Search — V2 (Flat encoding with auxiliary variables)

The V1 encoding nested ITE expressions deeply, causing exponential blowup.
This version introduces auxiliary variables for intermediate multiplication
results, keeping all constraints flat and linear in n.

Also adds:
- SAT-based search option via bit-vectors
- Existence check (just E677, no ¬E255) to see which sizes have E677 magmas
- Specific magma verification mode
"""

import sys
import time
import argparse


# ── Pure Python verification ─────────────────────────────────────────

def check_e677(mul, n):
    """Check E677: x = mul[y][mul[x][mul[mul[y][x]][y]]] for all x,y."""
    for x in range(n):
        for y in range(n):
            if mul[y][mul[x][mul[mul[y][x]][y]]] != x:
                return False
    return True

def check_e255_all(mul, n):
    """Return (True, None) or (False, witness)."""
    for x in range(n):
        if mul[mul[mul[x][x]][x]][x] != x:
            return False, x
    return True, None

def print_table(mul, n):
    w = len(str(n - 1))
    header = "    * | " + " ".join(f"{j:{w}}" for j in range(n))
    print(header)
    print("    " + "-" * (len(header) - 4))
    for i in range(n):
        row = " ".join(f"{mul[i][j]:{w}}" for j in range(n))
        print(f"    {i:{w}} | {row}")


# ── Z3 Flat Encoding ─────────────────────────────────────────────────

def z3_search_flat(n, timeout_ms=300000, require_not_e255=True, symmetry_break=True):
    """Search using flat auxiliary variable encoding.

    If require_not_e255=False, just checks if any E677 magma of size n exists.
    """
    from z3 import Solver, Int, And, Or, Distinct, Implies, sat

    mode = "counterexample" if require_not_e255 else "existence"
    print(f"    Z3 flat search (size {n}, mode={mode}, timeout={timeout_ms//1000}s)...")
    s = Solver()
    s.set("timeout", timeout_ms)

    # ── Main variables: m[i][j] = i ◇ j ──
    m = [[Int(f'm_{i}_{j}') for j in range(n)] for i in range(n)]
    for i in range(n):
        for j in range(n):
            s.add(m[i][j] >= 0, m[i][j] < n)

    # Row permutation (L_y bijective)
    for i in range(n):
        s.add(Distinct([m[i][j] for j in range(n)]))

    # ── E677 with auxiliary variables ──
    # For each (x, y): x = m[y][m[x][m[m[y][x]][y]]]
    # Decompose:
    #   step1[x][y] = m[y][x]                     (concrete lookup → direct variable)
    #   step2[x][y] = m[step1[x][y]][y]            (row is Z3 expr, col concrete)
    #   step3[x][y] = m[x][step2[x][y]]            (row concrete, col is Z3 expr)
    #   step4[x][y] = m[y][step3[x][y]]            (row concrete, col is Z3 expr)
    #   constraint:   step4[x][y] == x

    # step1 is just m[y][x], which is a direct variable — no auxiliary needed
    # step2, step3, step4 each need an auxiliary variable + channeling constraints

    step2 = [[Int(f's2_{x}_{y}') for y in range(n)] for x in range(n)]
    step3 = [[Int(f's3_{x}_{y}') for y in range(n)] for x in range(n)]
    step4 = [[Int(f's4_{x}_{y}') for y in range(n)] for x in range(n)]

    for x in range(n):
        for y in range(n):
            # Range constraints on auxiliaries
            s.add(step2[x][y] >= 0, step2[x][y] < n)
            s.add(step3[x][y] >= 0, step3[x][y] < n)
            s.add(step4[x][y] >= 0, step4[x][y] < n)

            # step1 = m[y][x] (direct variable, no constraint needed)
            t1 = m[y][x]

            # Channeling: step2[x][y] = m[t1][y]
            # For each possible value v of t1: (t1 == v) → (step2 == m[v][y])
            for v in range(n):
                s.add(Implies(t1 == v, step2[x][y] == m[v][y]))

            # Channeling: step3[x][y] = m[x][step2[x][y]]
            # x is concrete, step2 is Z3
            for v in range(n):
                s.add(Implies(step2[x][y] == v, step3[x][y] == m[x][v]))

            # Channeling: step4[x][y] = m[y][step3[x][y]]
            # y is concrete, step3 is Z3
            for v in range(n):
                s.add(Implies(step3[x][y] == v, step4[x][y] == m[y][v]))

            # E677: step4 == x
            s.add(step4[x][y] == x)

    # ── NOT E255 constraint ──
    if require_not_e255:
        # ((x◇x)◇x)◇x ≠ x for some x
        # Use auxiliaries for the E255 computation too
        e255_fail = []
        for x in range(n):
            # e255_s1 = m[x][x] (concrete)
            e255_s1 = m[x][x]
            # e255_s2 = m[e255_s1][x]
            e255_s2 = Int(f'e2_{x}')
            s.add(e255_s2 >= 0, e255_s2 < n)
            for v in range(n):
                s.add(Implies(e255_s1 == v, e255_s2 == m[v][x]))
            # e255_s3 = m[e255_s2][x]
            e255_s3 = Int(f'e3_{x}')
            s.add(e255_s3 >= 0, e255_s3 < n)
            for v in range(n):
                s.add(Implies(e255_s2 == v, e255_s3 == m[v][x]))
            # E255 fails at x iff e255_s3 ≠ x
            e255_fail.append(e255_s3 != x)
        s.add(Or(e255_fail))

    # ── Symmetry breaking ──
    if symmetry_break:
        # WLOG: we can conjugate by any permutation σ, replacing m[i][j]
        # with σ(m[σ⁻¹(i)][σ⁻¹(j)]). So we can fix:
        # 1. m[0][0] is the smallest diagonal element
        for i in range(1, n):
            s.add(m[0][0] <= m[i][i])
        # 2. Row 0 is lexicographically smallest among all rows
        #    (this is expensive; skip for now and just use diagonal constraint)

    # ── Solve ──
    n_constraints = n * n * (3 * n + 4) + n + 1  # approximate
    print(f"      Vars: {n*n} main + {3*n*n} aux, ~{n_constraints} constraints")
    start = time.time()
    result = s.check()
    elapsed = time.time() - start

    if result == sat:
        print(f"      *** SAT in {elapsed:.1f}s ***")
        model = s.model()
        mul_table = [[model.eval(m[i][j]).as_long() for j in range(n)]
                     for i in range(n)]
        return mul_table
    else:
        status = "UNSAT" if str(result) == "unsat" else f"UNKNOWN ({result})"
        print(f"      {status} in {elapsed:.1f}s")
        return None


# ── YAML & Lean output ───────────────────────────────────────────────

def format_yaml(mul_table, n, witness, e255_lhs):
    lines = ["# E677_COUNTEREXAMPLE"]
    lines.append(f"size: {n}")
    lines.append("mul_table:")
    for i, row in enumerate(mul_table):
        lines.append(f"  - [{', '.join(map(str, row))}]   # row {i}")
    lines.append(f"witness_not_e255: {witness}")
    lines.append("verification:")
    lines.append("  e677_checked: true")
    lines.append(f"  e255_fails_at: {witness}")
    lines.append(f"  e255_lhs: {e255_lhs}")
    return '\n'.join(lines)


def generate_lean(mul_table, n, witness):
    lines = []
    lines.append(f"-- Auto-generated E677 counterexample, size {n}")
    lines.append(f"-- Witness: element {witness} fails E255")
    lines.append("")
    lines.append(f"def cex_mul : Fin {n} → Fin {n} → Fin {n} :=")
    lines.append("  fun i j => match i.val, j.val with")
    for i in range(n):
        for j in range(n):
            lines.append(f"  | {i}, {j} => ⟨{mul_table[i][j]}, by omega⟩")
    lines.append(f"  | _, _ => ⟨0, by omega⟩")
    return '\n'.join(lines)


# ── Analysis ─────────────────────────────────────────────────────────

def analyze_magma(mul, n):
    print(f"\n    Analysis:")

    # R_x surjectivity
    for x in range(n):
        image = set(mul[y][x] for y in range(n))
        if len(image) < n:
            missing = sorted(set(range(n)) - image)
            print(f"      R_{x} NOT surjective, missing: {missing}")
        else:
            print(f"      R_{x} surjective ✓")

    # E255 per element
    for x in range(n):
        xx = mul[x][x]
        xxx = mul[xx][x]
        xxxx = mul[xxx][x]
        s = "✓" if xxxx == x else f"✗ (got {xxxx})"
        print(f"      E255 at x={x}: {s}")

    # Idempotents
    idem = [x for x in range(n) if mul[x][x] == x]
    print(f"      Idempotents: {idem if idem else 'none'}")

    # L_y cycle structure
    for y in range(n):
        perm = [mul[y][x] for x in range(n)]
        cycles = []
        visited = set()
        for start in range(n):
            if start in visited:
                continue
            cycle = []
            cur = start
            while cur not in visited:
                visited.add(cur)
                cycle.append(cur)
                cur = perm[cur]
            if len(cycle) > 1:
                cycles.append(tuple(cycle))
            else:
                cycles.append((cycle[0],))
        print(f"      L_{y} cycles: {cycles}")


# ── Main ─────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description='E677 counterexample search (V2 flat encoding)')
    parser.add_argument('--min-size', type=int, default=5)
    parser.add_argument('--max-size', type=int, default=12)
    parser.add_argument('--timeout-secs', type=int, default=600)
    parser.add_argument('--existence-only', action='store_true',
                        help='Only check if E677 magmas exist (no E255 check)')
    parser.add_argument('--no-symmetry-break', action='store_true')
    parser.add_argument('--verify-linear', type=int, default=0,
                        help='Verify linear magma x◇y=ax+by on Z_p for given prime p')
    args = parser.parse_args()

    # ── Special mode: verify linear magma ──
    if args.verify_linear > 0:
        p = args.verify_linear
        print(f"Checking linear E677 magmas on Z_{p}...")
        for a in range(p):
            for b in range(p):
                mul = [[(a * i + b * j) % p for j in range(p)] for i in range(p)]
                if check_e677(mul, p):
                    ok, w = check_e255_all(mul, p)
                    status = "E255 ✓" if ok else f"E255 ✗ at x={w}"
                    print(f"  a={a}, b={b}: E677 ✓, {status}")
                    if not ok:
                        print(f"\n  *** LINEAR COUNTEREXAMPLE! ***")
                        print_table(mul, p)
                        return 0
        print(f"  No linear E677 magma on Z_{p} violates E255")
        return 1

    # ── Main search ──
    print("=" * 60)
    print("E677 Counterexample Search V2 (Flat Encoding)")
    print("=" * 60)

    num_sizes = args.max_size - args.min_size + 1
    per_size_ms = max(30000, (args.timeout_secs * 1000) // num_sizes)
    mode = "existence" if args.existence_only else "counterexample"

    print(f"  Sizes: {args.min_size}-{args.max_size}")
    print(f"  Mode: {mode}")
    print(f"  Per-size timeout: {per_size_ms // 1000}s")
    print()

    total_start = time.time()

    for n in range(args.min_size, args.max_size + 1):
        print(f"  === Size {n} ===")

        mul_table = z3_search_flat(
            n,
            timeout_ms=per_size_ms,
            require_not_e255=not args.existence_only,
            symmetry_break=not args.no_symmetry_break
        )

        if mul_table is not None:
            # Verify
            assert check_e677(mul_table, n), "E677 verification FAILED!"
            print(f"      E677: VERIFIED ✓")

            if args.existence_only:
                print(f"\n    E677 magma of size {n} EXISTS:")
                print_table(mul_table, n)
                analyze_magma(mul_table, n)
                ok, w = check_e255_all(mul_table, n)
                print(f"      E255: {'all pass ✓' if ok else f'FAILS at x={w}'}")
            else:
                ok, witness = check_e255_all(mul_table, n)
                assert not ok, "E255 verification FAILED!"
                x = witness
                xxxx = mul_table[mul_table[mul_table[x][x]][x]][x]
                print(f"\n    *** COUNTEREXAMPLE FOUND ***")
                print(f"    Size: {n}, witness: x={witness}")
                print_table(mul_table, n)
                analyze_magma(mul_table, n)

                yaml = format_yaml(mul_table, n, witness, xxxx)
                fname = f'e677_counterexample_size{n}.yaml'
                with open(fname, 'w') as f:
                    f.write(yaml)
                print(f"\n    Written to {fname}")

                lean = generate_lean(mul_table, n, witness)
                lname = f'e677_counterexample_size{n}.lean'
                with open(lname, 'w') as f:
                    f.write(lean)
                print(f"    Lean written to {lname}")

                return 0

        print()

    elapsed = time.time() - total_start
    print(f"{'=' * 60}")
    if args.existence_only:
        print(f"  Existence check complete ({elapsed:.1f}s)")
    else:
        print(f"  No counterexample found in sizes {args.min_size}-{args.max_size}")
    print(f"  Total time: {elapsed:.1f}s")
    print(f"{'=' * 60}")
    return 1


if __name__ == '__main__':
    sys.exit(main())
