#!/usr/bin/env python3
"""
E677 ⊨_fin E255 — Counterexample Search Script
Instance F: External Computational Search (NEG path)

Searches for a finite magma satisfying E677 but NOT E255.

E677:  x = y * (x * ((y * x) * y))       for all x, y
E255:  x = ((x * x) * x) * x             for all x

Uses Z3 SMT solver for constraint-based search.
"""

import sys
import time
import argparse


# ── Pure Python verification ─────────────────────────────────────────

def check_e677(mul, n):
    """Return True iff all x,y satisfy E677: x = mul[y][mul[x][mul[mul[y][x]][y]]]."""
    for x in range(n):
        for y in range(n):
            yx = mul[y][x]
            yx_y = mul[yx][y]
            x_yxy = mul[x][yx_y]
            result = mul[y][x_yxy]
            if result != x:
                return False
    return True


def check_e255(mul, n):
    """Return (True, None) if all x satisfy E255, or (False, witness) if some x fails."""
    for x in range(n):
        xx = mul[x][x]
        xxx = mul[xx][x]
        xxxx = mul[xxx][x]
        if xxxx != x:
            return False, x
    return True, None


def check_rows_are_permutations(mul, n):
    """Check that each row is a permutation (L_y bijective)."""
    for y in range(n):
        if sorted(mul[y]) != list(range(n)):
            return False
    return True


def print_table(mul, n):
    """Pretty-print a multiplication table."""
    w = len(str(n - 1))
    header = "  * | " + " ".join(f"{j:{w}}" for j in range(n))
    print(header)
    print("  " + "-" * (len(header) - 2))
    for i in range(n):
        row = " ".join(f"{mul[i][j]:{w}}" for j in range(n))
        print(f"  {i:{w}} | {row}")


def analyze_magma(mul, n):
    """Print structural analysis of a magma."""
    print(f"\n  Structural analysis (size {n}):")

    # Check L_y bijectivity
    all_l_bij = check_rows_are_permutations(mul, n)
    print(f"  L_y bijective for all y: {all_l_bij}")

    # Check R_x surjectivity
    for x in range(n):
        image_rx = set(mul[y][x] for y in range(n))
        if len(image_rx) < n:
            print(f"  R_{x} NOT surjective: image = {sorted(image_rx)}, missing {sorted(set(range(n)) - image_rx)}")

    # Check E255 per element
    for x in range(n):
        xx = mul[x][x]
        xxx = mul[xx][x]
        xxxx = mul[xxx][x]
        status = "✓" if xxxx == x else f"✗ (got {xxxx})"
        print(f"  E255 at x={x}: ((({x}*{x})*{x})*{x}) = (({xx}*{x})*{x}) = ({xxx}*{x}) = {xxxx} {status}")

    # Idempotents
    idem = [x for x in range(n) if mul[x][x] == x]
    print(f"  Idempotent elements: {idem if idem else 'none'}")


# ── Z3 Search ────────────────────────────────────────────────────────

def z3_search(n, timeout_ms=300000, symmetry_break=True):
    """Search for a size-n counterexample using Z3.

    Returns the multiplication table (list of lists) if found, else None.
    """
    from z3 import Solver, Int, If, And, Or, Distinct, sat, IntVal

    print(f"  Z3 search for size {n} (timeout={timeout_ms // 1000}s)...")
    s = Solver()
    s.set("timeout", timeout_ms)

    # ── Variables: m[i][j] represents i ◇ j ──
    m = [[Int(f'm_{i}_{j}') for j in range(n)] for i in range(n)]

    # Range constraints
    for i in range(n):
        for j in range(n):
            s.add(m[i][j] >= 0, m[i][j] < n)

    # Each row is a permutation (L_y bijective — mathematically proven)
    for i in range(n):
        s.add(Distinct([m[i][j] for j in range(n)]))

    # ── Lookup helpers ──
    # lookup_row(expr, j): returns m[expr][j] where expr is Z3, j is concrete
    def lookup_row(row_expr, j):
        result = m[n - 1][j]
        for i in range(n - 2, -1, -1):
            result = If(row_expr == i, m[i][j], result)
        return result

    # lookup_col(i, expr): returns m[i][expr] where i is concrete, expr is Z3
    def lookup_col(i, col_expr):
        result = m[i][n - 1]
        for j in range(n - 2, -1, -1):
            result = If(col_expr == j, m[i][j], result)
        return result

    # ── E677 constraints ──
    # For all concrete x, y: x == m[y][m[x][m[m[y][x]][y]]]
    for x in range(n):
        for y in range(n):
            # t1 = m[y][x]  (both concrete → just a variable)
            t1 = m[y][x]
            # t2 = m[t1][y]  (t1 is Z3, y concrete)
            t2 = lookup_row(t1, y)
            # t3 = m[x][t2]  (x concrete, t2 is Z3)
            t3 = lookup_col(x, t2)
            # t4 = m[y][t3]  (y concrete, t3 is Z3)
            t4 = lookup_col(y, t3)
            # E677: x == t4
            s.add(t4 == x)

    # ── NOT E255: ∃ x such that ((x*x)*x)*x ≠ x ──
    e255_violations = []
    for x in range(n):
        xx = m[x][x]                        # Z3 expr
        xxx = lookup_row(xx, x)             # Z3 expr
        xxxx = lookup_row(xxx, x)           # Z3 expr
        e255_violations.append(xxxx != x)
    s.add(Or(e255_violations))

    # ── Symmetry breaking ──
    if symmetry_break:
        # We can relabel elements by any permutation. So WLOG:
        # Fix that element 0 satisfies: m[0][0] <= m[1][1] (lex ordering on diagonal)
        if n >= 2:
            s.add(m[0][0] <= m[1][1])
        # Also: the E255-failing witness can be taken as the smallest such element.
        # This is safe because we're just picking a canonical representative.

    # ── Solve ──
    print(f"    Constraints: {n*n} vars, {n*n} E677 eqs, {n} row-perm, 1 not-E255")
    start = time.time()
    result = s.check()
    elapsed = time.time() - start

    if result == sat:
        print(f"    *** SAT in {elapsed:.1f}s ***")
        model = s.model()
        mul_table = []
        for i in range(n):
            row = []
            for j in range(n):
                val = model.eval(m[i][j])
                row.append(val.as_long())
            mul_table.append(row)
        return mul_table
    else:
        status = "UNSAT" if str(result) == "unsat" else f"UNKNOWN ({result})"
        print(f"    {status} in {elapsed:.1f}s")
        return None


# ── YAML output (Instance G format) ─────────────────────────────────

def format_yaml(mul_table, n, witness, e255_lhs):
    """Format counterexample as YAML for Instance G."""
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


# ── Lean code generation ─────────────────────────────────────────────

def generate_lean_counterexample(mul_table, n, witness):
    """Generate Lean 4 code for a verified counterexample."""
    lines = []
    lines.append("/-")
    lines.append("  FILE: equational_theories/E677/Counterexample.lean")
    lines.append("  INSTANCE: G")
    lines.append("  PATH: NEG")
    lines.append("  DEPENDS ON: A, E")
    lines.append("  STATUS: Complete")
    lines.append("  SORRY COUNT: 0")
    lines.append("")
    lines.append("  Auto-generated counterexample from Z3 search.")
    lines.append("-/")
    lines.append("")
    lines.append("import equational_theories.E677.Defs")
    lines.append("")
    lines.append(f"private def cex_size : Nat := {n}")
    lines.append("")

    # Generate the multiplication table as nested vectors
    lines.append("private def cex_mul : Fin cex_size → Fin cex_size → Fin cex_size :=")
    lines.append("  fun i j => match i.val, j.val with")
    for i in range(n):
        for j in range(n):
            lines.append(f"  | {i}, {j} => ⟨{mul_table[i][j]}, by omega⟩")
    lines.append(f"  | _, _ => ⟨0, by omega⟩")
    lines.append("")

    lines.append("private theorem cex_satisfies_e677 :")
    lines.append("    ∀ x y : Fin cex_size,")
    lines.append("      x = cex_mul y (cex_mul x (cex_mul (cex_mul y x) y)) := by")
    lines.append("  decide")
    lines.append("")

    lines.append(f"private def cex_witness : Fin cex_size := ⟨{witness}, by omega⟩")
    lines.append("")

    lines.append("private theorem cex_fails_e255 :")
    lines.append("    ¬ (cex_mul (cex_mul (cex_mul cex_witness cex_witness) cex_witness) cex_witness = cex_witness) := by")
    lines.append("  decide")

    return '\n'.join(lines)


# ── Main ─────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description='Search for finite E677 magma counterexample to E255')
    parser.add_argument('--min-size', type=int, default=6,
                        help='Minimum magma size to search (default: 6)')
    parser.add_argument('--max-size', type=int, default=12,
                        help='Maximum magma size to search (default: 12)')
    parser.add_argument('--timeout-secs', type=int, default=3600,
                        help='Total timeout in seconds (default: 3600)')
    parser.add_argument('--no-symmetry-break', action='store_true',
                        help='Disable symmetry breaking constraints')
    args = parser.parse_args()

    num_sizes = args.max_size - args.min_size + 1
    per_size_timeout_ms = max(30000, (args.timeout_secs * 1000) // num_sizes)

    print("=" * 60)
    print("E677 ⊨_fin E255 — Counterexample Search")
    print("=" * 60)
    print(f"  Sizes: {args.min_size} to {args.max_size}")
    print(f"  Per-size timeout: {per_size_timeout_ms // 1000}s")
    print(f"  Symmetry breaking: {not args.no_symmetry_break}")
    print()

    total_start = time.time()

    for n in range(args.min_size, args.max_size + 1):
        print(f"{'=' * 40}")
        print(f"  Size {n}")
        print(f"{'=' * 40}")

        mul_table = z3_search(
            n,
            timeout_ms=per_size_timeout_ms,
            symmetry_break=not args.no_symmetry_break
        )

        if mul_table is not None:
            # ── Verify independently ──
            print("\n  Independent verification:")
            assert check_e677(mul_table, n), "  VERIFICATION FAILED: E677 not satisfied!"
            print("    E677: VERIFIED ✓")

            e255_ok, witness = check_e255(mul_table, n)
            assert not e255_ok, "  VERIFICATION FAILED: E255 is actually satisfied!"
            print(f"    E255 fails at x={witness} ✓")

            perm_ok = check_rows_are_permutations(mul_table, n)
            print(f"    Rows are permutations: {perm_ok}")

            # Compute E255 LHS at witness
            x = witness
            xx = mul_table[x][x]
            xxx = mul_table[xx][x]
            xxxx = mul_table[xxx][x]

            print(f"\n  *** COUNTEREXAMPLE FOUND ***")
            print(f"  Size: {n}")
            print(f"  Witness: x={witness}, ((({witness}*{witness})*{witness})*{witness}) = {xxxx} ≠ {witness}")
            print(f"\n  Multiplication table:")
            print_table(mul_table, n)
            analyze_magma(mul_table, n)

            # YAML output
            yaml_out = format_yaml(mul_table, n, witness, xxxx)
            print(f"\n  YAML output:")
            print(yaml_out)

            yaml_file = f'e677_counterexample_size{n}.yaml'
            with open(yaml_file, 'w') as f:
                f.write(yaml_out)
            print(f"\n  Written to {yaml_file}")

            # Lean output
            lean_code = generate_lean_counterexample(mul_table, n, witness)
            lean_file = f'e677_counterexample_size{n}.lean'
            with open(lean_file, 'w') as f:
                f.write(lean_code)
            print(f"  Lean code written to {lean_file}")

            total_elapsed = time.time() - total_start
            print(f"\n  Total search time: {total_elapsed:.1f}s")
            return 0

        print(f"  No counterexample of size {n}\n")

    total_elapsed = time.time() - total_start
    print(f"{'=' * 60}")
    print(f"  No counterexample found in sizes {args.min_size}-{args.max_size}")
    print(f"  Total time: {total_elapsed:.1f}s")
    print(f"{'=' * 60}")
    return 1


if __name__ == '__main__':
    sys.exit(main())
