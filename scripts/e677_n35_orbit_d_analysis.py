#!/usr/bin/env python3
"""
Orbit and d_k analysis for Adam McKenna's n=35 E677 magma.

For each non-idempotent element x:
  1. Compute the left orbit: c_0 = x, c_{k+1} = mul[x][c_k], period p
  2. Compute d_k = mul[c_k][x] for all k in 0..p-1
  3. Check if d_k is in the orbit; record orbit positions or "out"
  4. Check the single-point identity: c_{p-4} * c_{p-4} == c_{p-5}
  5. Report distributions, patterns, permutation f(k) when d_k stays in orbit
"""

from collections import Counter, defaultdict

# ── Adam McKenna's n=35 E677 table ──────────────────────────────────

table = [
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

n = 35


def compute_left_orbit(mul, x):
    """Compute left orbit c_0=x, c_{k+1}=mul[x][c_k]. Returns orbit list (period = len)."""
    orbit = [x]
    cur = mul[x][x]
    steps = 0
    while cur != x:
        orbit.append(cur)
        cur = mul[x][cur]
        steps += 1
        if steps > n + 5:
            raise RuntimeError(f"Orbit of {x} did not close within {n+5} steps")
    return orbit


def main():
    mul = table
    print(f"=" * 75)
    print(f"E677 n=35 Orbit and d_k Analysis (Adam McKenna's magma)")
    print(f"=" * 75)

    # ── 0. Quick sanity: verify E677 ────────────────────────────────
    print(f"\n[0] Verifying E677...")
    e677_ok = True
    for x in range(n):
        for y in range(n):
            if mul[y][mul[x][mul[mul[y][x]][y]]] != x:
                print(f"  E677 FAILS at x={x}, y={y}")
                e677_ok = False
                break
        if not e677_ok:
            break
    print(f"  E677: {'VERIFIED' if e677_ok else 'FAILED'}")

    # ── 1. Idempotents and orbit periods ────────────────────────────
    idempotents = [x for x in range(n) if mul[x][x] == x]
    non_idempotents = [x for x in range(n) if mul[x][x] != x]
    print(f"\n[1] Idempotents: {idempotents}  (count: {len(idempotents)})")
    print(f"    Non-idempotents: {len(non_idempotents)} elements")

    orbits = {}
    period_dist = Counter()
    for x in range(n):
        orb = compute_left_orbit(mul, x)
        orbits[x] = orb
        period_dist[len(orb)] += 1

    print(f"\n[2] Orbit period distribution:")
    for p in sorted(period_dist):
        elems = [x for x in range(n) if len(orbits[x]) == p]
        print(f"    period {p:2d}: {period_dist[p]:3d} elements  {elems}")

    # ── 2. theta map ────────────────────────────────────────────────
    theta = [mul[mul[z][z]][z] for z in range(n)]
    print(f"\n[3] theta(z) = (z*z)*z map:")
    print(f"    {theta}")
    theta_image = set(theta)
    print(f"    |image(theta)| = {len(theta_image)} / {n}")
    print(f"    theta injective: {len(theta_image) == n}")

    # ── 3. E255 check ──────────────────────────────────────────────
    e255_fails = [x for x in range(n) if mul[mul[mul[x][x]][x]][x] != x]
    print(f"\n[4] E255: {'ALL PASS' if not e255_fails else f'FAILS at {e255_fails}'}")

    # ── 4. d_k analysis for each non-idempotent ────────────────────
    print(f"\n{'=' * 75}")
    print(f"[5] d_k = c_k * x analysis for non-idempotent elements")
    print(f"{'=' * 75}")

    # Aggregate stats
    period_stats = defaultdict(lambda: {
        'count': 0,
        'all_in_orbit': 0,
        'some_escape': 0,
        'escape_position_counts': None,  # will init per-period
        'f_patterns': Counter(),
        'escape_patterns': Counter(),
        'single_point_pass': 0,
        'single_point_fail': 0,
    })

    detail_examples = defaultdict(list)  # period -> list of detail dicts (up to 5)

    for x in non_idempotents:
        orb = orbits[x]
        p = len(orb)
        orb_set = set(orb)
        orb_pos = {orb[k]: k for k in range(p)}

        stats = period_stats[p]
        stats['count'] += 1
        if stats['escape_position_counts'] is None:
            stats['escape_position_counts'] = [0] * p

        # d_k = c_k * x
        d_vals = [mul[orb[k]][x] for k in range(p)]

        # Classify each d_k
        d_pattern = []
        has_escape = False
        for k in range(p):
            dk = d_vals[k]
            if dk in orb_set:
                d_pattern.append(orb_pos[dk])
            else:
                d_pattern.append('out')
                has_escape = True
                stats['escape_position_counts'][k] += 1

        pattern_tuple = tuple(d_pattern)

        if has_escape:
            stats['some_escape'] += 1
            stats['escape_patterns'][pattern_tuple] += 1
        else:
            stats['all_in_orbit'] += 1
            stats['f_patterns'][pattern_tuple] += 1

        # Single-point identity: c_{p-4} * c_{p-4} == c_{p-5}
        if p >= 5:
            c_pm4 = orb[p - 4]
            c_pm5 = orb[p - 5]
            sp_ok = (mul[c_pm4][c_pm4] == c_pm5)
        elif p == 4:
            c_pm4 = orb[0]
            c_pm5 = orb[p - 5] if p >= 5 else orb[(p - 5) % p]
            sp_ok = (mul[c_pm4][c_pm4] == c_pm5)
        else:
            sp_ok = None  # not applicable for very short orbits

        if sp_ok is True:
            stats['single_point_pass'] += 1
        elif sp_ok is False:
            stats['single_point_fail'] += 1

        # Save detail example
        if len(detail_examples[p]) < 5:
            # Also compute: outsider set
            outsiders = sorted(set(range(n)) - orb_set)
            detail_examples[p].append({
                'x': x,
                'orbit': list(orb),
                'period': p,
                'd_vals': d_vals,
                'd_pattern': d_pattern,
                'has_escape': has_escape,
                'sp_ok': sp_ok,
                'outsiders': outsiders,
            })

    # ── 5. Report by period ────────────────────────────────────────
    for p in sorted(period_stats):
        stats = period_stats[p]
        print(f"\n--- Period {p} ({stats['count']} non-idempotent elements) ---")
        print(f"    All d_k in orbit:  {stats['all_in_orbit']}")
        print(f"    Some d_k escape:   {stats['some_escape']}")

        if stats['escape_position_counts'] and stats['some_escape'] > 0:
            print(f"    Escape by position k:")
            for k in range(p):
                cnt = stats['escape_position_counts'][k]
                if cnt > 0:
                    print(f"      k={k}: {cnt} escapes ({100*cnt/stats['count']:.1f}%)")

        if stats['f_patterns']:
            print(f"    Permutation f(k) patterns (d_k = c_{{f(k)}}, all in orbit):")
            for pat, cnt in stats['f_patterns'].most_common(15):
                pat_str = list(pat)
                print(f"      {pat_str}: {cnt} orbits")

                # Analyze the permutation
                f_list = list(pat)
                is_perm = sorted(f_list) == list(range(p))
                if is_perm:
                    # Check shift
                    shift = (f_list[0] - 0) % p
                    is_shift = all((f_list[k] - k) % p == shift for k in range(p))
                    # Compute order
                    fk = list(range(p))
                    for power in range(1, p + 2):
                        fk = [f_list[fk[k]] for k in range(p)]
                        if fk == list(range(p)):
                            break
                    print(f"        is_permutation=True, is_cyclic_shift={'shift='+str(shift) if is_shift else 'No'}, order={power}")
                else:
                    print(f"        NOT a permutation of {{0..{p-1}}}")

        if stats['escape_patterns']:
            print(f"    Escape patterns (d_k positions, 'out' = outside orbit):")
            for pat, cnt in stats['escape_patterns'].most_common(15):
                print(f"      {list(pat)}: {cnt} orbits")

        # Single-point identity
        total_sp = stats['single_point_pass'] + stats['single_point_fail']
        if total_sp > 0:
            pct = 100 * stats['single_point_pass'] / total_sp
            print(f"    Single-point identity c_{{p-4}}*c_{{p-4}} == c_{{p-5}}:")
            print(f"      PASS: {stats['single_point_pass']}, FAIL: {stats['single_point_fail']} ({pct:.1f}% pass)")

    # ── 6. Detailed examples ───────────────────────────────────────
    print(f"\n{'=' * 75}")
    print(f"[6] Detailed examples (up to 5 per period)")
    print(f"{'=' * 75}")

    for p in sorted(detail_examples):
        print(f"\n--- Period {p} ---")
        for ex in detail_examples[p]:
            x = ex['x']
            orb = ex['orbit']
            d_vals = ex['d_vals']
            d_pat = ex['d_pattern']
            outsiders = ex['outsiders']
            sp = ex['sp_ok']

            print(f"\n  x={x}: orbit={orb}, period={p}")
            print(f"    outsiders (not in orbit): {outsiders}")
            print(f"    d_k = c_k*x values:   {d_vals}")
            print(f"    d_k orbit positions:   {d_pat}")
            if sp is not None:
                c_pm4 = orb[p - 4] if p >= 4 else orb[(p-4) % p]
                c_pm5 = orb[p - 5] if p >= 5 else orb[(p-5) % p]
                actual = mul[c_pm4][c_pm4]
                print(f"    c_{{p-4}}*c_{{p-4}} = {c_pm4}*{c_pm4} = {actual}, c_{{p-5}} = {c_pm5}: {'PASS' if sp else 'FAIL'}")

            # Also show the full orbit multiplication grid (first 2 examples per period)
            if detail_examples[p].index(ex) < 2:
                orb_set = set(orb)
                orb_pos = {orb[k]: k for k in range(p)}
                print(f"    Full orbit product table c_i * c_j (orbit position or 'out'):")
                header = "      c_i\\c_j |" + "".join(f" {j:3d}" for j in range(p))
                print(header)
                print("      " + "-" * (len(header) - 6))
                for i in range(p):
                    row_str = f"      c_{i:2d}    |"
                    for j in range(p):
                        prod = mul[orb[i]][orb[j]]
                        if prod in orb_set:
                            row_str += f" {orb_pos[prod]:3d}"
                        else:
                            row_str += "   *"
                    print(row_str)

    # ── 7. Generalized T1 search ──────────────────────────────────
    print(f"\n{'=' * 75}")
    print(f"[7] Generalized T1 identity search: c_i * c_j = c_? for ALL elements with given period")
    print(f"{'=' * 75}")

    all_periods = sorted(set(len(orbits[x]) for x in non_idempotents))
    for p in all_periods:
        elems = [x for x in non_idempotents if len(orbits[x]) == p]
        print(f"\n  Period {p} ({len(elems)} elements)")

        # For each (i,j) pair, check if c_i*c_j always lands at the same orbit position
        universal_identities = {}
        for i in range(p):
            for j in range(p):
                positions = set()
                all_in = True
                for x in elems:
                    orb = orbits[x]
                    orb_set = set(orb)
                    orb_pos = {orb[k]: k for k in range(p)}
                    prod = mul[orb[i]][orb[j]]
                    if prod in orb_set:
                        positions.add(orb_pos[prod])
                    else:
                        all_in = False
                        break
                if all_in and len(positions) == 1:
                    pos = positions.pop()
                    universal_identities[(i, j)] = pos

        if universal_identities:
            print(f"    Universal within-orbit identities (c_i*c_j = c_k for ALL elements):")
            # Show as a grid
            grid = [[None]*p for _ in range(p)]
            for (i, j), k in universal_identities.items():
                grid[i][j] = k

            header = "    c_i\\c_j |" + "".join(f" {j:3d}" for j in range(p))
            print(header)
            print("    " + "-" * (len(header) - 4))
            for i in range(p):
                row_str = f"    c_{i:2d}    |"
                for j in range(p):
                    if grid[i][j] is not None:
                        row_str += f" {grid[i][j]:3d}"
                    else:
                        row_str += "   ."
                print(row_str)

            # Highlight key identities
            key_ids = []
            # c_0 * c_j should be c_{j+1} (that's the definition of the orbit)
            for j in range(p):
                expected = (j + 1) % p
                if (0, j) in universal_identities and universal_identities[(0, j)] == expected:
                    pass
                else:
                    key_ids.append(f"c_0*c_{j} != c_{{{(j+1)%p}}} (unexpected!)")

            # Check c_{p-4} * c_{p-4} == c_{p-5}
            if p >= 5:
                key = (p-4, p-4)
                if key in universal_identities:
                    val = universal_identities[key]
                    if val == p - 5:
                        key_ids.append(f"c_{{p-4}}*c_{{p-4}} = c_{{p-5}} CONFIRMED (T1 analog)")
                    else:
                        key_ids.append(f"c_{{p-4}}*c_{{p-4}} = c_{{{val}}} (expected c_{{{p-5}}})")
                else:
                    key_ids.append(f"c_{{p-4}}*c_{{p-4}}: NOT universal or escapes orbit")

            # Check c_{p-2} * c_0 == c_0 (E255: theta(x) * x = x)
            key_e255 = (p-2, 0)
            if key_e255 in universal_identities:
                val = universal_identities[key_e255]
                if val == 0:
                    key_ids.append(f"c_{{p-2}}*c_0 = c_0 CONFIRMED (E255)")
                else:
                    key_ids.append(f"c_{{p-2}}*c_0 = c_{{{val}}} (expected c_0 for E255)")

            for kid in key_ids:
                print(f"    >>> {kid}")

            # Check if the universal pattern is affine: c_i*c_j = c_{(alpha*i + beta*j + gamma) mod p}
            if len(universal_identities) == p * p:
                # Try to find alpha, beta, gamma
                gamma = universal_identities.get((0, 0))
                beta_cand = (universal_identities.get((0, 1), 0) - gamma) % p if gamma is not None else None
                alpha_cand = (universal_identities.get((1, 0), 0) - gamma) % p if gamma is not None else None

                if alpha_cand is not None and beta_cand is not None and gamma is not None:
                    is_affine = True
                    for i in range(p):
                        for j in range(p):
                            expected = (alpha_cand * i + beta_cand * j + gamma) % p
                            if universal_identities[(i, j)] != expected:
                                is_affine = False
                                break
                        if not is_affine:
                            break
                    if is_affine:
                        print(f"    >>> AFFINE: c_i*c_j = c_{{({alpha_cand}*i + {beta_cand}*j + {gamma}) mod {p}}}")
                    else:
                        print(f"    >>> NOT affine (alpha={alpha_cand}, beta={beta_cand}, gamma={gamma} doesn't fit)")
            else:
                num_universal = len(universal_identities)
                print(f"    >>> Only {num_universal}/{p*p} positions are universal (some escape or vary)")

        else:
            print(f"    No universal within-orbit identities found")

    # ── 8. Summary ─────────────────────────────────────────────────
    print(f"\n{'=' * 75}")
    print(f"[8] SUMMARY")
    print(f"{'=' * 75}")
    print(f"  n = {n}")
    print(f"  E677: {'VERIFIED' if e677_ok else 'FAILED'}")
    print(f"  E255: {'ALL PASS' if not e255_fails else f'FAILS at {e255_fails}'}")
    print(f"  Idempotents: {len(idempotents)}  ({idempotents})")
    print(f"  Non-idempotents: {len(non_idempotents)}")
    print(f"  theta injective: {len(theta_image) == n}")
    print(f"  Orbit periods: {dict(sorted(period_dist.items()))}")

    for p in sorted(period_stats):
        stats = period_stats[p]
        total_sp = stats['single_point_pass'] + stats['single_point_fail']
        sp_str = f"{stats['single_point_pass']}/{total_sp}" if total_sp > 0 else "N/A"
        print(f"  Period {p}: {stats['count']} elements, "
              f"all-in-orbit={stats['all_in_orbit']}, "
              f"escape={stats['some_escape']}, "
              f"T1(c_{{p-4}}^2=c_{{p-5}})={sp_str}")
        if stats['f_patterns']:
            print(f"    f(k) patterns: {dict(stats['f_patterns'])}")


if __name__ == '__main__':
    main()
