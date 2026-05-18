#!/usr/bin/env python3
"""
Deep R_x Analysis for E677 Magmas — Approaches #13, #16, #33
=============================================================

Approach #13: R_x image on orbits — how many orbit elements does R_x map
              back into the orbit? Where do they land?

Approach #16: Left-fixer counting — the fixer map θ(x) = (x◇x)◇x.
              Is F = {(x,y): y◇x=x} total? Is Σ|Fix(L_y)| = |M|?
              Is θ bijective? Does the double-counting argument close?

Approach #33: Minimal criminal — structural constraints on smallest
              counterexample. Sub-magma closure, quotient properties.

Tests on: Jihoon (size 31), Adam (size 35), enumerated size-7.
"""

from collections import Counter, defaultdict
import sys

# ══════════════════════════════════════════════════════════════════════
# MODEL DEFINITIONS
# ══════════════════════════════════════════════════════════════════════

def jihoon_model():
    """f(x,y) = (5x + 27y + 1) % 31.  No idempotents, period 10."""
    N = 31
    return [[(5*x + 27*y + 1) % N for y in range(N)] for x in range(N)], N

def adam_model():
    """Size-35 model with period-7 orbits."""
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


# ══════════════════════════════════════════════════════════════════════
# CORE ANALYSIS FUNCTIONS
# ══════════════════════════════════════════════════════════════════════

def check_e677(mul, n):
    for x in range(n):
        for y in range(n):
            if mul[y][mul[x][mul[mul[y][x]][y]]] != x:
                return False
    return True

def check_e255_element(mul, x):
    """Check E255 at single element: ((x◇x)◇x)◇x = x"""
    return mul[mul[mul[x][x]][x]][x] == x

def get_orbit(mul, x, n):
    """Get left orbit of x: c_0=x, c_{k+1} = x◇c_k = mul[x][c_k]."""
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
    return c, tail, period

def theta(mul, x):
    """θ(x) = (x◇x)◇x — the candidate left-fixer."""
    return mul[mul[x][x]][x]


def full_analysis(mul, n, label):
    """Run all three approaches on a single model."""
    print(f"\n{'═' * 70}")
    print(f"  MODEL: {label}  (n = {n})")
    print(f"{'═' * 70}")

    assert check_e677(mul, n), "E677 verification failed!"
    e255_all = all(check_e255_element(mul, x) for x in range(n))
    print(f"  E677: ✓   E255: {'✓' if e255_all else '✗'}")

    # ── APPROACH #16: Left-fixer / R_x bijectivity ──────────────────
    print(f"\n{'─' * 70}")
    print("  APPROACH #16: Left-Fixer & R_x Analysis")
    print(f"{'─' * 70}")

    # R_x bijectivity: is column x a permutation?
    rx_bijective = {}
    rx_image_sizes = {}
    for x in range(n):
        col = [mul[y][x] for y in range(n)]  # R_x(y) = y◇x = mul[y][x]
        rx_image_sizes[x] = len(set(col))
        rx_bijective[x] = (rx_image_sizes[x] == n)

    all_rx_bij = all(rx_bijective.values())
    print(f"  R_x bijective for all x: {'✓' if all_rx_bij else '✗'}")
    if not all_rx_bij:
        fails = [x for x in range(n) if not rx_bijective[x]]
        img_dist = Counter(rx_image_sizes[x] for x in fails)
        print(f"    Non-bijective at {len(fails)} elements, image size dist: {dict(img_dist)}")

    # Left-fixers: y such that y◇x = x (i.e., L_y(x) = x)
    fixer_count = {}
    fixer_map = {}  # x -> list of fixers
    for x in range(n):
        fixers = [y for y in range(n) if mul[y][x] == x]
        fixer_count[x] = len(fixers)
        fixer_map[x] = fixers

    fixer_dist = Counter(fixer_count.values())
    total_F = sum(fixer_count.values())
    print(f"  |F| = Σ|fixers of x| = {total_F}  (should be {n} if E255 holds)")
    print(f"  Fixer count distribution: {dict(sorted(fixer_dist.items()))}")
    print(f"    (key=number of fixers, value=how many elements have that many)")

    # Dual count: for each y, |Fix(L_y)| = number of x with y◇x=x
    fix_ly = {}
    for y in range(n):
        fix_ly[y] = sum(1 for x in range(n) if mul[y][x] == x)
    fix_ly_dist = Counter(fix_ly.values())
    print(f"  |Fix(L_y)| distribution: {dict(sorted(fix_ly_dist.items()))}")
    print(f"    Σ|Fix(L_y)| = {sum(fix_ly.values())} (= |F|, cross-check)")

    # θ map analysis
    theta_map = [theta(mul, x) for x in range(n)]
    theta_image = set(theta_map)
    theta_injective = len(theta_image) == n
    print(f"  θ(x) = (x◇x)◇x:")
    print(f"    Injective: {'✓' if theta_injective else f'✗ (|image|={len(theta_image)})'}")
    theta_fixes_all = all(mul[theta_map[x]][x] == x for x in range(n))
    print(f"    θ(x) is a fixer of x for all x: {'✓' if theta_fixes_all else '✗'}  (= E255)")

    # θ cycle structure
    visited = [False] * n
    theta_cycles = []
    for start in range(n):
        if visited[start]:
            continue
        cycle = []
        cur = start
        while not visited[cur]:
            visited[cur] = True
            cycle.append(cur)
            cur = theta_map[cur]
        theta_cycles.append(len(cycle))
    theta_cycle_dist = Counter(theta_cycles)
    print(f"    Cycle structure of θ: {dict(sorted(theta_cycle_dist.items()))}")

    # ── L_x ∘ R_x analysis ──────────────────────────────────────────
    print(f"\n  L_x ∘ R_x fixed point analysis:")
    lxrx_has_fp = {}
    lxrx_fp_count = {}
    for x in range(n):
        fps = []
        for z in range(n):
            rz = mul[z][x]      # R_x(z) = z◇x
            lrz = mul[x][rz]    # L_x(R_x(z)) = x◇(z◇x)
            if lrz == z:
                fps.append(z)
        lxrx_has_fp[x] = len(fps) > 0
        lxrx_fp_count[x] = len(fps)

    all_have_fp = all(lxrx_has_fp.values())
    fp_dist = Counter(lxrx_fp_count.values())
    print(f"    L_x∘R_x has fixed point for all x: {'✓' if all_have_fp else '✗'}  (= E255)")
    print(f"    Fixed point count distribution: {dict(sorted(fp_dist.items()))}")

    # ── R_x ∘ L_x analysis ──────────────────────────────────────────
    print(f"\n  R_x ∘ L_x fixed point analysis:")
    rxlx_fp_count = {}
    for x in range(n):
        fps = []
        for z in range(n):
            lz = mul[x][z]      # L_x(z) = x◇z
            rlz = mul[lz][x]    # R_x(L_x(z)) = (x◇z)◇x
            if rlz == z:
                fps.append(z)
        rxlx_fp_count[x] = len(fps)

    rxlx_fp_dist = Counter(rxlx_fp_count.values())
    print(f"    R_x∘L_x fixed point count distribution: {dict(sorted(rxlx_fp_dist.items()))}")

    # ── APPROACH #13: R_x image on orbits ───────────────────────────
    print(f"\n{'─' * 70}")
    print("  APPROACH #13: R_x Image on Orbits")
    print(f"{'─' * 70}")

    orbit_data = {}
    for x in range(n):
        c, tail, period = get_orbit(mul, x, n)
        orbit_data[x] = (c, tail, period)

    period_dist = Counter(orbit_data[x][2] for x in range(n))
    print(f"  Orbit period distribution: {dict(sorted(period_dist.items()))}")

    # For each x, how many orbit elements does R_x map into the orbit?
    # R_x(c_k) = c_k ◇ x.  Is c_k ◇ x in the orbit?
    rx_orbit_stats = []
    for x in range(n):
        c, tail, period = orbit_data[x]
        orbit_set = set(c[tail:tail+period])
        cycle = c[tail:tail+period]
        cycle_pos = {cycle[i]: i for i in range(period)}

        # R_x applied to each orbit element
        rx_in_orbit = 0
        rx_positions = []  # (k, d_k, position_in_orbit or None)
        for k in range(period):
            ck = cycle[k]
            dk = mul[ck][x]  # c_k ◇ x = R_x(c_k)
            if dk in cycle_pos:
                rx_in_orbit += 1
                rx_positions.append((k, dk, cycle_pos[dk]))
            else:
                rx_positions.append((k, dk, None))

        rx_orbit_stats.append({
            'x': x, 'period': period, 'rx_in_orbit': rx_in_orbit,
            'rx_positions': rx_positions, 'orbit_set': orbit_set,
            'cycle': cycle, 'cycle_pos': cycle_pos
        })

    # Aggregate R_x-in-orbit statistics by period
    by_period = defaultdict(list)
    for s in rx_orbit_stats:
        by_period[s['period']].append(s)

    for p in sorted(by_period):
        stats = by_period[p]
        in_counts = [s['rx_in_orbit'] for s in stats]
        in_dist = Counter(in_counts)
        print(f"\n  Period {p} ({len(stats)} elements):")
        print(f"    R_x hits on orbit: {dict(sorted(in_dist.items()))}")
        print(f"    (key = #orbit elements mapped back into orbit by R_x)")

        # Show the d_k pattern for first few
        for s in stats[:3]:
            x = s['x']
            positions = s['rx_positions']
            pattern = []
            for k, dk, pos in positions:
                if pos is not None:
                    pattern.append(f"c_{pos}")
                else:
                    pattern.append(f"OUT")
            print(f"    x={x}: d_k = [{', '.join(pattern)}]")

    # ── KEY: Which R_x positions are ALWAYS in-orbit? ─────────────
    print(f"\n  UNIVERSAL R_x anchor analysis (across all elements):")
    for p in sorted(by_period):
        stats = by_period[p]
        if p < 3:
            continue
        print(f"\n    Period {p}:")
        for k in range(p):
            # For position k, what fraction of elements have d_k in orbit?
            in_count = 0
            pos_values = Counter()
            for s in stats:
                _, _, pos = s['rx_positions'][k]
                if pos is not None:
                    in_count += 1
                    pos_values[pos] += 1
            pct = 100 * in_count / len(stats)
            if pct == 100:
                val = list(pos_values.keys())[0] if len(pos_values) == 1 else pos_values
                print(f"      k={k}: ALWAYS in orbit ({pct:.0f}%), position = {val}")
            elif pct > 0:
                print(f"      k={k}: sometimes in orbit ({pct:.0f}%), positions = {dict(pos_values)}")
            else:
                print(f"      k={k}: NEVER in orbit")

    # ── APPROACH #13 DEEP: R_x restricted to orbit — full image ───
    print(f"\n{'─' * 70}")
    print("  APPROACH #13 DEEP: R_x full image structure")
    print(f"{'─' * 70}")

    # For each x, look at R_x: M → M restricted to orbit elements as INPUTS
    # and also R_x: M → M with orbit elements as OUTPUTS (preimage)
    for p in sorted(by_period):
        stats = by_period[p]
        if p < 5:
            continue
        print(f"\n  Period {p}:")

        # How many elements of M map INTO the orbit under R_x?
        for s in stats[:3]:
            x = s['x']
            orbit_set = s['orbit_set']
            # Elements z such that R_x(z) = z◇x is in the orbit
            preimage_in_orbit = [z for z in range(n) if mul[z][x] in orbit_set]
            preimage_count = len(preimage_in_orbit)
            # How many of those preimage elements are themselves in the orbit?
            preimage_from_orbit = [z for z in preimage_in_orbit if z in orbit_set]
            preimage_from_outside = [z for z in preimage_in_orbit if z not in orbit_set]
            print(f"    x={x}: |{{z: R_x(z) ∈ orbit}}| = {preimage_count} "
                  f"(from orbit: {len(preimage_from_orbit)}, from outside: {len(preimage_from_outside)})")

            # Specifically: which orbit positions are hit by R_x from ANY source?
            orbit_hit_by_rx = set()
            for z in range(n):
                rz = mul[z][x]
                if rz in s['cycle_pos']:
                    orbit_hit_by_rx.add(s['cycle_pos'][rz])
            hit_positions = sorted(orbit_hit_by_rx)
            print(f"      Orbit positions hit by R_x (from all of M): {hit_positions} "
                  f"({len(hit_positions)}/{p})")

    # ── APPROACH #16 DEEP: Double counting on fixers ──────────────
    print(f"\n{'─' * 70}")
    print("  APPROACH #16 DEEP: Fixer Map & Double Counting")
    print(f"{'─' * 70}")

    # The fixer map: φ(x) = θ(x) = (x◇x)◇x
    # E255 says φ(x)◇x = x for all x.
    # If E255 holds, then φ is injective:
    #   Proof: if φ(x) = φ(y), then φ(x)◇x = x and φ(y)◇y = y,
    #          and φ(x) = φ(y) fixes both x and y under left mult.
    #   Since L_{φ(x)} is a bijection fixing both x and y... no that doesn't help.
    # Actually: if φ(x)◇x = x and φ(x)◇y = y (same fixer), then x=y?
    # Only if L_{φ(x)} is injective, which it IS (L is always bijective).
    # So: φ(x) = φ(y) AND both are fixers → x = y. ✓

    # Check: is θ injective even without assuming E255?
    print(f"  θ injective: {'✓' if theta_injective else '✗'}")

    # Key question: for which x does θ(x) actually fix x?
    fixes = [x for x in range(n) if mul[theta_map[x]][x] == x]
    print(f"  θ(x)◇x = x (E255) holds at {len(fixes)}/{n} elements")

    # The set of "fixers" = {θ(x) : θ(x)◇x = x} = range of θ restricted to E255-satisfying x
    fixer_set = set(theta_map[x] for x in fixes)
    print(f"  Set of actual fixers: {len(fixer_set)} distinct elements")

    # Does any element appear as θ(x) for multiple x?
    theta_preimage = defaultdict(list)
    for x in range(n):
        theta_preimage[theta_map[x]].append(x)
    multi_preimage = {k: v for k, v in theta_preimage.items() if len(v) > 1}
    if multi_preimage:
        print(f"  θ collisions (same fixer for multiple x): {len(multi_preimage)}")
        for k, v in list(multi_preimage.items())[:5]:
            print(f"    θ maps {v} → {k}")
    else:
        print(f"  No θ collisions (θ is injective)")

    # ── The "fixer graph": directed graph x → θ(x) ──────────────
    # If θ is a bijection, this is a permutation with cycle structure
    print(f"\n  Fixer graph x → θ(x) cycle structure:")
    visited = set()
    fixer_cycles = []
    for start in range(n):
        if start in visited:
            continue
        path = []
        cur = start
        while cur not in visited:
            visited.add(cur)
            path.append(cur)
            cur = theta_map[cur]
        fixer_cycles.append(path)
    cycle_lens = sorted([len(c) for c in fixer_cycles], reverse=True)
    print(f"    Cycle lengths: {cycle_lens}")

    # ── KEY NEW: Cross-orbit E677 applications ────────────────────
    print(f"\n{'─' * 70}")
    print("  CROSS-ORBIT E677: Using y from outside orbit of x")
    print(f"{'─' * 70}")

    # E677: x = y◇(x◇((y◇x)◇y)) for all x,y.
    # When x is in its own orbit, and y is NOT in the orbit:
    # This gives us information about products involving non-orbit elements.
    # Key: which NEW R_x values does this reveal?

    for p in sorted(by_period):
        stats = by_period[p]
        if p < 5:
            continue

        s = stats[0]  # Pick first element with this period
        x = s['x']
        orbit_set = s['orbit_set']
        cycle = s['cycle']
        cycle_pos = s['cycle_pos']

        # For each y NOT in orbit, E677 gives:
        #   x = y◇(x◇((y◇x)◇y))
        # Let's trace what this tells us about products with orbit elements
        new_rx_info = set()
        cross_products = defaultdict(set)  # (a,b) -> set of known a◇b values

        for y in range(n):
            # E677 with this specific x and y:
            yx = mul[y][x]       # y◇x
            yx_y = mul[yx][y]    # (y◇x)◇y
            x_yxy = mul[x][yx_y] # x◇((y◇x)◇y)
            result = mul[y][x_yxy] # y◇(x◇((y◇x)◇y)) = x ✓

            # Track which orbit elements appear in intermediate products
            if y not in orbit_set:
                # y is external. What products involve orbit elements?
                for a in [y, yx, yx_y, x_yxy]:
                    for b in [y, yx, yx_y, x_yxy, x]:
                        prod = mul[a][b]
                        if a in orbit_set or b in orbit_set or prod in orbit_set:
                            cross_products[(a in orbit_set, b in orbit_set, prod in orbit_set)].add((a, b, prod))

        print(f"\n  Period {p}, x={x}:")
        print(f"    Cross-orbit product patterns (external y):")
        for key in sorted(cross_products.keys()):
            a_in, b_in, p_in = key
            count = len(cross_products[key])
            label_a = "orb" if a_in else "ext"
            label_b = "orb" if b_in else "ext"
            label_p = "orb" if p_in else "ext"
            if count <= 20:
                print(f"      {label_a}◇{label_b}→{label_p}: {count} products")

    # ── APPROACH #33: Minimal criminal structural analysis ────────
    print(f"\n{'─' * 70}")
    print("  APPROACH #33: Minimal Criminal Analysis")
    print(f"{'─' * 70}")

    # Sub-magma closure: is any orbit a sub-magma?
    for p in sorted(by_period):
        stats = by_period[p]
        if p < 3:
            continue
        closed_count = 0
        for s in stats:
            orbit_set = s['orbit_set']
            closed = True
            for a in orbit_set:
                for b in orbit_set:
                    if mul[a][b] not in orbit_set:
                        closed = False
                        break
                if not closed:
                    break
            if closed:
                closed_count += 1
        print(f"  Period {p}: {closed_count}/{len(stats)} orbits are sub-magmas")

    # Minimal sub-magmas: find all sub-magmas
    print(f"\n  Sub-magma search (closure under ◇):")
    # Start from each singleton and close
    sub_magma_sizes = set()
    for start in range(min(n, 10)):  # Check a few starting elements
        closure = {start}
        changed = True
        while changed:
            changed = False
            new = set()
            for a in closure:
                for b in closure:
                    p = mul[a][b]
                    if p not in closure:
                        new.add(p)
            if new:
                closure.update(new)
                changed = True
        sub_magma_sizes.add(len(closure))
        if len(closure) < n:
            # Verify E677 on this sub-magma
            elems = sorted(closure)
            e677_sub = all(
                mul[y][mul[x][mul[mul[y][x]][y]]] == x
                for x in elems for y in elems
            )
            if e677_sub and len(closure) > 1:
                print(f"    Starting from {start}: sub-magma of size {len(closure)}"
                      f" (E677: {'✓' if e677_sub else '✗'})")

    if sub_magma_sizes == {n}:
        print(f"    No proper sub-magmas found (magma is simple)")

    # ── FINAL SUMMARY ─────────────────────────────────────────────
    print(f"\n{'═' * 70}")
    print(f"  SUMMARY for {label}")
    print(f"{'═' * 70}")
    print(f"  n={n}, E677=✓, E255={'✓' if e255_all else '✗'}")
    print(f"  R_x bijective (quasigroup): {'✓ ALL' if all_rx_bij else '✗ NOT ALL'}")
    print(f"  θ injective: {'✓' if theta_injective else '✗'}")
    print(f"  |F| = {total_F} (target: {n})")
    print(f"  L_x∘R_x has FP for all x: {'✓' if all_have_fp else '✗'}")
    print(f"  Orbit periods: {dict(sorted(period_dist.items()))}")
    print()

    return {
        'n': n, 'e255': e255_all, 'rx_bij': all_rx_bij,
        'theta_inj': theta_injective, 'F_size': total_F,
        'lxrx_fp': all_have_fp, 'periods': dict(period_dist),
    }


# ══════════════════════════════════════════════════════════════════════
# MAIN
# ══════════════════════════════════════════════════════════════════════

if __name__ == '__main__':
    print("E677 Deep R_x Analysis — Approaches #13, #16, #33")
    print("=" * 70)

    # Run on Jihoon model
    mul31, n31 = jihoon_model()
    r31 = full_analysis(mul31, n31, "Jihoon f(x,y)=(5x+27y+1)%31")

    # Run on Adam's n=35
    mul35, n35 = adam_model()
    r35 = full_analysis(mul35, n35, "Adam's n=35 model")

    print("\n\n" + "=" * 70)
    print("CROSS-MODEL COMPARISON")
    print("=" * 70)
    for label, r in [("Jihoon n=31", r31), ("Adam n=35", r35)]:
        print(f"  {label}: E255={'✓' if r['e255'] else '✗'}, "
              f"R_x bij={'✓' if r['rx_bij'] else '✗'}, "
              f"θ inj={'✓' if r['theta_inj'] else '✗'}, "
              f"|F|={r['F_size']}/{r['n']}, "
              f"L_x∘R_x FP={'✓' if r['lxrx_fp'] else '✗'}")
