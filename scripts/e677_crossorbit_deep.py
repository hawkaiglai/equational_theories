#!/usr/bin/env python3
"""
E677 Cross-Orbit Deep Flow Analysis
====================================
Phase 1: Trace the exact chain of E677 applications that forces
d_{p-3} = c_{p-4} in finite E677 magmas.

The d_k recurrence: d_{k+1} = L_{c_k}^{-1}(c_{k-1})
This exits the orbit. What brings it back?

We build a DEPENDENCY GRAPH: for each d_k value, which E677(a,b)
instances were needed to determine L_{c_k}^{-1} at the relevant point?

Models: Jihoon (n=31, p=10), Adam (n=35, p=7), size-7 affine.
"""

import numpy as np
from itertools import product as iprod
from collections import defaultdict, deque


# ═══════════════════════════════════════════════════════════════════
# MODEL DEFINITIONS
# ═══════════════════════════════════════════════════════════════════

def make_jihoon(n=31):
    """Jihoon Hyun's model: f(x,y) = (5x + 27y + 1) mod n."""
    return [[(5*x + 27*y + 1) % n for y in range(n)] for x in range(n)], n

def make_size7():
    """Size-7 affine model: c_i◇c_j = c_{(4i+j+1) mod 7}."""
    n = 7
    return [[(4*i + j + 1) % n for j in range(n)] for i in range(n)], n

def make_adam():
    """Adam's size-35 model."""
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


# ═══════════════════════════════════════════════════════════════════
# CORE UTILITIES
# ═══════════════════════════════════════════════════════════════════

def verify_e677(mul, n):
    for x in range(n):
        for y in range(n):
            if mul[y][mul[x][mul[mul[y][x]][y]]] != x:
                return False
    return True

def verify_e255(mul, n):
    for x in range(n):
        if mul[mul[mul[x][x]][x]][x] != x:
            return False
    return True

def get_orbit(mul, n, x):
    """L_x orbit of x: [c_0=x, c_1=x◇x, c_2=x◇(x◇x), ...]"""
    orbit = [x]
    cur = mul[x][x]
    while cur != x:
        orbit.append(cur)
        cur = mul[x][cur]
    return orbit

def get_L_perm(mul, n, y):
    """L_y as a list: L_y[i] = y◇i = mul[y][i]"""
    return [mul[y][i] for i in range(n)]

def perm_inverse(p, n):
    inv = [0]*n
    for i in range(n):
        inv[p[i]] = i
    return inv

def d_sequence(mul, orbit, x):
    """d_k = c_k ◇ x for each c_k in orbit."""
    return [mul[c][x] for c in orbit]


# ═══════════════════════════════════════════════════════════════════
# ANALYSIS 1: d_k RECURRENCE DEPENDENCY GRAPH
# ═══════════════════════════════════════════════════════════════════

def trace_dk_recurrence(mul, n, x):
    """
    The d_k recurrence: d_{k+1} = L_{c_k}^{-1}(c_{k-1}).

    L_{c_k}^{-1} is determined by L_{c_k} on ALL of M. But from E677,
    L_y^{-1}(x) = x ◇ R_y(L_y(x)).

    So: d_{k+1} = L_{c_k}^{-1}(c_{k-1}) = c_{k-1} ◇ R_{c_k}(L_{c_k}(c_{k-1}))
                = c_{k-1} ◇ R_{c_k}(c_k ◇ c_{k-1})
                = c_{k-1} ◇ ((c_k ◇ c_{k-1}) ◇ c_k)

    This expression for d_{k+1} involves:
      (a) c_k ◇ c_{k-1}    — orbit multiplication (may or may not stay in orbit)
      (b) (result) ◇ c_k   — right-multiply by c_k
      (c) c_{k-1} ◇ (result) — right-multiply c_{k-1} by that

    Key: we can also verify this using E677(c_{k-1}, c_k) directly:
      E677(c_{k-1}, c_k): c_{k-1} = c_k ◇ (c_{k-1} ◇ ((c_k ◇ c_{k-1}) ◇ c_k))
      So: c_{k-1} = L_{c_k}(c_{k-1} ◇ R_{c_k}(c_k ◇ c_{k-1}))
      i.e., L_{c_k}^{-1}(c_{k-1}) = c_{k-1} ◇ R_{c_k}(c_k ◇ c_{k-1})
    """
    orbit = get_orbit(mul, n, x)
    p = len(orbit)
    orbit_set = set(orbit)

    print(f"\n{'═'*70}")
    print(f"  d_k RECURRENCE TRACE for x={x}, period={p}")
    print(f"{'═'*70}")
    print(f"  Orbit: {orbit}")

    # Compute d_k directly
    dk = d_sequence(mul, orbit, x)
    print(f"  d_k:   {dk}")
    print(f"  d_k in orbit: {['Y' if d in orbit_set else 'N' for d in dk]}")

    # Verify the recurrence formula
    print(f"\n  Verifying d_{{k+1}} = c_{{k-1}} ◇ ((c_k ◇ c_{'{k-1}'}) ◇ c_k):")
    print(f"  (This is E677's L_y^{{-1}} formula applied to L_{{c_k}} at c_{{k-1}})")
    print()

    # Track which intermediate products go in/out of orbit
    for k in range(p):
        ck = orbit[k]
        ck_minus1 = orbit[(k-1) % p]

        # Step 1: c_k ◇ c_{k-1} (orbit multiplication)
        step1 = mul[ck][ck_minus1]
        step1_in = step1 in orbit_set

        # Step 2: (c_k ◇ c_{k-1}) ◇ c_k  (right-mult by c_k)
        step2 = mul[step1][ck]
        step2_in = step2 in orbit_set

        # Step 3: c_{k-1} ◇ step2  (the final d_{k+1})
        step3 = mul[ck_minus1][step2]
        step3_in = step3 in orbit_set

        # Verify
        expected = dk[(k+1) % p]
        match = "✓" if step3 == expected else "✗"

        # Location labels
        s1_loc = f"c_{orbit.index(step1)}" if step1_in else f"OUT({step1})"
        s2_loc = f"c_{orbit.index(step2)}" if step2_in else f"OUT({step2})"
        s3_loc = f"c_{orbit.index(step3)}" if step3_in else f"OUT({step3})"

        print(f"  k={k:2d}: c_k◇c_{{k-1}} = {s1_loc:>8} | "
              f"(...)◇c_k = {s2_loc:>8} | "
              f"c_{{k-1}}◇(...) = d_{(k+1)%p} = {s3_loc:>8} {match}")

    return orbit, dk


# ═══════════════════════════════════════════════════════════════════
# ANALYSIS 2: E677 INSTANCE DEPENDENCY FOR EACH d_k
# ═══════════════════════════════════════════════════════════════════

def build_dependency_graph(mul, n, x):
    """
    For each d_k, determine which E677 instances are needed to compute it.

    The formula d_{k+1} = c_{k-1} ◇ ((c_k ◇ c_{k-1}) ◇ c_k) uses products
    that may involve elements outside the orbit. These products are themselves
    determined by E677 at various (a,b) pairs.

    We trace the FULL dependency: if an intermediate product involves an
    element w outside the orbit, what E677 instances determine w's
    multiplication behavior?
    """
    orbit = get_orbit(mul, n, x)
    p = len(orbit)
    orbit_set = set(orbit)
    dk = d_sequence(mul, orbit, x)

    print(f"\n{'═'*70}")
    print(f"  E677 DEPENDENCY GRAPH for x={x}, period={p}")
    print(f"{'═'*70}")

    # For each d_k, trace what we need
    # d_{k+1} = c_{k-1} ◇ ((c_k ◇ c_{k-1}) ◇ c_k)
    # = c_{k-1} ◇ R_{c_k}(L_{c_k}(c_{k-1}))
    #
    # From E677(c_{k-1}, c_k):
    #   c_{k-1} = L_{c_k}(c_{k-1} ◇ R_{c_k}(L_{c_k}(c_{k-1})))
    #   => L_{c_k}^{-1}(c_{k-1}) = c_{k-1} ◇ R_{c_k}(L_{c_k}(c_{k-1}))
    # This is ONE E677 instance: E677(c_{k-1}, c_k).

    # But wait — do we need MORE E677 instances to determine the
    # intermediate products if they involve out-of-orbit elements?
    # NO! The formula c_{k-1} ◇ ((c_k ◇ c_{k-1}) ◇ c_k) is computable
    # directly from the multiplication table. E677 is what CONSTRAINS
    # the table to be consistent.

    # The real question: which E677 instances constrain the SPECIFIC
    # table entries used in computing d_{k+1}?

    # Table entries used for d_{k+1}:
    #   mul[c_k][c_{k-1}]       — this is L_{c_k}(c_{k-1})
    #   mul[step1][c_k]         — this is R_{c_k}(step1)
    #   mul[c_{k-1}][step2]     — this is R_{step2}(c_{k-1})

    # E677(a,b) constrains: mul[b][mul[a][mul[mul[b][a]][b]]] = a
    # i.e., it relates mul[b][a], mul[...][b], mul[a][...], mul[b][...]

    print(f"\n  Table entries needed for each d_k:")
    print(f"  {'k':>3} | {'mul[c_k][c_{k-1}]':>20} | {'mul[s1][c_k]':>15} | {'mul[c_{k-1}][s2]':>18} | {'d_{k+1}':>8}")
    print(f"  {'-'*3}-+-{'-'*20}-+-{'-'*15}-+-{'-'*18}-+-{'-'*8}")

    entries_used = []  # List of (row, col) table entries needed

    for k in range(p):
        ck = orbit[k]
        ck1 = orbit[(k-1) % p]

        # Entry 1: mul[c_k][c_{k-1}]
        s1 = mul[ck][ck1]
        entry1 = (ck, ck1)

        # Entry 2: mul[s1][c_k]
        s2 = mul[s1][ck]
        entry2 = (s1, ck)

        # Entry 3: mul[c_{k-1}][s2]
        d_next = mul[ck1][s2]
        entry3 = (ck1, s2)

        entries_used.append({
            'k': k,
            'entries': [entry1, entry2, entry3],
            's1': s1, 's2': s2, 'd_next': d_next,
            's1_in': s1 in orbit_set,
            's2_in': s2 in orbit_set,
            'd_in': d_next in orbit_set,
        })

        s1_label = f"c_{orbit.index(s1)}" if s1 in orbit_set else f"{s1}(OUT)"
        s2_label = f"c_{orbit.index(s2)}" if s2 in orbit_set else f"{s2}(OUT)"
        d_label = f"c_{orbit.index(d_next)}" if d_next in orbit_set else f"{d_next}(OUT)"

        print(f"  {k:3d} | mul[{ck:2d}][{ck1:2d}]={s1:2d} ({s1_label:>6}) | "
              f"mul[{s1:2d}][{ck:2d}]={s2:2d} ({s2_label:>6}) | "
              f"mul[{ck1:2d}][{s2:2d}]={d_next:2d} ({d_label:>6}) | d_{(k+1)%p}={d_next}")

    # Now: which E677(a,b) instances constrain each table entry?
    # mul[r][c] is constrained by any E677(a,b) where the computation
    # of E677(a,b) reads or writes mul[r][c].

    print(f"\n  Which E677(a,b) instances constrain each table entry?")
    print(f"  (E677(a,b): a = mul[b][mul[a][mul[mul[b][a]][b]]])")
    print()

    # For each table entry (r,c), find all E677(a,b) that INVOLVE it
    # E677(a,b) uses entries: mul[b][a], mul[ba][b], mul[a][bab], mul[b][a_bab]
    # where ba=mul[b][a], bab=mul[ba][b], a_bab=mul[a][bab]

    def e677_entries_used(a, b):
        """Return the 4 table entries used by E677(a,b)."""
        ba = mul[b][a]       # entry (b,a)
        bab = mul[ba][b]     # entry (ba, b)
        a_bab = mul[a][bab]  # entry (a, bab)
        result = mul[b][a_bab]  # entry (b, a_bab)
        return [(b, a), (ba, b), (a, bab), (b, a_bab)]

    # For the critical entries, find constraining E677 instances
    critical_entries = set()
    for info in entries_used:
        for e in info['entries']:
            critical_entries.add(e)

    print(f"  Total critical table entries: {len(critical_entries)}")
    print(f"  Entries involving out-of-orbit elements:")
    for (r, c) in sorted(critical_entries):
        r_in = r in orbit_set
        c_in = c in orbit_set
        if not r_in or not c_in:
            r_label = f"c_{orbit.index(r)}" if r_in else f"{r}(OUT)"
            c_label = f"c_{orbit.index(c)}" if c_in else f"{c}(OUT)"
            print(f"    mul[{r_label}][{c_label}] = {mul[r][c]}")

    # Find E677 instances that touch critical entries
    print(f"\n  E677 instances touching critical entries:")
    touching_instances = defaultdict(list)
    for a in range(n):
        for b in range(n):
            entries = e677_entries_used(a, b)
            for e in entries:
                if e in critical_entries:
                    a_in = a in orbit_set
                    b_in = b in orbit_set
                    cross = not (a_in and b_in)
                    touching_instances[e].append((a, b, cross))

    cross_orbit_instances = set()
    orbit_only_instances = set()
    for entry, instances in touching_instances.items():
        for (a, b, cross) in instances:
            if cross:
                cross_orbit_instances.add((a, b))
            else:
                orbit_only_instances.add((a, b))

    print(f"    Orbit-only E677 instances touching critical entries: {len(orbit_only_instances)}")
    print(f"    Cross-orbit E677 instances touching critical entries: {len(cross_orbit_instances)}")

    # Show the cross-orbit instances grouped by which d_k they affect
    print(f"\n  Cross-orbit instances by target d_k:")
    for info in entries_used:
        k = info['k']
        dk_cross = set()
        for e in info['entries']:
            for (a, b, cross) in touching_instances.get(e, []):
                if cross:
                    dk_cross.add((a, b))
        if dk_cross:
            print(f"    d_{(k+1)%p}: {len(dk_cross)} cross-orbit E677 instances")
            for (a, b) in sorted(dk_cross)[:5]:
                a_lab = f"c_{orbit.index(a)}" if a in orbit_set else f"{a}(OUT)"
                b_lab = f"c_{orbit.index(b)}" if b in orbit_set else f"{b}(OUT)"
                print(f"      E677({a_lab}, {b_lab})")
            if len(dk_cross) > 5:
                print(f"      ... and {len(dk_cross)-5} more")

    return entries_used, touching_instances


# ═══════════════════════════════════════════════════════════════════
# ANALYSIS 3: THE ALTERNATIVE FORMULA — Identity iii
# ═══════════════════════════════════════════════════════════════════

def trace_identity_iii(mul, n, x):
    """
    Identity iii: x = (L_y(x)) ◇ R_y(L_y²(x))
    i.e., x = (y◇x) ◇ ((y◇(y◇x)) ◇ y)

    Applied with specific orbit elements, this gives relationships
    between d_k values.

    Setting y = c_j, x = c_k:
      c_k = (c_j◇c_k) ◇ ((c_j◇(c_j◇c_k))◇c_j)
      c_k = L_{c_j}(c_k) ◇ R_{c_j}(L_{c_j}²(c_k))

    When j = 0 (y = x, the orbit generator):
      c_k = L_x(c_k) ◇ R_x(L_x²(c_k))
      c_k = c_{k+1} ◇ R_x(c_{k+2})
      c_k = c_{k+1} ◇ (c_{k+2}◇x)
      c_k = c_{k+1} ◇ d_{k+2}
      i.e., mul[c_{k+1}][d_{k+2}] = c_k

    This is IDENTITY iii specialized to the orbit!
    It says: c_{k+1} ◇ d_{k+2} = c_k, i.e., L_{c_{k+1}}(d_{k+2}) = c_k
    i.e., d_{k+2} = L_{c_{k+1}}^{-1}(c_k)

    Comparing with the d_k recurrence: d_{k+1} = L_{c_k}^{-1}(c_{k-1})
    These are the SAME (shift index by 1).
    """
    orbit = get_orbit(mul, n, x)
    p = len(orbit)
    orbit_set = set(orbit)
    dk = d_sequence(mul, orbit, x)

    print(f"\n{'═'*70}")
    print(f"  IDENTITY iii ANALYSIS for x={x}, period={p}")
    print(f"{'═'*70}")

    # Verify: mul[c_{k+1}][d_{k+2}] = c_k for all k
    print(f"\n  Verifying identity iii: c_{{k+1}} ◇ d_{{k+2}} = c_k")
    for k in range(p):
        ck = orbit[k]
        ck1 = orbit[(k+1) % p]
        dk2 = dk[(k+2) % p]
        result = mul[ck1][dk2]
        status = "✓" if result == ck else "✗"
        print(f"    k={k}: mul[c_{(k+1)%p}={ck1}][d_{(k+2)%p}={dk2}] = {result}, expected c_{k}={ck} {status}")

    # Now use identity iii with y = external element:
    # For y NOT in orbit, x = c_k in orbit:
    # c_k = (y◇c_k) ◇ ((y◇(y◇c_k))◇y)
    # = L_y(c_k) ◇ R_y(L_y²(c_k))

    outside = [z for z in range(n) if z not in orbit_set]
    if not outside:
        print(f"\n  Orbit = M, no external identity iii analysis possible.")
        return

    print(f"\n  Identity iii with y = external element:")
    print(f"  For y outside orbit, x = c_k in orbit:")
    print(f"  c_k = L_y(c_k) ◇ R_y(L_y²(c_k))")
    print()

    # For each external y, trace where L_y maps orbit elements
    for y in outside[:3]:
        print(f"  y={y} (external):")
        Ly = get_L_perm(mul, n, y)
        for k in range(min(p, 5)):
            ck = orbit[k]
            Ly_ck = Ly[ck]          # y◇c_k
            Ly2_ck = Ly[Ly_ck]      # y◇(y◇c_k)
            Ry_Ly2 = mul[Ly2_ck][y] # (y◇(y◇c_k))◇y
            result = mul[Ly_ck][Ry_Ly2]  # L_y(c_k) ◇ R_y(L_y²(c_k))

            Ly_in = Ly_ck in orbit_set
            Ly2_in = Ly2_ck in orbit_set

            print(f"    c_{k}: L_y(c_{k})={'IN' if Ly_in else 'OUT'}({Ly_ck}), "
                  f"L_y²(c_{k})={'IN' if Ly2_in else 'OUT'}({Ly2_ck}), "
                  f"result={result} {'✓' if result==ck else '✗'}")


# ═══════════════════════════════════════════════════════════════════
# ANALYSIS 4: WHAT MAKES d_{p-3} LAND ON c_{p-4}?
# ═══════════════════════════════════════════════════════════════════

def analyze_dp3_forcing(mul, n, x):
    """
    The target: d_{p-3} = c_{p-4}. Equivalently, c_{p-4} ◇ x = c_{p-4}...
    no wait. d_k = c_k ◇ x. So d_{p-3} = c_{p-3} ◇ x.

    Wait, let me be careful. d_k = mul[orbit[k]][x] = c_k ◇ x.

    The target is d_{p-3} = c_{p-4}:
      c_{p-3} ◇ x = c_{p-4}

    From the recurrence: d_{p-3} = L_{c_{p-4}}^{-1}(c_{p-5})
    (using d_{k+1} = L_{c_k}^{-1}(c_{k-1}) with k = p-4)

    So c_{p-4} ◇ x = ... wait no. d_{p-3} = c_{p-3} ◇ x.

    Let me reindex. d_k = c_k ◇ x.
    The recurrence says d_{k+1} = L_{c_k}^{-1}(c_{k-1}).
    Let's verify: from E677(c_{k-1}, c_k) applied at x=c_{k-1}, y=c_k:
      Actually no, E677(a, b): a = b ◇ (a ◇ ((b◇a)◇b))

    From identity iii (y=x, x=c_k):
      c_k = c_{k+1} ◇ d_{k+2}
      i.e., d_{k+2} = L_{c_{k+1}}^{-1}(c_k)

    So d_{k} = L_{c_{k-1}}^{-1}(c_{k-2}).

    Target: d_{p-3} = c_{p-4}
    From recurrence: d_{p-3} = L_{c_{p-4}}^{-1}(c_{p-5})

    So target is: L_{c_{p-4}}^{-1}(c_{p-5}) = c_{p-4}
    i.e., L_{c_{p-4}}(c_{p-4}) = c_{p-5}
    i.e., c_{p-4} ◇ c_{p-4} = c_{p-5}

    This IS the single-point identity: c_{p-4}² = c_{p-5}.
    """
    orbit = get_orbit(mul, n, x)
    p = len(orbit)
    orbit_set = set(orbit)
    dk = d_sequence(mul, orbit, x)

    print(f"\n{'═'*70}")
    print(f"  d_{{p-3}} FORCING ANALYSIS for x={x}, period={p}")
    print(f"{'═'*70}")

    if p < 5:
        print(f"  Period too small ({p} < 5). This case should be handled by")
        print(f"  period impossibility proofs (p=2,3 proven, p=4 SAT-verified).")
        return

    # Verify the target
    target_k = p - 3
    target_d = dk[target_k]
    target_c = orbit[p-4]
    holds = target_d == target_c
    print(f"\n  Target: d_{{p-3}} = d_{target_k} = {target_d}")
    print(f"  Expected: c_{{p-4}} = c_{p-4} = {target_c}")
    print(f"  Holds: {holds} {'(E255 confirmed)' if holds else '(E255 FAILS!)'}")

    # Equivalently: c_{p-4}² = c_{p-5}
    sq = mul[orbit[p-4]][orbit[p-4]]
    print(f"\n  Single-point identity: c_{{p-4}}◇c_{{p-4}} = {sq}")
    print(f"  Expected c_{{p-5}} = {orbit[p-5]}")
    print(f"  Holds: {sq == orbit[p-5]}")

    # Trace the recurrence BACKWARD from d_{p-3}:
    # d_{p-3} is determined by L_{c_{p-4}}^{-1}(c_{p-5})
    # = c_{p-5} ◇ ((c_{p-4} ◇ c_{p-5}) ◇ c_{p-4})
    print(f"\n  Backward trace from d_{{p-3}}:")
    print(f"  d_{{p-3}} = L_{{c_{{p-4}}}}^{{-1}}(c_{{p-5}})")

    # What determines this? We need L_{c_{p-4}} evaluated at c_{p-4}
    # (to check if L_{c_{p-4}}(c_{p-4}) = c_{p-5}, which IS the target)
    # The formula: L_y^{-1}(x) = x ◇ R_y(L_y(x))
    # With y = c_{p-4}, x = c_{p-5}:
    #   L_{c_{p-4}}^{-1}(c_{p-5}) = c_{p-5} ◇ R_{c_{p-4}}(c_{p-4} ◇ c_{p-5})
    #                              = c_{p-5} ◇ ((c_{p-4} ◇ c_{p-5}) ◇ c_{p-4})

    cp4 = orbit[p-4]
    cp5 = orbit[p-5]

    step1 = mul[cp4][cp5]  # c_{p-4} ◇ c_{p-5}
    step2 = mul[step1][cp4]  # (c_{p-4} ◇ c_{p-5}) ◇ c_{p-4}
    step3 = mul[cp5][step2]  # c_{p-5} ◇ (...)

    s1_in = step1 in orbit_set
    s2_in = step2 in orbit_set

    print(f"    c_{{p-4}} ◇ c_{{p-5}} = mul[{cp4}][{cp5}] = {step1} "
          f"({'IN orbit' if s1_in else 'OUTSIDE orbit'})")
    print(f"    (...) ◇ c_{{p-4}} = mul[{step1}][{cp4}] = {step2} "
          f"({'IN orbit' if s2_in else 'OUTSIDE orbit'})")
    print(f"    c_{{p-5}} ◇ (...) = mul[{cp5}][{step2}] = {step3} "
          f"(should be d_{{p-3}} = {dk[target_k]})")

    # Now the KEY question: if step1 or step2 exits the orbit,
    # what determines mul[step1][cp4] or mul[cp5][step2]?
    # These are RIGHT-multiplication values that may involve
    # elements outside the orbit. Their values are constrained
    # by E677 instances involving those elements.

    if not s1_in:
        print(f"\n  *** c_{{p-4}} ◇ c_{{p-5}} = {step1} EXITS orbit! ***")
        print(f"  mul[{step1}][{cp4}] needs to be determined.")
        print(f"  This entry is constrained by E677(a,b) where the computation touches ({step1},{cp4}).")

        # Find all E677(a,b) that use entry (step1, cp4)
        constraints = []
        for a in range(n):
            for b in range(n):
                ba = mul[b][a]
                bab = mul[ba][b]
                a_bab = mul[a][bab]
                # Entries used: (b,a), (ba,b), (a,bab), (b,a_bab)
                if (b, a) == (step1, cp4) or (ba, b) == (step1, cp4) or \
                   (a, bab) == (step1, cp4) or (b, a_bab) == (step1, cp4):
                    a_lab = f"c_{orbit.index(a)}" if a in orbit_set else f"{a}(OUT)"
                    b_lab = f"c_{orbit.index(b)}" if b in orbit_set else f"{b}(OUT)"
                    constraints.append((a, b, a_lab, b_lab))

        print(f"  E677 instances using entry ({step1}, {cp4}):")
        for (a, b, al, bl) in constraints[:10]:
            print(f"    E677({al}, {bl})")

    if not s2_in:
        print(f"\n  *** intermediate step2 = {step2} EXITS orbit! ***")

    # Additionally trace the full "backward chain":
    # We know d_0 = c_1 (provable from E677(x,x))
    # We know d_1 = c_{p-2} (provable from E677(x,x))
    # We need d_{p-3} = c_{p-4}
    # The recurrence d_{k+2} = L_{c_{k+1}}^{-1}(c_k) connects them

    print(f"\n  Full d_k chain:")
    print(f"  Known: d_0 = c_1 = {orbit[1]} (proven)")
    print(f"  Known: d_1 = c_{{p-2}} = {orbit[p-2]} (proven)")
    print(f"  Target: d_{{p-3}} = c_{{p-4}} = {orbit[p-4]} (= E255)")
    print(f"  Also target: d_{{p-2}} = c_0 = x = {x} (= E255 directly)")
    print()

    # Show which d_k are provably known vs which need the full argument
    print(f"  d_k status:")
    for k in range(p):
        val = dk[k]
        in_orb = val in orbit_set
        if in_orb:
            pos = orbit.index(val)
            label = f"c_{pos}"
        else:
            label = f"OUT({val})"

        known = ""
        if k == 0:
            known = " [PROVEN: d_0 = c_1]"
        elif k == 1:
            known = " [PROVEN: d_1 = c_{p-2}]"
        elif k == p-3:
            known = " [TARGET: d_{p-3} = c_{p-4} ⟺ E255]"
        elif k == p-2:
            known = " [TARGET: d_{p-2} = c_0 = x ⟺ E255]"

        print(f"    d_{k:2d} = {val:3d} = {label:>10}{known}")


# ═══════════════════════════════════════════════════════════════════
# ANALYSIS 5: ALTERNATIVE d_k EXPRESSION VIA E677 CASCADING
# ═══════════════════════════════════════════════════════════════════

def analyze_e677_cascade(mul, n, x):
    """
    Try to express d_k values using cascading E677 applications.

    E677(a, b) at specific (a,b) gives relationships between products.
    Can we chain E677 instances to connect the known d_0, d_1 to the
    target d_{p-3}?

    Key E677 specializations:
    - E677(x, x): gives d_1 = c_{p-2} [known]
    - E677(x, c_k): x = c_k ◇ (x ◇ ((c_k◇x)◇c_k))
                       = L_{c_k}(x ◇ R_{c_k}(c_{k+1}))
                       = L_{c_k}(x ◇ (c_{k+1}◇c_k))
                       = L_{c_k}(x ◇ d_{k+1}... no wait)

    Actually: E677(x, c_k): x = L_{c_k}(x ◇ R_{c_k}(L_{c_k}(x)))
                             = L_{c_k}(x ◇ R_{c_k}(c_k ◇ x))
                             = L_{c_k}(x ◇ ((c_k◇x)◇c_k))
                             = L_{c_k}(x ◇ (d_k ◇ c_k))  [d_k = c_k◇x... no]

    Wait. d_k = c_k◇x. But L_{c_k}(x) = c_k◇x = d_k? No!
    L_{c_k}(x) = c_k ◇ x = d_k? Let me be careful:
    L_y(x) = y ◇ x = mul[y][x].

    So L_{c_k}(x) = c_k ◇ x = mul[c_k][x] = d_k. Yes!

    E677(x, c_k): x = L_{c_k}(x ◇ R_{c_k}(L_{c_k}(x)))
                    = L_{c_k}(x ◇ R_{c_k}(d_k))
                    = L_{c_k}(x ◇ (d_k ◇ c_k))

    So L_{c_k}^{-1}(x) = x ◇ (d_k ◇ c_k)
    But L_{c_k}^{-1}(x) is just a specific element.

    Actually, from the E677 L-inverse formula:
    L_y^{-1}(a) = a ◇ R_y(L_y(a))

    So L_{c_k}^{-1}(x) = x ◇ R_{c_k}(c_k ◇ x) = x ◇ R_{c_k}(d_k) = x ◇ (d_k ◇ c_k)

    This tells us: L_{c_k}^{-1}(x) = x ◇ (d_k ◇ c_k)
    But also from identity iii: c_{-1} = c_{p-1} = c_0 ◇ d_2...
    no, identity iii says c_k = c_{k+1} ◇ d_{k+2}.

    Let me just use identity iii: d_{k+2} = L_{c_{k+1}}^{-1}(c_k)
    And the L-inverse formula: L_{c_{k+1}}^{-1}(c_k) = c_k ◇ R_{c_{k+1}}(c_{k+1}◇c_k)
                              = c_k ◇ ((c_{k+1}◇c_k)◇c_{k+1})

    So d_{k+2} = c_k ◇ ((c_{k+1}◇c_k)◇c_{k+1})
    """
    orbit = get_orbit(mul, n, x)
    p = len(orbit)
    orbit_set = set(orbit)
    dk = d_sequence(mul, orbit, x)

    print(f"\n{'═'*70}")
    print(f"  E677 CASCADE ANALYSIS for x={x}, period={p}")
    print(f"{'═'*70}")

    # The formula: d_{k+2} = c_k ◇ ((c_{k+1}◇c_k) ◇ c_{k+1})
    # This involves only orbit elements in the FIRST and THIRD positions (c_k, c_{k+1})
    # but c_{k+1}◇c_k might exit the orbit!

    print(f"\n  Formula: d_{{k+2}} = c_k ◇ ((c_{{k+1}}◇c_k) ◇ c_{{k+1}})")
    print(f"  This is the L-inverse formula applied to the d_k recurrence.")
    print()

    # Build the orbit multiplication table
    orb_mul = [[mul[orbit[i]][orbit[j]] for j in range(p)] for i in range(p)]

    print(f"  Orbit multiplication table (indices are orbit positions):")
    if p <= 12:
        header = "     " + " ".join(f"{j:3d}" for j in range(p))
        print(f"  {header}")
        for i in range(p):
            row_str = f"  {i:2d}: "
            for j in range(p):
                val = orb_mul[i][j]
                if val in orbit_set:
                    pos = orbit.index(val)
                    row_str += f"{pos:3d} "
                else:
                    row_str += f"  * "
            print(row_str)

    print(f"\n  d_k chain computation (using the formula):")
    for k in range(p):
        ck = orbit[k]
        ck1 = orbit[(k+1) % p]

        # c_{k+1} ◇ c_k
        inner = mul[ck1][ck]
        inner_in = inner in orbit_set

        # (...) ◇ c_{k+1}
        middle = mul[inner][ck1]
        middle_in = middle in orbit_set

        # c_k ◇ (...)
        result = mul[ck][middle]

        expected = dk[(k+2) % p]
        match = "✓" if result == expected else "✗"

        inner_lab = f"c_{orbit.index(inner)}" if inner_in else f"OUT"
        middle_lab = f"c_{orbit.index(middle)}" if middle_in else f"OUT"

        print(f"    k={k:2d}: c_{{k+1}}◇c_k={inner:3d}({inner_lab:>3}), "
              f"(...)◇c_{{k+1}}={middle:3d}({middle_lab:>3}), "
              f"c_k◇(...)={result:3d} = d_{(k+2)%p} (exp={expected}) {match}")

    # KEY INSIGHT: The formula for d_{k+2} uses the ORBIT MULTIPLICATION TABLE
    # at position (k+1, k). If orbit multiplication stays in orbit, we have a
    # closed recurrence. If it exits, we need external information.

    n_exits = sum(1 for i in range(p) for j in range(p)
                  if mul[orbit[i]][orbit[j]] not in orbit_set)
    print(f"\n  Orbit multiplication exits: {n_exits}/{p*p} entries go outside orbit")

    # For the specific d_{p-3} computation:
    # d_{p-3} = d_{(p-5)+2} = c_{p-5} ◇ ((c_{p-4}◇c_{p-5}) ◇ c_{p-4})
    if p >= 5:
        k = p - 5
        ck = orbit[k]
        ck1 = orbit[k+1]  # c_{p-4}

        inner = mul[ck1][ck]  # c_{p-4} ◇ c_{p-5}
        middle = mul[inner][ck1]  # (...) ◇ c_{p-4}
        result = mul[ck][middle]  # c_{p-5} ◇ (...)

        print(f"\n  *** THE CRITICAL COMPUTATION for d_{{p-3}}: ***")
        print(f"  d_{{p-3}} = c_{{p-5}} ◇ ((c_{{p-4}} ◇ c_{{p-5}}) ◇ c_{{p-4}})")
        print(f"  c_{{p-4}} ◇ c_{{p-5}} = mul[{ck1}][{ck}] = {inner}")
        print(f"    {'IN orbit at position ' + str(orbit.index(inner)) if inner in orbit_set else 'OUTSIDE orbit'}")
        print(f"  (...) ◇ c_{{p-4}} = mul[{inner}][{ck1}] = {middle}")
        print(f"    {'IN orbit at position ' + str(orbit.index(middle)) if middle in orbit_set else 'OUTSIDE orbit'}")
        print(f"  c_{{p-5}} ◇ (...) = mul[{ck}][{middle}] = {result}")
        print(f"  Expected: c_{{p-4}} = {orbit[p-4]}")
        print(f"  Match: {result == orbit[p-4]}")


# ═══════════════════════════════════════════════════════════════════
# ANALYSIS 6: GLOBAL PATTERN IN L_y PERMUTATION STRUCTURE
# ═══════════════════════════════════════════════════════════════════

def analyze_Ly_on_orbit(mul, n, x):
    """
    For each external element y, how does L_y permute the orbit of x?

    L_x restricted to its own orbit is a p-cycle by definition.
    But L_y (y ≠ x) may permute orbit elements differently, or
    map some orbit elements outside the orbit.

    Key question: for which y does L_y map orbit elements BACK into
    the orbit? These create "intra-orbit constraints" from external elements.
    """
    orbit = get_orbit(mul, n, x)
    p = len(orbit)
    orbit_set = set(orbit)
    outside = [z for z in range(n) if z not in orbit_set]

    if not outside:
        print(f"\n  Orbit = M for x={x}, skipping L_y analysis.")
        return

    print(f"\n{'═'*70}")
    print(f"  L_y ON ORBIT ANALYSIS for x={x}, period={p}")
    print(f"{'═'*70}")
    print(f"  Orbit: {orbit}")
    print(f"  External elements: {outside[:20]}{'...' if len(outside)>20 else ''}")

    # For each external y, compute L_y restricted to orbit elements
    print(f"\n  L_y action on orbit elements (y external):")
    print(f"  {'y':>4} | {'# orbit->orbit':>14} | {'# orbit->outside':>16} | {'mapping':>30}")
    print(f"  {'-'*4}-+-{'-'*14}-+-{'-'*16}-+-{'-'*30}")

    for y in outside[:15]:
        images = [mul[y][c] for c in orbit]
        in_orbit = sum(1 for img in images if img in orbit_set)
        out_orbit = p - in_orbit

        # Show the mapping
        mapping = []
        for k, img in enumerate(images):
            if img in orbit_set:
                mapping.append(f"c{k}→c{orbit.index(img)}")
            else:
                mapping.append(f"c{k}→OUT")

        map_str = " ".join(mapping[:6])
        if p > 6:
            map_str += "..."

        print(f"  {y:4d} | {in_orbit:>14} | {out_orbit:>16} | {map_str}")

    # KEY: For elements y where L_y maps MANY orbit elements back into orbit,
    # E677(a, y) with a in orbit gives intra-orbit constraints.
    # These are the "cross-orbit bridges" that force consistency.

    # Find y that preserves the most orbit elements
    best_y = max(outside, key=lambda y: sum(1 for c in orbit if mul[y][c] in orbit_set))
    best_count = sum(1 for c in orbit if mul[best_y][c] in orbit_set)
    print(f"\n  Best orbit-preserving external element: y={best_y} "
          f"({best_count}/{p} orbit elements stay in orbit)")

    # For this y, what does E677(c_k, y) tell us?
    print(f"\n  E677(c_k, {best_y}) constraints for orbit elements c_k:")
    for k in range(min(p, 8)):
        ck = orbit[k]
        # E677(c_k, y): c_k = L_y(c_k ◇ R_y(L_y(c_k)))
        Ly_ck = mul[best_y][ck]   # L_y(c_k)
        Ry_Ly = mul[Ly_ck][best_y]  # R_y(L_y(c_k)) = (L_y(c_k))◇y
        ck_Ry = mul[ck][Ry_Ly]     # c_k ◇ R_y(L_y(c_k))
        final = mul[best_y][ck_Ry]  # L_y(...)

        Ly_in = Ly_ck in orbit_set
        print(f"    E677(c_{k}, {best_y}): L_y(c_{k})={Ly_ck}({'IN' if Ly_in else 'OUT'}), "
              f"result={final} (should be c_{k}={ck}): {'✓' if final==ck else '✗'}")


# ═══════════════════════════════════════════════════════════════════
# MAIN
# ═══════════════════════════════════════════════════════════════════

def run_analysis(mul, n, name, test_elements=None):
    """Run full cross-orbit deep analysis on a model."""
    print(f"\n{'#'*70}")
    print(f"# {name}")
    print(f"{'#'*70}")

    assert verify_e677(mul, n), f"{name}: E677 verification FAILED!"
    assert verify_e255(mul, n), f"{name}: E255 verification FAILED!"
    print(f"E677 ✓, E255 ✓")

    if test_elements is None:
        # Find non-idempotent elements
        test_elements = []
        seen_periods = set()
        for x in range(n):
            orb = get_orbit(mul, n, x)
            p = len(orb)
            if p > 1 and p not in seen_periods:
                test_elements.append(x)
                seen_periods.add(p)
                if len(test_elements) >= 3:
                    break

    for x in test_elements:
        trace_dk_recurrence(mul, n, x)
        build_dependency_graph(mul, n, x)
        trace_identity_iii(mul, n, x)
        analyze_dp3_forcing(mul, n, x)
        analyze_e677_cascade(mul, n, x)
        analyze_Ly_on_orbit(mul, n, x)


def main():
    print("E677 Cross-Orbit Deep Flow Analysis")
    print("=" * 70)
    print("Goal: Trace the mechanism by which cross-orbit E677 forces E255")
    print()

    # Jihoon model (n=31, period 10 — most interesting)
    mul_j, n_j = make_jihoon()
    run_analysis(mul_j, n_j, "JIHOON MODEL (n=31, period=10)", test_elements=[0])

    # Size-7 affine (orbit = M, no cross-orbit possible)
    mul7, n7 = make_size7()
    run_analysis(mul7, n7, "SIZE-7 AFFINE (orbit=M, p=7)", test_elements=[0])

    # Adam model (n=35, mixed periods)
    mul_a, n_a = make_adam()
    run_analysis(mul_a, n_a, "ADAM MODEL (n=35)", test_elements=[0, 4])


if __name__ == '__main__':
    main()
