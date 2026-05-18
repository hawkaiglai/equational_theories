#!/usr/bin/env python3
"""
Investigate the structure of image(R_x) and its relationship to L_x orbits.

Key question: Why does L_x ∘ R_x always have a fixed point, even when R_x
is non-surjective? What structure of image(R_x) forces this?

Concretely:
  - Is image(R_x) a union of L_x orbits (L_x-invariant)?
  - How does L_x act on image(R_x) vs its complement?
  - The FP condition: z = L_x(R_x(z)), i.e., R_x(z) = L_x^{-1}(z).
    So the FP is where R_x and L_x^{-1} agree. Why must they intersect?
  - What is the "fiber structure" of R_x? (preimage sizes)
"""

from collections import Counter, defaultdict
import sys

# ══════════════════════════════════════════════════════════════════════
# GF(16) and 496-model construction (same as before)
# ══════════════════════════════════════════════════════════════════════

MODPOLY = 0b10011

def gf16_mul(a, b):
    result = 0
    while b:
        if b & 1: result ^= a
        a <<= 1
        if a & 0b10000: a ^= MODPOLY
        b >>= 1
    return result

def gf16_add(a, b): return a ^ b

def gf16_pow(a, k):
    result = 1
    base = a
    while k > 0:
        if k & 1: result = gf16_mul(result, base)
        base = gf16_mul(base, base)
        k >>= 1
    return result

def gf16_find_root_of_unity(k):
    for g in range(2, 16):
        order, x = 1, g
        while x != 1 and order <= 15:
            x = gf16_mul(x, g); order += 1
        if order == 15:
            return gf16_pow(g, 15 // k)

def f31_qr(x):
    if x == 0: return None
    return pow(x, 15, 31) == 1

def build_496():
    beta = 2
    base_mul = [[(((1+beta)*x - beta*y) % 31) for y in range(31)] for x in range(31)]
    omega = gf16_find_root_of_unity(3)
    zeta = gf16_find_root_of_unity(5)
    opz = gf16_add(1, zeta)
    opw = gf16_add(1, omega)
    def op0(s,t): return gf16_add(gf16_mul(opz,s), gf16_mul(zeta,t))
    def op_plus(s,t): return t
    def op_minus(s,t): return gf16_add(gf16_mul(opw,s), gf16_mul(omega,t))
    N = 496
    mul = [[0]*N for _ in range(N)]
    for i in range(N):
        x,s = i//16, i%16
        for j in range(N):
            y,t = j//16, j%16
            br = base_mul[x][y]
            diff = (y-x)%31
            if diff==0: fr = op0(s,t)
            elif f31_qr(diff): fr = op_plus(s,t)
            else: fr = op_minus(s,t)
            mul[i][j] = br*16 + fr
    return mul, N

def jihoon_model():
    N = 31
    return [[(5*x + 27*y + 1) % N for y in range(N)] for x in range(N)], N

def adam_model():
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
# L_x orbit decomposition
# ══════════════════════════════════════════════════════════════════════

def lx_orbits(mul, x, n):
    """Decompose M into orbits of L_x (the permutation y ↦ x◇y)."""
    visited = [False] * n
    orbits = []
    for start in range(n):
        if visited[start]:
            continue
        orb = []
        cur = start
        while not visited[cur]:
            visited[cur] = True
            orb.append(cur)
            cur = mul[x][cur]
        orbits.append(orb)
    return orbits

def lx_inverse(mul, x, n):
    """Compute L_x^{-1} as a list: lx_inv[y] = z where x◇z = y."""
    inv = [0] * n
    for z in range(n):
        inv[mul[x][z]] = z
    return inv


# ══════════════════════════════════════════════════════════════════════
# Core analysis
# ══════════════════════════════════════════════════════════════════════

def analyze_image_rx(mul, n, label):
    print(f"\n{'═' * 70}")
    print(f"  IMAGE(R_x) STRUCTURE: {label}  (n={n})")
    print(f"{'═' * 70}")

    # Pick a few representative x values to analyze deeply
    # First collect orbit period info
    orbit_periods = {}
    for x in range(n):
        orbs = lx_orbits(mul, x, n)
        orbit_periods[x] = sorted([len(o) for o in orbs], reverse=True)

    period_types = Counter(tuple(orbit_periods[x]) for x in range(n))
    print(f"\n  L_x orbit structure types: {len(period_types)}")
    for sig, cnt in period_types.most_common(5):
        print(f"    {sig}: {cnt} elements")

    # For each x, analyze image(R_x) vs L_x orbits
    # Sample a few elements per orbit type
    analyzed = set()
    representatives = []
    for sig, cnt in period_types.most_common():
        for x in range(n):
            if tuple(orbit_periods[x]) == sig and x not in analyzed:
                representatives.append(x)
                analyzed.add(x)
                break

    for x in representatives[:4]:  # Analyze up to 4 representative x
        print(f"\n{'─' * 70}")
        print(f"  x = {x}, L_x orbit structure: {orbit_periods[x]}")
        print(f"{'─' * 70}")

        # image(R_x) = {y◇x : y ∈ M}
        image_rx = set(mul[y][x] for y in range(n))
        image_rx_size = len(image_rx)
        complement = set(range(n)) - image_rx

        print(f"  |image(R_x)| = {image_rx_size} / {n}")
        print(f"  |complement| = {len(complement)}")

        # L_x orbits
        orbits = lx_orbits(mul, x, n)
        print(f"  L_x has {len(orbits)} orbits: {[len(o) for o in orbits]}")

        # Is image(R_x) a union of L_x orbits?
        orbits_fully_in = 0
        orbits_fully_out = 0
        orbits_partial = 0
        for orb in orbits:
            orb_set = set(orb)
            intersection = orb_set & image_rx
            if len(intersection) == len(orb):
                orbits_fully_in += 1
            elif len(intersection) == 0:
                orbits_fully_out += 1
            else:
                orbits_partial += 1
                print(f"    PARTIAL orbit: size {len(orb)}, "
                      f"{len(intersection)}/{len(orb)} in image(R_x)")

        print(f"  Orbits fully in image(R_x): {orbits_fully_in}")
        print(f"  Orbits fully outside:       {orbits_fully_out}")
        print(f"  Orbits partially in:        {orbits_partial}")

        if orbits_partial == 0:
            print(f"  *** image(R_x) IS a union of L_x orbits! ***")
        else:
            print(f"  *** image(R_x) is NOT L_x-invariant ***")

        # Is image(R_x) L_x-invariant? i.e., L_x(image(R_x)) ⊆ image(R_x)?
        lx_image = set(mul[x][y] for y in image_rx)
        lx_invariant = lx_image.issubset(image_rx)
        print(f"  L_x(image(R_x)) ⊆ image(R_x): {'✓' if lx_invariant else '✗'}")

        # Is image(R_x) L_x^{-1}-invariant?
        lx_inv = lx_inverse(mul, x, n)
        lxinv_image = set(lx_inv[y] for y in image_rx)
        lxinv_invariant = lxinv_image.issubset(image_rx)
        print(f"  L_x^{{-1}}(image(R_x)) ⊆ image(R_x): {'✓' if lxinv_invariant else '✗'}")

        # R_x fiber structure: for each y in image(R_x), how many preimages?
        fiber_sizes = Counter()
        for y in range(n):
            ry = mul[y][x]
            fiber_sizes[ry] = fiber_sizes.get(ry, 0) + 1
        # Exclude elements not in image
        fiber_dist = Counter(fiber_sizes[y] for y in image_rx)
        print(f"  R_x fiber sizes (preimage counts): {dict(sorted(fiber_dist.items()))}")

        # THE KEY: Fixed point analysis
        # z is FP of L_x∘R_x iff x◇(z◇x) = z iff R_x(z) = L_x^{-1}(z)
        # So the FP is the intersection of the graphs of R_x and L_x^{-1}
        fp_z = None
        for z in range(n):
            rz = mul[z][x]
            liz = lx_inv[z]
            if rz == liz:
                fp_z = z
                break

        if fp_z is not None:
            rz = mul[fp_z][x]
            print(f"\n  Fixed point: z={fp_z}")
            print(f"    R_x(z) = {rz}, L_x^{{-1}}(z) = {lx_inv[fp_z]} (equal ✓)")
            print(f"    z in image(R_x): {fp_z in image_rx}")
            print(f"    R_x(z) in image(R_x): {rz in image_rx}")

            # What L_x orbit is z in?
            for i, orb in enumerate(orbits):
                if fp_z in set(orb):
                    pos = orb.index(fp_z)
                    print(f"    z is in L_x orbit #{i} (size {len(orb)}), position {pos}")
                    break
        else:
            print(f"\n  NO fixed point found! (BUG)")

        # ═══ New analysis: R_x as a map between L_x orbits ═══════
        print(f"\n  R_x orbit-to-orbit map:")
        orbit_map = {}  # maps orbit index of input to orbit index of output
        for i, orb in enumerate(orbits):
            targets = set()
            for y in orb:
                ry = mul[y][x]
                for j, orb2 in enumerate(orbits):
                    if ry in set(orb2):
                        targets.add(j)
                        break
            orbit_map[i] = targets
            if len(targets) <= 3:
                print(f"    Orbit {i} (size {len(orb)}) → orbits {targets}")

        # ═══ Key structural test: does R_x commute with L_x on any subset? ═══
        # R_x ∘ L_x = L_x ∘ R_x on which elements?
        commute_count = 0
        for z in range(n):
            rxlxz = mul[mul[x][z]][x]   # R_x(L_x(z))
            lxrxz = mul[x][mul[z][x]]   # L_x(R_x(z))
            if rxlxz == lxrxz:
                commute_count += 1
        print(f"\n  R_x∘L_x = L_x∘R_x at {commute_count}/{n} elements")

        # ═══ E677 constraint: what does E677 say about R_x directly? ═══
        # E677: for all y, x = y◇(x◇((y◇x)◇y))
        # Rearranging: L_y^{-1}(x) = x◇((y◇x)◇y) = R_{(y◇x)◇y}(x)
        # So for each y, we learn ONE value of some R_w at x:
        #   R_{(y◇x)◇y}(x) = L_y^{-1}(x)
        # What is the set {(y◇x)◇y : y ∈ M}?
        e677_rw_values = set()
        for y in range(n):
            yx = mul[y][x]
            w = mul[yx][y]  # w = (y◇x)◇y
            e677_rw_values.add(w)
        print(f"  E677 constrains R_w(x) for {len(e677_rw_values)} distinct w values")
        print(f"    (These w = (y◇x)◇y as y ranges over M)")

        # Is x always among those w? i.e., does w=x for some y?
        # w = x means (y◇x)◇y = x, i.e., R_y(L_y(x)) = R_y(y◇x) = (y◇x)◇y = x
        # So R_y(L_y(x)) = x for some y.
        x_in_w = x in e677_rw_values
        print(f"    x={x} is among constrained w: {x_in_w}")
        if x_in_w:
            # Which y gives w=x?
            for y in range(n):
                yx = mul[y][x]
                w = mul[yx][y]
                if w == x:
                    # Then R_x(x) = R_{w}(x) = L_y^{-1}(x)
                    ly_inv_x = lx_inv_at(mul, y, x, n)
                    print(f"    At y={y}: (y◇x)◇y = x, so R_x(x) = L_y^{{-1}}(x) = {ly_inv_x}")
                    print(f"    Verify: R_x(x) = x◇x = {mul[x][x]}, L_y^{{-1}}(x) = {ly_inv_x}")
                    break

    # ═══ GLOBAL: Check image(R_x) is L_x-invariant for ALL x ═════
    print(f"\n{'═' * 70}")
    print(f"  GLOBAL: Is image(R_x) always L_x-invariant?")
    print(f"{'═' * 70}")

    all_invariant = True
    invariant_count = 0
    for x in range(n):
        image_rx = set(mul[y][x] for y in range(n))
        lx_image_of_rx = set(mul[x][y] for y in image_rx)
        if lx_image_of_rx.issubset(image_rx):
            invariant_count += 1
        else:
            all_invariant = False

    print(f"  L_x-invariant: {invariant_count}/{n}")
    print(f"  All L_x-invariant: {'✓' if all_invariant else '✗'}")

    # ═══ GLOBAL: image(R_x) = union of L_x orbits? ═══════════════
    all_union = True
    union_count = 0
    for x in range(n):
        image_rx = set(mul[y][x] for y in range(n))
        orbits = lx_orbits(mul, x, n)
        is_union = True
        for orb in orbits:
            orb_set = set(orb)
            inter = orb_set & image_rx
            if 0 < len(inter) < len(orb):
                is_union = False
                break
        if is_union:
            union_count += 1
        else:
            all_union = False

    print(f"  image(R_x) = union of L_x orbits: {union_count}/{n}")
    print(f"  All unions: {'✓' if all_union else '✗'}")

    return all_invariant, all_union


def lx_inv_at(mul, y, x, n):
    """Compute L_y^{-1}(x): find z such that y◇z = x, i.e., mul[y][z] = x."""
    for z in range(n):
        if mul[y][z] == x:
            return z
    return None


# ══════════════════════════════════════════════════════════════════════
# Run on all models
# ══════════════════════════════════════════════════════════════════════

if __name__ == '__main__':
    print("Image(R_x) Structure Analysis")
    print("=" * 70)

    # Jihoon model
    mul31, n31 = jihoon_model()
    inv31, union31 = analyze_image_rx(mul31, n31, "Jihoon (5x+27y+1)%31")

    # Adam model
    mul35, n35 = adam_model()
    inv35, union35 = analyze_image_rx(mul35, n35, "Adam n=35")

    # 496-element model
    print("\nBuilding 496 model...")
    mul496, n496 = build_496()
    inv496, union496 = analyze_image_rx(mul496, n496, "Blueprint n=496")

    print(f"\n{'═' * 70}")
    print(f"  CROSS-MODEL SUMMARY")
    print(f"{'═' * 70}")
    for label, inv, union in [
        ("Jihoon n=31", inv31, union31),
        ("Adam n=35", inv35, union35),
        ("Blueprint n=496", inv496, union496)
    ]:
        print(f"  {label}: L_x-invariant={'✓' if inv else '✗'}, "
              f"union of orbits={'✓' if union else '✗'}")
