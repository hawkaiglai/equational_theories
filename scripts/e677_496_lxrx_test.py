#!/usr/bin/env python3
"""
Test L_x∘R_x fixed point structure on the 496-element blueprint model.

Key question: Does L_x∘R_x have exactly 1 fixed point per x, even though
R_x is non-bijective in this model?

The 496-model is entirely idempotent (x◇x=x for all x), has non-bijective
R_x, yet E255 holds trivially. If L_x∘R_x still has exactly 1 FP, that's
a non-circular structural observation worth proving from E677 + finiteness.
"""

import sys
from collections import Counter

# ══════════════════════════════════════════════════════════════════════
# GF(16) arithmetic
# ══════════════════════════════════════════════════════════════════════

MODPOLY = 0b10011  # x^4 + x + 1

def gf16_mul(a, b):
    result = 0
    while b:
        if b & 1:
            result ^= a
        a <<= 1
        if a & 0b10000:
            a ^= MODPOLY
        b >>= 1
    return result

def gf16_add(a, b):
    return a ^ b

def gf16_pow(a, k):
    result = 1
    base = a
    while k > 0:
        if k & 1:
            result = gf16_mul(result, base)
        base = gf16_mul(base, base)
        k >>= 1
    return result

def gf16_find_root_of_unity(k):
    """Find primitive k-th root of unity in GF(16)*. Group order=15."""
    # Find primitive root of GF(16)*
    for g in range(2, 16):
        order = 1
        x = g
        while x != 1 and order <= 15:
            x = gf16_mul(x, g)
            order += 1
        if order == 15:
            prim = g
            break
    root = gf16_pow(prim, 15 // k)
    return root

# ══════════════════════════════════════════════════════════════════════
# Build the 496-element model
# ══════════════════════════════════════════════════════════════════════

def f31_qr(x):
    """Is x a quadratic residue mod 31? (x != 0)"""
    if x == 0:
        return None
    return pow(x, 15, 31) == 1

def build_496():
    """Build F_31 × F_16 product magma."""
    beta = 2
    # Base magma on F_31: x◇y = (1+β)x - βy mod 31
    base_mul = [[(((1 + beta) * x - beta * y) % 31) for y in range(31)] for x in range(31)]

    # Fiber operations on GF(16)
    omega = gf16_find_root_of_unity(3)  # primitive cube root
    zeta = gf16_find_root_of_unity(5)   # primitive 5th root

    one_plus_zeta = gf16_add(1, zeta)
    one_plus_omega = gf16_add(1, omega)

    # ◇^0(s,t) = (1+ζ)s + ζt
    def op0(s, t):
        return gf16_add(gf16_mul(one_plus_zeta, s), gf16_mul(zeta, t))
    # ◇^+(s,t) = t
    def op_plus(s, t):
        return t
    # ◇^-(s,t) = (1+ω)s + ωt
    def op_minus(s, t):
        return gf16_add(gf16_mul(one_plus_omega, s), gf16_mul(omega, t))

    N = 31 * 16  # 496

    def encode(x, s):
        return x * 16 + s
    def decode(idx):
        return idx // 16, idx % 16
    def get_fiber_op(x, y):
        diff = (y - x) % 31
        if diff == 0:
            return op0
        elif f31_qr(diff):
            return op_plus
        else:
            return op_minus

    print(f"Building 496-element model... (ω={omega}, ζ={zeta})")
    mul = [[0] * N for _ in range(N)]
    for i in range(N):
        x, s = decode(i)
        for j in range(N):
            y, t = decode(j)
            base_result = base_mul[x][y]
            fiber_op = get_fiber_op(x, y)
            fiber_result = fiber_op(s, t)
            mul[i][j] = encode(base_result, fiber_result)

    return mul, N

# ══════════════════════════════════════════════════════════════════════
# Analysis
# ══════════════════════════════════════════════════════════════════════

def main():
    mul, N = build_496()

    # Verify E677 on a sample (full check is slow for 496^2)
    print("Verifying E677 (sampling 1000 random pairs)...")
    import random
    random.seed(42)
    e677_ok = True
    for _ in range(1000):
        x = random.randint(0, N-1)
        y = random.randint(0, N-1)
        if mul[y][mul[x][mul[mul[y][x]][y]]] != x:
            e677_ok = False
            break
    print(f"E677 sample check: {'✓' if e677_ok else '✗'}")

    # Check E255
    print("Checking E255...")
    e255_ok = True
    for x in range(N):
        if mul[mul[mul[x][x]][x]][x] != x:
            e255_ok = False
            break
    print(f"E255: {'✓' if e255_ok else '✗'}")

    # Check idempotency
    idem_count = sum(1 for x in range(N) if mul[x][x] == x)
    print(f"Idempotent elements: {idem_count}/{N}")

    # R_x bijectivity
    print("\nChecking R_x bijectivity...")
    rx_bij_count = 0
    rx_image_sizes = []
    for x in range(N):
        col = set(mul[y][x] for y in range(N))
        if len(col) == N:
            rx_bij_count += 1
        rx_image_sizes.append(len(col))
    rx_img_dist = Counter(rx_image_sizes)
    print(f"R_x bijective: {rx_bij_count}/{N}")
    print(f"R_x image size distribution: {dict(sorted(rx_img_dist.items()))}")

    # ══ THE KEY TEST: L_x∘R_x fixed point count ══════════════════
    print("\n" + "=" * 60)
    print("KEY TEST: L_x ∘ R_x fixed point count")
    print("=" * 60)

    lxrx_fp_counts = []
    for x in range(N):
        fp_count = 0
        for z in range(N):
            rz = mul[z][x]      # R_x(z) = z◇x
            lrz = mul[x][rz]    # L_x(R_x(z)) = x◇(z◇x)
            if lrz == z:
                fp_count += 1
        lxrx_fp_counts.append(fp_count)

    fp_dist = Counter(lxrx_fp_counts)
    print(f"L_x∘R_x FP count distribution: {dict(sorted(fp_dist.items()))}")
    print(f"  (key = number of fixed points, value = how many x have that count)")

    all_have_fp = all(c > 0 for c in lxrx_fp_counts)
    all_exactly_1 = all(c == 1 for c in lxrx_fp_counts)
    print(f"Every x has ≥1 FP: {'✓' if all_have_fp else '✗'}  (= E255)")
    print(f"Every x has exactly 1 FP: {'✓' if all_exactly_1 else '✗'}")

    # ══ R_x∘L_x fixed point count ════════════════════════════════
    print("\nR_x ∘ L_x fixed point count:")
    rxlx_fp_counts = []
    for x in range(N):
        fp_count = 0
        for z in range(N):
            lz = mul[x][z]      # L_x(z) = x◇z
            rlz = mul[lz][x]    # R_x(L_x(z)) = (x◇z)◇x
            if rlz == z:
                fp_count += 1
        rxlx_fp_counts.append(fp_count)

    rxlx_fp_dist = Counter(rxlx_fp_counts)
    print(f"R_x∘L_x FP count distribution: {dict(sorted(rxlx_fp_dist.items()))}")
    all_rxlx_1 = all(c == 1 for c in rxlx_fp_counts)
    print(f"Every x has exactly 1 FP: {'✓' if all_rxlx_1 else '✗'}")

    # ══ Left-fixer count per element ══════════════════════════════
    print("\nLeft-fixer count (#{y: y◇x = x}):")
    fixer_counts = []
    for x in range(N):
        fc = sum(1 for y in range(N) if mul[y][x] == x)
        fixer_counts.append(fc)
    fixer_dist = Counter(fixer_counts)
    print(f"Fixer count distribution: {dict(sorted(fixer_dist.items()))}")
    total_F = sum(fixer_counts)
    print(f"|F| = {total_F}  (|M| = {N})")

    # ══ |Fix(L_y)| distribution ═══════════════════════════════════
    print("\n|Fix(L_y)| distribution:")
    fix_ly = []
    for y in range(N):
        fc = sum(1 for x in range(N) if mul[y][x] == x)
        fix_ly.append(fc)
    fix_ly_dist = Counter(fix_ly)
    print(f"Distribution: {dict(sorted(fix_ly_dist.items()))}")
    print(f"Σ|Fix(L_y)| = {sum(fix_ly)}")

    # ══ SUMMARY ═══════════════════════════════════════════════════
    print("\n" + "=" * 60)
    print("SUMMARY — 496-element blueprint model")
    print("=" * 60)
    print(f"E677=✓, E255={'✓' if e255_ok else '✗'}, fully idempotent={idem_count==N}")
    print(f"R_x bijective: {rx_bij_count}/{N}")
    print(f"L_x∘R_x FP count: {dict(sorted(fp_dist.items()))}")
    print(f"R_x∘L_x FP count: {dict(sorted(rxlx_fp_dist.items()))}")
    print(f"|F| = {total_F}, |M| = {N}")

    if all_exactly_1:
        print("\n*** L_x∘R_x has EXACTLY 1 FP everywhere — even with non-bijective R_x! ***")
        print("*** This is a non-trivial structural observation. ***")
    elif all_have_fp:
        print("\n*** L_x∘R_x has ≥1 FP everywhere, but NOT always exactly 1. ***")
        print("*** The 'exactly 1' pattern breaks in this model. ***")
    else:
        print("\n*** Something is wrong — E255 should guarantee ≥1 FP. ***")


if __name__ == '__main__':
    main()
