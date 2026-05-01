#!/usr/bin/env python3
"""
Construct the specific non-right-cancellative E677 magma from the blueprint
(Section "A finite non-right-cancellative example") and check E255.

Construction:
- Base: G = F_31 with x ◇ y = x - β(y-x) = (1+β)x - βy where β=2
  (β is primitive 5th root of unity in F_31: 2^5 = 32 ≡ 1 mod 31)
- Fiber: M = F_16 (has primitive cube root ω and primitive 5th root ζ)
- Three operations on M:
  s ◇^0 t = s - ζ(t-s) = (1+ζ)s - ζt
  s ◇^+ t = t
  s ◇^- t = s - ω(t-s) = (1+ω)s - ωt
- Assignment: ◇_{x,y} is ◇^0 if y=x, ◇^+ if y-x is QR, ◇^- if y-x is QNR
- Product magma: (x,s) ◇ (y,t) = (x ◇ y, s ◇_{x,y} t)
"""

import sys

# ── F_31 arithmetic ──────────────────────────────────────────────────

def f31_qr(x):
    """Check if x is a quadratic residue in F_31 (x ≠ 0)."""
    if x == 0:
        return None  # neither QR nor QNR
    return pow(x, 15, 31) == 1


def build_base_magma():
    """Build the base E677 magma on F_31: x ◇ y = (1+β)x - βy mod 31.
    β = 2 (primitive 5th root of unity).
    """
    beta = 2
    n = 31
    mul = [[(((1 + beta) * x - beta * y) % n) for y in range(n)] for x in range(n)]
    return mul, n


# ── F_16 = F_2[t]/(t^4 + t + 1) arithmetic ─────────────────────────

class GF16:
    """Elements of GF(16) = F_2[t]/(t^4 + t + 1).
    Represented as integers 0-15, where bit i = coefficient of t^i.
    """
    # Irreducible polynomial: t^4 + t + 1 (binary: 10011 = 19)
    MODPOLY = 0b10011  # x^4 + x + 1

    @staticmethod
    def add(a, b):
        return a ^ b

    @staticmethod
    def mul(a, b):
        result = 0
        while b:
            if b & 1:
                result ^= a
            a <<= 1
            if a & 0b10000:
                a ^= GF16.MODPOLY
            b >>= 1
        return result

    @staticmethod
    def neg(a):
        return a  # In characteristic 2, -a = a

    @staticmethod
    def sub(a, b):
        return a ^ b  # In characteristic 2, a - b = a + b

    @staticmethod
    def inv(a):
        """Multiplicative inverse via a^(2^4 - 2) = a^14."""
        if a == 0:
            raise ZeroDivisionError
        # a^14 = a^8 * a^4 * a^2
        a2 = GF16.mul(a, a)
        a4 = GF16.mul(a2, a2)
        a8 = GF16.mul(a4, a4)
        return GF16.mul(GF16.mul(a8, a4), a2)

    @staticmethod
    def pow(a, k):
        result = 1
        base = a
        while k > 0:
            if k & 1:
                result = GF16.mul(result, base)
            base = GF16.mul(base, base)
            k >>= 1
        return result

    @staticmethod
    def find_primitive_root():
        """Find a generator of the multiplicative group (order 15)."""
        for g in range(2, 16):
            order = 1
            x = g
            while x != 1:
                x = GF16.mul(x, g)
                order += 1
                if order > 15:
                    break
            if order == 15:
                return g
        return None

    @staticmethod
    def find_root_of_unity(k):
        """Find a primitive k-th root of unity in GF(16)*.
        The multiplicative group has order 15 = 3 * 5.
        So we have primitive 3rd and 5th roots of unity.
        """
        g = GF16.find_primitive_root()
        if 15 % k != 0:
            return None
        root = GF16.pow(g, 15 // k)
        # Verify it's primitive
        x = root
        for i in range(1, k):
            if x == 1 and i < k:
                return None  # not primitive
            x = GF16.mul(x, root)
        if x != 1:
            return None
        return root


def build_fiber_operations():
    """Build the three fiber operations on GF(16):
    ◇^0: s ◇ t = s + ζ(s - t) = (1+ζ)s + ζt  [char 2: -ζt = ζt]
    ◇^+: s ◇ t = t
    ◇^-: s ◇ t = s + ω(s - t) = (1+ω)s + ωt  [char 2]

    Wait, in char 2: s - ζ(t - s) = s + ζ(t + s) = s + ζt + ζs = (1+ζ)s + ζt
    And s - ω(t - s) = (1+ω)s + ωt
    """
    omega = GF16.find_root_of_unity(3)
    zeta = GF16.find_root_of_unity(5)

    if omega is None or zeta is None:
        print(f"ERROR: Could not find roots of unity! ω={omega}, ζ={zeta}")
        return None, None, None, None, None

    print(f"  GF(16) primitive roots: ω (cube) = {omega}, ζ (5th) = {zeta}")

    # Verify
    assert GF16.pow(omega, 3) == 1 and omega != 1, "ω not primitive cube root"
    assert GF16.pow(zeta, 5) == 1 and zeta != 1, "ζ not primitive 5th root"

    one_plus_zeta = GF16.add(1, zeta)
    one_plus_omega = GF16.add(1, omega)

    # ◇^0(s, t) = (1+ζ)s + ζt
    def op0(s, t):
        return GF16.add(GF16.mul(one_plus_zeta, s), GF16.mul(zeta, t))

    # ◇^+(s, t) = t
    def op_plus(s, t):
        return t

    # ◇^-(s, t) = (1+ω)s + ωt
    def op_minus(s, t):
        return GF16.add(GF16.mul(one_plus_omega, s), GF16.mul(omega, t))

    return op0, op_plus, op_minus, omega, zeta


def verify_fiber_identities(op0, op_plus, op_minus):
    """Verify the three identities from the blueprint:
    s = t ◇^0 (s ◇^0 ((t ◇^0 s) ◇^0 t))
    s = t ◇^+ (s ◇^+ ((t ◇^- s) ◇^- t))
    s = t ◇^- (s ◇^- ((t ◇^+ s) ◇^+ t))
    """
    print("\n  Verifying fiber identities...")
    ok = True

    for s in range(16):
        for t in range(16):
            # Identity 1: s = op0(t, op0(s, op0(op0(t,s), t)))
            val = op0(t, op0(s, op0(op0(t, s), t)))
            if val != s:
                print(f"    Identity 1 FAILS at s={s}, t={t}: got {val}")
                ok = False

            # Identity 2: s = op_plus(t, op_plus(s, op_minus(op_minus(t,s), t)))
            val = op_plus(t, op_plus(s, op_minus(op_minus(t, s), t)))
            if val != s:
                print(f"    Identity 2 FAILS at s={s}, t={t}: got {val}")
                ok = False

            # Identity 3: s = op_minus(t, op_minus(s, op_plus(op_plus(t,s), t)))
            val = op_minus(t, op_minus(s, op_plus(op_plus(t, s), t)))
            if val != s:
                print(f"    Identity 3 FAILS at s={s}, t={t}: got {val}")
                ok = False

    if ok:
        print("    All fiber identities verified ✓")
    return ok


def build_product_magma():
    """Build the product magma G × M = F_31 × F_16 (size 496).

    (x, s) ◇ (y, t) = (x ◇_G y, s ◇_{x,y} t)

    where ◇_{x,y} is:
    - ◇^0 if y = x (i.e., y - x = 0)
    - ◇^+ if y - x is a nonzero QR in F_31
    - ◇^- if y - x is a QNR in F_31
    """
    base_mul, base_n = build_base_magma()
    result = build_fiber_operations()
    if result[0] is None:
        return None, 0

    op0, op_plus, op_minus, omega, zeta = result

    # Verify base satisfies E677
    from e677_search_v2 import check_e677, check_e255_all
    assert check_e677(base_mul, base_n), "Base magma does not satisfy E677!"
    base_e255_ok, _ = check_e255_all(base_mul, base_n)
    print(f"\n  Base magma (F_31): E677 ✓, E255 {'✓' if base_e255_ok else '✗'}")

    # Verify fiber identities
    verify_fiber_identities(op0, op_plus, op_minus)

    # Build product
    N = base_n * 16  # 496
    print(f"\n  Building product magma of size {N}...")

    def encode(x, s):
        return x * 16 + s

    def decode(idx):
        return idx // 16, idx % 16

    # Determine which fiber operation to use
    def get_fiber_op(x, y):
        diff = (y - x) % 31
        if diff == 0:
            return op0
        elif f31_qr(diff):
            return op_plus
        else:
            return op_minus

    # Build the full multiplication table
    mul = [[0] * N for _ in range(N)]
    for i in range(N):
        x, s = decode(i)
        for j in range(N):
            y, t = decode(j)
            # Base: x ◇ y
            base_result = base_mul[x][y]
            # Fiber: s ◇_{x,y} t
            fiber_op = get_fiber_op(x, y)
            fiber_result = fiber_op(s, t)
            mul[i][j] = encode(base_result, fiber_result)

    return mul, N


def main():
    print("=" * 60)
    print("Blueprint Non-Right-Cancellative E677 Magma Construction")
    print("=" * 60)

    mul, n = build_product_magma()
    if mul is None:
        print("Construction failed!")
        return 1

    print(f"\n  Verifying E677 on product magma (size {n})...")
    from e677_search_v2 import check_e677, check_e255_all

    if check_e677(mul, n):
        print(f"  E677: VERIFIED ✓")
    else:
        print(f"  E677: FAILED ✗")
        return 1

    ok, witness = check_e255_all(mul, n)
    if ok:
        print(f"  E255: ALL PASS ✓ — this magma satisfies E255")
        print(f"  (Non-right-cancellative but still satisfies E255)")
    else:
        x, s = witness // 16, witness % 16
        xxxx_idx = mul[mul[mul[witness][witness]][witness]][witness]
        x2, s2 = xxxx_idx // 16, xxxx_idx % 16
        print(f"  E255: FAILS at element ({x},{s}) ✗")
        print(f"  ((({x},{s})◇({x},{s}))◇({x},{s}))◇({x},{s}) = ({x2},{s2}) ≠ ({x},{s})")
        print(f"\n  *** THIS IS A FINITE COUNTEREXAMPLE TO E677 ⊨_fin E255 ***")

    # Check right-cancellativity
    print(f"\n  Checking right-cancellativity...")
    non_rc_count = 0
    for x_idx in range(n):
        col = [mul[y][x_idx] for y in range(n)]
        if len(set(col)) < n:
            non_rc_count += 1
    print(f"  Non-right-cancellative columns: {non_rc_count} out of {n}")

    return 0


if __name__ == '__main__':
    sys.exit(main())
