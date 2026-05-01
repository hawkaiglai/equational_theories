#!/usr/bin/env python3
"""
Verify the key mathematical reduction:
  E255 for all ⟺ θ(z) = (z◇z)◇z is injective
  θ injective ⟺ for each a, z◇(z◇a)=z has at most one solution in z

Also explore whether we can prove the uniqueness algebraically.
"""

import sys
sys.path.insert(0, '.')
from e677_enumerate import enumerate_e677, check_e677


def theta(mul, z):
    """θ(z) = (z◇z)◇z"""
    return mul[mul[z][z]][z]


def check_theta_injective(mul, n):
    """Check if θ is injective."""
    image = {}
    for z in range(n):
        t = theta(mul, z)
        if t in image:
            return False, z, image[t]
        image[t] = z
    return True, None, None


def check_Lz_squared_uniqueness(mul, n):
    """For each a, check that z◇(z◇a) = z has at most one solution."""
    for a in range(n):
        solutions = []
        for z in range(n):
            if mul[z][mul[z][a]] == z:
                solutions.append(z)
        if len(solutions) > 1:
            return False, a, solutions
    return True, None, None


def analyze_theta_structure(mul, n):
    """Deep analysis of θ and related maps."""
    print(f"  θ map: {[theta(mul, z) for z in range(n)]}")

    # Check injectivity
    inj, z1, z2 = check_theta_injective(mul, n)
    print(f"  θ injective: {inj}")
    if not inj:
        print(f"    COLLISION: θ({z1}) = θ({z2})")
        return False

    # Check L_z² uniqueness
    uniq, a, sols = check_Lz_squared_uniqueness(mul, n)
    print(f"  L_z²(a)=z unique: {uniq}")
    if not uniq:
        print(f"    COLLISION: z◇(z◇{a})=z has solutions {sols}")
        return False

    # Analyze the L_y fixed-point structure
    print(f"  L_y fixed points:")
    for y in range(n):
        fps = [z for z in range(n) if mul[y][z] == z]
        print(f"    Fix(L_{y}) = {fps}", end="")
        # Verify: each z in fps should have θ(z) = y
        for z in fps:
            t = theta(mul, z)
            if t != y:
                print(f"  *** ERROR: θ({z}) = {t} ≠ {y} ***")
        print()

    # The candidate-identity map: for each x, compute (x◇x)◇x and check if it left-fixes x
    print(f"  E255 verification via θ:")
    for x in range(n):
        t = theta(mul, x)
        left_fixes = mul[t][x] == x
        print(f"    x={x}: θ(x)={t}, θ(x)◇x = {mul[t][x]}, "
              f"left-fixes: {'✓' if left_fixes else '✗'}")

    return True


def explore_algebraic_constraints(mul, n):
    """Explore what E677 tells us about the relationship between
    different solutions of L_z²(a) = z (if they existed)."""

    # For each pair (z1, z2) with z1 ≠ z2, check if they could both
    # satisfy L_z²(a) = z for the same a.
    # I.e., check if z1◇(z1◇y) = z1 AND z2◇(z2◇y) = z2 for some y.
    for z1 in range(n):
        for z2 in range(z1 + 1, n):
            for a in range(n):
                if mul[z1][mul[z1][a]] == z1 and mul[z2][mul[z2][a]] == z2:
                    print(f"    *** z1={z1}, z2={z2} both satisfy L_z²({a}) = z ***")
                    # Check what E677 at (z1, z2) gives us
                    t = mul[z2][z1]  # z2◇z1
                    rhs = mul[z2][mul[z1][mul[t][z2]]]
                    print(f"      E677({z1},{z2}): {rhs} should = {z1}: {'✓' if rhs == z1 else '✗'}")


def main():
    # Enumerate small E677 magmas and check
    for n in [5, 7]:
        print(f"\n{'='*60}")
        print(f"Analyzing E677 magmas of size {n}")
        print(f"{'='*60}")

        magmas = enumerate_e677(n, max_count=20, timeout_ms=120000)

        for i, mul in enumerate(magmas[:5]):
            print(f"\n--- Magma #{i+1} ---")
            analyze_theta_structure(mul, n)
            explore_algebraic_constraints(mul, n)


if __name__ == '__main__':
    main()
