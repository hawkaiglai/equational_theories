#!/usr/bin/env python3
"""
Verify Adam McKenna's n=35 example:
- E677 ✓
- E255 ✓ (all elements)
- θ non-injective (θ(0) = θ(4) = 32, |image(θ)| = 5)
- No global left identity

Then analyse:
1. Orbit structure under L_z for each z
2. θ(z)◇z = z verification
3. Period distribution
4. T1 analogs: for each z with period p, check c_{p-3}◇c_{p-3}
5. ExactBaseGeneric pattern: does Adam's T1 identity generalise?
"""

import sys
from collections import Counter

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


def check_e677(mul, n):
    for x in range(n):
        for y in range(n):
            if mul[y][mul[x][mul[mul[y][x]][y]]] != x:
                return False, x, y
    return True, None, None


def check_e255_all(mul, n):
    fails = []
    for x in range(n):
        if mul[mul[mul[x][x]][x]][x] != x:
            fails.append(x)
    return fails


def theta(mul, z):
    return mul[mul[z][z]][z]


def L_inv(mul, y, x):
    return mul[x][mul[mul[y][x]][y]]


def orbit_of(mul, z, n):
    """L_z-orbit starting from z."""
    orbit = [z]
    cur = z
    for _ in range(n):
        cur = mul[z][cur]
        if cur == orbit[0]:
            break
        orbit.append(cur)
    return orbit


def main():
    n = len(table)
    mul = table
    print(f"n = {n}")

    # E677
    ok, bx, by = check_e677(mul, n)
    print(f"E677: {'✓' if ok else f'✗ at x={bx},y={by}'}")

    # E255
    fails = check_e255_all(mul, n)
    print(f"E255: {'✓ all ' + str(n) + ' elements' if not fails else f'✗ at {fails}'}")

    # θ
    t_map = [theta(mul, z) for z in range(n)]
    t_image = set(t_map)
    print(f"θ map: {t_map}")
    print(f"|image(θ)| = {len(t_image)} / {n}")
    print(f"θ injective: {len(t_image) == n}")

    # Collisions
    preimages = {}
    for z in range(n):
        preimages.setdefault(t_map[z], []).append(z)
    print(f"θ collisions:")
    for a, zs in sorted(preimages.items()):
        if len(zs) > 1:
            print(f"  θ⁻¹({a}) = {zs}  (|preimage| = {len(zs)})")

    # Global left identity?
    global_lid = [y for y in range(n) if all(mul[y][x] == x for x in range(n))]
    print(f"Global left identity: {global_lid}")

    # θ(z)◇z = z for all z?
    e255_via_theta = all(mul[t_map[z]][z] == z for z in range(n))
    print(f"θ(z)◇z = z for all z: {e255_via_theta}")

    # Period distribution
    periods = {}
    orbits_by_z = {}
    for z in range(n):
        orb = orbit_of(mul, z, n)
        p = len(orb)
        orbits_by_z[z] = orb
        periods.setdefault(p, []).append(z)

    print(f"\nOrbit period distribution:")
    for p in sorted(periods):
        print(f"  period {p}: {len(periods[p])} elements — {periods[p]}")

    # For each z, show orbit and θ position
    print(f"\nOrbit analysis (first 15 elements):")
    for z in range(15):
        orb = orbits_by_z[z]
        p = len(orb)
        tz = t_map[z]
        try:
            theta_pos = orb.index(tz)
        except ValueError:
            theta_pos = -1
        # Check θ at position p-2
        if p >= 2:
            expected_theta = orb[p - 2]
            match = "✓" if expected_theta == tz else "✗"
        else:
            expected_theta = z
            match = "✓" if tz == z else "✗"
        print(f"  z={z:2d}: period={p}, orbit={orb}, "
              f"θ(z)={tz} at pos={theta_pos} (expect p-2={p-2}): {match}")

    # T1 analysis: for each z with period p, check orbit[p-3]◇orbit[p-3]
    print(f"\nT1 analog analysis (c_{{p-3}}◇c_{{p-3}} = ?):")
    for z in range(n):
        orb = orbits_by_z[z]
        p = len(orb)
        if p < 4:
            continue
        c_pm3 = orb[p - 3]   # element at position p-3 in orbit
        c_pm3_sq = mul[c_pm3][c_pm3]
        # What orbit position is c_pm3_sq?
        try:
            sq_pos = orb.index(c_pm3_sq)
        except ValueError:
            sq_pos = -1
        # T1 hypothesis from Adam: c3◇c3 = c1, i.e., orb[3]◇orb[3] = orb[1]
        # Generalized: orb[p-3]◇orb[p-3] = orb[?]
        print(f"  z={z:2d}: p={p}, orb[p-3]={c_pm3}, "
              f"orb[p-3]²={c_pm3_sq}, orbit pos of square: {sq_pos}")

    # What does S(z) = z◇z look like for orbit elements?
    print(f"\nS(z) = z◇z analysis:")
    for z in range(min(n, 15)):
        sz = mul[z][z]
        orb = orbits_by_z[z]
        p = len(orb)
        try:
            s_pos = orb.index(sz)
        except ValueError:
            s_pos = -1
        print(f"  z={z:2d}: S(z)=z◇z={sz}, orbit pos of S(z): {s_pos} "
              f"(expect 1? {'✓' if s_pos == 1 else '✗'})")

    # Key: why does E255 hold despite θ non-injective?
    # For each collision pair (z1,z2) with θ(z1)=θ(z2)=a:
    # both satisfy θ(zᵢ)◇zᵢ = a◇zᵢ = zᵢ
    # meaning a = θ(z1) = θ(z2) is the left-fixer of BOTH z1 and z2.
    print(f"\nCollision pair analysis (why E255 still holds):")
    for a, zs in sorted(preimages.items()):
        if len(zs) <= 1:
            continue
        print(f"\n  θ⁻¹({a}) = {zs}")
        # For each z in zs, a◇z should = z
        for z in zs:
            fix_check = mul[a][z]
            print(f"    {a}◇{z} = {fix_check} (should be {z}): "
                  f"{'✓' if fix_check == z else '✗'}")
        # So element a left-fixes MULTIPLE elements
        # This means |Fix(L_a)| > 1
        Fix_La = [z for z in range(n) if mul[a][z] == z]
        print(f"    Fix(L_{a}) = {Fix_La}  (|Fix| = {len(Fix_La)})")
        # By uniqueness: if a◇z = z, then a = θ(z) = L_z^{-2}(z)
        # So z1 and z2 both have the same left-fixer a = θ(z1) = θ(z2)
        # This is consistent! θ doesn't need to be injective for E255 to hold.
        # The CORRECT condition is: ∀z, θ(z)◇z = z
        # Not: ∀z, θ(z) = unique...

    # Now: what is the TRUE algebraic reason θ(z)◇z = z holds?
    # Let's look at identity: for each collision pair z1,z2 with a=θ(z1)=θ(z2):
    # z1 = L_{z1}²(a) and z2 = L_{z2}²(a)
    # So both z1 and z2 are 2 steps ahead of a in their respective L-orbits
    print(f"\nOrbit structure for collision pairs:")
    for a, zs in sorted(preimages.items()):
        if len(zs) <= 1:
            continue
        print(f"\n  Collisions: θ(·) = {a}")
        for z in zs:
            orb_z = orbits_by_z[z]
            p = len(orb_z)
            try:
                a_pos = orb_z.index(a)
            except ValueError:
                a_pos = -1
            print(f"    z={z:2d}: orbit = {orb_z}, period = {p}, "
                  f"a={a} at orbit pos {a_pos}")
            # z should be 2 steps ahead of a, so a is at pos p-2
            print(f"    Expected: a at pos p-2 = {p-2}. Got: {a_pos}. "
                  f"{'✓' if a_pos == p - 2 else '✗'}")

    # The generalized T1 question:
    # For each orbit period p, find the universal identity that forces
    # orbit[p-2]◇z = z (E255).
    # Adam's d=6: orbit has period 6, T1 = c3◇c3 = c1 = orbit[3]◇orbit[3] = orbit[1]
    # For other periods, find the analogous T1.
    print(f"\nGeneralized T1 search:")
    all_periods = sorted(set(len(orbits_by_z[z]) for z in range(n)))
    print(f"All orbit periods in n=35: {all_periods}")

    for p in all_periods:
        elems = [z for z in range(n) if len(orbits_by_z[z]) == p]
        if not elems or p < 3:
            continue
        print(f"\n  Period {p} (elements: {elems[:8]}...):")
        # For each element z with this period, what identities hold on its orbit?
        z0 = elems[0]
        orb = orbits_by_z[z0]
        # Check all pairs ci◇cj for orbit elements
        print(f"  Orbit of z={z0}: {orb}")
        print(f"  Products within orbit (ci◇cj → position in orbit):")
        for i in range(p):
            for j in range(p):
                prod = mul[orb[i]][orb[j]]
                try:
                    prod_pos = orb.index(prod)
                    print(f"    orb[{i}]◇orb[{j}] = orb[{prod_pos}]", end="")
                    if i == p-3 and j == p-3:
                        print(f"  ← T1 analog (c_{{p-3}}²)", end="")
                    print()
                except ValueError:
                    print(f"    orb[{i}]◇orb[{j}] = {prod} (OUTSIDE orbit!)")


if __name__ == '__main__':
    main()
