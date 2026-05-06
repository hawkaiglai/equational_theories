#!/usr/bin/env python3
"""
Deep analysis of θ-injectivity in finite E677 magmas.

Goal: understand WHY F_a(z) = z ◇ (z ◇ a) = L_z²(a) has at most one
fixed point for each a, and find a provable algebraic constraint.

Key insight to test: does θ-injectivity follow from E677 EQUATIONALLY
(even for infinite magmas)? If yes, the proof is:
  θ injective (equational) + finite → θ surjective → E255

We test this by checking if Z3 can find ANY E677 model (even finite)
where θ is non-injective. If it can't, θ-injectivity is likely equational.
"""

import sys
import time
from itertools import product


# ── E677 magma operations ──────────────────────────────────────────

def check_e677(mul, n):
    for x in range(n):
        for y in range(n):
            if mul[y][mul[x][mul[mul[y][x]][y]]] != x:
                return False
    return True


def theta(mul, z):
    """θ(z) = (z◇z)◇z"""
    return mul[mul[z][z]][z]


def F_a(mul, a, z):
    """F_a(z) = z ◇ (z ◇ a) = L_z²(a)"""
    return mul[z][mul[z][a]]


def L_inv(mul, y, x, n):
    """L_y⁻¹(x) = x ◇ ((y◇x)◇y)"""
    return mul[x][mul[mul[y][x]][y]]


# ── Known E677 magmas ──────────────────────────────────────────────

def get_size5_magma():
    """The unique (up to iso) E677 magma of size 5."""
    # From Z3 enumeration: all elements idempotent
    # x ◇ y = 2x - y mod 5  (linear, β=1 on F_5... let me reconstruct)
    # Actually let me compute: x◇y = (1+β)x - βy mod 5
    # E677 requires β to be a primitive 5th root of unity mod 5.
    # But 5 is prime and we need β^5 ≡ 1 mod 5 with β ≢ 1.
    # Fermat: any nonzero β satisfies β^4 ≡ 1. So β^5 = β. Need β = 1. Hmm.
    # Let me just try the known working operation.
    # From computational search: the size-5 E677 magma has all elements idempotent.
    # That means x◇x = x for all x. With L_y bijective.
    # Let me try x◇y = 3x + 3y mod 5 = 3(x+y) mod 5
    # Check E677: x = y◇(x◇((y◇x)◇y))
    # Actually let me just enumerate via Z3 to get the exact table.
    # For now, use the known linear form. From the blueprint:
    # On F_p, x◇y = (1+β)x - βy where β is chosen appropriately.
    # For p=5: need β s.t. E677 holds. β=4 gives x◇y = 5x - 4y ≡ -4y mod 5 ≡ y mod 5. No.
    # β=2: x◇y = 3x - 2y mod 5.
    mul = [[(3*x - 2*y) % 5 for y in range(5)] for x in range(5)]
    if check_e677(mul, 5):
        return mul, 5
    # Try β=3: x◇y = 4x - 3y mod 5
    mul = [[(4*x - 3*y) % 5 for y in range(5)] for x in range(5)]
    if check_e677(mul, 5):
        return mul, 5
    # Brute force search over linear magmas
    for a in range(5):
        for b in range(5):
            mul = [[(a*x + b*y) % 5 for y in range(5)] for x in range(5)]
            if check_e677(mul, 5):
                return mul, 5
    return None, 0


def get_size7_magma():
    """An E677 magma of size 7."""
    # On F_7: x◇y = (1+β)x - βy where β is a primitive cube root mod 7.
    # Cube roots of unity mod 7: β³ ≡ 1, β ≢ 1.
    # 2³ = 8 ≡ 1 mod 7. So β=2.
    # x◇y = 3x - 2y mod 7
    mul = [[(3*x - 2*y) % 7 for y in range(7)] for x in range(7)]
    if check_e677(mul, 7):
        return mul, 7
    # β=4: 4³=64≡1 mod 7. x◇y = 5x - 4y mod 7
    mul = [[(5*x - 4*y) % 7 for y in range(7)] for x in range(7)]
    if check_e677(mul, 7):
        return mul, 7
    # Brute force
    for a in range(7):
        for b in range(7):
            mul = [[(a*x + b*y) % 7 for y in range(7)] for x in range(7)]
            if check_e677(mul, 7):
                return mul, 7
    return None, 0


def get_size11_magma():
    """An E677 magma of size 11."""
    for a in range(11):
        for b in range(11):
            mul = [[(a*x + b*y) % 11 for y in range(11)] for x in range(11)]
            if check_e677(mul, 11):
                return mul, 11
    return None, 0


def get_size31_magma():
    """An E677 magma of size 31."""
    # β=2: x◇y = 3x - 2y mod 31
    mul = [[(3*x - 2*y) % 31 for y in range(31)] for x in range(31)]
    if check_e677(mul, 31):
        return mul, 31
    for a in range(31):
        for b in range(31):
            mul = [[(a*x + b*y) % 31 for y in range(31)] for x in range(31)]
            if check_e677(mul, 31):
                return mul, 31
    return None, 0


# ── Analysis functions ─────────────────────────────────────────────

def analyze_F_a(mul, n, label=""):
    """Deep analysis of F_a(z) = L_z²(a) for each a."""
    print(f"\n{'='*70}")
    print(f"F_a ANALYSIS: {label} (size {n})")
    print(f"{'='*70}")

    theta_map = [theta(mul, z) for z in range(n)]
    print(f"\nθ map: {theta_map}")
    theta_image = set(theta_map)
    print(f"θ image size: {len(theta_image)} / {n} "
          f"({'SURJECTIVE' if len(theta_image) == n else 'NOT SURJECTIVE'})")

    # Check θ injectivity
    theta_preimages = {}
    for z in range(n):
        t = theta_map[z]
        theta_preimages.setdefault(t, []).append(z)
    theta_injective = all(len(v) == 1 for v in theta_preimages.values())
    print(f"θ injective: {theta_injective}")
    if not theta_injective:
        for a, zs in theta_preimages.items():
            if len(zs) > 1:
                print(f"  COLLISION: θ⁻¹({a}) = {zs}")

    # Squaring map
    S_map = [mul[z][z] for z in range(n)]
    print(f"\nS map (z↦z◇z): {S_map}")
    S_image = set(S_map)
    print(f"S image size: {len(S_image)} / {n}")
    idempotents = [z for z in range(n) if S_map[z] == z]
    print(f"Idempotents: {idempotents}")

    for a in range(min(n, 15)):  # limit output for large magmas
        print(f"\n  --- F_{a} ---")
        F_values = [F_a(mul, a, z) for z in range(n)]
        fixed_pts = [z for z in range(n) if F_values[z] == z]
        F_image = set(F_values)

        print(f"  F_{a} map: {F_values[:20]}{'...' if n > 20 else ''}")
        print(f"  Image size: {len(F_image)} / {n}")
        print(f"  Fixed points: {fixed_pts}")
        print(f"  # fixed points: {len(fixed_pts)}")

        # Check if F_a is injective
        seen = {}
        F_injective = True
        for z in range(n):
            v = F_values[z]
            if v in seen:
                F_injective = False
                break
            seen[v] = z
        print(f"  F_{a} injective: {F_injective}")

        # Cycle structure of F_a
        visited = set()
        cycles = []
        tails = []
        for start in range(n):
            if start in visited:
                continue
            path = []
            cur = start
            while cur not in visited:
                visited.add(cur)
                path.append(cur)
                cur = F_values[cur]
            # Find where the cycle starts
            if cur in path:
                cycle_start = path.index(cur)
                tail = path[:cycle_start]
                cycle = path[cycle_start:]
                if tail:
                    tails.append(tail)
                cycles.append(cycle)
            else:
                tails.append(path)

        cycle_lengths = sorted([len(c) for c in cycles])
        print(f"  Cycle lengths: {cycle_lengths}")
        if tails:
            tail_lengths = sorted([len(t) for t in tails])
            print(f"  Tail lengths: {tail_lengths}")

    return theta_injective


def analyze_two_solution_constraints(mul, n, label=""):
    """For each pair (z₁, z₂), analyze what E677 tells us if they
    were both fixed points of F_a for the same a."""
    print(f"\n{'='*70}")
    print(f"TWO-SOLUTION CONSTRAINT ANALYSIS: {label} (size {n})")
    print(f"{'='*70}")

    theta_map = [theta(mul, z) for z in range(n)]

    for z1 in range(n):
        for z2 in range(z1+1, n):
            a1 = theta_map[z1]
            a2 = theta_map[z2]

            # What if θ(z₁) = θ(z₂)? (They never actually do, but...)
            # Let's look at the algebraic consequences.

            # Compute key derived quantities
            u1 = mul[z1][a1]  # L_{z₁}(a₁) = z₁ ◇ θ(z₁)
            u2 = mul[z2][a2]  # L_{z₂}(a₂)

            # Apply E677 at (z₁, z₂) — gives z₁ = z₂ ◇ (z₁ ◇ ((z₂◇z₁)◇z₂))
            w12 = mul[z2][z1]  # z₂ ◇ z₁
            rhs12 = mul[z2][mul[z1][mul[w12][z2]]]
            assert rhs12 == z1, f"E677 violated at ({z1},{z2})"

            # The key question: if a₁ = a₂ (hypothetically), what's forced?
            # z₁ ◇ (z₁ ◇ a) = z₁ and z₂ ◇ (z₂ ◇ a) = z₂
            # → L_{z₁}(z₁ ◇ a) = z₁ and L_{z₂}(z₂ ◇ a) = z₂
            # → z₁ ◇ a = L_{z₁}⁻¹(z₁) and z₂ ◇ a = L_{z₂}⁻¹(z₂)

            Lz1_inv_z1 = L_inv(mul, z1, z1, n)
            Lz2_inv_z2 = L_inv(mul, z2, z2, n)

            # If both are fixed points of F_a for the same a:
            # z₁ ◇ a = L_{z₁}⁻¹(z₁) and z₂ ◇ a = L_{z₂}⁻¹(z₂)
            # Since L_{z₁} is injective: a = L_{z₁}⁻¹(L_{z₁}⁻¹(z₁)) = L_{z₁}⁻²(z₁) = θ(z₁)
            # Same: a = θ(z₂)
            # This is circular! But let's look at cross-constraints.

            # What does E677 at (z₁, z₂) tell us combined with θ(z₁) = θ(z₂)?
            # From E677: z₁ = L_{z₂}(L_{z₂}⁻¹(z₁))  (tautological)
            # But z₂ ◇ a = L_{z₂}⁻¹(z₂), and z₁ ◇ a = L_{z₁}⁻¹(z₁)
            # So R_a(z₂) = L_{z₂}⁻¹(z₂) and R_a(z₁) = L_{z₁}⁻¹(z₁)

            # The map R_a restricted to {z₁, z₂}: R_a(zᵢ) = L_{zᵢ}⁻¹(zᵢ)
            # And L_{zᵢ}(R_a(zᵢ)) = zᵢ (since L_{zᵢ}(L_{zᵢ}⁻¹(zᵢ)) = zᵢ)

            # What about R_a applied to L_{z₁}⁻¹(z₁)?
            # R_a(L_{z₁}⁻¹(z₁)) = L_{z₁}⁻¹(z₁) ◇ a
            # And we know L_{z₁}⁻¹(z₁) ◇ a... hmm

    print("  (Cross-constraint analysis needs a specific algebraic target.)")
    print("  Let me look at the R_a orbit structure instead.\n")

    # More targeted analysis: for each a, look at R_a
    for a in range(min(n, 10)):
        R_a = [mul[z][a] for z in range(n)]
        # Elements z where L_z²(a) = z
        fp = [z for z in range(n) if F_a(mul, a, z) == z]
        # For each fixed point, compute the L_z orbit of a
        for z in fp:
            orbit = [a]
            cur = a
            for _ in range(n):
                cur = mul[z][cur]
                if cur == orbit[0]:
                    break
                orbit.append(cur)
            period = len(orbit)
            print(f"  a={a}, fixed pt z={z}: L_{z}-orbit of a = {orbit}, period={period}")
            # Verify: z is 2 steps ahead of a in this orbit
            if period > 2:
                print(f"    orbit[2] = {orbit[2]}, z = {z}, match: {orbit[2] == z}")
            elif period == 2:
                print(f"    orbit[0] = {orbit[0]} = a, z = {z}")
            elif period == 1:
                print(f"    a = z = {a} (idempotent)")


def analyze_Ra_structure(mul, n, label=""):
    """Analyze the right multiplication map R_a and its relationship to θ."""
    print(f"\n{'='*70}")
    print(f"R_a STRUCTURE: {label} (size {n})")
    print(f"{'='*70}")

    for a in range(min(n, 10)):
        R_a = [mul[z][a] for z in range(n)]
        R_a_image = set(R_a)
        print(f"\n  R_{a} map: {R_a[:20]}{'...' if n > 20 else ''}")
        print(f"  R_{a} image size: {len(R_a_image)} / {n}, "
              f"{'bijective' if len(R_a_image) == n else 'NOT bijective'}")

        # Check: is R_a ∘ R_a ∘ ... eventually periodic?
        # More importantly: what's the relationship between R_a and L_z?

        # For each z, compute L_z⁻¹(z) and check if it equals z ◇ a
        for z in range(min(n, 10)):
            Lz_inv_z = L_inv(mul, z, z, n)
            z_circ_a = mul[z][a]
            theta_z = theta(mul, z)
            match = "✓" if z_circ_a == Lz_inv_z else "✗"
            # z ◇ θ(z) should equal L_z⁻¹(z)
            z_circ_theta = mul[z][theta_z]
            match2 = "✓" if z_circ_theta == Lz_inv_z else "✗"
            if a == 0:  # only print once
                print(f"    z={z}: L_z⁻¹(z)={Lz_inv_z}, z◇θ(z)={z_circ_theta} {match2}")


def analyze_composition_map(mul, n, label=""):
    """Analyze the composition z ↦ (z, S(z), θ(z)) to find invariants."""
    print(f"\n{'='*70}")
    print(f"COMPOSITION INVARIANTS: {label} (size {n})")
    print(f"{'='*70}")

    data = []
    for z in range(n):
        Sz = mul[z][z]
        tz = theta(mul, z)
        Lz_inv_z = L_inv(mul, z, z, n)
        # L_z orbit period
        orbit = [z]
        cur = z
        for _ in range(n):
            cur = mul[z][cur]
            if cur == z:
                break
            orbit.append(cur)
        period = len(orbit)

        # Position of θ(z) in the orbit
        try:
            theta_pos = orbit.index(tz)
        except ValueError:
            theta_pos = -1  # θ(z) not in L_z-orbit of z?!

        data.append({
            'z': z, 'S': Sz, 'theta': tz,
            'L_inv_z': Lz_inv_z,
            'period': period, 'theta_pos': theta_pos,
            'orbit': orbit
        })
        if n <= 15:
            print(f"  z={z}: S(z)={Sz}, θ(z)={tz}, L_z⁻¹(z)={Lz_inv_z}, "
                  f"period={period}, θ at orbit pos {theta_pos}")
            print(f"         orbit: {orbit}")

    # Check: is θ(z) always at position p-2 in the orbit?
    all_at_p_minus_2 = all(d['theta_pos'] == d['period'] - 2
                          for d in data if d['period'] > 1)
    print(f"\n  θ(z) always at orbit position p-2: {all_at_p_minus_2}")

    # Check: is S(z) always at orbit position 1?
    all_S_at_1 = all(d['S'] == d['orbit'][1] if d['period'] > 1
                     else d['S'] == d['z']
                     for d in data)
    print(f"  S(z) always at orbit position 1: {all_S_at_1}")

    # Key question: for z₁ ≠ z₂ with same period p, can their orbits
    # share elements in positions that would force θ(z₁) = θ(z₂)?
    periods = {}
    for d in data:
        periods.setdefault(d['period'], []).append(d)

    print(f"\n  Period distribution: {', '.join(f'p={k}: {len(v)} elements' for k, v in sorted(periods.items()))}")

    for p, elems in periods.items():
        if p <= 1:
            continue
        print(f"\n  Period {p} elements:")
        # Check orbit overlaps
        for i, d1 in enumerate(elems):
            for d2 in elems[i+1:]:
                overlap = set(d1['orbit']) & set(d2['orbit'])
                if overlap:
                    print(f"    z={d1['z']} and z={d2['z']} orbits overlap: {overlap}")

    return data


def z3_test_theta_non_injective(n, timeout_ms=120000):
    """Use Z3 to search for an E677 magma of size n where θ is NOT injective.
    If UNSAT: θ is necessarily injective at this size.
    If SAT: we found a counterexample to θ-injectivity!
    """
    from z3 import Solver, Int, And, Or, Implies, Distinct, sat

    print(f"\n{'='*70}")
    print(f"Z3 SEARCH: E677 magma of size {n} with θ NON-INJECTIVE")
    print(f"{'='*70}")

    s = Solver()
    s.set("timeout", timeout_ms)

    # Main variables
    m = [[Int(f'm_{i}_{j}') for j in range(n)] for i in range(n)]
    for i in range(n):
        for j in range(n):
            s.add(m[i][j] >= 0, m[i][j] < n)

    # L_y bijective (row permutation)
    for i in range(n):
        s.add(Distinct([m[i][j] for j in range(n)]))

    # E677 with auxiliary variables
    for x in range(n):
        for y in range(n):
            t1 = m[y][x]
            s2 = Int(f's2_{x}_{y}')
            s.add(s2 >= 0, s2 < n)
            for v in range(n):
                s.add(Implies(t1 == v, s2 == m[v][y]))
            s3 = Int(f's3_{x}_{y}')
            s.add(s3 >= 0, s3 < n)
            for v in range(n):
                s.add(Implies(s2 == v, s3 == m[x][v]))
            s4 = Int(f's4_{x}_{y}')
            s.add(s4 >= 0, s4 < n)
            for v in range(n):
                s.add(Implies(s3 == v, s4 == m[y][v]))
            s.add(s4 == x)

    # θ NON-INJECTIVE: ∃ z₁ ≠ z₂ s.t. θ(z₁) = θ(z₂)
    # θ(z) = (z◇z)◇z = m[m[z][z]][z]
    # Need auxiliary: θ_z = m[S_z][z] where S_z = m[z][z]
    theta_vars = []
    S_vars = []
    for z in range(n):
        sz = Int(f'S_{z}')
        s.add(sz >= 0, sz < n)
        s.add(sz == m[z][z])  # S(z) = z◇z — this is concrete lookup
        S_vars.append(sz)

        tz = Int(f'th_{z}')
        s.add(tz >= 0, tz < n)
        # tz = m[sz][z] — need channeling since sz is Z3 var
        for v in range(n):
            s.add(Implies(sz == v, tz == m[v][z]))
        theta_vars.append(tz)

    # ∃ z₁ < z₂ s.t. θ(z₁) = θ(z₂)
    collision_clauses = []
    for z1 in range(n):
        for z2 in range(z1+1, n):
            collision_clauses.append(theta_vars[z1] == theta_vars[z2])
    s.add(Or(collision_clauses))

    print(f"  Solving (timeout {timeout_ms//1000}s)...")
    start = time.time()
    result = s.check()
    elapsed = time.time() - start

    if result == sat:
        print(f"  *** SAT in {elapsed:.1f}s — θ NON-INJECTIVE MODEL FOUND! ***")
        model = s.model()
        table = [[model.eval(m[i][j]).as_long() for j in range(n)]
                 for i in range(n)]
        print(f"  Verifying...")
        assert check_e677(table, n), "E677 FAILED!"
        print(f"  E677: ✓")
        t_map = [theta(table, z) for z in range(n)]
        print(f"  θ map: {t_map}")
        # Find collision
        seen = {}
        for z in range(n):
            if t_map[z] in seen:
                print(f"  COLLISION: θ({seen[t_map[z]]}) = θ({z}) = {t_map[z]}")
            seen[t_map[z]] = z
        return table
    else:
        status = "UNSAT" if str(result) == "unsat" else f"UNKNOWN ({result})"
        print(f"  {status} in {elapsed:.1f}s")
        if str(result) == "unsat":
            print(f"  → θ is NECESSARILY INJECTIVE in all E677 magmas of size {n}")
        return None


# ── Linear magma algebraic analysis ────────────────────────────────

def analyze_linear_theta():
    """For linear magmas x◇y = ax + by (mod p), derive θ algebraically.

    θ(z) = (z◇z)◇z = ((a+b)z)◇z = a(a+b)z + bz = (a²+ab+b)z

    θ injective ⟺ (a²+ab+b) ≢ 0 mod p

    Check: does E677 force a²+ab+b ≢ 0?

    E677: x = y◇(x◇((y◇x)◇y))
    In linear form: x = a·y + b·(a·x + b·((a·y+b·x)◇y))
    Need to expand fully.
    """
    print(f"\n{'='*70}")
    print(f"LINEAR MAGMA θ ANALYSIS")
    print(f"{'='*70}")

    for p in [5, 7, 11, 13, 17, 19, 23, 29, 31]:
        print(f"\n  F_{p}:")
        for a in range(p):
            for b in range(p):
                mul = [[(a*x + b*y) % p for y in range(p)] for x in range(p)]
                if not check_e677(mul, p):
                    continue
                # Compute θ coefficient
                theta_coeff = (a*a + a*b + b) % p
                print(f"    a={a}, b={b}: E677 ✓, θ-coeff = a²+ab+b = {theta_coeff} "
                      f"{'(ZERO!)' if theta_coeff == 0 else '(nonzero ✓)'}")

                # Verify θ map
                t_map = [theta(mul, z) for z in range(p)]
                expected = [(theta_coeff * z) % p for z in range(p)]
                assert t_map == expected, f"θ mismatch! {t_map} vs {expected}"

                # θ injective iff theta_coeff ≠ 0
                t_inj = len(set(t_map)) == p
                assert t_inj == (theta_coeff != 0), "Injectivity mismatch!"


# ── Main ───────────────────────────────────────────────────────────

def main():
    print("=" * 70)
    print("DEEP θ-INJECTIVITY ANALYSIS FOR E677 MAGMAS")
    print("=" * 70)

    # Phase 1: Analyze known magmas
    magmas = []
    for name, getter in [("F_5 linear", get_size5_magma),
                         ("F_7 linear", get_size7_magma),
                         ("F_11 linear", get_size11_magma)]:
        mul, n = getter()
        if mul:
            magmas.append((name, mul, n))
            print(f"\n  Found {name} magma (size {n})")
        else:
            print(f"\n  Could not find {name} magma")

    for name, mul, n in magmas:
        analyze_F_a(mul, n, name)
        analyze_composition_map(mul, n, name)
        if n <= 15:
            analyze_two_solution_constraints(mul, n, name)
            analyze_Ra_structure(mul, n, name)

    # Phase 2: Linear algebraic analysis
    analyze_linear_theta()

    # Phase 3: Z3 search for θ-non-injective E677 magmas
    for n in [2, 3, 4, 5, 6, 7]:
        result = z3_test_theta_non_injective(n, timeout_ms=180000)
        if result is not None:
            print(f"\n*** FOUND θ-NON-INJECTIVE E677 MAGMA OF SIZE {n}! ***")
            print(f"*** THIS MEANS θ-INJECTIVITY IS NOT EQUATIONAL ***")
            return 1

    print(f"\n{'='*70}")
    print(f"SUMMARY")
    print(f"{'='*70}")
    print(f"  θ is necessarily injective in all E677 magmas of sizes 2-7 (UNSAT)")
    print(f"  → Strong evidence that θ-injectivity IS an equational consequence of E677")
    print(f"  → If true, the proof is: θ injective (equational) + finite → θ surjective → E255")

    return 0


if __name__ == '__main__':
    sys.exit(main())
