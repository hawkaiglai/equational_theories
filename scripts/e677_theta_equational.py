#!/usr/bin/env python3
"""
Test whether θ-injectivity is an EQUATIONAL consequence of E677.

Key insight: In the infinite greedy E677 construction, E255 fails.
That means θ is not surjective. But is θ INJECTIVE in that construction?

If θ is injective even in infinite E677 magmas, then:
  - θ-injectivity is equational (follows from E677 alone)
  - In finite sets: injective → surjective
  - θ surjective ↔ E255 for all
  - QED

This script tests the idea by examining what E677 forces algebraically
when we assume θ(z₁) = θ(z₂).

From E677 at (x, y): x = y ◇ (x ◇ ((y◇x)◇y))
Define: L_y⁻¹(x) = x ◇ ((y◇x)◇y)  [the explicit inverse]

Claim: θ(z₁) = θ(z₂) → z₁ = z₂, purely from E677.

PROOF ATTEMPT:
Suppose (z₁◇z₁)◇z₁ = (z₂◇z₂)◇z₂ = a.

Then z₁ = L_{z₁}²(a) and z₂ = L_{z₂}²(a).

Step 1: z₁ ◇ a = L_{z₁}(a) =: u₁
        z₂ ◇ a = L_{z₂}(a) =: u₂

Step 2: z₁ ◇ u₁ = L_{z₁}²(a) = z₁
        z₂ ◇ u₂ = L_{z₂}²(a) = z₂

So u₁ = L_{z₁}⁻¹(z₁) and u₂ = L_{z₂}⁻¹(z₂).

Step 3: Apply E677 at (u₁, z₂):
        u₁ = z₂ ◇ (u₁ ◇ ((z₂◇u₁)◇z₂))

Step 4: Apply E677 at (a, z₁):
        a = z₁ ◇ (a ◇ ((z₁◇a)◇z₁))
        = z₁ ◇ (a ◇ (u₁◇z₁))
        = L_{z₁}(a ◇ R_{z₁}(u₁))

Step 5: L_{z₁}⁻¹(a) = a ◇ R_{z₁}(u₁)

But L_{z₁}⁻¹(a) = a ◇ ((z₁◇a)◇z₁) = a ◇ (u₁◇z₁) = a ◇ R_{z₁}(u₁). ✓ consistent.

Step 6: Apply identity iii at (a, z₁):
        a = (z₁◇a) ◇ ((z₁◇(z₁◇a))◇z₁)
        = u₁ ◇ ((z₁◇u₁)◇z₁)
        = u₁ ◇ (z₁◇z₁)         [since z₁◇u₁ = z₁]
        = u₁ ◇ S(z₁)
        = L_{u₁}(S(z₁))

So a = L_{u₁}(S(z₁)) = u₁ ◇ (z₁◇z₁).

Similarly: a = u₂ ◇ (z₂◇z₂) = L_{u₂}(S(z₂)).

Step 7: From θ(z) = L_{S(z)}(z) = S(z) ◇ z:
        a = S(z₁) ◇ z₁ = S(z₂) ◇ z₂

And from Step 6: a = u₁ ◇ S(z₁) = u₂ ◇ S(z₂)

So: S(z₁) ◇ z₁ = u₁ ◇ S(z₁)  ... (★)
And: S(z₂) ◇ z₂ = u₂ ◇ S(z₂)  ... (★★)

(★) says: L_{S(z₁)}(z₁) = L_{u₁}(S(z₁))

Step 8: Let's define for any element w:
        w̃ = L_w⁻¹(w) = L_w^{p-1}(w) where p is L_w-orbit period

We have u₁ = L_{z₁}⁻¹(z₁) = z̃₁.

And from (★): L_{S(z₁)}(z₁) = L_{z̃₁}(S(z₁))

This says: the left-multiply of z₁ by S(z₁) equals the left-multiply of
S(z₁) by z̃₁. In other words, swapping the "base" and "argument" while
going through the inverse gives the same result.

Step 9: Now use E677 at (z₂, z₁):
        z₂ = z₁ ◇ (z₂ ◇ ((z₁◇z₂)◇z₁))
        = L_{z₁}(z₂ ◇ R_{z₁}(L_{z₁}(z₂)))
        = L_{z₁}(L_{z₁}⁻¹(z₂))
        = z₂ ✓ (tautological)

Step 10: Apply E677 at (z₂, u₁):
         z₂ = u₁ ◇ (z₂ ◇ ((u₁◇z₂)◇u₁))
         = L_{u₁}(L_{u₁}⁻¹(z₂))
         = z₂ ✓ (also tautological)

Hmm. Pure E677 applications are always tautological.
The only non-trivial constraints come from COMBINING multiple facts.

Step 11: From Step 6: a = u₁ ◇ S(z₁) and a = u₂ ◇ S(z₂)
So: u₁ ◇ S(z₁) = u₂ ◇ S(z₂)

Also: a = S(z₁) ◇ z₁ = S(z₂) ◇ z₂
So: L_{S(z₁)}(z₁) = L_{S(z₂)}(z₂)

If S(z₁) = S(z₂), then L_{S(z₁)} is the same map, and by injectivity z₁ = z₂. ✓

So the hard case is S(z₁) ≠ S(z₂).

Step 12: Suppose S(z₁) ≠ S(z₂), but θ(z₁) = θ(z₂) = a.
Then L_{S(z₁)}(z₁) = L_{S(z₂)}(z₂) = a.

This means: z₁ is a preimage of a under L_{S(z₁)}, and
            z₂ is a preimage of a under L_{S(z₂)}.

Since S(z₁) ≠ S(z₂), these are different maps, so the preimages
z₁ = L_{S(z₁)}⁻¹(a) and z₂ = L_{S(z₂)}⁻¹(a) are determined by
different operators applied to the same a.

KEY QUESTION: Can L_{S(z₁)}⁻¹(a) ≠ L_{S(z₂)}⁻¹(a) while maintaining
all E677 constraints?

Since L_y⁻¹(a) = a ◇ R_y(L_y(a)):
z₁ = a ◇ R_{S(z₁)}(L_{S(z₁)}(a)) = a ◇ ((S(z₁)◇a)◇S(z₁))
z₂ = a ◇ R_{S(z₂)}(L_{S(z₂)}(a)) = a ◇ ((S(z₂)◇a)◇S(z₂))

For z₁ ≠ z₂, we need: (S(z₁)◇a)◇S(z₁) ≠ (S(z₂)◇a)◇S(z₂)

Define h(s) = (s◇a)◇s = R_s(L_s(a)) for s = S(zᵢ).

Then zᵢ = a ◇ h(S(zᵢ)), i.e., zᵢ = R_{h(S(zᵢ))}(a).

So z₁ ≠ z₂ iff h(S(z₁)) ≠ h(S(z₂)).

Step 13: Recall θ(z) = S(z) ◇ z. So a = S(zᵢ) ◇ zᵢ.
And zᵢ = L_{S(zᵢ)}⁻¹(a) = a ◇ h(S(zᵢ)).

So: a = S(zᵢ) ◇ (a ◇ h(S(zᵢ)))
This is: L_{S(zᵢ)}(a ◇ h(S(zᵢ))) = a
i.e.: L_{S(zᵢ)}(L_{S(zᵢ)}⁻¹(a)) = a ✓ (tautological)

Step 14: We also have S(zᵢ) = zᵢ ◇ zᵢ = (a ◇ h(S(zᵢ))) ◇ (a ◇ h(S(zᵢ)))

Let sᵢ = S(zᵢ) and hᵢ = h(sᵢ) = (sᵢ◇a)◇sᵢ.
Then zᵢ = a ◇ hᵢ.
And sᵢ = (a ◇ hᵢ) ◇ (a ◇ hᵢ) = S(a ◇ hᵢ).

So: sᵢ = S(R_{hᵢ}(a))

This is a SELF-CONSISTENCY EQUATION for sᵢ:
sᵢ = S(R_{h(sᵢ)}(a))

In other words, s is a fixed point of the map
    Φ_a(s) = S(R_{h(s)}(a)) = S(a ◇ ((s◇a)◇s))

If Φ_a has a UNIQUE fixed point, then s₁ = s₂, hence z₁ = z₂.
Even if Φ_a has multiple fixed points, we need s₁ ≠ s₂ to give z₁ ≠ z₂.

Let me test computationally: does Φ_a have unique fixed points?
"""

import sys


def check_e677(mul, n):
    for x in range(n):
        for y in range(n):
            if mul[y][mul[x][mul[mul[y][x]][y]]] != x:
                return False
    return True


def theta(mul, z):
    return mul[mul[z][z]][z]


def get_linear_magmas():
    """Get all linear E677 magmas for small primes."""
    magmas = []
    for p in [5, 7, 11, 13]:
        for a in range(p):
            for b in range(p):
                mul = [[(a*x + b*y) % p for y in range(p)] for x in range(p)]
                if check_e677(mul, p):
                    magmas.append((f"F_{p}(a={a},b={b})", mul, p))
    return magmas


def analyze_Phi_a(mul, n, label=""):
    """Analyze the self-consistency map Φ_a(s) = S(a ◇ h(s))
    where h(s) = (s◇a)◇s.
    """
    print(f"\n{'='*60}")
    print(f"Φ_a FIXED POINT ANALYSIS: {label} (size {n})")
    print(f"{'='*60}")

    all_unique = True
    for a in range(n):
        # h(s) = (s◇a)◇s = R_s(L_s(a))
        def h(s):
            return mul[mul[s][a]][s]

        # Φ_a(s) = S(a ◇ h(s)) = (a◇h(s)) ◇ (a◇h(s))
        def Phi(s):
            z = mul[a][h(s)]  # z = a ◇ h(s)
            return mul[z][z]   # S(z)

        Phi_map = [Phi(s) for s in range(n)]
        fixed_pts = [s for s in range(n) if Phi_map[s] == s]

        if len(fixed_pts) != 1:
            print(f"  a={a}: Φ_a map = {Phi_map}")
            print(f"    FIXED POINTS: {fixed_pts} — {'UNIQUE ✓' if len(fixed_pts) == 1 else 'MULTIPLE!'}")
            all_unique = False
        elif n <= 13:
            # Also check: does the fixed point s give θ(z) = a?
            s = fixed_pts[0]
            z = mul[a][h(s)]
            tz = theta(mul, z)
            print(f"  a={a}: unique fixed pt s={s}, z=a◇h(s)={z}, θ(z)={tz}, "
                  f"match={'✓' if tz == a else '✗'}")

    if all_unique:
        print(f"\n  ★ Φ_a has UNIQUE fixed point for ALL a. This forces θ-injectivity!")
    return all_unique


def analyze_h_map(mul, n, label=""):
    """Analyze h(s) = (s◇a)◇s = R_s(L_s(a)) more carefully."""
    print(f"\n{'='*60}")
    print(f"h(s) = R_s(L_s(a)) ANALYSIS: {label} (size {n})")
    print(f"{'='*60}")

    for a in range(min(n, 7)):
        h_map = [mul[mul[s][a]][s] for s in range(n)]
        h_image = set(h_map)
        h_injective = len(h_image) == n

        print(f"\n  a={a}: h map = {h_map[:15]}{'...' if n > 15 else ''}")
        print(f"    h image size: {len(h_image)}/{n}, "
              f"{'injective' if h_injective else 'NOT injective'}")

        # If h is injective for all a, that's interesting
        # h(s) = R_s(L_s(a)) — this is a "twisted" version of evaluation

        # Check: h(s₁) = h(s₂) with s₁ ≠ s₂?
        if not h_injective:
            collisions = {}
            for s in range(n):
                collisions.setdefault(h_map[s], []).append(s)
            for v, ss in collisions.items():
                if len(ss) > 1:
                    print(f"    h collision: h({ss}) all = {v}")


def linear_algebra_theta():
    """For linear magma x◇y = ax+by on F_p:
    S(z) = (a+b)z
    θ(z) = (a(a+b)+b)z = (a²+ab+b)z
    h(s) = (s◇a_val)◇s = R_s(L_s(a_val))
         = (a·s + b·a_val)◇s ... wait, a_val is the element a, not param a.

    Let me use different notation. Operation: x*y = αx + βy (mod p).
    S(z) = (α+β)z
    θ(z) = α(α+β)z + βz = (α²+αβ+β)z

    For θ to be injective: α²+αβ+β ≢ 0 mod p.

    E677 constraint on α,β:
    x = y*(x*((y*x)*y))
    y*x = αy + βx
    (y*x)*y = α(αy+βx) + βy = (α²+β)y + αβx
    x*((y*x)*y) = αx + β((α²+β)y + αβx) = (α+αβ²)x + β(α²+β)y
    y*(x*((y*x)*y)) = αy + β((α+αβ²)x + β(α²+β)y)
                     = (α + β²(α²+β))y + β(α+αβ²)x
                     = (α + α²β² + β³)y + (αβ + αβ³)x

    For this to equal x for all x,y:
    Coefficient of y: α + α²β² + β³ = 0
    Coefficient of x: αβ + αβ³ = 1

    From coeff of x: αβ(1 + β²) = 1

    Now, is α²+αβ+β = 0 consistent with these constraints?

    If α²+αβ+β = 0, then α² = -αβ-β = -(αβ+β) = -β(α+1).
    So α² = -β(α+1).

    From coeff of x: αβ(1+β²) = 1.
    From coeff of y: α + α²β² + β³ = 0.

    Substitute α² = -β(α+1) into coeff of y:
    α + (-β(α+1))β² + β³ = 0
    α - β³(α+1) + β³ = 0
    α - αβ³ - β³ + β³ = 0
    α - αβ³ = 0
    α(1 - β³) = 0

    So either α = 0 or β³ = 1.

    Case 1: α = 0. Then coeff of x: 0·β(1+β²) = 0 ≠ 1. Contradiction!

    Case 2: β³ = 1. Then from coeff of x: αβ(1+β²) = 1.
    If β = 1: α·1·2 = 1, so α = 1/2. Then α² = 1/4.
    Check α²+αβ+β = 1/4 + 1/2 + 1 = 7/4 ≠ 0 (if char ≠ 2,7). Contradiction for most p.
    If char = 7: 7/4 ≡ 0 mod 7. So α²+αβ+β = 0 mod 7 when α=4, β=1.
    But α=1/2=4 mod 7, β=1: check E677. α=4,β=1: 4·1·(1+1)=8≡1 mod 7. ✓
    θ-coeff = 16+4+1 = 21 ≡ 0 mod 7. So θ IS non-injective!

    Wait, that would mean the F_7 magma with a=4, b=1 has θ non-injective?!
    Let me verify computationally.
    """
    print(f"\n{'='*60}")
    print(f"LINEAR ALGEBRA: Can α²+αβ+β = 0 with E677?")
    print(f"{'='*60}")

    for p in [5, 7, 11, 13, 17, 19, 23, 29, 31]:
        for alpha in range(p):
            for beta in range(p):
                # Check E677 constraints
                coeff_x = (alpha * beta * (1 + beta*beta)) % p
                coeff_y = (alpha + alpha*alpha*beta*beta + beta*beta*beta) % p
                if coeff_x != 1 or coeff_y != 0:
                    continue

                # E677 satisfied
                theta_coeff = (alpha*alpha + alpha*beta + beta) % p
                is_zero = theta_coeff == 0

                if is_zero:
                    print(f"\n  *** F_{p}: α={alpha}, β={beta}: "
                          f"θ-coeff = {theta_coeff} = 0! ***")
                    print(f"  θ is the ZERO MAP — non-injective!")
                    # Verify
                    mul = [[(alpha*x + beta*y) % p for y in range(p)]
                           for x in range(p)]
                    assert check_e677(mul, p), "E677 check failed!"
                    t_map = [theta(mul, z) for z in range(p)]
                    print(f"  θ map = {t_map}")
                    print(f"  This would be a counterexample to θ-injectivity!")
                    print(f"  Checking E255...")
                    e255_ok = all(mul[mul[mul[x][x]][x]][x] == x for x in range(p))
                    print(f"  E255: {'✓' if e255_ok else '✗'}")


def main():
    print("=" * 60)
    print("θ-INJECTIVITY EQUATIONAL ANALYSIS")
    print("=" * 60)

    # Phase 1: Check Φ_a uniqueness
    magmas = get_linear_magmas()
    for name, mul, n in magmas:
        analyze_Phi_a(mul, n, name)

    # Phase 2: Check h(s) injectivity
    for name, mul, n in magmas[:3]:
        analyze_h_map(mul, n, name)

    # Phase 3: Linear algebra — can θ-coeff vanish?
    linear_algebra_theta()


if __name__ == '__main__':
    sys.exit(main())
