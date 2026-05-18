#!/usr/bin/env python3
"""
E677 S-map Global Analysis (Phase 4)
======================================
Goal: What global identities does S(x) = x◇x satisfy in finite E677 magmas?
Key question: what constrains L_z ∘ S to always have a fixed point?

Identities to test:
- S ∘ L_a = ? ∘ S (commutation with left-mult)
- The fixed-point map θ(z) = unique x with L_z(S(x))=x
- θ as a composition of known operators
- S expressed in terms of L-operators on the orbit

From E677(x,x): L_x^{-1}(x) = x ◇ R_x(S(x)) = x ◇ (S(x)◇x)
So c_{p-1} = x ◇ (S(x)◇x), i.e., L_x(c_{p-1}) = ... wait, that's
just L_x^{-1}(x) = c_{p-1} which is the orbit definition.

Key known facts:
- E255 ⟺ L_z∘S has a fixed point for every z
- The fixed point is unique (proven: left-fixers are unique)
- The FP is at position c_{p-3} in the orbit of z (finding #17)
- θ(z) = c_{p-3} of z's orbit (verified in all models)
"""

from itertools import permutations
from collections import defaultdict


# ═══════════════════════════════════════════════════════════════════
# MODEL DEFINITIONS
# ═══════════════════════════════════════════════════════════════════

def make_jihoon(n=31):
    return [[(5*x + 27*y + 1) % n for y in range(n)] for x in range(n)], n

def make_size7():
    n = 7
    return [[(4*i + j + 1) % n for j in range(n)] for i in range(n)], n

def make_size5():
    """Size-5 idempotent model: f(x,y) = (2x + 4y) mod 5."""
    n = 5
    return [[(2*x + 4*y) % n for y in range(n)] for x in range(n)], n


# ═══════════════════════════════════════════════════════════════════
# UTILITIES
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
    orbit = [x]
    cur = mul[x][x]
    while cur != x:
        orbit.append(cur)
        cur = mul[x][cur]
    return orbit

def perm_inverse(p, n):
    inv = [0]*n
    for i in range(n):
        inv[p[i]] = i
    return inv

def compose_perm(p, q, n):
    """(p∘q)(x) = p(q(x))"""
    return [p[q[x]] for x in range(n)]

def perm_to_cycles(p, n):
    """Return cycle decomposition of permutation."""
    visited = [False]*n
    cycles = []
    for i in range(n):
        if visited[i]:
            continue
        cycle = []
        j = i
        while not visited[j]:
            visited[j] = True
            cycle.append(j)
            j = p[j]
        if len(cycle) > 1:
            cycles.append(tuple(cycle))
    return cycles


# ═══════════════════════════════════════════════════════════════════
# ANALYSIS 1: S-MAP BASIC PROPERTIES
# ═══════════════════════════════════════════════════════════════════

def analyze_S_basic(mul, n, name):
    print(f"\n{'═'*70}")
    print(f"  S-MAP BASIC PROPERTIES: {name} (n={n})")
    print(f"{'═'*70}")

    S = [mul[x][x] for x in range(n)]
    print(f"\n  S(x) = x◇x: {S[:20]}{'...' if n>20 else ''}")

    # Is S bijective?
    is_bij = len(set(S)) == n
    print(f"  S bijective: {is_bij}")

    if is_bij:
        S_inv = perm_inverse(S, n)
        # Cycle structure
        cycles = perm_to_cycles(S, n)
        cycle_lengths = sorted([len(c) for c in cycles], reverse=True)
        print(f"  Cycle type: {cycle_lengths}")
        # Order
        from math import lcm
        order = 1
        for l in cycle_lengths:
            order = lcm(order, l)
        print(f"  Order of S: {order}")
    else:
        image_size = len(set(S))
        print(f"  |image(S)| = {image_size} / {n}")
        # Fiber sizes
        fibers = defaultdict(list)
        for x in range(n):
            fibers[S[x]].append(x)
        fiber_sizes = sorted([len(v) for v in fibers.values()], reverse=True)
        print(f"  Fiber sizes: {fiber_sizes[:15]}{'...' if len(fiber_sizes)>15 else ''}")

    # Fixed points of S (idempotent elements)
    fixed_pts = [x for x in range(n) if S[x] == x]
    print(f"  Fixed points (idempotents): {len(fixed_pts)} — {fixed_pts[:10]}")

    return S


# ═══════════════════════════════════════════════════════════════════
# ANALYSIS 2: COMMUTATION OF S WITH L AND R
# ═══════════════════════════════════════════════════════════════════

def analyze_S_commutation(mul, n, name):
    """
    Test: S ∘ L_a = ? ∘ S for various a.
    I.e., is S(a◇x) related to a◇S(x) or S(a)◇x or similar?

    From E677: S(x) = L_x(x). So S = "evaluate L on the diagonal."
    S ∘ L_a(x) = S(a◇x) = (a◇x)◇(a◇x) = L_{a◇x}(a◇x)

    Is there a simple relation? Let's check computationally.
    """
    print(f"\n{'═'*70}")
    print(f"  S COMMUTATION ANALYSIS: {name} (n={n})")
    print(f"{'═'*70}")

    S = [mul[x][x] for x in range(n)]

    # Test: S(L_a(x)) vs L_a(S(x)) for each a
    print(f"\n  Testing S∘L_a vs L_a∘S:")
    commutes_count = 0
    for a in range(min(n, 10)):
        La = [mul[a][x] for x in range(n)]
        S_La = [S[La[x]] for x in range(n)]   # S(L_a(x)) = S(a◇x)
        La_S = [La[S[x]] for x in range(n)]   # L_a(S(x)) = a◇(x◇x)
        if S_La == La_S:
            commutes_count += 1
            print(f"    a={a}: S∘L_a = L_a∘S ✓ (commutes!)")
        else:
            # How many positions differ?
            diffs = sum(1 for x in range(n) if S_La[x] != La_S[x])
            print(f"    a={a}: S∘L_a ≠ L_a∘S ({diffs}/{n} positions differ)")

    # Test: S(R_a(x)) vs R_a(S(x))
    print(f"\n  Testing S∘R_a vs R_a∘S:")
    for a in range(min(n, 10)):
        Ra = [mul[x][a] for x in range(n)]
        S_Ra = [S[Ra[x]] for x in range(n)]   # S(R_a(x)) = S(x◇a)
        Ra_S = [Ra[S[x]] for x in range(n)]   # R_a(S(x)) = (x◇x)��a
        if S_Ra == Ra_S:
            print(f"    a={a}: S∘R_a = R_a∘S ✓")
        else:
            diffs = sum(1 for x in range(n) if S_Ra[x] != Ra_S[x])
            print(f"    a={a}: S∘R_a ≠ R_a∘S ({diffs}/{n} differ)")

    # Test: S(L_a(x)) = L_{S(a)}(something)?
    print(f"\n  Testing S∘L_a = L_{{f(a)}}∘g for some f, g:")
    for a in range(min(n, 10)):
        La = [mul[a][x] for x in range(n)]
        S_La = [S[La[x]] for x in range(n)]  # S(a◇x)

        # Is S∘L_a = L_c for some c?
        found_c = None
        for c in range(n):
            Lc = [mul[c][x] for x in range(n)]
            if S_La == Lc:
                found_c = c
                break

        if found_c is not None:
            print(f"    a={a}: S∘L_a = L_{found_c}")
        else:
            # Is it L_c ∘ S for some c?
            for c in range(n):
                Lc_S = [mul[c][S[x]] for x in range(n)]
                if S_La == Lc_S:
                    print(f"    a={a}: S∘L_a = L_{c}∘S")
                    break
            else:
                print(f"    a={a}: S∘L_a is not any single L_c or L_c∘S")


# ═══════════════════════════════════════════════════════════════════
# ANALYSIS 3: THE FIXED-POINT MAP θ
# ═══════════════════════════════════════════════════════════════════

def analyze_theta(mul, n, name):
    """
    θ(z) = unique x such that L_z(S(x)) = x, i.e., z◇(x◇x) = x.
    E255 says θ is defined everywhere.

    Questions:
    - Is θ a permutation?
    - Is θ = L_z^k for some universal k?
    - Is θ expressible as a composition of known maps?
    """
    print(f"\n{'═'*70}")
    print(f"  FIXED-POINT MAP θ: {name} (n={n})")
    print(f"{'═'*70}")

    S = [mul[x][x] for x in range(n)]

    # Compute θ(z) for each z
    theta = [None] * n
    for z in range(n):
        fps = [x for x in range(n) if mul[z][S[x]] == x]
        if len(fps) == 1:
            theta[z] = fps[0]
        elif len(fps) == 0:
            print(f"  WARNING: θ({z}) undefined (no fixed point)!")
            theta[z] = -1
        else:
            print(f"  WARNING: θ({z}) has {len(fps)} fixed points: {fps}")
            theta[z] = fps[0]

    print(f"\n  θ: {theta[:20]}{'...' if n>20 else ''}")

    if -1 in theta:
        print("  θ is NOT total (E255 fails somewhere)!")
        return theta

    # Is θ a permutation?
    is_perm = len(set(theta)) == n
    print(f"  θ is permutation: {is_perm}")

    if is_perm:
        cycles = perm_to_cycles(theta, n)
        cycle_lengths = sorted([len(c) for c in cycles], reverse=True)
        print(f"  θ cycle type: {cycle_lengths}")

        theta_inv = perm_inverse(theta, n)

    # Check: is θ(z) = c_{p-3} of z's orbit?
    print(f"\n  Check θ(z) = c_{{p-3}} of z's orbit:")
    all_match = True
    for z in range(min(n, 15)):
        orbit = get_orbit(mul, n, z)
        p = len(orbit)
        if p >= 4:
            expected = orbit[p-3]
        elif p == 1:
            expected = z  # idempotent: θ(z) = z
        else:
            expected = None

        match = theta[z] == expected
        if not match:
            all_match = False
        if z < 10 or not match:
            print(f"    z={z}: θ(z)={theta[z]}, c_{{p-3}}={expected} (p={p}) "
                  f"{'✓' if match else '✗'}")

    if all_match:
        print(f"  ✓ θ(z) = c_{{p-3}} confirmed for all tested z")

    # Check: is θ a power of S?
    print(f"\n  Check θ = S^k for some k:")
    if len(set(S)) == n:  # S bijective
        Sk = list(range(n))  # S^0 = id
        for k in range(1, n+1):
            Sk = [S[Sk[x]] for x in range(n)]
            if Sk == theta:
                print(f"  θ = S^{k} ✓")
                break
        else:
            print(f"  θ is NOT any power of S")

    # Check: is θ a composition of L operators?
    # θ(z) = L_z^{p-3}(z) where p = period of z
    # But p varies with z! So θ is not a "uniform" operator.
    # However: for the Jihoon model (all periods = 10):
    print(f"\n  Check θ(z) = L_z^{{p-3}}(z) for each z:")
    for z in range(min(n, 10)):
        orbit = get_orbit(mul, n, z)
        p = len(orbit)
        if p >= 4:
            Lz_iter = z
            for _ in range(p-3):
                Lz_iter = mul[z][Lz_iter]
            match = (Lz_iter == theta[z])
            print(f"    z={z}: L_z^{{{p-3}}}(z) = {Lz_iter}, θ(z) = {theta[z]} {'✓' if match else '✗'}")

    # Key identity from finding #43:
    # θ(z) = x means z◇(x◇x) = x, i.e., L_z(S(x)) = x
    # So S(θ(z)) = L_z^{-1}(θ(z))
    # I.e., S = L_z^{-1} at the point θ(z)
    print(f"\n  Verify S(θ(z)) = L_z^{{-1}}(θ(z)):")
    for z in range(min(n, 10)):
        x = theta[z]
        Sx = S[x]
        Lz_inv = perm_inverse([mul[z][i] for i in range(n)], n)
        Lz_inv_x = Lz_inv[x]
        match = Sx == Lz_inv_x
        print(f"    z={z}: S(θ(z))=S({x})={Sx}, L_z^{{-1}}({x})={Lz_inv_x} {'✓' if match else '✗'}")

    # NEW: What is θ∘θ? θ∘S? S∘θ?
    print(f"\n  Compositions:")
    theta_theta = [theta[theta[z]] for z in range(n)]
    S_theta = [S[theta[z]] for z in range(n)]
    theta_S = [theta[S[z]] for z in range(n)]

    # Check if θ∘θ equals something known
    # θ(z) = c_{p-3}(z). θ(θ(z)) = c_{p'-3}(θ(z)) where p' = period of θ(z).
    # In Jihoon (all period 10): θ(z) = L_z^7(z), and the orbit of θ(z) has the same period.
    print(f"  θ∘θ: {theta_theta[:15]}{'...' if n>15 else ''}")

    # Check: is θ∘θ = L_z^k for a universal k?
    # In Jihoon: θ(z) = L_z^7(z), θ(θ(z)) = L_{L_z^7(z)}^7(L_z^7(z))
    # This is in a DIFFERENT orbit (the orbit of θ(z) under L_{θ(z)}).

    # Check: is S∘θ = some known map?
    # S(θ(z)) = L_z^{-1}(θ(z)) = L_z^{p-1}(θ(z)) = L_z^{p-1}(L_z^{p-3}(z))
    #         = L_z^{2p-4}(z) = L_z^{p-4}(z) (mod p) = c_{p-4}
    print(f"\n  Check S∘θ(z) = c_{{p-4}} of z's orbit:")
    for z in range(min(n, 10)):
        orbit = get_orbit(mul, n, z)
        p = len(orbit)
        val = S_theta[z]
        if p >= 5:
            expected = orbit[p-4]
        elif p == 1:
            expected = z
        else:
            expected = None
        match = val == expected
        print(f"    z={z}: S(θ(z))={val}, c_{{p-4}}={expected} (p={p}) {'✓' if match else '✗'}")

    return theta


# ═══════════════════════════════════════════════════════════════════
# ANALYSIS 4: S-MAP FUNCTIONAL EQUATIONS FROM E677
# ═══════════════════════════════════════════════════════════════════

def analyze_S_identities(mul, n, name):
    """
    What algebraic identities relate S to L and R operators?

    From E677 with y=x:
      x = x◇(x◇((x◇x)◇x)) = L_x(x◇(S(x)◇x)) = L_x(R_{S(x)◇x}(x))
      So L_x^{-1}(x) = R_{S(x)◇x}(x) = x ◇ (S(x)◇x)
      i.e., c_{p-1} = x ◇ (S(x)◇x) = R_{R_x(S(x))}(x)

    Rewriting: R_x(S(x)) = S(x)◇x = d_1 where d_1 = c_{p-2}.
    So S(x)◇x = c_{p-2}. This means c_1◇x = c_{p-2}.
    (Since S(x) = x◇x = c_1.)
    Check: S(x) = c_1, S(x)◇x = c_1◇x = d_1. Yes, d_1 = c_{p-2}. ✓

    What about S(c_k) for other orbit elements?
    S(c_k) = c_k◇c_k = orbit multiplication at (k,k).

    Identity: For orbit element c_k with period p under L_x:
    S(c_k) = c_k◇c_k.
    The orbit of c_k under L_{c_k} is a DIFFERENT orbit.
    """
    print(f"\n{'═'*70}")
    print(f"  S-MAP IDENTITIES FROM E677: {name} (n={n})")
    print(f"{'═'*70}")

    S = [mul[x][x] for x in range(n)]

    # Test: S(c_k) positions relative to orbits
    print(f"\n  S(c_k) relative to the L_x orbit of x:")
    for x in range(min(n, 5)):
        orbit = get_orbit(mul, n, x)
        p = len(orbit)
        if p <= 1:
            continue
        orbit_set = set(orbit)

        print(f"\n    x={x}, orbit={orbit}, period={p}")
        for k in range(p):
            ck = orbit[k]
            Sck = S[ck]
            in_orbit = Sck in orbit_set
            if in_orbit:
                pos = orbit.index(Sck)
                print(f"      S(c_{k}) = S({ck}) = {Sck} = c_{pos} (IN orbit)")
            else:
                print(f"      S(c_{k}) = S({ck}) = {Sck} (OUTSIDE orbit)")

    # Key: in the size-7 affine model, all S(c_k) stay in orbit
    # because orbit = M. In Jihoon (period 10), S(c_k) may exit.

    # The crucial functional equation:
    # From E677(c_k, x) (identity iii specialization):
    #   c_k = c_{k+1} ◇ d_{k+2}
    # And d_{k+2} = L_{c_{k+1}}^{-1}(c_k)

    # From E677 with (a=c_k, b=c_k):
    #   c_k = c_k◇(c_k◇((c_k◇c_k)◇c_k)) = L_{c_k}(c_k◇(S(c_k)◇c_k))
    # This gives L_{c_k}^{-1}(c_k) = c_k ◇ (S(c_k)◇c_k)

    print(f"\n  Identity from E677(c_k, c_k):")
    print(f"  L_{{c_k}}^{{-1}}(c_k) = c_k ◇ (S(c_k) ◇ c_k)")
    print(f"  = c_k ◇ R_{{c_k}}(S(c_k))")

    for x in range(min(n, 5)):
        orbit = get_orbit(mul, n, x)
        p = len(orbit)
        if p <= 1:
            continue

        print(f"\n    x={x}, period={p}:")
        for k in range(min(p, 7)):
            ck = orbit[k]
            Sck = S[ck]
            Sck_ck = mul[Sck][ck]  # S(c_k)◇c_k
            ck_Sck_ck = mul[ck][Sck_ck]  # c_k ◇ (S(c_k)◇c_k)

            # L_{c_k}^{-1}(c_k)
            Lck = [mul[ck][i] for i in range(n)]
            Lck_inv = perm_inverse(Lck, n)
            expected = Lck_inv[ck]

            # The orbit of c_k under L_{c_k}
            ck_orbit = get_orbit(mul, n, ck)
            pk = len(ck_orbit)
            # L_{c_k}^{-1}(c_k) = last element in c_k's own orbit
            # = ck_orbit[pk-1]

            match = ck_Sck_ck == expected
            print(f"      k={k}: L_{{c_{k}}}^{{-1}}(c_{k}) = {expected} = c_{k}◇(S(c_{k})◇c_{k}) "
                  f"= {ck}◇({Sck}◇{ck}) = {ck}◇{Sck_ck} = {ck_Sck_ck} {'✓' if match else '✗'}")

    # NEW QUESTION: What is S∘S? And S^k in general?
    print(f"\n  Powers of S:")
    if len(set(S)) == n:
        Sk = S[:]
        for power in range(2, 8):
            Sk = [S[Sk[x]] for x in range(n)]
            # Check if S^power equals something on orbits
            # In Jihoon: S has order 31. S^k(x) = ?
            # S(x) = x◇x = c_1 in orbit of x.
            # S(c_1) = c_1◇c_1 = orbit entry (1,1) = ?
            # In size-7: S(c_0) = c_1, S(c_1) = c_1◇c_1 = c_{4*1+1+1 mod 7} = c_6
            # S^2(c_0) = S(c_1) = c_6
            pass
        # Just print S^2
        S2 = [S[S[x]] for x in range(n)]
        print(f"  S²: {S2[:15]}{'...' if n>15 else ''}")

        # Is S² related to θ?
        theta = [None]*n
        for z in range(n):
            fps = [x for x in range(n) if mul[z][S[x]] == x]
            if fps:
                theta[z] = fps[0]
        if None not in theta:
            if S2 == theta:
                print(f"  S² = θ !")
            else:
                diffs = sum(1 for z in range(n) if S2[z] != theta[z])
                print(f"  S² ≠ θ ({diffs}/{n} differ)")


# ═══════════════════════════════════════════════════════════════════
# ANALYSIS 5: WHAT MAKES L_z∘S ALWAYS HAVE A FIXED POINT?
# ═══════════════════════════════════════════════════════════════════

def analyze_LzS_structure(mul, n, name):
    """
    L_z∘S is a map M → M. Its fixed points are the x with z◇(x◇x)=x.
    In a random permutation, ~63% have at least one fixed point.
    E677 forces L_z∘S to NEVER be a derangement.

    What structural property of L_z∘S prevents it from being a derangement?

    Key observation: if S is bijective, L_z∘S is a permutation.
    If S is not bijective, L_z∘S is not a permutation (not injective).
    In that case having a "fixed point" is about the equation L_z(S(x))=x,
    which may have solutions even if L_z∘S is not bijective.
    """
    print(f"\n{'═'*70}")
    print(f"  L_z∘S STRUCTURE: {name} (n={n})")
    print(f"{'═'*70}")

    S = [mul[x][x] for x in range(n)]
    S_bij = len(set(S)) == n

    print(f"  S bijective: {S_bij}")

    if not S_bij:
        print("  L_z∘S is not a permutation. Fixed-point analysis different.")
        # Count solutions to L_z(S(x)) = x for each z
        for z in range(min(n, 10)):
            sols = [x for x in range(n) if mul[z][S[x]] == x]
            print(f"    z={z}: {len(sols)} solution(s)")
        return

    # S is bijective. L_z∘S is a permutation for each z.
    print(f"\n  Cycle structure of L_z∘S for each z:")

    all_have_fp = True
    for z in range(min(n, 15)):
        LzS = [mul[z][S[x]] for x in range(n)]
        fps = [x for x in range(n) if LzS[x] == x]
        cycles = perm_to_cycles(LzS, n)
        cycle_lengths = sorted([len(c) for c in cycles], reverse=True)
        fp_count = sum(1 for x in range(n) if LzS[x] == x)

        if fp_count == 0:
            all_have_fp = False
            print(f"    z={z}: DERANGEMENT! cycles={cycle_lengths}")
        else:
            print(f"    z={z}: {fp_count} FP(s), cycles inc. 1-cycles: {cycle_lengths + [1]*fp_count}")

    if all_have_fp:
        print(f"\n  ✓ L_z∘S is never a derangement (E255 confirmed)")

    # Key test: what is the SIGN of L_z∘S?
    # If L_z∘S always has a specific sign, that constrains its cycle structure.
    print(f"\n  Sign of L_z∘S:")
    for z in range(min(n, 10)):
        LzS = [mul[z][S[x]] for x in range(n)]
        # Compute sign via cycle decomposition
        cycles = perm_to_cycles(LzS, n)
        # Sign = (-1)^(sum of (cycle_length - 1))
        total_transpositions = sum(len(c) - 1 for c in cycles)
        # Also add fixed points (1-cycles, contribute 0)
        sign = (-1) ** total_transpositions
        print(f"    z={z}: sign(L_z∘S) = {'+' if sign == 1 else '-'}")

    # Key test: is L_z∘S always conjugate to the same permutation?
    # Compute L_z∘S cycle types
    print(f"\n  Cycle type distribution of L_z∘S:")
    type_counts = defaultdict(int)
    for z in range(n):
        LzS = [mul[z][S[x]] for x in range(n)]
        cycles = perm_to_cycles(LzS, n)
        fp_count = sum(1 for x in range(n) if LzS[x] == x)
        ctype = tuple(sorted([len(c) for c in cycles] + [1]*fp_count, reverse=True))
        type_counts[ctype] += 1
    for ctype, count in sorted(type_counts.items()):
        print(f"    {ctype}: {count} element(s)")


# ═══════════════════════════════════════════════════════════════════
# MAIN
# ═══════════════════════════════════════════════════════════════════

def run_full_analysis(mul, n, name):
    print(f"\n{'#'*70}")
    print(f"# {name}")
    print(f"{'#'*70}")

    assert verify_e677(mul, n), f"{name}: E677 fails!"
    assert verify_e255(mul, n), f"{name}: E255 fails!"
    print("E677 ✓, E255 ✓")

    analyze_S_basic(mul, n, name)
    analyze_S_commutation(mul, n, name)
    analyze_theta(mul, n, name)
    analyze_S_identities(mul, n, name)
    analyze_LzS_structure(mul, n, name)


def main():
    print("E677 S-Map Global Analysis")
    print("=" * 70)

    # Size-7 affine
    mul7, n7 = make_size7()
    run_full_analysis(mul7, n7, "SIZE-7 AFFINE (n=7)")

    # Jihoon
    mul31, n31 = make_jihoon()
    run_full_analysis(mul31, n31, "JIHOON (n=31)")

    # Size-5 idempotent
    mul5, n5 = make_size5()
    run_full_analysis(mul5, n5, "SIZE-5 IDEMPOTENT (n=5)")


if __name__ == '__main__':
    main()
