#!/usr/bin/env python3
"""
Reproduce the database-level claims about E677 magmas used in the conjugation /
perfect-matching note (Chuks-Onah, 2026).

Usage:  python3 verify_perfect_matching.py /path/to/eq677_database/tables

For every well-formed n x n multiplication table T (with T[a][b] = a <> b) it checks:
  * E677   : a = b <> (a <> ((b<>a)<>b))           for all a,b
  * E255   : ((x<>x)<>x)<>x = x                     for all x
  * deg_L==1 : every P_z = L_z o S has exactly one fixed point      (z-side of rho)
  * deg_R==1 : every x is conjugation-fixed by exactly one z        (x-side of rho)
               where rho = {(z,x) : (z<>x)<>z = x}  ==  {(z,x): z<>(x<>x)=x}
  * single-point identity c_{p-4}<>c_{p-4} = c_{p-5} on every orbit of period p>=5
and reports totals.  All counts should come out equal to the number of valid models
(perfect matching), with the single-point identity holding on every p>=5 orbit.
"""
import sys, glob, os

def load(fn):
    with open(fn) as f:
        return [list(map(int, line.split())) for line in f if line.strip()]

def valid(T):
    n = len(T)
    return n > 0 and all(len(r) == n and 0 <= min(r) and max(r) < n for r in T)

def check_e677(T, n):
    return all(T[b][T[a][T[T[b][a]][b]]] == a for a in range(n) for b in range(n))

def check_e255(T, n):
    return all(T[T[T[x][x]][x]][x] == x for x in range(n))

def degrees(T, n):
    """rho = {(z,x): (z<>x)<>z = x}; return (degL list, degR list)."""
    S = [T[i][i] for i in range(n)]
    degL = [0]*n; degR = [0]*n
    for z in range(n):
        for x in range(n):
            if T[z][S[x]] == x:           # z<>(x<>x)=x  <=>  (z<>x)<>z=x  (Identity A)
                degL[z] += 1; degR[x] += 1
    return degL, degR

def single_point(T, n):
    """Check c_{p-4}<>c_{p-4}=c_{p-5} on every non-idempotent orbit of period p>=5."""
    ok = tot = 0
    seen = set()
    for x in range(n):
        if x in seen: continue
        orb = [x]; cur = x
        for _ in range(n+1):
            cur = T[x][cur]
            if cur == x: break
            orb.append(cur)
        for e in orb: seen.add(e)
        p = len(orb)
        if p < 5: continue
        tot += 1
        if T[orb[p-4]][orb[p-4]] == orb[p-5]: ok += 1
    return ok, tot

def main():
    path = sys.argv[1] if len(sys.argv) > 1 else "."
    files = sorted(glob.glob(os.path.join(path, "*.txt")))
    nval = e677ok = e255ok = degLok = degRok = perfect = 0
    sp_ok = sp_tot = 0
    nonRC = 0
    for fn in files:
        T = load(fn); n = len(T)
        if not valid(T): continue
        nval += 1
        if check_e677(T, n): e677ok += 1
        if check_e255(T, n): e255ok += 1
        degL, degR = degrees(T, n)
        if all(d == 1 for d in degL): degLok += 1
        if all(d == 1 for d in degR): degRok += 1
        if all(d == 1 for d in degL) and all(d == 1 for d in degR): perfect += 1
        if not all(len({T[z][x] for z in range(n)}) == n for x in range(n)): nonRC += 1
        a, b = single_point(T, n); sp_ok += a; sp_tot += b
    print(f"files scanned                 : {len(files)}")
    print(f"valid n x n tables            : {nval}")
    print(f"satisfy E677                  : {e677ok}/{nval}")
    print(f"satisfy E255                  : {e255ok}/{nval}")
    print(f"deg_L == 1 everywhere         : {degLok}/{nval}")
    print(f"deg_R == 1 everywhere         : {degRok}/{nval}   (perfect matching rho)")
    print(f"both (perfect matching)       : {perfect}/{nval}")
    print(f"non-right-cancellative models : {nonRC}")
    print(f"single-point c_{{p-4}}^2=c_{{p-5}}  : {sp_ok}/{sp_tot} orbits (p>=5)")

if __name__ == "__main__":
    main()
