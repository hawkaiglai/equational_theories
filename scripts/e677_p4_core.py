"""
Extract the UNSAT core for period 4 at n=5.
Which E677 instances are needed? Can we identify a short proof chain?
"""
from pysat.solvers import Cadical153, Minisat22
from pysat.formula import CNF
import time

def var(i, j, k, n):
    return i * n * n + j * n + k + 1

def encode_period4_with_assumptions(n):
    """
    Encode period-4 E677 with E677 instances as assumption-gated clauses.
    Each E677(x,y) instance gets a selector variable; we can then extract
    which instances are needed for UNSAT.
    """
    cnf = CNF()
    selectors = {}  # (x,y) -> selector variable
    next_sel = n * n * n + 1
    
    # Cell + permutation constraints (hard clauses)
    for i in range(n):
        for j in range(n):
            cnf.append([var(i, j, k, n) for k in range(n)])
            for k1 in range(n):
                for k2 in range(k1 + 1, n):
                    cnf.append([-var(i, j, k1, n), -var(i, j, k2, n)])
    
    for i in range(n):
        for k in range(n):
            cnf.append([var(i, j, k, n) for j in range(n)])
            for j1 in range(n):
                for j2 in range(j1 + 1, n):
                    cnf.append([-var(i, j1, k, n), -var(i, j2, k, n)])
    
    # Orbit + derived constraints (hard)
    cnf.append([var(0, 0, 1, n)])
    cnf.append([var(0, 1, 2, n)])
    cnf.append([var(0, 2, 3, n)])
    cnf.append([var(0, 3, 0, n)])
    for ext in range(4, n):
        for orb in range(4):
            cnf.append([-var(0, ext, orb, n)])
    cnf.append([var(1, 0, 2, n)])
    cnf.append([var(3, 1, 2, n)])
    
    # E677 instances as soft (gated) clauses
    for x in range(n):
        for y in range(n):
            sel = next_sel
            next_sel += 1
            selectors[(x, y)] = sel
            
            for a in range(n):
                for b in range(n):
                    for c in range(n):
                        # -sel v -var(y,x,a) v -var(a,y,b) v -var(x,b,c) v var(y,c,x)
                        cnf.append([-sel, -var(y,x,a,n), -var(a,y,b,n), -var(x,b,c,n), var(y,c,x,n)])
    
    return cnf, selectors, next_sel - 1

# For n=5, use assumption-based approach with Minisat22
n = 5
print(f"=== UNSAT core extraction for period 4, n={n} ===")
print()

cnf, selectors, num_vars = encode_period4_with_assumptions(n)
print(f"Variables: {num_vars}, Clauses: {len(cnf.clauses)}")
print(f"E677 selector variables: {len(selectors)} (one per (x,y) pair)")

# First verify UNSAT with all selectors active
assumptions = list(selectors.values())
solver = Minisat22()
solver.append_formula(cnf)

t0 = time.time()
result = solver.solve(assumptions=assumptions)
elapsed = time.time() - t0
print(f"\nWith all E677 instances: {'SAT' if result else 'UNSAT'} ({elapsed:.2f}s)")

if not result:
    # Extract UNSAT core
    core = solver.get_core()
    print(f"UNSAT core size: {len(core)} selector variables (out of {len(assumptions)})")
    
    # Map core back to (x,y) pairs
    sel_to_pair = {v: k for k, v in selectors.items()}
    core_pairs = sorted([sel_to_pair[s] for s in core])
    
    print(f"\nE677 instances needed for UNSAT:")
    for (x, y) in core_pairs:
        label = ""
        if x < 4 and y < 4:
            label = f"  (orbit pair c_{x}, c_{y})"
        elif x < 4:
            label = f"  (c_{x}, ext_{y})"
        elif y < 4:
            label = f"  (ext_{x}, c_{y})"
        else:
            label = f"  (ext_{x}, ext_{y})"
        print(f"  E677({x}, {y}){label}")
    
    # Separate orbit-only pairs from cross-orbit pairs
    orbit_pairs = [(x,y) for (x,y) in core_pairs if x < 4 and y < 4]
    cross_pairs = [(x,y) for (x,y) in core_pairs if x >= 4 or y >= 4]
    
    print(f"\nOrbit-only pairs: {len(orbit_pairs)}")
    for p in orbit_pairs:
        print(f"  E677({p[0]}, {p[1]})")
    print(f"\nCross-orbit pairs: {len(cross_pairs)}")
    for p in cross_pairs:
        print(f"  E677({p[0]}, {p[1]})")
    
    # Can we get UNSAT with ONLY orbit pairs?
    orbit_assumptions = [selectors[(x,y)] for (x,y) in orbit_pairs]
    result2 = solver.solve(assumptions=orbit_assumptions)
    print(f"\nWith only orbit E677 pairs: {'SAT' if result2 else 'UNSAT'}")
    
    if result2:
        print("=> Cross-orbit E677 instances ARE needed for the proof!")
        # Which cross-orbit instances are essential?
        # Try adding them one by one
        
        # Try with only orbit + pairs involving element 4 (the external)
        ext_pairs_4 = [(x,y) for (x,y) in core_pairs if x == 4 or y == 4]
        ext_assumptions = [selectors[(x,y)] for (x,y) in ext_pairs_4]
        result3 = solver.solve(assumptions=orbit_assumptions + ext_assumptions)
        print(f"  With orbit + ext_4 pairs: {'SAT' if result3 else 'UNSAT'}")
    else:
        print("=> Orbit-only E677 instances SUFFICE!")

solver.delete()

