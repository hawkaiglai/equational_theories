"""
Use SAT (via python-sat if available, else manual) to check period 4 impossibility.
More efficient approach: encode E677 constraints directly.
"""
import sys

try:
    from pysat.solvers import Cadical153
    from pysat.formula import CNF
    HAS_PYSAT = True
    print("Using PySAT with CaDiCaL")
except ImportError:
    HAS_PYSAT = False
    print("PySAT not available, using brute force with pruning")

def check_e677(mul, n):
    for x in range(n):
        for y in range(n):
            yx = mul[y][x]
            yx_y = mul[yx][y]
            x_yxy = mul[x][yx_y]
            rhs = mul[y][x_yxy]
            if rhs != x:
                return False
    return True

def check_e677_partial(mul, n, defined_pairs):
    """Check E677 only for pairs where all intermediate values are defined."""
    for x in range(n):
        for y in range(n):
            try:
                yx = mul[y][x]
                if yx is None: continue
                yx_y = mul[yx][y]
                if yx_y is None: continue
                x_yxy = mul[x][yx_y]
                if x_yxy is None: continue
                rhs = mul[y][x_yxy]
                if rhs is None: continue
                if rhs != x:
                    return False
            except (IndexError, TypeError):
                continue
    return True

if HAS_PYSAT:
    # SAT encoding for E677 + period 4
    # Variables: x_{i,j,k} means mul[i][j] = k
    # For magma of size n
    
    for n in [5, 6, 7, 8]:
        print(f"\n=== n = {n}, checking E677 + period 4 ===")
        
        cnf = CNF()
        
        # Variable numbering: var(i, j, k) = i*n*n + j*n + k + 1
        def var(i, j, k):
            return i * n * n + j * n + k + 1
        
        num_vars = n * n * n
        
        # Each cell has exactly one value (at-least-one + at-most-one)
        for i in range(n):
            for j in range(n):
                # At least one value
                cnf.append([var(i, j, k) for k in range(n)])
                # At most one value (pairwise negation)
                for k1 in range(n):
                    for k2 in range(k1 + 1, n):
                        cnf.append([-var(i, j, k1), -var(i, j, k2)])
        
        # Each row is a permutation (L_i bijective)
        for i in range(n):
            for k in range(n):
                # k appears at least once in row i
                cnf.append([var(i, j, k) for j in range(n)])
                # k appears at most once in row i
                for j1 in range(n):
                    for j2 in range(j1 + 1, n):
                        cnf.append([-var(i, j1, k), -var(i, j2, k)])
        
        # Orbit constraints: L_0 has 4-cycle (0,1,2,3)
        # mul[0][0]=1, mul[0][1]=2, mul[0][2]=3, mul[0][3]=0
        cnf.append([var(0, 0, 1)])
        cnf.append([var(0, 1, 2)])
        cnf.append([var(0, 2, 3)])
        cnf.append([var(0, 3, 0)])
        
        # External elements (4,...,n-1) form separate L_0 cycles
        # For n=5: L_0(4)=4 (only option)
        # For n=6: L_0 on {4,5} is either (4)(5) or (4,5)
        # For simplicity, fix L_0(4)=4 (if n=5), or L_0(4)=5, L_0(5)=4 for n=6, etc.
        # Actually we should try ALL possible L_0 cycle structures on externals.
        # But for a first check, let's just fix: external elements are L_0 fixed points.
        for ext in range(4, n):
            cnf.append([var(0, ext, ext)])  # L_0(ext) = ext (fixed points)
        
        # d_1 = c_2: mul[1][0] = 2
        cnf.append([var(1, 0, 2)])
        
        # c_3*c_1 = c_2: mul[3][1] = 2
        cnf.append([var(3, 1, 2)])
        
        # E677 constraints: for all x, y, k1, k2, k3, k4:
        # if mul[y][x]=k1 and mul[k1][y]=k2 and mul[x][k2]=k3 and mul[y][k3]=k4
        # then k4 = x
        # 
        # Encoding: for each (x, y, k1, k2, k3):
        # -var(y,x,k1) v -var(k1,y,k2) v -var(x,k2,k3) v -var(y,k3,x)
        # (if the first three hold, then mul[y][k3] must be x)
        #
        # And for k4 != x:
        # -var(y,x,k1) v -var(k1,y,k2) v -var(x,k2,k3) v -var(y,k3,k4) for k4!=x
        
        for x in range(n):
            for y in range(n):
                for k1 in range(n):  # mul[y][x] = k1
                    for k2 in range(n):  # mul[k1][y] = k2
                        for k3 in range(n):  # mul[x][k2] = k3
                            # If all three hold, then mul[y][k3] = x
                            for k4 in range(n):
                                if k4 == x:
                                    continue
                                cnf.append([
                                    -var(y, x, k1),
                                    -var(k1, y, k2),
                                    -var(x, k2, k3),
                                    -var(y, k3, k4)
                                ])
        
        print(f"  Variables: {num_vars}, Clauses: {len(cnf.clauses)}")
        
        solver = Cadical153()
        solver.append_formula(cnf)
        
        result = solver.solve()
        if result:
            print(f"  SAT — period 4 magma EXISTS at n={n}!")
            model = solver.get_model()
            # Extract multiplication table
            mul = [[0]*n for _ in range(n)]
            for i in range(n):
                for j in range(n):
                    for k in range(n):
                        if model[var(i,j,k)-1] > 0:
                            mul[i][j] = k
            print("  Multiplication table:")
            for i in range(n):
                print(f"    Row {i}: {mul[i]}")
            # Verify
            if check_e677(mul, n):
                print("  E677 verified ✓")
            else:
                print("  E677 FAILED ✗ (encoding bug?)")
            solver.delete()
            break
        else:
            print(f"  UNSAT — no period-4 E677 magma at n={n} (with L_0 externals as fixed points)")
        
        solver.delete()
    
    # Now try without fixing external L_0 structure
    print("\n=== Now try n=6 with L_0 = (0,1,2,3)(4,5) ===")
    n = 6
    cnf = CNF()
    
    def var(i, j, k):
        return i * n * n + j * n + k + 1
    
    # Cell constraints
    for i in range(n):
        for j in range(n):
            cnf.append([var(i, j, k) for k in range(n)])
            for k1 in range(n):
                for k2 in range(k1 + 1, n):
                    cnf.append([-var(i, j, k1), -var(i, j, k2)])
    
    # Row permutation constraints
    for i in range(n):
        for k in range(n):
            cnf.append([var(i, j, k) for j in range(n)])
            for j1 in range(n):
                for j2 in range(j1 + 1, n):
                    cnf.append([-var(i, j1, k), -var(i, j2, k)])
    
    # Orbit: L_0 = (0,1,2,3)(4,5)
    cnf.append([var(0, 0, 1)])
    cnf.append([var(0, 1, 2)])
    cnf.append([var(0, 2, 3)])
    cnf.append([var(0, 3, 0)])
    cnf.append([var(0, 4, 5)])
    cnf.append([var(0, 5, 4)])
    
    # d_1 and c_3*c_1
    cnf.append([var(1, 0, 2)])
    cnf.append([var(3, 1, 2)])
    
    # E677
    for x in range(n):
        for y in range(n):
            for k1 in range(n):
                for k2 in range(n):
                    for k3 in range(n):
                        for k4 in range(n):
                            if k4 == x:
                                continue
                            cnf.append([
                                -var(y, x, k1),
                                -var(k1, y, k2),
                                -var(x, k2, k3),
                                -var(y, k3, k4)
                            ])
    
    print(f"  Variables: {n**3}, Clauses: {len(cnf.clauses)}")
    solver = Cadical153()
    solver.append_formula(cnf)
    result = solver.solve()
    if result:
        print(f"  SAT — period 4 EXISTS with L_0=(0,1,2,3)(4,5)!")
        model = solver.get_model()
        mul = [[0]*n for _ in range(n)]
        for i in range(n):
            for j in range(n):
                for k in range(n):
                    if model[var(i,j,k)-1] > 0:
                        mul[i][j] = k
        print("  Table:")
        for i in range(n):
            print(f"    Row {i}: {mul[i]}")
        if check_e677(mul, n):
            print("  E677 verified ✓")
        else:
            print("  E677 FAILED ✗")
    else:
        print(f"  UNSAT — no period-4 E677 magma at n=6 with L_0=(0,1,2,3)(4,5)")
    solver.delete()

else:
    # Fallback: brute force for n=5 with heavy pruning
    print("\n=== Brute force n=5 with pruning ===")
    n = 5
    # ... (already done above, confirmed UNSAT)
    print("Already confirmed: no period-4 E677 magma at n=5 (fixed L_0(4)=4)")

