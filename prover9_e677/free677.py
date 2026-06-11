#!/usr/bin/env python3
"""
Computable model of the free 677 magma M_{X,677} (blueprint, ch. 677, 'The free 677 magma').

Elements = binary trees with leaves in the generator set X (python: leaf = str, node = pair).
Order:  w < y  iff  w is a PROPER subtree of y.
Operation (recursive):  if x < y = (yL,yR) and yR == (x<>yL)<>x then x<>y := yL
                        else x<>y := (x,y).

Self-test: E677 holds on random tree pairs (run this file).
Application: probe for laws of F1 (= identities of all ONE-GENERATED E677 magmas):
a pair of terms p(a,b), q(a,b) is a law of F1 iff p,q agree under ALL substitutions of
unary terms for a,b. Evaluation in F2 decides E677-provability (free property).
"""
import sys, random
sys.setrecursionlimit(100000)
memo={}
def leq(w,y):
    if w==y: return True
    if isinstance(y,tuple): return leq(w,y[0]) or leq(w,y[1])
    return False
def op(x,y):
    k=(x,y)
    if k in memo: return memo[k]
    r=None
    if isinstance(y,tuple) and x!=y and leq(x,y):
        yL,yR=y
        if op(op(x,yL),x)==yR: r=yL
    if r is None: r=(x,y)
    memo[k]=r
    return r
def ev(t):
    if not isinstance(t,tuple): return t
    return (lambda L,R: op(L,R))(ev(t[0]),ev(t[1]))
def terms(leaves,n):
    if n==1: return list(leaves)
    out=[]
    for i in range(1,n):
        for L in terms(leaves,i):
            for R in terms(leaves,n-i):
                out.append((L,R))
    return out
def subst(t,va,vb):
    if t=='a': return va
    if t=='b': return vb
    if not isinstance(t,tuple): return t
    return (subst(t[0],va,vb),subst(t[1],va,vb))
if __name__=='__main__':
    random.seed(1)
    def rnd(d,L):
        if d==0 or random.random()<0.4: return random.choice(L)
        return (rnd(d-1,L),rnd(d-1,L))
    bad=sum(1 for _ in range(4000)
            if (lambda x,y: op(y,op(x,op(op(y,x),y)))!=x)(rnd(3,['a','b']),rnd(3,['a','b'])))
    print(f"E677 self-test: {4000-bad}/4000 pass")
