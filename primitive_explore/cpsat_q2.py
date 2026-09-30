#!/usr/bin/env python3
"""Heuristic evidence for Q2 (NOT a proof): search, with the CP-SAT solver of OR-Tools, for a
primitive set T of integers (no element divides another) with sum 1/n = 1 and |T| <= K,
inside a restricted finite universe.

Usage (from the repository root):
  python3 primitive_explore/cpsat_q2.py X Pmax K seconds workers BIGMAX ["# i: hint set"]
  universe: non-prime-powers n <= X whose prime factors are <= Pmax, except possibly one extra
            prime factor <= BIGMAX to the first power (BIGMAX = 0: none).
Constraints: primitive (pairwise), the congruence  sum (D/n mod M) x_n = M k_p  at every prime
(D = lcm of the universe, M = p^{v_p(D)}), the value  sum ceil(S/n) x_n >= S >= sum floor(S/n) x_n
(S = 2^40), and |T| <= K.  All of these are necessary conditions, so INFEASIBLE means that the
solver found no solution in the universe; solutions it reports are re-verified exactly.
The result depends on the correctness of the solver and is used only as evidence.
"""
import sys, math, re, itertools
from fractions import Fraction
from ortools.sat.python import cp_model
X=int(sys.argv[1]); Pmax=int(sys.argv[2]); K=int(sys.argv[3]); tl=float(sys.argv[4]); workers=int(sys.argv[5])
def primes(n): return [p for p in range(2,n+1) if all(p%d for d in range(2,int(p**.5)+1))]
PS=primes(Pmax)
BIGMAX=int(sys.argv[6]) if len(sys.argv)>6 else 0
ALLP=primes(max(Pmax,BIGMAX))
def fac(n):
    f={}
    for p in PS:
        while n%p==0: f[p]=f.get(p,0)+1; n//=p
    if n==1: return f
    # at most one extra prime factor > Pmax, to the first power, <= BIGMAX
    if n<=BIGMAX and all(n%d for d in range(2,int(n**.5)+1)): f[n]=1; return f
    return None
U=[]
for n in range(6,X+1):
    f=fac(n)
    if f is None or len(f)<2: continue
    U.append(n)
PS=sorted(set(p for n in U for p in ALLP if n%p==0))
print("universe",len(U),flush=True)
D=1
for n in U: D=D*n//math.gcd(D,n)
m=cp_model.CpModel()
x={n:m.NewBoolVar(str(n)) for n in U}
Us=set(U)
for a in U:
    for b in range(2*a,X+1,a):
        if b in Us: m.AddBoolOr([x[a].Not(),x[b].Not()])
for p in PS:
    M=1
    while D%(M*p)==0: M*=p
    idx=[((D//n)%M,n) for n in U if n%p==0]
    idx=[(c,n) for c,n in idx if c]
    if not idx: continue
    k=m.NewIntVar(0,sum(c for c,_ in idx)//M+1,"k%d"%p)
    m.Add(sum(c*x[n] for c,n in idx)==M*k)
S=1<<40
m.Add(sum(((S+n-1)//n)*x[n] for n in U)>=S)
m.Add(sum((S//n)*x[n] for n in U)<=S)
m.Add(sum(x.values())<=K)
m.Minimize(sum(x.values()))
# hint: a known 47-term solution restricted to the universe
for line in open('solutions47.txt') if len(sys.argv)<8 else [sys.argv[7]]:
    mm=re.match(r'#\s*\d+:\s*([\d ]+)',line)
    if mm:
        T=list(map(int,mm.group(1).split()))
        if all(t in Us for t in T):
            for n in U: m.AddHint(x[n], 1 if n in T else 0)
            print("hint",T,flush=True); break
s=cp_model.CpSolver(); s.parameters.max_time_in_seconds=tl; s.parameters.num_workers=workers
class CB(cp_model.CpSolverSolutionCallback):
    def __init__(s2): super().__init__()
    def on_solution_callback(s2):
        T=[n for n in U if s2.Value(x[n])]
        v=sum(Fraction(1,n) for n in T)
        print("solution |T|=%d sum=%s"%(len(T),v), T, flush=True)
r=s.Solve(m, CB())
print(s.StatusName(r), s.ObjectiveValue(), s.BestObjectiveBound(), flush=True)
