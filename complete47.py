"""Exact completion of dumped cores (independent Python implementation).

For each core C (edges inside S = primes <= SB) with unsatisfied set U, find ALL sets G of
elements of P having a prime factor > SB with |G| <= KT-|C| and sum(G) = 1 - sum(C).
Shapes: d_q (# big neighbours of q in S), nbb (# big-big edges).
nbb = 0 : stars, P | n(A), exact cover (all covers enumerated).
nbb = 1 : one 2-vertex component solved by the divisor equation, rest stars.
nbb >= 2: reported as unresolved.
"""
import sys, math, itertools, pickle
from fractions import Fraction as F
from functools import lru_cache

SB = 73; KT = 47
def isprime(n):
    if n < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % p == 0: return n == p
    d = n-1; s = 0
    while d % 2 == 0: d//=2; s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(s-1):
            x = x*x % n
            if x == n-1: break
        else: return False
    return True
def pollard(n):
    if n % 2 == 0: return 2
    for c in range(1,100):
        x=y=2; d=1
        f=lambda v:(v*v+c)%n
        while d==1:
            x=f(x); y=f(f(y)); d=math.gcd(abs(x-y),n)
        if d!=n: return d
def factor(n, out=None):
    if out is None: out=[]
    if n==1: return out
    if isprime(n): out.append(n); return out
    for p in range(2,1000):
        if n%p==0:
            out.append(p); return factor(n//p,out)
    d=pollard(n); factor(d,out); factor(n//d,out); return out
def divisors_from(fs):
    fc={}
    for p in fs: fc[p]=fc.get(p,0)+1
    ds=[1]
    for p,e in fc.items():
        ds=[d*p**k for d in ds for k in range(e+1)]
    return ds

S = [p for p in range(2, SB+1) if isprime(p)]
BIG = [p for p in range(SB+1, 5000) if isprime(p)]

def pmin(q, r):
    a = pow((-r) % q, -1, q); P = a
    while P <= SB or not isprime(P): P += q
    return P

def mult_val(q, d): return sum(F(1, q*BIG[k]) for k in range(d))

def shapes(U, slack):
    res = []
    def rec(i, used, cur):
        if i == len(S):
            for nbb in range(0, slack-used+1): res.append((dict(cur), nbb))
            return
        q = S[i]
        if q in U:
            for m in range(0, slack-used+1):
                cur[q] = 1+m; rec(i+1, used+m, cur); del cur[q]
        else:
            rec(i+1, used, cur)
            for d in range(2, slack-used+1):
                cur[q] = d; rec(i+1, used+d, cur); del cur[q]
    rec(0, 0, {})
    return res

@lru_cache(maxsize=None)
def stars_for(A):
    """all primes P > SB with P | n(A)"""
    D = math.prod(A); n = sum(D//q for q in A)
    r = n
    for p in S:
        while r % p == 0: r //= p
    return tuple(sorted(set(factor(r))))

def solve_core(C, U, Z, g):
    """return (list of G solutions, list of unresolved notes, stats)"""
    slack = g - len(U)
    sols = []; unresolved = []; nshape = 0; nalive = 0
    if slack < 0: return sols, unresolved, (0,0)
    single = {q: F(1, q*pmin(q, U[q])) for q in U}
    for mult, nbb in shapes(U, slack):
        if (U.get(2,0) + mult.get(2,0)) % 2: continue            # parity at 2
        nshape += 1
        ub = sum((single[q] if mult[q]==1 else mult_val(q, mult[q])) if q in U else mult_val(q, mult[q]) for q in mult)
        ub += nbb * F(1, BIG[0]*BIG[1])
        if ub < Z: continue
        nalive += 1
        if nbb >= 2:
            unresolved.append((dict(mult), nbb)); continue
        W = sorted(mult)
        # candidate stars (complete neighbour set A subset of W)
        cands = []
        for k in range(2, len(W)+1):
            for A in itertools.combinations(W, k):
                for P in stars_for(A):
                    if all(mult[q] > 1 or (pow(P,-1,q) + U.get(q,0)) % q == 0 for q in A):
                        cands.append((P, A))
        def cover(need, resid, used, start_idx, out):
            # choose stars in canonical increasing index order to avoid duplicates
            if all(v == 0 for v in need.values()):
                out.append(list(used)); return
            for idx in range(start_idx, len(cands)):
                P, A = cands[idx]
                if any(need[q] == 0 for q in A): continue
                if any(P == u for u, _ in used): continue
                for q in A: need[q] -= 1
                used.append((P, A)); cover(need, resid, used, idx+1, out); used.pop()
                for q in A: need[q] += 1
        if nbb == 0:
            covers = []; cover(dict(mult), None, [], 0, covers)
            for cv in covers:
                G = sorted(q*P for P, A in cv for q in A)
                if sum(F(1,x) for x in G) == Z: sols.append(G)
        else:
            # one 2-component (P1 > P2 not required): attachments A1, A2 (nonempty sets),
            # multiplicities: A1 and A2 use one unit each of their elements; rest covered by stars.
            for k1 in range(1, len(W)+1):
                for A1 in itertools.combinations(W, k1):
                    for k2 in range(1, len(W)+1):
                        for A2 in itertools.combinations(W, k2):
                            if A1 > A2: continue          # unordered pair {P1,P2}: fix order of sets
                            need = dict(mult); ok = True
                            for q in A1: need[q] -= 1
                            for q in A2: need[q] -= 1
                            if any(v < 0 for v in need.values()): continue
                            covers = []; cover(need, None, [], 0, covers)
                            for cv in covers:
                                Zk = Z - sum(F(1, q*P) for P, A in cv for q in A)
                                if Zk <= 0: continue
                                b1 = math.prod(A1); b2 = math.prod(A2)
                                a1 = sum(b1//q for q in A1); a2 = sum(b2//q for q in A2)
                                t = Zk * b1 * b2
                                if t.denominator != 1: continue
                                t = t.numerator
                                N = b1*b2*(t + a1*a2)
                                for X in divisors_from(factor(N)):
                                    Y = N // X
                                    if (X + a1*b2) % t or (Y + a2*b1) % t: continue
                                    P1 = (X + a1*b2)//t; P2 = (Y + a2*b1)//t
                                    if P1 == P2 or P1 <= SB or P2 <= SB: continue
                                    if not (isprime(P1) and isprime(P2)): continue
                                    starPs = {P for P, A in cv}
                                    if P1 in starPs or P2 in starPs: continue
                                    G = sorted([q*P for P, A in cv for q in A] + [q*P1 for q in A1] + [q*P2 for q in A2] + [P1*P2])
                                    if len(set(G)) == len(G) and sum(F(1,x) for x in G) == Z: sols.append(G)
    # dedupe
    uniq = sorted(set(tuple(x) for x in sols))
    return [list(x) for x in uniq], unresolved, (nshape, nalive)

def parse_dump(path):
    for line in open(path):
        parts = line.split()
        if not parts: continue
        if parts[0] == 'S':
            C = [int(x) for x in parts[3:]]
            yield C, {}
        elif parts[0] == 'E':
            i = parts.index('U'); j = parts.index('C')
            U = {}
            for tok in parts[i+1:j]:
                q, r = tok.split(':'); U[int(q)] = int(r)
            C = [int(x) for x in parts[j+1:]]
            yield C, U

def fac2(n):
    for p in S:
        if n % p == 0: return p, n//p

def recompute(C):
    res = {}
    for n in C:
        p, q = fac2(n)
        res[p] = (res.get(p,0) + pow(q,-1,p)) % p
        res[q] = (res.get(q,0) + pow(p,-1,q)) % q
    return {q:r for q,r in res.items() if r}

if __name__ == '__main__':
    path = sys.argv[1]; KT = int(sys.argv[2]) if len(sys.argv) > 2 else 47
    allT = set(); nunres = 0; ncores = 0
    for C, Ud in parse_dump(path):
        ncores += 1
        U = recompute(C)
        assert U == Ud, (U, Ud)
        Z = 1 - sum(F(1,n) for n in C)
        if not U:
            if Z == 0: allT.add(tuple(sorted(C)))
            continue
        sols, unres, st = solve_core(C, U, Z, KT - len(C))
        for G in sols:
            T = tuple(sorted(C + G))
            assert sum(F(1,x) for x in T) == 1
            allT.add(T)
        if unres:
            nunres += 1; print("UNRESOLVED", len(C), U, unres[:3], flush=True)
    print("cores", ncores, "solutions", len(allT), "unresolved cores", nunres)
    for T in sorted(allT): print(len(T), ' '.join(map(str, T)))
