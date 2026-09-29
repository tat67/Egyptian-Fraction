"""Independent check of a lower-bound certificate written by `a101877 prove ... cert=FILE`.

A certificate claims: no set S of distinct integers in [1..K] has sum_{x in S} 1/x = n.
It lists integer weights lam[p][x] (scale 2^F) for pairs (prime p, x in U with p | x).
This script recomputes everything else from scratch (it shares no code with the C++ program)
and uses integer arithmetic only:

  1. U = candidate set: repeatedly drop x if for some prime p | x no subset of the remaining
     multiples of p containing x has res_p == 0 (mod p^E).  Every S with integral sum lies in U.
  2. For every x in U: sum over p of lam[p][x] <= floor(2^F / x).
  3. R_p = res_p(U).  For every prime p in the certificate: m_p = min over subsets T of the
     multiples of p in U with res_p(T) == R_p of sum_{x in T} lam[p][x]  (plain DP mod p^E).
  4. Dhi = sum_{x in U} ceil(2^F / x) - n * 2^F  (>= 2^F * Delta).
  5. Accept iff sum_p m_p > Dhi.
Why this proves the claim: if S had sum n, then E = U \\ S satisfies res_p(E) == R_p for all p
and sum_E 1/x = Delta, but 2^F * sum_E 1/x >= sum_x in E sum_p lam[p][x] >= sum_p m_p > Dhi >= 2^F Delta.
With --forced-in K the claim is: no such S contains K (K may not be excluded, so it is
skipped in every per-prime minimum); this is what `a101877 witness n K cert=FILE` proves.
Usage: verify_cert.py cert_file [--forced-in K]
"""
import sys, math
import numpy as np
from verify_witness import candidates, primes_upto

def main(path, forced=None):
    with open(path) as fh:
        lines=[l for l in fh if not l.startswith("#")]
    n,K,F=map(int,lines[0].split())
    lam={}
    for l in lines[1:]:
        p,x,v=l.split(); lam.setdefault(int(p),{})[int(x)]=int(v)
    U=candidates(K); inU=bytearray(K+1)
    for x in U: inU[x]=1
    ONE=1<<F
    # 2. split condition
    tot={}
    for p,d in lam.items():
        for x,v in d.items():
            assert x%p==0 and inU[x], f"bad pair {p},{x}"
            tot[x]=tot.get(x,0)+v
    for x,v in tot.items():
        assert v <= ONE//x, f"split exceeds floor(2^F/x) at x={x}"
    # 3. per-prime minima
    P=set(primes_upto(K)); INF=1<<62; LB=0
    for p,d in lam.items():
        assert p in P
        q=1
        while q*p<=K: q*=p
        mult=[x for x in range(p,K+1,p) if inU[x]]
        def coef(x):
            v=0;r=x
            while r%p==0: r//=p; v+=1
            return (q//p**v)*pow(r,-1,q)%q
        cs=[coef(x) for x in mult]
        R=sum(cs)%q
        best=np.full(q,INF,dtype=np.int64); best[0]=0
        for x,c in zip(mult,cs):
            if forced is not None and x==forced: continue      # x must stay in S: never in T
            w=d.get(x,0)
            shifted=np.roll(best,c)
            cand=np.where(shifted>=INF//2, INF, shifted+w)
            best=np.minimum(best,cand)
        m=int(best[R]); assert m<INF//2, f"prime {p}: residue unreachable"
        LB+=m
    # 4. Delta bound
    Dhi=sum(-(-ONE//x) for x in U)-n*ONE
    ok=LB>Dhi
    if forced is not None: assert inU[forced]
    claim = f"no S in [1..K] with {forced} in S has sum n" if forced is not None else "no S in [1..K] has sum n"
    print(f"certificate n={n} K={K}: |U|={len(U)} primes={len(lam)} LB-Dhi={LB-Dhi}  -> {'VALID: '+claim if ok else 'NOT a proof'}")
    return ok

if __name__=="__main__":
    forced=None
    if len(sys.argv)>3 and sys.argv[2]=="--forced-in": forced=int(sys.argv[3])
    sys.exit(0 if main(sys.argv[1],forced) else 1)
