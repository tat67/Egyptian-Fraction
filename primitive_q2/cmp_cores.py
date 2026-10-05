import sys
from fractions import Fraction as F
from sympy import factorint
K=int(sys.argv[1]); Y=int(sys.argv[2]); hmax=int(sys.argv[3]); brute=sys.argv[4]; dump=sys.argv[5]
def U_and_ok(C, h):
    s=sum(F(1,n) for n in C); d=1-s
    if h==0: return (d==0), None
    if not (0<d<=F(h,Y+1)): return False, None
    U=factorint(d.denominator)
    Cs=set(C)
    # pairwise conflicts: core element dividing p^ep q^eq containing both p and q
    def confl(p,q):
        x=p
        while x<=p**U[p]:
            y=q
            while y<=q**U[q] and x*y<=Y:
                if x*y in Cs: return True
                y*=q
            x*=p
        return False
    ps=list(U)
    # chromatic number <= h ? brute force small
    import itertools
    n=len(ps)
    adj={(a,b):confl(ps[a],ps[b]) for a in range(n) for b in range(n) if a<b}
    def colorable(k):
        col=[-1]*n
        def rec(i):
            if i==n: return True
            for c in range(k):
                if all(not(adj[(min(i,j),max(i,j))] and col[j]==c) for j in range(i)):
                    col[i]=c
                    if rec(i+1): return True
                    col[i]=-1
            return False
        return rec(0)
    return colorable(h), (d.numerator,d.denominator)
bset=set()
for l in open(brute):
    C=tuple(sorted(map(int,l.split())))
    if not C: continue
    h=K-len(C)
    ok,_=U_and_ok(C,h)
    if ok: bset.add(C)
dset=set()
for l in open(dump):
    C=tuple(sorted(map(int,l.split('|')[0].split())))
    dset.add(C)
print("brute-force cores satisfying the leaf conditions:",len(bset)," solver cores:",len(dset)," equal:",bset==dset)
print("only brute:",len(bset-dset)," only solver:",len(dset-bset))
