import re, itertools, sys
from fractions import Fraction
from math import gcd
sols=[]
for fn in ['solutions47.txt','solutions48.txt']:
    for line in open(fn):
        m=re.match(r'#\s*\d+:\s*([\d ]+)',line)
        if m: sols.append(sorted(map(int,m.group(1).split())))
# also 47-term results of 2->1 compressions of the 48-term ones
extra=[]
for T in sols:
    if len(T)!=48: continue
    S=set(T)
    for a,b in itertools.combinations(T,2):
        if (a*b)%(a+b)==0:
            c=a*b//(a+b)
            if c not in S and all(x%c and c%x for x in S-{a,b}): extra.append(sorted((S-{a,b})|{c}))
T47=[T for T in sols if len(T)==47]+extra
print(len(T47),"47-term sets")
def ok(rest,new):
    for c in new:
        for a in rest:
            if a%c==0 or c%a==0: return False
    for a,b in itertools.combinations(new,2):
        if a%b==0 or b%a==0: return False
    return len(set(new))==len(new)
found=[]
for T in T47:
    S=set(T)
    for a,b,c in itertools.combinations(T,3):
        # q = 1/a+1/b+1/c = N/Dq
        N=b*c+a*c+a*b; Dq=a*b*c; g=gcd(N,Dq); N//=g; Dq//=g
        lo=Dq//N+1; hi=(2*Dq)//N
        if hi-lo>200000: continue
        for x in range(lo,hi+1):
            den=N*x-Dq
            if den<=0: continue
            if (x*Dq)%den==0:
                y=x*Dq//den
                if y<x: continue
                rest=S-{a,b,c}
                if x in rest or y in rest: continue
                if ok(rest,[x,y]):
                    newT=sorted(rest|{x,y})
                    assert sum(Fraction(1,t) for t in newT)==1
                    found.append(newT); print("3->2:",(a,b,c),"->",(x,y),"size",len(newT),flush=True)
print("found",len(found))
