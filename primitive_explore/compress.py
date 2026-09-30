import re, itertools
from fractions import Fraction
sols=[]
for fn in ['solutions47.txt','solutions48.txt']:
    for line in open(fn):
        m=re.match(r'#\s*\d+:\s*([\d ]+)',line)
        if m: sols.append(sorted(map(int,m.group(1).split())))
print(len(sols),"solutions")
def prim_ok(rest,new):
    for c in new:
        for a in rest:
            if a%c==0 or c%a==0: return False
    for a,b in itertools.combinations(new,2):
        if a%b==0 or b%a==0: return False
    return True
found=0
best=None
for T in sols:
    S=set(T)
    # 2 -> 1
    for a,b in itertools.combinations(T,2):
        num=a*b; den=a+b
        if num%den==0:
            c=num//den
            if c not in S and c>1:
                rest=S-{a,b}
                if prim_ok(rest,[c]):
                    found+=1
                    newT=sorted(rest|{c})
                    assert sum(Fraction(1,x) for x in newT)==1
                    if best is None or len(newT)<len(best): best=newT
                    print("2->1",len(T),"->",len(newT),(a,b),"->",c)
print("found",found)
print("best",best and len(best), best)
