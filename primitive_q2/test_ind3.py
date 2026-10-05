# Validation of the h = 3 path of complete_ind (raw mode) against brute force over all x1, x2,
# on random fractions 1/x1 + 1/x2 + 1/x3; run in pure AP mode and in pure divisor mode.
import random, subprocess
from fractions import Fraction as F
random.seed(11)
def isppow(n):
    for p in range(2,int(n**0.5)+1):
        if n%p==0:
            while n%p==0: n//=p
            return n==1
    return True
def rnd():
    n=1
    for p in [2,3,5,7,11,13]:
        if random.random()<0.45: n*=p**random.randint(1,2)
    return n
Y=12
cases=set()
while len(cases)<120:
    xs=sorted({rnd() for _ in range(3)})
    if len(xs)<3 or xs[0]<=Y: continue
    d=sum(F(1,x) for x in xs)
    if 3*d.denominator//d.numerator>3000: continue
    cases.add((d.numerator,d.denominator))
cases=sorted(cases)
def brute(a,b):
    out=[]
    d=F(a,b)
    for x1 in range(max(b//a+1,Y+1),3*b//a+1):
        if isppow(x1): continue
        r=d-F(1,x1)
        if r<=0: continue
        a2,b2=r.numerator,r.denominator
        for x2 in range(max(b2//a2+1,x1+1),2*b2//a2+1):
            n=a2*x2-b2
            if n>0 and (b2*x2)%n==0:
                x3=b2*x2//n
                if x3>x2:
                    H=[x1,x2,x3]
                    if all(H[j]%H[i] for i in range(3) for j in range(3) if i!=j): out.append(tuple(H))
    return out
exp=sorted((a,b)+h for a,b in cases for h in brute(a,b))
open('tc4.txt','w').write("".join(f" | h=3 {a}/{b}\n" for a,b in cases))
for lim in ['1000000000','0']:
    out=subprocess.run(['./complete_ind','tc4.txt',str(Y),'3',lim],capture_output=True,text=True).stdout
    got=[]
    for o in out.splitlines():
        if o.startswith('SOLUTION'):
            H=tuple(map(int,o.split()[1:])); d=sum(F(1,x) for x in H); got.append((d.numerator,d.denominator)+H)
    print("apLimit",lim,"cases",len(cases),"expected",len(exp),"got",len(got),"match",sorted(got)==exp)
    if sorted(got)!=exp:
        print(set(exp)-set(got)); print(set(got)-set(exp))
