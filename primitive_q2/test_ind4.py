# Validation of the h = 4 path of complete_ind (raw mode: empty core) against an exhaustive search over
# all x1 < x2 (each in its full range), the last two terms by enumerating ALL divisors of b2^2 (sympy):
# 1/x3 + 1/x4 = a2/b2 iff d = a2*x3 - b2 divides b2^2 (d < b2).  Random fractions 1/x1+1/x2+1/x3+1/x4;
# rules as in complete_ind: every x_i > Y, x1 and x2 not prime powers, H primitive.
import random, subprocess
from sympy import divisors
from fractions import Fraction as F
random.seed(5)
def isppow(n):
    for p in range(2,int(n**0.5)+1):
        if n%p==0:
            while n%p==0: n//=p
            return n==1
    return True
def rnd():
    n=1
    for p in [2,3,5,7,11]:
        if random.random()<0.5: n*=p**random.randint(1,2)
    return n
Y=6
cases=set()
while len(cases)<20:
    xs=sorted({rnd() for _ in range(4)})
    if len(xs)<4 or xs[0]<=Y: continue
    d=sum(F(1,x) for x in xs)
    if 4*d.denominator//d.numerator>400: continue
    a,b=d.numerator,d.denominator
    # keep only cases whose exhaustive brute force (sum over x1 of the x2 range) is affordable in Python
    cost=0
    for x1 in range(max(b//a+1,Y+1),4*b//a+1):
        r1=d-F(1,x1)
        if r1>0: cost+=3*r1.denominator//r1.numerator
    if cost>20000: continue
    cases.add((a,b))
cases=sorted(cases)
def brute(a,b):
    out=[]; d=F(a,b)
    for x1 in range(max(b//a+1,Y+1),4*b//a+1):
        if isppow(x1): continue
        r1=d-F(1,x1)
        if r1<=0: continue
        for x2 in range(max(r1.denominator//r1.numerator+1,x1+1),3*r1.denominator//r1.numerator+1):
            if isppow(x2): continue
            r2=r1-F(1,x2)
            if r2<=0: continue
            a2,b2=r2.numerator,r2.denominator
            for dv in divisors(b2*b2):
                if dv>=b2: break
                if (b2+dv)%a2 or (b2+b2*b2//dv)%a2: continue
                x3=(b2+dv)//a2; x4=(b2+b2*b2//dv)//a2
                if x3>x2 and x4>x3:
                    H=[x1,x2,x3,x4]
                    if all(H[j]%H[i] for i in range(4) for j in range(4) if i!=j): out.append(tuple(H))
    return out
exp=sorted((a,b)+h for a,b in cases for h in brute(a,b))
open('tc5.txt','w').write("".join(f" | h=4 {a}/{b}\n" for a,b in cases))
for lim in ['1000000000','0']:
    out=subprocess.run(['./complete_ind','tc5.txt',str(Y),'4',lim],capture_output=True,text=True).stdout
    got=[]
    for o in out.splitlines():
        if o.startswith('SOLUTION'):
            H=tuple(map(int,o.split()[1:])); d=sum(F(1,x) for x in H); got.append((d.numerator,d.denominator)+H)
    print("apLimit",lim,"cases",len(cases),"expected",len(exp),"got",len(got),"match",sorted(got)==exp)
