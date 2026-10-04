# Validation of the two-term solver of ind2.h (via complete_ind, raw mode: empty core) against brute force,
# on random fractions 1/x + 1/y with many solutions; run in pure AP mode and in pure divisor mode.
import random, subprocess
from fractions import Fraction as F
from math import gcd
random.seed(7)
cases=[]
for _ in range(1500):
    # numbers built from small primes so that b has many divisors (many solutions)
    def rnd():
        n=1
        for p in [2,3,5,7,11,13,17,19,23]:
            if random.random()<0.35: n*=p**random.randint(1,2)
        return n
    x,y=rnd()*random.choice([1,1,29,31]),rnd()*random.choice([1,37,41])
    if x==y or x<2 or y<2: continue
    d=F(1,x)+F(1,y); cases.append((d.numerator,d.denominator))
Y=10
open('tc3.txt','w').write("".join(f" | h=2 {a}/{b}\n" for a,b in cases))
def brute(a,b):
    out=[]
    for x in range(max(b//a+1,Y+1), 2*b//a+1):
        n=a*x-b
        if n>0 and (b*x)%n==0:
            y=b*x//n
            if y>x and y%x: out.append((x,y))
    return out
ok=[c for c in cases if 2*c[1]//c[0] < 3_000_000]
exp=sorted((a,b,x,y) for a,b in ok for x,y in brute(a,b))
for lim in ['100000000','0']:
    open('tc3.txt','w').write("".join(f" | h=2 {a}/{b}\n" for a,b in ok))
    out=subprocess.run(['./complete_ind','tc3.txt',str(Y),'2',lim],capture_output=True,text=True).stdout
    # map solutions back: each line's solutions printed in order; recompute a/b from x,y
    got=[]
    for o in out.splitlines():
        if o.startswith('SOLUTION'):
            x,y=map(int,o.split()[1:]); d=F(1,x)+F(1,y); got.append((d.numerator,d.denominator,x,y))
    print("limit",lim,"cases",len(ok),"expected",len(exp),"got",len(got),"match",sorted(got)==exp, out.splitlines()[-1])
