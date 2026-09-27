"""Exact, solver-free check of every witness: for each n, the stored set has n
distinct positive integers, its maximum is the claimed a(n), and the sum of
reciprocals is exactly 1 (Python Fractions).  Writes witnesses.txt."""
import json
from records import load_records
from fractions import Fraction
recs=load_records()
f={r["M"]:r["f"] for r in recs}
wit={}
for r in recs:
    for n,s in r["witnesses"].items():
        wit[int(n)]=(r["M"],s)
a={}
for M in sorted(f):
    for n in range(3,f[M]+1): a.setdefault(n,M)
N=max(a)
ok=True
with open("witnesses.txt","w") as fo:
    fo.write("# n a(n) : denominators of 1 = sum 1/d over n distinct d, max d = a(n)\n")
    for n in range(3,N+1):
        M,s=wit[n]
        good=(M==a[n] and len(s)==n and len(set(s))==n and min(s)>=1 and max(s)==M
              and sum(Fraction(1,d) for d in s)==1)
        ok&=good
        fo.write(f"{n} {M} : {' '.join(map(str,sorted(s)))}\n")
print("n range 3 ..",N,"; all witnesses exact and consistent:",ok)
print("f nondecreasing:",all(f[M]<=f[M+1] for M in range(1,max(f))))
