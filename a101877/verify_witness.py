"""Exact check of a witness given as the exclusion set E: recompute the candidate set U
(iterated per-prime subset-sum test, as in the C++ program), set S = U minus E, and verify with
Python Fractions that S consists of distinct positive integers, max(S) = K and sum 1/x = n.
Usage: verify_witness.py n K E_comma_list   or   verify_witness.py n K --S S_comma_list"""
import sys, math
from fractions import Fraction
def primes_upto(n):
    s=bytearray([1])*(n+1); s[0:2]=b"\0\0"
    for i in range(2,math.isqrt(n)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(n+1) if s[i]]
def candidates(K):
    P=primes_upto(K); adm=[False]+[True]*K
    changed=True
    while changed:
        changed=False
        for p in P:
            q=1
            while q*p<=K: q*=p
            ks=[d for d in range(p,K+1,p) if adm[d]]
            def coef(d):
                v=0;r=d
                while r%p==0: r//=p; v+=1
                return (q//p**v)*pow(r,-1,q)%q
            cs=[coef(d) for d in ks]; m=len(ks)
            if not m: continue
            full=(1<<q)-1
            def rot(b,s): return ((b<<s)|(b>>(q-s)))&full if s else b
            pre=[1]*(m+1)
            for i in range(m): pre[i+1]=pre[i]|rot(pre[i],cs[i])
            suf=[1]*(m+1)
            for i in range(m-1,-1,-1): suf[i]=suf[i+1]|rot(suf[i+1],cs[i])
            for i in range(m):
                need=(q-cs[i])%q; a=pre[i]; b=suf[i+1]; ok=False
                while a:
                    low=a&-a; r1=low.bit_length()-1; a^=low
                    if (b>>((need-r1)%q))&1: ok=True; break
                if not ok: adm[ks[i]]=False; changed=True
    return [x for x in range(1,K+1) if adm[x]]
def check(n,K,S):
    assert len(S)==len(set(S)) and min(S)>=1 and max(S)==K, "set/max check failed"
    tot=sum(Fraction(1,x) for x in S)
    return tot==n
if __name__=="__main__":
    n=int(sys.argv[1]); K=int(sys.argv[2])
    if sys.argv[3]=="--S": S=sorted(map(int,sys.argv[4].split(",")))
    else:
        E=set(map(int,sys.argv[3].split(","))) if sys.argv[3] else set()
        S=[x for x in candidates(K) if x not in E]
    ok=check(n,K,S)
    print(f"n={n} K={K} |S|={len(S)} max={max(S)} sum==n exactly: {ok}")
