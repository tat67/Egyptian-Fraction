"""Admissibility prefilter used by compute_f.py (a sound relaxation).

k <= M is dropped if for some prime p | k there is no set K of multiples of p in
[1..M] with k in K and v_p(sum_{K} 1/j) >= 0.  Any S with sum_{S} 1/j = 1 has
S & pZ of that form for every p, so dropped numbers never occur in a solution.
The test is a subset-sum over residues mod p^E (p^E the largest power <= M)."""

def primes_upto(n):
    s = bytearray([1])*(n+1); s[0:2]=b'\0\0'
    for i in range(2,int(n**.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(n+1) if s[i]]

PR = primes_upto(2000)

def vp(k,p):
    e=0
    while k%p==0: k//=p; e+=1
    return e

def admissible_prime(M, p):
    """set of multiples k of p (k<=M) lying in some K subset of multiples of p with v_p(sum 1/K)>=0"""
    E=0; q=1
    while q*p<=M: q*=p; E+=1
    mod=q
    ks=[k for k in range(p,M+1,p)]
    c={}
    for k in ks:
        e=vp(k,p); m=k//p**e
        c[k]=(p**(E-e)*pow(m,-1,mod))%mod
    # reachable residues using bitmask ints (cyclic shift)
    full=(1<<mod)-1
    def shift(bits,s):
        return ((bits<<s)|(bits>>(mod-s)))&full if s else bits
    n=len(ks)
    pre=[1]*(n+1)
    for i,k in enumerate(ks):
        pre[i+1]=pre[i]|shift(pre[i],c[k])
    suf=[1]*(n+1)
    for i in range(n-1,-1,-1):
        suf[i]=suf[i+1]|shift(suf[i+1],c[ks[i]])
    ok=set()
    for i,k in enumerate(ks):
        # need r1 in pre[i], r2 in suf[i+1] with r1+r2+c = 0
        need=(-c[k])%mod
        a=pre[i]; b=suf[i+1]
        # exists r1: r1 in a and need-r1 in b
        found=False
        x=a
        while x:
            low=x&-x; r1=low.bit_length()-1; x^=low
            if (b>>((need-r1)%mod))&1: found=True;break
        if found: ok.add(k)
    return ok

def admissible(M):
    adm=set(range(1,M+1))
    for p in PR:
        if p>M: break
        ok=admissible_prime(M,p)
        for k in range(p,M+1,p):
            if k not in ok: adm.discard(k)
    return adm
