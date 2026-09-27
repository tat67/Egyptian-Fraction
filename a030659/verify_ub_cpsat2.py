"""Second, independently written CP-SAT model for the upper bounds.
Differences from compute_f.py: no admissibility prefilter (all k in [1..Mmax]),
p-adic conditions via AddModuloEquality instead of an integer multiplier,
rounded-UP scaled sum, feasibility form |S| >= N with nothing forced.
Claim checked: no S in [1..Mmax] with |S| >= N and sum 1/k = 1."""
import sys, json, time
from records import load_records
from ortools.sat.python import cp_model

def sieve(n):
    s=bytearray([1])*(n+1); s[0:2]=b"\0\0"
    for i in range(2,int(n**.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(n+1) if s[i]]

def status(Mmax, N, tl=3600, workers=4, seed=1):
    m=cp_model.CpModel()
    x=[None]+[m.NewBoolVar(f"x{k}") for k in range(1,Mmax+1)]
    for p in sieve(Mmax):
        q=p
        while q*p<=Mmax: q*=p
        coef=[]
        for k in range(p,Mmax+1,p):
            v=0;r=k
            while r%p==0: r//=p;v+=1
            coef.append(((q//p**v)*pow(r,-1,q)%q, k))
        tot=sum(c for c,_ in coef)
        s=m.NewIntVar(0,tot,f"s{p}")
        m.Add(s==sum(c*x[k] for c,k in coef))
        zero=m.NewConstant(0)
        m.AddModuloEquality(zero, s, q)
    W=2**40
    up=sum(((W+k-1)//k)*x[k] for k in range(1,Mmax+1))   # >= W*sum
    m.Add(up>=W); m.Add(up<=W+Mmax)
    m.Add(sum(x[1:])>=N)
    sol=cp_model.CpSolver()
    sol.parameters.max_time_in_seconds=tl
    sol.parameters.num_workers=workers
    sol.parameters.random_seed=seed
    st=sol.Solve(m)
    return sol.StatusName(st)

if __name__=="__main__":
    recs=load_records()
    f={r["M"]:r["f"] for r in recs}
    a={}
    for M in sorted(f):
        for n in range(3,f[M]+1): a.setdefault(n,M)
    claims=[]  # (Mmax, N): claim f(Mmax) < N
    seen=set()
    for n in sorted(a):
        v=a[n]
        if v not in seen:
            seen.add(v); claims.append((v-1,n))
    claims.append((1000,max(a)+1))
    out=open("ub_cpsat2.txt","w")
    bad=0; t0=time.time()
    for Mmax,N in claims:
        t=time.time(); st=status(Mmax,N)
        out.write(f"{Mmax} {N} {st} {time.time()-t:.2f}\n"); out.flush()
        if st!="INFEASIBLE": bad+=1; print("NOT PROVED",Mmax,N,st,flush=True)
    print(len(claims),"claims; not proved:",bad,"; secs",round(time.time()-t0),flush=True)
