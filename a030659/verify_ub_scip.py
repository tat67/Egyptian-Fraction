"""Independent upper-bound check with SCIP (no shared code with the CP-SAT run).
Decides whether 1 = sum_{k in S} 1/k with S in [1..Mmax], |S| >= N is feasible.
Model: x_k binary; for every prime p <= Mmax, with p^E the largest power <= Mmax:
   sum_{p|k} x_k * p^(E-v_p(k)) * (k/p^v_p(k))^(-1) mod p^E  ==  p^E * z_p ,  z_p integer
(this is exactly "v_p(sum) >= 0"), plus W-Mmax <= sum x_k*floor(W/k) <= W, which with
integrality forces the sum to be exactly 1."""
import sys, time
from pyscipopt import Model, quicksum

def sieve(n):
    s=bytearray([1])*(n+1); s[0:2]=b"\0\0"
    for i in range(2,int(n**.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(n+1) if s[i]]

def feasible(Mmax, N, tlimit=3600, threads=1, seed=0):
    m=Model(); m.hideOutput()
    m.setParam("limits/time",tlimit)
    m.setParam("randomization/randomseedshift",seed)
    x={k:m.addVar(vtype="B",name=f"x{k}") for k in range(1,Mmax+1)}
    for p in sieve(Mmax):
        q=p
        while q*p<=Mmax: q*=p
        terms=[]
        for k in range(p,Mmax+1,p):
            v=0;r=k
            while r%p==0: r//=p;v+=1
            c=((q//p**v)*pow(r,-1,q))%q
            if c: terms.append((c,k))
        z=m.addVar(vtype="I",lb=0,ub=sum(c for c,_ in terms)//q)
        m.addCons(quicksum(c*x[k] for c,k in terms)==q*z)
    W=10**9
    s=quicksum((W//k)*x[k] for k in x)
    m.addCons(s<=W); m.addCons(s>=W-Mmax)
    m.addCons(quicksum(x.values())>=N)
    t=time.time(); m.optimize(); dt=time.time()-t
    st=m.getStatus(); sol=None
    if st=="optimal":
        sol=[k for k in x if m.getVal(x[k])>0.5]
    return st, dt, sol

if __name__=="__main__":
    Mmax=int(sys.argv[1]); N=int(sys.argv[2]); tl=float(sys.argv[3]) if len(sys.argv)>3 else 3600
    st,dt,sol=feasible(Mmax,N,tl)
    print(Mmax,N,st,f"{dt:.1f}s",(len(sol) if sol else ""),flush=True)
