"""Compute f(M) = max #terms in 1 = sum of distinct unit fractions 1/k, k <= M,
for M = 1..MMAX, with CP-SAT, plus a witness for every size n that first
becomes possible at M (so a(n) = M).  Results appended to f_values.jsonl."""
import sys, json, time, os
from fractions import Fraction
from ortools.sat.python import cp_model
from admissible import admissible, PR, vp

def build(M, adm):
    m=cp_model.CpModel()
    x={k:m.NewBoolVar(f"x{k}") for k in adm}
    W=10**12
    wsum=sum(x[k]*(W//k) for k in adm)
    m.Add(wsum <= W); m.Add(wsum >= W-M)
    for p in PR:
        if p>M: break
        E=0;q=1
        while q*p<=M: q*=p;E+=1
        terms=[]
        for k in adm:
            if k%p==0:
                e=vp(k,p); mm=k//p**e
                c=(p**(E-e)*pow(mm,-1,q))%q
                if c: terms.append((c,k))
        if not terms: continue
        z=m.NewIntVar(0,sum(c for c,_ in terms)//q,f"z{p}")
        m.Add(sum(c*x[k] for c,k in terms)==q*z)
    return m,x

def run(m, x, adm, tl, workers, hint=None):
    s=cp_model.CpSolver()
    s.parameters.max_time_in_seconds=tl
    s.parameters.num_workers=workers
    if hint:
        hs=set(hint)
        for k in adm: m.AddHint(x[k], k in hs)
    st=s.Solve(m)
    name=s.StatusName(st)
    sol=[k for k in adm if s.Value(x[k])] if st in (cp_model.OPTIMAL,cp_model.FEASIBLE) else None
    return name, sol

def check(sol, M, n):
    assert len(sol)==n==len(set(sol)) and max(sol)==M and sum(Fraction(1,k) for k in sol)==1

def main():
    MMAX=int(sys.argv[1]); workers=int(sys.argv[2]) if len(sys.argv)>2 else 4
    out=sys.argv[3] if len(sys.argv)>3 else "f_values.jsonl"
    done={}
    if os.path.exists(out):
        for line in open(out):
            r=json.loads(line); done[r["M"]]=r
    fprev=0; prev_sol=None
    for M in range(1,MMAX+1):
        if M in done:
            fprev=done[M]["f"]; continue
        t=time.time()
        adm=sorted(admissible(M))
        rec={"M":M,"admissible_M":M in adm}
        if M not in adm:
            rec.update(f=fprev, status="M_inadmissible", witnesses={})
        else:
            m,x=build(M,adm)
            m.Add(x[M]==1)
            m.Add(sum(x.values())>=fprev+1)
            m.Maximize(sum(x.values()))
            st,sol=run(m,x,adm,3600,workers)
            if st=="INFEASIBLE":
                rec.update(f=fprev,status="no_larger",witnesses={})
            elif st=="OPTIMAL":
                fM=len(sol); check(sol,M,fM)
                wit={str(fM):sol}
                for n in range(fprev+1,fM):
                    m2,x2=build(M,adm); m2.Add(x2[M]==1); m2.Add(sum(x2.values())==n)
                    st2,sol2=run(m2,x2,adm,3600,workers)
                    if st2 not in("OPTIMAL","FEASIBLE"):
                        rec.setdefault("gaps",[]).append([n,st2]); continue
                    check(sol2,M,n); wit[str(n)]=sol2
                rec.update(f=fM,status="OPTIMAL",witnesses=wit)
            else:
                print("UNRESOLVED",M,st,flush=True); rec.update(f=None,status=st,witnesses={})
                with open(out,"a") as fo: fo.write(json.dumps(rec)+"\n")
                sys.exit(1)
        rec["secs"]=round(time.time()-t,2)
        with open(out,"a") as fo: fo.write(json.dumps(rec)+"\n")
        if rec["f"]!=fprev: print(M,rec["f"],rec["status"],rec["secs"],flush=True)
        fprev=rec["f"]

if __name__=="__main__": main()
