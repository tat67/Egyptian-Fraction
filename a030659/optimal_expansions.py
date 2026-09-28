"""For each k, the canonical optimal expansion of 1 into k distinct unit fractions:
  1. the largest denominator is as small as possible (= a(k), A030659);
  2. among those, the denominator list in increasing order is lexicographically
     smallest (smallest d_1, then smallest d_2, ...).
Criterion 2 is optimised exactly with CP-SAT, window by window: a window of W
consecutive undecided candidates gets weights 2^(W-1), ..., 2^0 (smaller
denominator = larger weight), which is exactly lexicographic order inside the
window; the optimum is fixed and the next window is solved.
Usage: optimal_expansions.py KMIN KMAX [workers] -> appends to expansions.jsonl"""
import sys, json, time, os
from fractions import Fraction
from ortools.sat.python import cp_model
from admissible import admissible
from compute_f import build

W=56

def solve(m, workers, tl=1800):
    s=cp_model.CpSolver()
    s.parameters.max_time_in_seconds=tl
    s.parameters.num_workers=workers
    st=s.Solve(m)
    return s, s.StatusName(st)

def lexmin(M, k, workers=4, hint=None):
    adm=sorted(admissible(M))
    fixed={M:1}
    for d in adm:
        if d>M: fixed[d]=0
    order=[d for d in adm if d<M]
    i=0; nsolves=0; cur=hint
    while i<len(order):
        chosen=sum(v for v in fixed.values())
        if chosen==k:                     # everything else must be 0
            for d in order[i:]: fixed[d]=0
            break
        win=order[i:i+W]
        m,x=build(M,adm)
        m.Add(sum(x.values())==k)
        for d,v in fixed.items(): m.Add(x[d]==v)
        m.Maximize(sum((1<<(len(win)-1-j))*x[d] for j,d in enumerate(win)))
        if cur:
            cs=set(cur)
            for d in adm: m.AddHint(x[d], d in cs)
        s,st=solve(m,workers); nsolves+=1
        if st!="OPTIMAL": raise RuntimeError(f"M={M} k={k} window@{win[0]}: {st}")
        cur=[d for d in adm if s.Value(x[d])]
        for d in win: fixed[d]=s.Value(x[d])
        i+=len(win)
    sol=sorted(d for d,v in fixed.items() if v)
    assert len(sol)==k and max(sol)==M and sum(Fraction(1,d) for d in sol)==1
    return sol, nsolves

if __name__=="__main__":
    kmin,kmax=int(sys.argv[1]),int(sys.argv[2]); workers=int(sys.argv[3]) if len(sys.argv)>3 else 4
    out=sys.argv[4] if len(sys.argv)>4 else "expansions.jsonl"
    a={}
    for l in open("b030659.txt"):
        n,v=map(int,l.split()); a[n]=v
    done=set()
    if os.path.exists(out):
        for l in open(out): done.add(json.loads(l)["k"])
    wit={}
    for l in open("witnesses.txt"):
        if l.startswith("#"): continue
        h,ds=l.split(":"); wit[int(h.split()[0])]=list(map(int,ds.split()))
    for k in range(kmin,kmax+1):
        if k in done: continue
        t=time.time()
        sol,ns=lexmin(a[k],k,workers,hint=wit[k])
        rec={"k":k,"max":a[k],"denominators":sol,"solves":ns,"secs":round(time.time()-t,2)}
        with open(out,"a") as fo: fo.write(json.dumps(rec)+"\n")
        print(k,a[k],ns,rec["secs"],sol[:6],"...",flush=True)
