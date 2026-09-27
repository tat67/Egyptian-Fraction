"""SCIP cross-check of the upper-bound claims f(v-1) < n_v, in parallel.
Usage: run_scip_parallel.py MMAX_LIMIT TIME_LIMIT PROCS.  Claims already settled
in ub_scip.txt are skipped; new results are appended to ub_scip.txt."""
import json, sys, os
from records import load_records
from multiprocessing import Pool
from verify_ub_scip import feasible

def job(c):
    Mmax,N,tl=c
    st,dt,_=feasible(Mmax,N,tl)
    return Mmax,N,st,dt

if __name__=="__main__":
    lim=int(sys.argv[1]); tl=float(sys.argv[2]); procs=int(sys.argv[3])
    recs=load_records()
    f={r["M"]:r["f"] for r in recs}
    a={}
    for M in sorted(f):
        for n in range(3,f[M]+1): a.setdefault(n,M)
    claims=[]; seen=set()
    for n in sorted(a):
        if a[n] not in seen: seen.add(a[n]); claims.append((a[n]-1,n))
    done=set()
    if os.path.exists("ub_scip.txt"):
        for l in open("ub_scip.txt"):
            M,N,st=l.split()[:3]
            if st=="infeasible": done.add((int(M),int(N)))
    todo=[(M,N,tl) for M,N in claims if M<=lim and (M,N) not in done]
    with Pool(procs) as pool, open("ub_scip.txt","a") as out:
        for M,N,st,dt in pool.imap_unordered(job,todo):
            out.write(f"{M} {N} {st} {dt:.2f}\n"); out.flush()
            if st!="infeasible": print("not settled",M,N,st,flush=True)
    print("done",flush=True)
