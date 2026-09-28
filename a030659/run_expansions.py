"""Run optimal_expansions.lexmin for k = KMIN..KMAX with k % STEP == OFFSET
(largest k first; a k whose window search does not finish is logged and skipped)."""
import sys, json, os, time
from optimal_expansions import lexmin
kmin,kmax,step,off,workers,out=map(str,sys.argv[1:7])
kmin,kmax,step,off,workers=map(int,(kmin,kmax,step,off,workers))
a={}
for l in open("b030659.txt"):
    n,v=map(int,l.split()); a[n]=v
wit={}
for l in open("witnesses.txt"):
    if l.startswith("#"): continue
    h,ds=l.split(":"); wit[int(h.split()[0])]=list(map(int,ds.split()))
done=set()
if os.path.exists(out):
    for l in open(out): done.add(json.loads(l)["k"])
for k in range(kmax,kmin-1,-1):          # largest first
    if k%step!=off or k in done: continue
    t=time.time()
    try:
        sol,ns=lexmin(a[k],k,workers,hint=wit[k])
    except RuntimeError as e:
        print("FAILED",k,e,flush=True); continue
    with open(out,"a") as fo:
        fo.write(json.dumps({"k":k,"max":a[k],"denominators":sol,"solves":ns,"secs":round(time.time()-t,2)})+"\n")
    print(k,ns,round(time.time()-t,2),flush=True)
