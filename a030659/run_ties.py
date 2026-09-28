"""Run count_ties for k in a range (parallel).  Exact results go to ties_raw.txt,
time-limited lower bounds ("count>=N PARTIAL") to ties_partial.txt.  A k already
counted exactly (by an earlier run or by count_ties_cpsat.py) is skipped.
Usage: run_ties.py BINARY KMIN KMAX PROCS TIME_LIMIT_S LOG2SLOTS"""
import subprocess, sys, os, re
from concurrent.futures import ThreadPoolExecutor, as_completed
binary,kmin,kmax,procs,tl,slots=sys.argv[1],*map(int,sys.argv[2:7])
a={}
for l in open("b030659.txt"):
    n,v=map(int,l.split()); a[n]=v
def exact_done():
    done=set()
    if os.path.exists("ties_raw.txt"):
        for l in open("ties_raw.txt"):
            if " count=" in l: done.add(int(l.split()[0]))
    if os.path.exists("ties_cpsat.txt"):
        for l in open("ties_cpsat.txt"):
            if "status=OPTIMAL" in l: done.add(int(l.split()[0]))
    return done
todo=[k for k in range(kmin,kmax+1) if k not in exact_done()]
def job(k):
    if k in exact_done(): return k,"skipped","",""
    try:
        r=subprocess.run([binary,str(k),str(a[k]),str(slots),str(tl)],capture_output=True,text=True,timeout=tl+600)
        return k, r.returncode, r.stdout.strip(), r.stderr.strip()
    except subprocess.TimeoutExpired:
        return k, "timeout", "", ""
with ThreadPoolExecutor(procs) as ex, open("ties_raw.txt","a") as out, open("ties_partial.txt","a") as part, open("ties_failed.txt","a") as bad:
    futs=[ex.submit(job,k) for k in todo]
    for fu in as_completed(futs):
        k,rc,o,e=fu.result()
        if rc=="skipped": pass
        elif rc==0 and " count=" in o: out.write(o+"\n"); out.flush()
        elif rc==0 and "PARTIAL" in o: part.write(o+"\n"); part.flush()
        else: bad.write(f"{k} {a[k]} rc={rc} {e[:200]}\n"); bad.flush()
        print(k,rc,o[:60],flush=True)
