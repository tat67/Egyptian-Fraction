"""From f_values.jsonl: derive a(n), write b030659.txt (OEIS b-file format with the
header line of the OEIS b-file, n = 3..473) and f_table.txt (M, f(M)), and compare with the existing OEIS terms (oeis_b030659_original.txt)."""
import json
from records import load_records
recs=load_records()
f={r["M"]:r["f"] for r in recs}
assert sorted(f)==list(range(1,1001)) and all(r["status"] in ("OPTIMAL","no_larger","M_inadmissible") for r in recs)
a={}
for M in range(1,1001):
    for n in range(3,f[M]+1): a.setdefault(n,M)
N=max(a); assert sorted(a)==list(range(3,N+1))
with open("b030659.txt","w") as fo:
    fo.write("# A030659 (b-file synthesized from sequence entry)\n")   # same header line as the OEIS b-file
    for n in range(3,N+1): fo.write(f"{n} {a[n]}\n")
with open("f_table.txt","w") as fo:
    fo.write("# M f(M): max number of distinct unit fractions 1/k, k <= M, summing to 1\n")
    for M in range(1,1001): fo.write(f"{M} {f[M]}\n")
orig={}
for l in open("oeis_b030659_original.txt"):
    if l.strip() and not l.startswith("#"):
        n,v=map(int,l.split()); orig[n]=v
print(f"a(n) for n = 3..{N}; a({N}) = {a[N]}; f(1000) = {f[1000]}, so a({N+1}) > 1000")
diff=[(n,orig[n],a[n]) for n in sorted(orig) if orig[n]!=a[n]]
print(f"existing OEIS terms n = {min(orig)}..{max(orig)} ({len(orig)} terms) reproduced:", not diff, diff or "")
