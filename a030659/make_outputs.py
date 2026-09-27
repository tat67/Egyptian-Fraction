"""From f_values.jsonl: derive a(n), write b030659.txt (OEIS b-file format,
n = 3..473) and f_table.txt (M, f(M)), and compare with the OEIS data section."""
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
    for n in range(3,N+1): fo.write(f"{n} {a[n]}\n")
with open("f_table.txt","w") as fo:
    fo.write("# M f(M): max number of distinct unit fractions 1/k, k <= M, summing to 1\n")
    for M in range(1,1001): fo.write(f"{M} {f[M]}\n")
oeis=[6,12,15,15,18,20,24,24,28,30,33,33,35,36,40,42,48,52,52,54,55,55,56,60,63,72,75,75,
      76,76,77,78,80,85,85,88,90,95,96,96,100,102,104,104,108,110,114,115,115,119,119,120,
      126,130,132,135,138,143,144,144]
print(f"a(n) for n = 3..{N}; a({N}) = {a[N]}; f(1000) = {f[1000]}, so a({N+1}) > 1000")
print("OEIS data section (n = 3..62) reproduced:", [a[n] for n in range(3,63)]==oeis)
