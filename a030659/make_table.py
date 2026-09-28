"""Assemble the table of optimal expansions (k = 3..473) and cross-check it.

Columns: k | denominators of the optimal expansion | number of tied optimal sets.
  * optimal  = largest denominator a(k) (A030659), then the lexicographically
    smallest denominator list in increasing order (optimal_expansions.py, CP-SAT);
  * ties     = number of k-sets with largest denominator a(k) and sum 1
    (count_ties.cpp; count_ties_cpsat.py where the C++ counter was too slow).
    Where neither finished in the time allowed, the column shows a proven lower
    bound ">= N": solutions actually found (CP-SAT) or accounted for (C++).
Checks: every row is re-verified with Fractions; the smallest set reported by
the C++ enumerator / CP-SAT enumeration must equal the CP-SAT lexicographic one.
Writes optimal_expansions.txt, optimal_expansions.csv, optimal_expansions.tex.
"""
import glob, json, re
from fractions import Fraction

a = {}
for l in open("b030659.txt"):
    n, v = map(int, l.split()); a[n] = v
K = sorted(a)

lex = {}
for fn in sorted(glob.glob("expansions*.jsonl")):
    for l in open(fn):
        r = json.loads(l); lex[r["k"]] = r["denominators"]

ties, src, other_lexmin, partial_min = {}, {}, {}, {}
for l in open("ties_raw.txt"):                      # C++ counter
    m = re.match(r"(\d+) (\d+) count=(\d+) .*lexmin=(\S*)", l.strip())
    k, M, c, lm = int(m[1]), int(m[2]), int(m[3]), m[4]
    assert M == a[k]
    ties[k] = c; src[k] = "enumerator"
    if lm and lm != "SKIPPED": other_lexmin.setdefault(k, []).append(("enumerator", list(map(int, lm.split(",")))))
try:
    for l in open("ties_cpsat.txt"):                # CP-SAT enumeration (complete only if OPTIMAL)
        m = re.match(r"(\d+) (\d+) count=(\d+) status=(\w+) secs=\S+ lexmin=(\S*)", l.strip())
        k, M, c, st, lm = int(m[1]), int(m[2]), int(m[3]), m[4], m[5]
        if st != "OPTIMAL":
            partial_min.setdefault(k, []).append(list(map(int, lm.split(","))) if lm else None)
            continue
        if k in ties: assert ties[k] == c, (k, ties[k], c)
        else: ties[k] = c; src[k] = "cpsat"
        if lm: other_lexmin.setdefault(k, []).append(("cpsat", list(map(int, lm.split(",")))))
except FileNotFoundError:
    pass
lower = {}                                          # proven lower bounds where no exact count
for fn, pat in (("ties_partial.txt", r"(\d+) (\d+) count>=(\d+) PARTIAL"),
                ("ties_cpsat.txt", r"(\d+) (\d+) count=(\d+) status=(?!OPTIMAL)\w+")):
    try:
        for l in open(fn):
            m = re.match(pat, l.strip())
            if m:
                k, c = int(m[1]), int(m[3]); lower[k] = max(lower.get(k, 1), c)
    except FileNotFoundError:
        pass
for k in list(lower):
    if k in ties: assert ties[k] >= lower[k], k; del lower[k]
def tiecol(k):
    return str(ties[k]) if k in ties else (f">= {lower.get(k, 1)}")

missing_lex = [k for k in K if k not in lex]
missing_ties = [k for k in K if k not in ties]   # these get a lower bound
for k in K:
    if k not in lex: continue
    d = lex[k]
    assert len(d) == k == len(set(d)) and d == sorted(d) and max(d) == a[k]
    assert sum(Fraction(1, x) for x in d) == 1
    for who, lm in other_lexmin.get(k, []):
        assert lm == d, (k, who)
nx = sum(len(v) for v in other_lexmin.values())
for k, lst in partial_min.items():                   # a partial enumeration can never beat the optimum
    for lm in lst:
        if lm: assert lm >= lex[k], (k, "partial enumeration found a smaller set")

with open("optimal_expansions.txt", "w") as fo:
    fo.write("# k | number of tied optimal sets | denominators of the optimal expansion\n")
    fo.write("# optimal: largest denominator a(k) = A030659(k), then lexicographically smallest list\n")
    fo.write("# ties: exact number of k-sets with largest denominator a(k) and sum 1, or '>= N', a proven\n")
    fo.write(f"#   lower bound where the count could not be completed ({len(K)-len(missing_ties)} exact, {len(missing_ties)} lower bounds)\n")
    for k in K:
        fo.write(f"{k} | {tiecol(k)} | {', '.join(map(str, lex.get(k, [])))}\n")
with open("optimal_expansions.csv", "w") as fo:
    fo.write("k,max_denominator,tied_optimal_sets,denominators\n")
    for k in K:
        fo.write(f"{k},{a[k]},{tiecol(k)},\"{' '.join(map(str, lex.get(k, [])))}\"\n")
with open("optimal_expansions.tex", "w") as fo:
    fo.write("% Optimal expansions of 1 into k distinct unit fractions, k = 3..473.\n")
    fo.write("% Needs \\usepackage{longtable}.\n")
    fo.write("\\begin{longtable}{c|p{0.72\\textwidth}|r}\n")
    fo.write("$k$ & Denominators of an optimal expansion & Number of tied optimal sets \\\\\n\\hline\n\\endhead\n")
    sep = ",\\ "
    for k in K:
        tc = tiecol(k).replace(">= ", "$\\ge$ ")
        fo.write(f"{k} & {sep.join(map(str, lex.get(k, [])))} & {tc} " + "\\\\\n")
    fo.write("\\end{longtable}\n")

print(f"rows: {len(K)}; lexmin rows verified exactly: {len(K)-len(missing_lex)}; missing lexmin: {missing_lex}")
print(f"lower bounds only: {len(missing_ties)} k")
print(f"tie counts: {len(ties)} (enumerator {sum(1 for k in ties if src[k]=='enumerator')}, "
      f"CP-SAT {sum(1 for k in ties if src[k]=='cpsat')}); missing: {missing_ties}")
print(f"independent lexmin cross-checks passed: {nx} (over {len(other_lexmin)} k)")
print("unique optimum (1 tie):", sum(1 for k in ties if ties[k] == 1), "k;  max ties:",
      max(ties.values()) if ties else None, "at k =", max(ties, key=ties.get) if ties else None)
