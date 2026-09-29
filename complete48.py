"""Independent Python re-solution of Step 2 for the cores dumped by semiprime48 (--dump).

Uses the exact-fraction completion routine of complete47.py (its own shape enumeration, star
factoring without a size cap, exact covers, divisor equation for one big-big edge; shapes with
two or more big-big edges are reported as unresolved) with the budget given on the command line,
and runs it in parallel over chunks of the dump.

Usage: python3 complete48.py cores48.txt [KT=48] [processes=4]
Prints the number of cores, the solutions found (every T with |T| <= KT and sum 1), grouped by
size, and the number of unresolved cores.
"""
import sys, os
from fractions import Fraction as F
from multiprocessing import Pool

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from complete47 import solve_core, recompute


def parse_line(line):
    parts = line.split()
    i = parts.index('U'); j = parts.index('C')
    U = {}
    for tok in parts[i + 1:j]:
        q, r = tok.split(':'); U[int(q)] = int(r)
    return [int(x) for x in parts[j + 1:]], U


def work(args):
    lines, KT = args
    sols = set(); unresolved = []; ncores = 0
    for line in lines:
        if not line.strip():
            continue
        C, Ud = parse_line(line)
        ncores += 1
        U = recompute(C)
        assert U == Ud, (U, Ud)
        Z = 1 - sum(F(1, n) for n in C)
        if not U:
            if Z == 0:
                sols.add(tuple(sorted(C)))
            continue
        found, unres, _ = solve_core(C, U, Z, KT - len(C))
        for G in found:
            T = tuple(sorted(C + G))
            assert len(set(T)) == len(T) and sum(F(1, x) for x in T) == 1
            sols.add(T)
        if unres:
            unresolved.append((len(C), U, unres[:3]))
    return ncores, sols, unresolved


if __name__ == '__main__':
    path = sys.argv[1]
    KT = int(sys.argv[2]) if len(sys.argv) > 2 else 48
    procs = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    lines = open(path).read().splitlines()
    chunks = [(lines[k::procs * 8], KT) for k in range(procs * 8)]
    allT = set(); nunres = 0; ncores = 0
    with Pool(procs) as pool:
        for nc, sols, unres in pool.imap_unordered(work, chunks):
            ncores += nc; allT |= sols; nunres += len(unres)
            for u in unres:
                print("UNRESOLVED", u, flush=True)
    bysize = {}
    for T in allT:
        bysize.setdefault(len(T), []).append(T)
    print("cores", ncores, "solutions", len(allT), "unresolved cores", nunres)
    for k in sorted(bysize):
        print("solutions with |T| = %d: %d" % (k, len(bysize[k])))
    for T in sorted(allT, key=lambda T: (len(T), T)):
        print(len(T), ' '.join(map(str, T)))
