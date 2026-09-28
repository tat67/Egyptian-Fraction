"""Fallback tie counter: enumerate every optimal expansion for k with CP-SAT.

A set counts if it has k distinct denominators, largest denominator a(k), and
reciprocal sum exactly 1 (same exact integer model as compute_f.py).  CP-SAT is
run with enumerate_all_solutions; the count is complete only if the solver
reports OPTIMAL (search space exhausted).  Every enumerated set is re-checked
with Fractions.  Used for the k where count_ties.cpp is too slow; those k have
few ties, so enumeration is cheap.

Usage: count_ties_cpsat.py TIME_LIMIT k1 k2 ...   (appends to ties_cpsat.txt)
"""
import sys, time
from fractions import Fraction
from ortools.sat.python import cp_model
from admissible import admissible
from compute_f import build


class Collector(cp_model.CpSolverSolutionCallback):
    def __init__(self, x, adm):
        super().__init__(); self.x = x; self.adm = adm; self.sols = []

    def on_solution_callback(self):
        self.sols.append(tuple(d for d in self.adm if self.Value(self.x[d])))


def count(M, k, tl):
    adm = sorted(admissible(M))
    m, x = build(M, adm)
    m.Add(x[M] == 1); m.Add(sum(x.values()) == k)
    s = cp_model.CpSolver()
    s.parameters.enumerate_all_solutions = True
    s.parameters.num_workers = 1
    s.parameters.max_time_in_seconds = tl
    cb = Collector(x, adm)
    st = s.StatusName(s.Solve(m, cb))
    sols = set(cb.sols)
    for sol in sols:
        assert len(sol) == k and max(sol) == M and sum(Fraction(1, d) for d in sol) == 1
    return st, len(sols), (min(sorted(t) for t in sols) if sols else [])


if __name__ == "__main__":
    tl = float(sys.argv[1])
    a = {}
    for l in open("b030659.txt"):
        n, v = map(int, l.split()); a[n] = v
    for k in map(int, sys.argv[2:]):
        t = time.time()
        st, n, lm = count(a[k], k, tl)
        line = f"{k} {a[k]} count={n} status={st} secs={time.time()-t:.1f} lexmin={','.join(map(str, lm))}"
        with open("ties_cpsat.txt", "a") as fo: fo.write(line + "\n")
        print(line[:120], flush=True)
