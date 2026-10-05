"""noncandidates.py K1 K2 ... : independent check (Python, exact integers) of whether K can be the
largest element of a set of distinct integers with integral reciprocal sum.  It recomputes the
candidate set U of [1..K] with verify_witness.candidates (the iterated per-prime subset-sum test,
Rule 2) and reports whether K is in U.  If K is not in U, no set with max(S) = K has an integral
sum, so K cannot be a(n) for any n.  Shares no code with the C++ solvers."""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from verify_witness import candidates
for K in map(int, sys.argv[1:]):
    t = time.time(); U = set(candidates(K))
    print(f"K={K}: |U|={len(U)}  K in U: {K in U}  -> "
          f"{'K cannot be the maximum (not a candidate)' if K not in U else 'K is a candidate'}  ({time.time()-t:.0f} s)", flush=True)
