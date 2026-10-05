#!/usr/bin/env python3
"""Enumerate all primitive Egyptian fractions of 1 with exactly K terms and all elements <= X.

Usage (from the repository root):
  python3 primitive_explore/enum_q2.py X K workers [seconds_per_solve] [outfile] [options]
  options:  cut=A,N,Y,H   Lagrangian cuts (see 3b): A = threshold, N = the integer printed by
                          "q2exact K A" as "sigma*1e12 <= N", Y and H = its "Y" and "hmax"
            known=FILE    lines of known solutions: verified exactly, recorded, and excluded first
            mem=MB        CP-SAT memory limit (the solver then stops with UNKNOWN instead of OOM)
  e.g.  python3 primitive_explore/enum_q2.py 100000 44 2 0 out.txt cut=145,44450130017,1829,6 known=t44.txt mem=10000

A set T of integers >= 2 is primitive if no element divides another.  We want every primitive T
with |T| = K, max T <= X and sum_{n in T} 1/n = 1.

Status: the solutions printed are verified exactly (Fraction sum, primitivity), so they are
correct.  Completeness ("there are no others with elements <= X") rests on the CP-SAT solver's
final INFEASIBLE answer, which is not certified.  Elements > X are not covered.

Method.
 1. Universe: n <= X with at least two distinct prime factors.  A primitive solution contains no
    prime power p^j (j >= 1): it would be the only term of p-adic valuation -j (Lemma 1 of
    primitive_q2/README.md).
 2. Exact pre-filter (a necessary condition, applied to a fixed point).  For a prime p let M_p be
    the largest power of p dividing some universe element.  If T has sum 1, then
    sum_{n in T, p | n} c_p(n) == 0 (mod M_p), where c_p(n) = (M_p / p^v) * (n / p^v)^(-1) mod M_p
    and v = v_p(n): this is the condition v_p(sum) >= 0.  So n can be in T only if, for every
    prime p | n, some set of remaining multiples of p that contains n has residue 0 mod M_p.
    The test is done for the primes p with p^2 > X (then M_p = p); skipping the other primes is
    conservative (it only removes fewer elements).
 3. CP-SAT model: x_n in {0,1};  primitivity (x_a + x_b <= 1 for a | b);  the congruence at every
    prime, sum_{p | n} ((D/n) mod M) x_n = M k_p with D = lcm(universe), M = p^{v_p(D)};  the value
    sum ceil(S/n) x_n >= S >= sum floor(S/n) x_n (S = 2^40);  and sum x_n = K.
    The congruences make sum 1/n an integer and the value constraint puts it within 44/S of 1,
    so the model's solutions are exactly the solutions of the problem in the universe.
 3b. Optional valid cuts (Lemmas 2 and 3 of primitive_q2/README.md, constants from q2exact):
    sum_{n in T, n >= A} (1/A - 1/n) <= sigma < (N+1)/10^12, used with integer coefficients
    floor(S (1/A - 1/n)) <= S (1/A - 1/n) and right-hand side floor(S (N+1) / 10^12); and at most
    H elements exceed Y.  Both hold for every solution, so no solution is lost.
 4. Enumeration: solve; verify the solution exactly; add the no-good  sum_{n in T} x_n <= K - 1;
    repeat until the solver reports INFEASIBLE.  Each no-good removes exactly one set.
No floating point is used in any decision (the solver's own internals aside).
"""
import sys, math, time
from fractions import Fraction
from ortools.sat.python import cp_model

X = int(sys.argv[1]); K = int(sys.argv[2]); workers = int(sys.argv[3])
tl = int(sys.argv[4]) if len(sys.argv) > 4 else 0
outfile = sys.argv[5] if len(sys.argv) > 5 and "=" not in sys.argv[5] else None
opts = dict(a.split("=", 1) for a in sys.argv[4:] if "=" in a)
t0 = time.monotonic()
def el(): return "%ds" % int(time.monotonic() - t0)
def log(*a):
    print(*a, flush=True)
    if outfile:
        with open(outfile, "a") as f: print(*a, file=f)

# primes and smallest prime factors up to X
spf = list(range(X + 1))
for i in range(2, int(X ** 0.5) + 1):
    if spf[i] == i:
        for j in range(i * i, X + 1, i):
            if spf[j] == j: spf[j] = i
def factor(n):
    f = {}
    while n > 1:
        p = spf[n]; f[p] = f.get(p, 0) + 1; n //= p
    return f
fac = {n: factor(n) for n in range(2, X + 1)}
U = [n for n in range(6, X + 1) if len(fac[n]) >= 2]
log("X=%d K=%d universe (non-prime-powers) = %d" % (X, K, len(U)))

# ---- 2. exact pre-filter for primes p with p^2 > X (modulus p) ----
alive = set(U)
bigP = sorted(set(p for n in U for p in fac[n] if p * p > X))
changed = True; rounds = 0
while changed:
    changed = False; rounds += 1
    for p in bigP:
        A = [n for n in range(2 * p, X + 1, p) if n in alive]
        if not A: continue
        full = (1 << p) - 1
        cs = [pow(n // p, -1, p) for n in A]          # c_p(n) = (n/p)^(-1) mod p
        def rot(b, s): return ((b << s) | (b >> (p - s))) & full if s else b
        m = len(A)
        pre = [1] * (m + 1)
        for i in range(m): pre[i + 1] = pre[i] | rot(pre[i], cs[i])
        suf = [1] * (m + 1)
        for i in range(m - 1, -1, -1): suf[i] = suf[i + 1] | rot(suf[i + 1], cs[i])
        for i in range(m):
            need = (-cs[i]) % p                       # residues of the other chosen elements
            a = pre[i]; b = suf[i + 1]; ok = False
            # is there r in a with (need - r) mod p in b ?  reverse b and test the intersection
            while a and not ok:
                low = a & -a; r = low.bit_length() - 1; a ^= low
                if (b >> ((need - r) % p)) & 1: ok = True
            if not ok:
                alive.discard(A[i]); changed = True
U = sorted(alive)
log("after the exact residue filter (%d rounds, primes > sqrt(X)): universe = %d  [%s]" % (rounds, len(U), el()))

# ---- 3. CP-SAT model ----
D = 1
for n in U: D = D * n // math.gcd(D, n)
Us = set(U)
mdl = cp_model.CpModel()
x = {n: mdl.NewBoolVar(str(n)) for n in U}
npairs = 0
for a in U:
    for b in range(2 * a, X + 1, a):
        if b in Us: mdl.AddBoolOr([x[a].Not(), x[b].Not()]); npairs += 1
PS = sorted(set(p for n in U for p in fac[n]))
for p in PS:
    M = 1
    while D % (M * p) == 0: M *= p
    idx = [((D // n) % M, n) for n in U if n % p == 0]
    idx = [(c, n) for c, n in idx if c]
    if not idx: continue
    k = mdl.NewIntVar(0, sum(c for c, _ in idx) // M + 1, "k%d" % p)
    mdl.Add(sum(c * x[n] for c, n in idx) == M * k)
S = 1 << 40
mdl.Add(sum(((S + n - 1) // n) * x[n] for n in U) >= S)
mdl.Add(sum((S // n) * x[n] for n in U) <= S)
mdl.Add(sum(x.values()) == K)
if "cut" in opts:
    A, N, Ycut, H = map(int, opts["cut"].split(","))
    big = [n for n in U if n >= A]
    mdl.Add(sum((S * (n - A) // (A * n)) * x[n] for n in big) <= S * (N + 1) // 10 ** 12)
    mdl.Add(sum(x[n] for n in U if n > Ycut) <= H)
    log("cuts: Lagrangian (A=%d, sigma < %d e-12) on %d elements; at most %d elements > %d" % (A, N + 1, len(big), H, Ycut))
log("model: %d variables, %d primitivity clauses, %d prime congruences  [%s]" % (len(U), npairs, len(PS), el()))

def verify(T):
    T = sorted(T)
    assert len(T) == K and len(set(T)) == K and T[0] >= 2 and T[-1] <= X
    assert all(b % a for i, a in enumerate(T) for b in T[i + 1:]), "not primitive"
    assert sum(Fraction(1, n) for n in T) == 1, "sum is not 1"
    L = 1
    for n in T: L = L * n // math.gcd(L, n)
    assert sum(L // n for n in T) == L
    return T

# ---- 4. enumeration with no-goods ----
sols = []
if "known" in opts:
    for line in open(opts["known"]):
        if not line.strip() or line.startswith("#"): continue
        T = verify(list(map(int, line.split())))
        assert all(n in Us for n in T), "known solution outside the filtered universe"
        sols.append(T)
        log("solution %d (known, verified exactly: |T|=%d, primitive, sum 1/n = 1, max %d)" % (len(sols), len(T), T[-1]))
        log("  T = " + " ".join(map(str, T)))
        mdl.Add(sum(x[n] for n in T) <= K - 1)
while True:
    s = cp_model.CpSolver(); s.parameters.num_workers = workers
    if tl: s.parameters.max_time_in_seconds = tl
    if "mem" in opts: s.parameters.max_memory_in_mb = int(opts["mem"])
    r = s.Solve(mdl)
    st = s.StatusName(r)
    if st in ("OPTIMAL", "FEASIBLE"):
        T = verify([n for n in U if s.Value(x[n])])
        sols.append(T)
        log("solution %d (verified exactly: |T|=%d, primitive, sum 1/n = 1, max %d)  [%s]" % (len(sols), len(T), T[-1], el()))
        log("  T = " + " ".join(map(str, T)))
        mdl.Add(sum(x[n] for n in T) <= K - 1)        # exclude exactly this set
    else:
        log("solver status %s after %d solution(s)  [%s]" % (st, len(sols), el()))
        if st == "INFEASIBLE":
            log("RESULT: %d primitive solution(s) with |T| = %d and all elements <= %d (completeness: CP-SAT INFEASIBLE, uncertified)" % (len(sols), K, X))
        else:
            log("RESULT: enumeration incomplete (time limit); %d solution(s) found so far" % len(sols))
        break
