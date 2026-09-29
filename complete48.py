"""Independent Python re-solution of Step 2 for the cores dumped by semiprime48 (--dump).

For shapes with at most one big-big edge it uses the exact-fraction completion routine of
complete47.py: its own shape enumeration, star factoring without a size cap, exact covers, and
the divisor equation for one big-big edge.  Shapes with exactly two big-big edges, which
complete47.py leaves unresolved, are solved here with its own code (solve_two_bb below).
Shapes with three or more big-big edges would be reported as unresolved.  It runs in parallel
over chunks of the dump.

Usage: python3 complete48.py cores48.txt [KT=48] [processes=4]
       python3 complete48.py --selftest
Prints the number of cores, the solutions found (every T with |T| <= KT and sum 1), grouped by
size, and the number of unresolved cores.
"""
import sys, os, itertools, math
from fractions import Fraction as F
from multiprocessing import Pool

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from complete47 import solve_core, recompute, isprime, factor, divisors_from, S, SB, stars_for, pmin, mult_val, shapes, BIG


def big_factors(n):
    return sorted(set(p for p in factor(n) if p > SB))


def n_of(A):
    """(prod A, n(A) = sum_{q in A} prod(A)/q) for a tuple of distinct primes"""
    D = math.prod(A)
    return D, sum(D // q for q in A)


def primes_between(lo, hi):
    if hi < lo:
        return []
    sieve = bytearray([1]) * (hi + 1)
    sieve[0:2] = b'\x00\x00'
    for i in range(2, math.isqrt(hi) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(range(i * i, hi + 1, i)))
    return [p for p in range(max(lo, 2), hi + 1) if sieve[p]]


def pair_solve(b1, a1, b2, a2, Z):
    """all (P1, P2), distinct primes > SB, with a1/(b1 P1) + a2/(b2 P2) + 1/(P1 P2) = Z."""
    t = Z * b1 * b2
    if t.denominator != 1 or t <= 0:
        return []
    t = t.numerator
    N = b1 * b2 * (t + a1 * a2)
    out = []
    for X in divisors_from(factor(N)):
        Y = N // X
        if (X + a1 * b2) % t or (Y + a2 * b1) % t:
            continue
        P1, P2 = (X + a1 * b2) // t, (Y + a2 * b1) // t
        if P1 != P2 and P1 > SB and P2 > SB and isprime(P1) and isprime(P2):
            assert F(a1, b1 * P1) + F(a2, b2 * P2) + F(1, P1 * P2) == Z
            out.append((P1, P2))
    return out


def path_value(A, P):
    return sum(F(1, q * P[i]) for i in range(3) for q in A[i]) + F(1, P[0] * P[1]) + F(1, P[1] * P[2])


def two_value(A, P):
    return sum(F(1, q * P[i]) for i in range(4) for q in A[i]) + F(1, P[0] * P[1]) + F(1, P[2] * P[3])


def bound(A, ZK, nterms):
    """one of the nterms positive terms is >= ZK/nterms: P_i <= nterms*s_i/ZK or min(P,P') <= sqrt(nterms/ZK)"""
    b = math.isqrt(math.floor(F(nterms) / ZK))
    for Ai in A:
        s = sum(F(1, q) for q in Ai)
        if s:
            b = max(b, math.floor(nterms * s / ZK))
    return b


def solve_path(A, ZK):
    """big primes (P0, P1, P2), P1 the middle, of a path component with attachments A0, A1, A2"""
    (b0, a0), (b1, a1), (b2, a2) = [n_of(Ai) if Ai else (1, 0) for Ai in A]
    found = set()
    for p in primes_between(SB + 1, bound(A, ZK, 5)):
        # p in the middle: the ends are stars on A0 + {p} and A2 + {p}
        for P0 in big_factors(p * a0 + b0):
            for P2 in big_factors(p * a2 + b2):
                if len({P0, p, P2}) == 3 and path_value(A, (P0, p, P2)) == ZK:
                    found.add((P0, p, P2))
        # p at an end: the middle has the extra neighbour p (n(A1 + {p}) = p a1 + b1)
        for e in (0, 2):
            o = 2 - e
            Zr = ZK - sum(F(1, q * p) for q in A[e])
            if Zr <= 0:
                continue
            bo, ao = (b0, a0) if o == 0 else (b2, a2)
            for P1, Po in pair_solve(b1 * p, a1 * p + b1, bo, ao, Zr):
                P = [0, P1, 0]; P[e] = p; P[o] = Po
                if len(set(P)) == 3 and path_value(A, P) == ZK:
                    found.add(tuple(P))
    return found


def solve_two(A, ZK):
    """big primes (P0, P1, P2, P3) of two components P0 - P1 and P2 - P3"""
    ba = [n_of(Ai) for Ai in A]
    found = set()
    for p in primes_between(SB + 1, bound(A, ZK, 6)):
        for r in range(4):
            q = r ^ 1
            c0, c1 = (2, 3) if r < 2 else (0, 1)
            bq, aq = ba[q]
            for Pq in big_factors(p * aq + bq):
                if Pq == p:
                    continue
                V = sum(F(1, x * p) for x in A[r]) + sum(F(1, x * Pq) for x in A[q]) + F(1, p * Pq)
                Zr = ZK - V
                if Zr <= 0:
                    continue
                for X, Y in pair_solve(ba[c0][0], ba[c0][1], ba[c1][0], ba[c1][1], Zr):
                    P = [0] * 4; P[r] = p; P[q] = Pq; P[c0] = X; P[c1] = Y
                    if len(set(P)) == 4 and two_value(A, P) == ZK:
                        found.add(tuple(P))
    return found


def star_candidates(W, mult, U):
    cands = []
    for k in range(2, len(W) + 1):
        for Aset in itertools.combinations(W, k):
            for P in stars_for(Aset):
                if all(mult[q] > 1 or (pow(P, -1, q) + U.get(q, 0)) % q == 0 for q in Aset):
                    cands.append((P, Aset))
    return cands


def covers(need, cands):
    out = []
    def rec(start, used):
        if all(v == 0 for v in need.values()):
            out.append(list(used)); return
        for idx in range(start, len(cands)):
            P, Aset = cands[idx]
            if any(need[q] == 0 for q in Aset) or any(P == u for u, _ in used):
                continue
            for q in Aset: need[q] -= 1
            used.append((P, Aset)); rec(idx + 1, used); used.pop()
            for q in Aset: need[q] += 1
    rec(0, [])
    return out


def solve_two_bb(U, Z, mult):
    """all big parts G with shape (mult, nbb = 2) and value Z (a path or two one-edge components, plus stars)"""
    W = sorted(mult)
    cands = star_candidates(W, mult, U)
    sols = set()
    for kind, ns in (('path', 3), ('two', 4)):
        per_q = []
        for q in W:
            per_q.append([sub for k in range(0, min(mult[q], ns) + 1) for sub in itertools.combinations(range(ns), k)])
        for choice in itertools.product(*per_q):
            A = [tuple(q for q, sub in zip(W, choice) if s in sub) for s in range(ns)]
            if kind == 'path' and (not A[0] or not A[2]):
                continue
            if kind == 'two' and not all(A):
                continue
            need = {q: mult[q] - len(sub) for q, sub in zip(W, choice)}
            for cv in covers(need, cands):
                ZK = Z - sum(F(1, q * P) for P, Aset in cv for q in Aset)
                if ZK <= 0:
                    continue
                found = solve_path(A, ZK) if kind == 'path' else solve_two(A, ZK)
                starP = {P for P, _ in cv}
                for Ps in found:
                    if starP & set(Ps):
                        continue
                    G = [q * P for P, Aset in cv for q in Aset]
                    G += [q * Ps[s] for s in range(ns) for q in A[s]]
                    G += [Ps[0] * Ps[1], Ps[1] * Ps[2]] if kind == 'path' else [Ps[0] * Ps[1], Ps[2] * Ps[3]]
                    G = tuple(sorted(G))
                    assert len(set(G)) == len(G) and sum(F(1, x) for x in G) == Z
                    sols.add(G)
    return sols


def parse_line(line):
    parts = line.split()
    i = parts.index('U'); j = parts.index('C')
    U = {}
    for tok in parts[i + 1:j]:
        q, r = tok.split(':'); U[int(q)] = int(r)
    return [int(x) for x in parts[j + 1:]], U


def work(args):
    lines, KT = args
    sols = set(); unresolved = []; ncores = 0; n_two = 0
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
        still = []
        for mult, nbb in unres:
            if nbb == 2:
                n_two += 1
                found += [list(G) for G in solve_two_bb(U, Z, mult)]
            else:
                still.append((mult, nbb))
        for G in found:
            T = tuple(sorted(C + list(G)))
            assert len(set(T)) == len(T) and sum(F(1, x) for x in T) == 1
            sols.add(T)
        if still:
            unresolved.append((len(C), U, still[:3]))
    return ncores, sols, unresolved, n_two


def selftest():
    """the planted big parts of semiprime48 --selftest: all completions (any shape) with the same
    residues and value and at most as many elements"""
    for name, G in (('planted path', [334, 1497, 1585, 2219, 83333, 158183]),
                    ('planted pair of components', [386, 2101, 2483, 36863, 267, 8119, 10237, 31417])):
        res = {}
        for x in G:
            p = next(d for d in range(2, x) if x % d == 0); q = x // p
            for a, b in ((p, q), (q, p)):
                if a <= SB:
                    res[a] = (res.get(a, 0) - pow(b, -1, a)) % a
        U = {a: r for a, r in res.items() if r}
        Z = sum(F(1, x) for x in G)
        found, unres, _ = solve_core([], U, Z, len(G))
        sols = set(tuple(sorted(x)) for x in found)
        for mult, nbb in unres:
            assert nbb == 2
            sols |= solve_two_bb(U, Z, mult)
        print("%s: %d distinct completion(s); planted structure recovered: %s" % (name, len(sols), tuple(sorted(G)) in sols))
        for x in sorted(sols):
            print("   ", ' '.join(map(str, x)))


if __name__ == '__main__':
    if sys.argv[1] == '--selftest':
        selftest(); sys.exit(0)
    path = sys.argv[1]
    KT = int(sys.argv[2]) if len(sys.argv) > 2 else 48
    procs = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    lines = open(path).read().splitlines()
    chunks = [(lines[k::procs * 8], KT) for k in range(procs * 8)]
    allT = set(); nunres = 0; ncores = 0; ntwo = 0
    with Pool(procs) as pool:
        for nc, sols, unres, n2 in pool.imap_unordered(work, chunks):
            ncores += nc; allT |= sols; nunres += len(unres); ntwo += n2
            for u in unres:
                print("UNRESOLVED", u, flush=True)
    bysize = {}
    for T in allT:
        bysize.setdefault(len(T), []).append(T)
    print("cores", ncores, "solutions", len(allT), "unresolved cores", nunres)
    print("shapes with two big-big edges solved:", ntwo)
    for k in sorted(bysize):
        print("solutions with |T| = %d: %d" % (k, len(bysize[k])))
    for T in sorted(allT, key=lambda T: (len(T), T)):
        print(len(T), ' '.join(map(str, T)))
