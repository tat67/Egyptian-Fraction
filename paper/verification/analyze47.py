"""Instrumented re-run of complete47.py's Step 2 (same logic, extra statistics).
Collects: shapes after parity, shapes passing value, alive shapes by nbb, candidate stars
(|A| <= 11 as in the C++ program, and without cap), and for nbb = 1 the bit sizes of the
intermediate integers that semiprime47.cpp stores in 128-bit words."""
import sys, math, itertools, time, os
sys.path.insert(0, os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..')))  # repository root (complete47.py)
from fractions import Fraction as F
from complete47 import (isprime, factor, divisors_from, S, BIG, pmin, mult_val, shapes,
                        stars_for, parse_dump, recompute)
SB = 73
def analyze(path, KT, maxstar):
    tot = dict(cores=0, shapes=0, alive=0, alive_cores=0, cand_cap=0, cand_all=0,
               alive_nbb0=0, alive_nbb1=0, alive_nbb2plus=0, pairs_nbb1=0, t_integral=0)
    mx = dict(B=0, a1b2=0, a2b1=0, L=0, N=0, Wsize=0)
    allT = set(); unresolved = 0; t0 = time.time()
    for C, Ud in parse_dump(path):
        tot['cores'] += 1
        U = recompute(C); assert U == Ud
        Z = 1 - sum(F(1, n) for n in C)
        if not U:
            if Z == 0: allT.add(tuple(sorted(C)))
            continue
        g = KT - len(C); slack = g - len(U)
        if slack < 0: continue
        single = {q: F(1, q * pmin(q, U[q])) for q in U}
        core_alive = False
        for mult, nbb in shapes(U, slack):
            if (U.get(2, 0) + mult.get(2, 0)) % 2: continue
            tot['shapes'] += 1
            ub = sum((single[q] if mult[q] == 1 else mult_val(q, mult[q])) if q in U else mult_val(q, mult[q]) for q in mult)
            ub += nbb * F(1, BIG[0] * BIG[1])
            if ub < Z: continue
            tot['alive'] += 1; core_alive = True
            if nbb >= 2: tot['alive_nbb2plus'] += 1; unresolved += 1; continue
            tot['alive_nbb%d' % nbb] += 1
            W = sorted(mult); mx['Wsize'] = max(mx['Wsize'], len(W))
            cands = []
            for k in range(2, len(W) + 1):
                for A in itertools.combinations(W, k):
                    for P in stars_for(A):
                        if all(mult[q] > 1 or (pow(P, -1, q) + U.get(q, 0)) % q == 0 for q in A):
                            cands.append((P, A))
            tot['cand_all'] += len(cands)
            tot['cand_cap'] += sum(1 for P, A in cands if len(A) <= maxstar)
            def cover(need, used, start, out):
                if all(v == 0 for v in need.values()): out.append(list(used)); return
                for idx in range(start, len(cands)):
                    P, A = cands[idx]
                    if any(need[q] == 0 for q in A): continue
                    if any(P == u for u, _ in used): continue
                    for q in A: need[q] -= 1
                    used.append((P, A)); cover(need, used, idx + 1, out); used.pop()
                    for q in A: need[q] += 1
            if nbb == 0:
                covers = []; cover(dict(mult), [], 0, covers)
                for cv in covers:
                    G = sorted(q * P for P, A in cv for q in A)
                    if sum(F(1, x) for x in G) == Z: allT.add(tuple(sorted(C + G)))
                continue
            for k1 in range(1, len(W) + 1):
                for A1 in itertools.combinations(W, k1):
                    for k2 in range(1, len(W) + 1):
                        for A2 in itertools.combinations(W, k2):
                            if A1 > A2: continue
                            need = dict(mult)
                            for q in A1: need[q] -= 1
                            for q in A2: need[q] -= 1
                            if any(v < 0 for v in need.values()): continue
                            tot['pairs_nbb1'] += 1
                            b1 = math.prod(A1); b2 = math.prod(A2)
                            a1 = sum(b1 // q for q in A1); a2 = sum(b2 // q for q in A2)
                            mx['B'] = max(mx['B'], (b1 * b2).bit_length())
                            mx['a1b2'] = max(mx['a1b2'], (a1 * b2).bit_length())
                            mx['a2b1'] = max(mx['a2b1'], (a2 * b1).bit_length())
                            covers = []; cover(need, [], 0, covers)
                            for cv in covers:
                                Zk = Z - sum(F(1, q * P) for P, A in cv for q in A)
                                if Zk <= 0: continue
                                t = Zk * b1 * b2
                                if t.denominator != 1: continue
                                tot['t_integral'] += 1
                                t = t.numerator; L = t + a1 * a2; N = b1 * b2 * L
                                mx['L'] = max(mx['L'], L.bit_length()); mx['N'] = max(mx['N'], N.bit_length())
                                for X in divisors_from(factor(N)):
                                    Y = N // X
                                    if (X + a1 * b2) % t or (Y + a2 * b1) % t: continue
                                    P1 = (X + a1 * b2) // t; P2 = (Y + a2 * b1) // t
                                    if P1 == P2 or P1 <= SB or P2 <= SB: continue
                                    if not (isprime(P1) and isprime(P2)): continue
                                    if P1 in {P for P, A in cv} or P2 in {P for P, A in cv}: continue
                                    G = sorted([q * P for P, A in cv for q in A] + [q * P1 for q in A1] + [q * P2 for q in A2] + [P1 * P2])
                                    if len(set(G)) == len(G) and sum(F(1, x) for x in G) == Z:
                                        allT.add(tuple(sorted(C + G)))
        if core_alive: tot['alive_cores'] += 1
    print("KT", KT, "maxstar", maxstar, "elapsed_s", round(time.time() - t0))
    print("totals", tot); print("max_bits", mx)
    print("unresolved_shapes", unresolved, "solutions", len(allT))
    for T in sorted(allT): print(len(T), ' '.join(map(str, T)))
if __name__ == '__main__':
    # usage: python3 analyze47.py <core dump> <budget KT> <max star leaves>
    #   e.g. gunzip -c ../../cores47.txt.gz > cores47.txt && python3 analyze47.py cores47.txt 47 11
    analyze(sys.argv[1], int(sys.argv[2]), int(sys.argv[3]))
