#!/usr/bin/env python3
"""Independent re-check of the completion step (shares no code with the C++ programs).

Input: a core dump written by q2exact / q2b / q2k, one line per core:
    c1 c2 ... cj | h=H a/b
For each core it recomputes, with Python Fractions and its own factorisation,
    delta = 1 - sum 1/c  (must equal a/b),
and searches every set H of h distinct integers > Y with sum 1/x = delta such that no core element
divides an element of H and H is primitive.  Methods (different from the C++ ones):
  h = 1 : x = 1/delta must be an integer;
  h = 2 : (a x - b)(a y - b) = b^2: x = (b + d)/a for every divisor d < b of b^2 with d = -b (mod a),
          divisors found by meet in the middle on the residue of d mod a;
  h = 3 : smallest element x in (b/a, 3b/a], then the h = 2 method (only used for small ranges).
Usage: check_completion.py DUMP Y [maxRange3]
"""
import sys
from fractions import Fraction as F
from math import gcd

def factor(n):
    f = {}; p = 2
    while p * p <= n:
        while n % p == 0:
            f[p] = f.get(p, 0) + 1; n //= p
        p += 1 if p == 2 else 2
    if n > 1: f[n] = f.get(n, 0) + 1
    return f

def divisors_half(items):
    out = [1]
    for p, e in items:
        nxt = []
        for d in out:
            pw = 1
            for _ in range(e + 1):
                nxt.append(d * pw); pw *= p
        out = nxt
    return out

def two_term(a, b, fb):
    """all (x, y), x < y, 1/x + 1/y = a/b."""
    items = [(p, 2 * e) for p, e in fb.items()]          # divisors of b^2
    h1 = len(items) // 2
    L1 = divisors_half(items[:h1]); L2 = divisors_half(items[h1:])
    sols = []
    if a == 1:
        for d1 in L1:
            for d2 in L2:
                d = d1 * d2
                if d < b: sols.append(((b + d) // a, (b + b * b // d) // a))
        return sols
    idx = {}
    for d1 in L1: idx.setdefault(d1 % a, []).append(d1)
    target = (-b) % a
    for d2 in L2:
        inv = pow(d2, -1, a)                             # gcd(d2, a) = 1 since d2 | b^2, gcd(a, b) = 1
        for d1 in idx.get(target * inv % a, []):
            d = d1 * d2
            if d < b and (b + d) % a == 0 and (b + b * b // d) % a == 0:
                sols.append(((b + d) // a, (b + b * b // d) // a))
    return sols

def admissible(H, core):
    for x in H:
        if any(x % c == 0 for c in core): return False
    for i in range(len(H)):
        for j in range(len(H)):
            if i != j and H[j] % H[i] == 0: return False
    return True

def main():
    dump, Y = sys.argv[1], int(sys.argv[2])
    maxr = int(sys.argv[3]) if len(sys.argv) > 3 else 10**6
    n = 0; byh = {}; found = []; skipped = 0
    for line in open(dump):
        left, right = line.split('|')
        core = list(map(int, left.split()))
        hs, frac = right.split()
        h = int(hs[2:]); a0, b0 = map(int, frac.split('/'))
        d = 1 - sum(F(1, c) for c in core)
        assert d == F(a0, b0), "remainder mismatch"
        a, b = d.numerator, d.denominator
        n += 1; byh[h] = byh.get(h, 0) + 1
        cand = []
        if h == 1:
            if b % a == 0: cand.append([b // a])
        elif h == 2:
            for x, y in two_term(a, b, factor(b)):
                cand.append([x, y])
        elif h == 3:
            lo, hi = b // a + 1, 3 * b // a
            if hi - lo > maxr: skipped += 1; continue
            for x in range(max(lo, Y + 1), hi + 1):
                r = d - F(1, x)
                for y, z in two_term(r.numerator, r.denominator, factor(r.denominator)):
                    if y > x: cand.append([x, y, z])
        for H in cand:
            if min(H) > Y and len(set(H)) == len(H) and admissible(H, core):
                T = core + H
                if sum(F(1, t) for t in T) == 1: found.append(sorted(T))
    print(f"cores checked: {n}  by h: {dict(sorted(byh.items()))}  skipped (range too large): {skipped}  solutions: {len(found)}")
    for T in found: print("SOLUTION", len(T), T)

main()
