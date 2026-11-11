#!/usr/bin/env python3
"""Exact resolution (Python big integers) of two-term sub-cases that complete_search.cpp logs as UNRESOLVED
because a number left its 64/128-bit fast path (reasons y0big, ybig, zbig, q, wmax, P, h, manyprimes).

Such a line reads   UNRESOLVED <reason> prev: t_1 ... t_k core: m_1 ... m_s
and asks for all (y, z) with  t_k < y < z  and  1/y + 1/z = r := 1 - sum 1/m_i - sum 1/t_j,
such that  T = {m_i} u {t_j} u {y, z}  is an antichain of integers >= 2 without prime powers.

Method (complete): write r = a/D in lowest terms.  Every solution of 1/y + 1/z = a/D has the form
    w | D,  y' | w,  gcd(y', D/w) = 1,  a | y' + D/w,  h = (y' + D/w)/a,  y = h*w,  z = h*(D/w)*(w/y')
(w = D/gcd(z, D)... standard parametrisation; conversely every such tuple gives a solution).
Necessary for compatibility: neither w nor D/w is divisible by an element m_i (w | y and (D/w) | z).
All divisors w of D are enumerated with this pruning; for each w all y' are found.

Usage: python3 resolve_two.py FILE_WITH_UNRESOLVED_LINES
"""
import sys
from fractions import Fraction
from math import gcd, isqrt

def factor(n, primes):
    f = {}
    for p in primes:
        if p * p > n:
            break
        while n % p == 0:
            f[p] = f.get(p, 0) + 1
            n //= p
    if n > 1:
        # remaining cofactor: trial division up to its square root is too slow in general; use Pollard rho
        for q in pollard_factor(n):
            f[q] = f.get(q, 0) + 1
    return f

def is_probable_prime(n):
    if n < 2:
        return False
    small = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41]
    for p in small:
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in small:  # deterministic for n < 3.3e24; larger n: probable prime (reported)
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True

def pollard_factor(n):
    if n == 1:
        return []
    if is_probable_prime(n):
        if n >= 3_317_044_064_679_887_385_961_981:
            print("  note: primality of", n, "only probable (Miller-Rabin, 13 bases)")
        return [n]
    import random
    rnd = random.Random(12345)
    while True:
        c = rnd.randrange(1, n)
        f = lambda x: (x * x + c) % n
        x = y = rnd.randrange(2, n)
        d = 1
        while d == 1:
            x = f(x)
            y = f(f(y))
            d = gcd(abs(x - y), n)
        if d != n:
            return pollard_factor(d) + pollard_factor(n // d)

def is_prime_power(n):
    for p in range(2, isqrt(n) + 1):
        if n % p == 0:
            while n % p == 0:
                n //= p
            return n == 1
        if p > 10**6:
            break
    f = pollard_factor(n)
    return len(set(f)) == 1

def resolve(core, prev, primes):
    r = 1 - sum(Fraction(1, m) for m in core) - sum(Fraction(1, t) for t in prev)
    if r <= 0:
        return []
    a, D = r.numerator, r.denominator
    fD = sorted(factor(D, primes).items())
    M = list(core)
    def compat(n):
        return all(n % m for m in M)
    sols = []
    last = prev[-1] if prev else 0
    # enumerate divisors w of D; prune: w (and later D/w) must not be divisible by an element of M
    def rec(i, w, exps):
        if i == len(fD):
            c = D // w
            if not compat(w) or not compat(c):
                return
            # y' | w, gcd(y', c) = 1, y' = a*h - c  (1 <= y' <= w).  y' may only use primes whose full power of D lies in w.
            full = [(q, e) for (q, e), k in zip(fD, exps) if k == e and e > 0]
            ndiv = 1
            for _, e in full:
                ndiv *= e + 1
            cands = []
            if w // a + 1 <= ndiv:
                h = c // a + 1
                while a * h - c <= w:
                    cands.append(a * h - c)
                    h += 1
            else:
                divs = [1]
                for q, e in full:
                    divs = [d * q**j for d in divs for j in range(e + 1)]
                cands = [d for d in divs if (d + c) % a == 0]
            for yp in cands:
                if w % yp == 0 and gcd(yp, c) == 1:
                    h = (yp + c) // a
                    y = h * w
                    z = h * c * (w // yp)
                    if last < y < z:
                        sols.append((y, z))
            return
        p, e = fD[i]
        for k in range(e + 1):
            if not compat(w):
                break
            # the part of D/w fixed so far must not be divisible by an element of M either (D/w | z)
            cpart = 1
            for (q, eq), kq in zip(fD[:i] + [(p, e)], exps + [k]):
                cpart *= q ** (eq - kq)
            if compat(cpart):
                rec(i + 1, w, exps + [k])
            w *= p
    rec(0, 1, [])
    good = []
    for (y, z) in sols:
        T = list(core) + list(prev) + [y, z]
        if Fraction(1, y) + Fraction(1, z) != r:
            continue
        ok = all(t >= 2 for t in T) and len(set(T)) == len(T)
        if ok:
            S = sorted(T)
            for i, u in enumerate(S):
                for v in S[i + 1:]:
                    if v % u == 0:
                        ok = False
                        break
                if not ok:
                    break
        if ok and not is_prime_power(y) and not is_prime_power(z):
            assert sum(Fraction(1, t) for t in T) == 1
            good.append(T)
    return good

def main():
    primes = [p for p in range(2, 100000) if all(p % d for d in range(2, isqrt(p) + 1))]
    n = 0
    total = 0
    for line in open(sys.argv[1]):
        if not line.startswith("UNRESOLVED"):
            continue
        n += 1
        head, core = line.split("core:")
        prev = [int(x) for x in head.split("prev:")[1].split()]
        core = [int(x) for x in core.split()]
        sols = resolve(core, prev, primes)
        total += len(sols)
        print("case %d (%s, prev = %s): %d solution(s)" % (n, head.split()[1], prev, len(sols)))
        for T in sols:
            print("  SOLUTION size=%d :" % len(T), " ".join(map(str, sorted(T))))
    print("resolved %d case(s), %d solution(s)" % (n, total))

if __name__ == "__main__":
    main()
