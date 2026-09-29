#!/usr/bin/env python3
"""
Independent exact verifier for sphenic_solution.txt.

Checks, using ONLY integer / rational arithmetic (no float, no '/' operator,
no math module, no `random`):
  1. T is nonempty, has |T| <= bound (default 6096) elements, all distinct;
  2. every element is a product of exactly three DISTINCT primes
     (trial-division factorisation, independent of the search code);
  3. the sum of 1/n over T, computed with fractions.Fraction (exact rationals),
     is exactly 1;
  4. (second, independent method) the p-adic criterion
        sum_{n in T, p | n} (n/p)^(-1)  ==  0  (mod p)   for every prime p,
     and (as an independent cross-check) the exact sum is 1.
"""
import sys
from fractions import Fraction

K_MAX = 6096          # size bound of the current problem (override: 2nd command-line argument)


def factor(n):
    fs = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            e = 0
            while n % d == 0:
                n //= d
                e += 1
            fs.append((d, e))
        d += 1 if d == 2 else 2
    if n > 1:
        fs.append((n, 1))
    return fs


def main(path, bound=K_MAX):
    with open(path) as f:
        T = [int(tok) for tok in f.read().split()]
    print(f"read {len(T)} numbers from {path}")
    assert len(T) >= 1, "T must be nonempty"
    assert len(T) <= bound, f"|T| = {len(T)} exceeds {bound}"
    assert len(set(T)) == len(T), "elements are not distinct"
    print(f"|T| = {len(T)} <= {bound}: OK, all distinct: OK")

    fac = {}
    for n in T:
        fs = factor(n)
        assert len(fs) == 3 and all(e == 1 for (_, e) in fs), f"{n} is not sphenic: {fs}"
        fac[n] = [p for (p, _) in fs]
    print("every element is a product of exactly 3 distinct primes: OK")
    print("smallest / largest element:", min(T), "/", max(T))

    # (3) exact rational sum
    s = Fraction(0)
    for n in T:
        s += Fraction(1, n)
    print(f"exact sum of reciprocals = {s.numerator}/{s.denominator}")
    assert s == 1, "sum is not 1"
    print("sum of 1/n over T == 1 EXACTLY (Fraction arithmetic): OK")

    # (4) p-adic criterion at every prime that occurs
    nb = {}
    for n in T:
        for p in fac[n]:
            m = n // p
            nb.setdefault(p, []).append(m)
    for p, ms in nb.items():
        r = sum(pow(m % p, -1, p) for m in ms) % p
        assert r == 0, f"local criterion fails at p={p}"
    print(f"local criterion (sum of (n/p)^-1 == 0 mod p) holds at all {len(nb)} primes occurring in T: OK")
    print("VERIFIED")


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "sphenic_solution_6096.txt",
         int(sys.argv[2]) if len(sys.argv) > 2 else K_MAX)
