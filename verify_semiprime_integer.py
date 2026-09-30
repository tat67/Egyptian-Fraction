#!/usr/bin/env python3
"""
Independent exact verifier for sets of squarefree semiprimes with an INTEGER reciprocal sum.

    python3 verify_semiprime_integer.py FILE N [BOUND]

FILE holds one denominator per row.  Checks, with integer / rational arithmetic ONLY (no float, no '/',
no math / random modules):
  1. the set is nonempty, has at most BOUND elements (optional) and all elements are distinct;
  2. every element is p*q with p < q PRIME (trial-division factorisation, independent of the search code);
  3. sum of 1/n over the set is EXACTLY N   (fractions.Fraction for <= 20000 terms; otherwise an
     unreduced numerator/denominator pair from a balanced product tree, compared as  num == N*den);
  4. the p-adic criterion  sum_{q in N(p)} q^(-1) == 0 (mod p)  at every prime p that occurs.
"""
import sys
from fractions import Fraction


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


def tree_sum_equals(nums, N):
    layer = [(1, n) for n in nums]
    while len(layer) > 1:
        nxt = []
        for i in range(0, len(layer) - 1, 2):
            a, b = layer[i]
            c, d = layer[i + 1]
            nxt.append((a * d + c * b, b * d))
        if len(layer) & 1:
            nxt.append(layer[-1])
        layer = nxt
    num, den = layer[0]
    return num == N * den


def main(path, N, bound=None):
    with open(path) as f:
        T = [int(tok) for tok in f.read().split()]
    print(f"read {len(T)} denominators from {path}")
    assert len(T) >= 1, "set must be nonempty"
    if bound is not None:
        assert len(T) <= bound, f"{len(T)} terms exceed the bound {bound}"
    assert len(set(T)) == len(T), "denominators are not distinct"
    print(f"{len(T)} terms, all distinct: OK" + (f", at most {bound}: OK" if bound is not None else ""))

    nb = {}
    for n in T:
        fs = factor(n)
        assert len(fs) == 2 and all(e == 1 for (_, e) in fs), f"{n} is not a product of two distinct primes: {fs}"
        (p, _), (q, _) = fs
        nb.setdefault(p, []).append(q)
        nb.setdefault(q, []).append(p)
    print("every denominator is p*q with p < q prime: OK")
    print("smallest / largest denominator:", min(T), "/", max(T))

    if len(T) <= 20000:
        s = Fraction(0)
        for n in T:
            s += Fraction(1, n)
        print(f"exact sum of reciprocals = {s.numerator}/{s.denominator}")
        assert s == N, f"sum is not {N}"
        print(f"sum of 1/n == {N} EXACTLY (Fraction arithmetic): OK")
    else:
        assert tree_sum_equals(T, N), f"sum is not {N}"
        print(f"sum of 1/n == {N} EXACTLY (unreduced product-tree fraction, num == {N}*den): OK")

    for p, qs in nb.items():
        r = sum(pow(q % p, -1, p) for q in qs) % p
        assert r == 0, f"local criterion fails at p={p}"
    print(f"local criterion (sum of q^-1 over neighbours == 0 mod p) holds at all {len(nb)} primes occurring: OK")
    print("VERIFIED")


if __name__ == "__main__":
    if len(sys.argv) < 3:
        print(__doc__)
        sys.exit(2)
    main(sys.argv[1], int(sys.argv[2]), int(sys.argv[3]) if len(sys.argv) > 3 else None)
