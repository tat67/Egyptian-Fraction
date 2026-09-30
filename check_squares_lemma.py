#!/usr/bin/env python3
"""
Prime Puzzles 897 Q1: "repeat the A. W. Johnson task but allowing square denominators (4, 9, 25, ...)".

LEMMA.  Let T be a finite set of DISTINCT numbers of the form p*q (p < q primes) or p^2 (p prime).  If T
contains some p^2, then  sum_{n in T} 1/n  is NOT an integer.  Hence allowing squares changes nothing:
every Egyptian fraction with semiprime denominators (squares allowed) that is an integer is squarefree.

PROOF.  The denominators divisible by p are p^2 (at most once, T is a set) and p*q with q != p prime.
Their reciprocals add up to  (1/p^2) * (1 + p * sum_q 1/q),  and sum_q 1/q is a p-adic integer, so
1 + p*sum_q 1/q  is a p-adic unit: this part has p-adic valuation exactly -2.  Every other term of the
sum has a denominator prime to p, i.e. valuation >= 0.  Hence the whole sum has valuation exactly -2
and cannot be an integer.  (Only p^2 itself can give valuation -2; the products p*q give -1.)

EXHAUSTIVE COMPUTATIONAL CHECK (independent of the proof, exact integer arithmetic, no floating point):
take the N smallest numbers of the form p*q or p^2 (squares included) and look, by meet in the middle over
all 2^N subsets, for EVERY subset whose reciprocal sum is an integer.  With N = 34 the sum of all 34 is
below 2, so the only possible integer values are 0 (empty set) and 1.  The lemma predicts that the empty
set is the only solution.  This program counts all subsets with sum 0 or 1, and how many contain a square.
"""
import sys


def semiprimes_with_squares(count):
    """the `count` smallest n = p*q with p <= q primes (n = p^2 allowed), by omega-with-multiplicity == 2"""
    out = []
    n = 3
    limit = 200
    while len(out) < count:
        limit *= 2
        spf = list(range(limit + 1))
        i = 2
        while i * i <= limit:
            if spf[i] == i:
                for j in range(i * i, limit + 1, i):
                    if spf[j] == j:
                        spf[j] = i
            i += 1
        out = []
        for m in range(4, limit + 1):
            p = spf[m]
            r = m // p
            if r > 1 and spf[r] == r:          # m = p * r with r prime (r may equal p)
                out.append(m)
    return out[:count]


def is_square_of_prime(n):
    d = 2
    while d * d < n:
        d += 1
    return d * d == n


def subsets(vals, sq):
    """all subset sums of vals, with the flag 'contains a square' (as parallel lists)"""
    sums, flags = [0], [False]
    for v, s in zip(vals, sq):
        sums = sums + [x + v for x in sums]
        flags = flags + [f or s for f in flags]
    return sums, flags


def main(N):
    dens = semiprimes_with_squares(N)
    print(f"the {N} smallest numbers p*q (p<=q prime): {dens[:12]} ... {dens[-3:]}")
    squares = [d for d in dens if is_square_of_prime(d)]
    print("squares among them:", squares)
    L = 1
    for d in dens:
        a, b = L, d
        while b:
            a, b = b, a % b
        L = L // a * d
    vals = [L // d for d in dens]
    sq = [is_square_of_prime(d) for d in dens]
    total = sum(vals)
    assert total < 2 * L, "the sum of all denominators' reciprocals must be < 2 for this check"
    half = N // 2
    sl, fl = subsets(vals[:half], sq[:half])
    sr, fr = subsets(vals[half:], sq[half:])
    right = {}
    for s, f in zip(sr, fr):
        c = right.setdefault(s, [0, 0])
        c[0] += 1
        if f:
            c[1] += 1
    found = {0: [0, 0], 1: [0, 0]}                # integer value -> [subsets, subsets containing a square]
    for s, f in zip(sl, fl):
        for value in (0, 1):
            need = value * L - s
            if need in right:
                c = right[need]
                found[value][0] += c[0]
                if f:
                    found[value][1] += c[0]
                else:
                    found[value][1] += c[1]
    print(f"subsets examined: 2^{N} = {2 ** N}")
    print(f"subsets with integral sum 0 (the empty set): {found[0][0]}, of which contain a square: {found[0][1]}")
    print(f"subsets with sum exactly 1: {found[1][0]}, of which contain a square: {found[1][1]}")
    assert found[0][0] == 1 and found[1][0] == 0 and found[0][1] == 0 and found[1][1] == 0
    print("CONSISTENT with the lemma: no nonempty subset has an integral reciprocal sum.")


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 34)
