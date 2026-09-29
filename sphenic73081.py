#!/usr/bin/env python3
"""
Sphenic numbers p*q*r (p<q<r primes): can 1/n over a nonempty T, |T| <= K = 73081, be an integer?

Only integer arithmetic is used (no float anywhere): exact rational sums are kept as
unreduced (numerator, denominator) integer pairs.  Method:

  * Let a_1 < a_2 < ... be the sphenic numbers.  For a nonempty T with |T| = k,
    0 < sum_{n in T} 1/n <= 1/a_1 + ... + 1/a_k = H_k <= H_K.
  * If H_K < 1 then no such sum is an integer.  Here H_K > 1 (about 1.5558), so this
    trivial argument fails; but H_K < 2, hence an integral sum over <= K terms equals 1.
    (sphenic_search.py then constructs such a T explicitly.)
"""
import sys, time

K = 73081
LIMIT = 1_000_000          # sieve bound; we verify a_K < LIMIT so the list is complete

def sphenic_upto(limit):
    """All n <= limit with exactly three distinct prime factors and squarefree, ascending.
    Pure integer sieve: omega[n] = #distinct primes, sqf[n] = squarefree flag."""
    omega = bytearray(limit + 1)
    nonsqf = bytearray(limit + 1)
    isprime = bytearray([1]) * (limit + 1)
    isprime[0:2] = b"\x00\x00"
    for i in range(2, limit + 1):
        if isprime[i]:
            for m in range(i, limit + 1, i):
                omega[m] += 1
                if m != i:
                    isprime[m] = 0
            sq = i * i
            for m in range(sq, limit + 1, sq):
                nonsqf[m] = 1
    return [n for n in range(2, limit + 1) if omega[n] == 3 and not nonsqf[n]]

def sum_recips(nums):
    """Exact sum of 1/n as an integer pair (N, D), unreduced, by balanced product tree."""
    layer = [(1, n) for n in nums]
    while len(layer) > 1:
        nxt = []
        for i in range(0, len(layer) - 1, 2):
            a, b = layer[i]; c, d = layer[i + 1]
            nxt.append((a * d + c * b, b * d))
        if len(layer) & 1:
            nxt.append(layer[-1])
        layer = nxt
    return layer[0]

def main():
    t0 = time.time_ns()
    P = sphenic_upto(LIMIT)
    assert len(P) >= K and P[K - 1] < LIMIT, "sieve bound too small"
    print(f"number of sphenic numbers <= {LIMIT}: {len(P)}")
    print(f"first terms: {P[:8]}")
    print(f"a_K = a_{K} = {P[K-1]}   (K-th smallest sphenic number)")
    N, D = sum_recips(P[:K])
    print(f"H_K = N/D exact with N,D of {N.bit_length()} and {D.bit_length()} bits")
    # decimal expansion of H_K by integer division only
    digits = 40
    q = N * 10**digits // D
    s = str(q).rjust(digits + 1, "0")
    print(f"H_{K} = {s[:-digits]}.{s[-digits:]}...  (floor, integer arithmetic)")
    print("H_K < 1 ?", N < D)
    print("H_K < 2 ?", N < 2 * D)
    ms = (time.time_ns() - t0) // 1_000_000
    print(f"elapsed {ms // 1000}.{ms % 1000:03d}s")
    return P, N, D

if __name__ == "__main__":
    main()
