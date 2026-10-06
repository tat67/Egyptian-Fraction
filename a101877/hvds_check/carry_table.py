"""carry_table.py WITNESS K P -- p-adic "carry" table of a witness, using exact fractions only.

For each power q = P^b <= K, from the largest down, it prints
  G(q)    = {x <= K : the largest prime-power factor of x is q}   (one "structure" of the hvds solver),
  K_q     = sum of 1/x over the members of G(q) that the witness keeps,
  v_P(K_q) and v_P of the running sum K_{P^B} + ... + K_q.
A structure for q = P^a may by itself have v_P(K_q) < -(a-1) when the higher powers leave a carry;
then the running sum, not K_q alone, is what must lose its P^-a digit.
No code is shared with the hvds solver or the tracer.
Usage: python3 carry_table.py ../witnesses/witness_n8_max3228.txt 3230 2
"""
import sys
from fractions import Fraction


def largest_prime_power_factor(K):
    """g[x] = largest prime power exactly dividing x, and its prime, for 1 <= x <= K (sieve)."""
    g = [1] * (K + 1)
    prime = [0] * (K + 1)
    for p in range(2, K + 1):
        if prime[p] == 0 and g[p] == 1:             # p is prime
            for m in range(p, K + 1, p):
                y, q = m, 1
                while y % p == 0:
                    y //= p
                    q *= p
                if q > g[m]:
                    g[m], prime[m] = q, p
    return g, prime


def v(fr, p):
    if fr == 0:
        return "inf"
    a, n, d = 0, fr.numerator, fr.denominator
    while n % p == 0:
        n //= p
        a += 1
    while d % p == 0:
        d //= p
        a -= 1
    return a


if __name__ == "__main__":
    path, K, P = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    S = {int(t) for t in open(path).read().strip().split(",")}
    assert max(S) <= K
    g, prime = largest_prime_power_factor(K)
    powers = []
    q = P
    while q <= K:
        powers.append(q)
        q *= P
    run = Fraction(0)
    print(f"witness {path}, k = {K}, p = {P}")
    print(f"{'q':>6} {'|G(q)|':>7} {'kept':>5} {'v_p(K_q)':>9} {'v_p(running)':>13}  K_q")
    for q in reversed(powers):
        G = [x for x in range(1, K + 1) if g[x] == q]
        kept = [x for x in G if x in S]
        Kq = sum((Fraction(1, x) for x in kept), Fraction(0))
        run += Kq
        shown = f"{G} keeps {kept}" if len(G) <= 6 else ""
        print(f"{q:>6} {len(G):>7} {len(kept):>5} {str(v(Kq, P)):>9} {str(v(run, P)):>13}  {Kq}  {shown}")
