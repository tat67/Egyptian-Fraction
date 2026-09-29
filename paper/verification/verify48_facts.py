#!/usr/bin/env python3
"""Recompute every fact about the 48-term representations quoted in the paper (Theorem C and
Section "Forty-eight terms") from solutions48.txt, with exact integer arithmetic only.

Checks, for each of the listed sets T:
  * 48 distinct elements, each a product p*q of two distinct primes (trial division);
  * sum_{n in T} 1/n == 1 exactly (fractions.Fraction);
  * the local conditions (*) at every prime p: sum_{q in N(p)} q^{-1} == 0 (mod p);
and, over the whole list: the sets are pairwise distinct, the classification by the primes
> 73, the largest prime and element, the common elements, the maximal star size, H_48 < 2.

Usage: python3 verify48_facts.py ../../solutions48.txt
"""
import sys
from fractions import Fraction


def factor_sp(n):
    """Return (p, q) with p < q primes and n = p*q, or None."""
    d = 2
    m = n
    fac = []
    while d * d <= m:
        while m % d == 0:
            fac.append(d)
            m //= d
        d += 1
    if m > 1:
        fac.append(m)
    if len(fac) == 2 and fac[0] < fac[1]:
        return fac[0], fac[1]
    return None


def is_prime(n):
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


def main(path):
    sols = []
    for line in open(path):
        s = line.strip()
        if s.startswith('#') and ':' in s:
            head, body = s.split(':', 1)
            sols.append([int(x) for x in body.split()])
    print('sets read:', len(sols))
    assert len(sols) == 620

    keys = set()
    cats = {'small only': 0, 'one large prime': 0, 'two large primes, no large-large element': 0,
            'two large primes joined by P1*P2': 0, 'other': 0}
    maxP, maxP_set, maxE = 0, None, 0
    common = None
    max_star = 0
    for idx, T in enumerate(sols, 1):
        assert len(T) == 48 and len(set(T)) == 48, idx
        key = tuple(sorted(T))
        assert key not in keys, idx
        keys.add(key)
        fac = {}
        for n in T:
            f = factor_sp(n)
            assert f is not None, (idx, n)
            fac[n] = f
        assert sum(Fraction(1, n) for n in T) == 1, idx
        # local conditions (*)
        nbr = {}
        for n, (p, q) in fac.items():
            nbr.setdefault(p, []).append(q)
            nbr.setdefault(q, []).append(p)
        for p, qs in nbr.items():
            assert is_prime(p)
            assert sum(pow(q, p - 2, p) for q in qs) % p == 0, (idx, p)
        large = sorted(p for p in nbr if p > 73)
        if not large:
            cats['small only'] += 1
        elif len(large) == 1:
            cats['one large prime'] += 1
        elif len(large) == 2:
            if large[0] * large[1] in T:
                cats['two large primes joined by P1*P2'] += 1
            else:
                cats['two large primes, no large-large element'] += 1
        else:
            cats['other'] += 1
        for P in large:
            if all(q <= 73 for q in nbr[P]):
                max_star = max(max_star, len(nbr[P]))
        mp = max(nbr)
        if mp > maxP:
            maxP, maxP_set = mp, idx
        maxE = max(maxE, max(T))
        common = set(T) if common is None else common & set(T)
    print('all sets: 48 distinct squarefree semiprimes, sum exactly 1, (*) at every prime: OK')
    print('pairwise distinct sets:', len(keys))
    for k, v in cats.items():
        print(f'  {k}: {v}')
    print('largest prime:', maxP, 'in set #%d' % maxP_set)
    big = [n for n in sols[maxP_set - 1] if max(factor_sp(n)) > 73]
    print('  its elements with a prime > 73:', ' '.join(f'{factor_sp(n)[0]}*{factor_sp(n)[1]}' for n in big))
    print('largest element:', maxE, '=', '*'.join(map(str, factor_sp(maxE))))
    print('elements common to all 620 sets (%d):' % len(common), ' '.join(map(str, sorted(common))))
    print('largest star (large prime with only small neighbours):', max_star, 'neighbours')
    # H_48
    P = []
    n = 2
    while len(P) < 48:
        if factor_sp(n):
            P.append(n)
        n += 1
    H47 = sum(Fraction(1, a) for a in P[:47])
    H48 = H47 + Fraction(1, P[47])
    print('a_48 =', P[47], '; H_48 < 1.0704:', H48 < Fraction(10704, 10000), '; H_48 < 2:', H48 < 2,
          '; H_47 < 3/2:', H47 < Fraction(3, 2))


if __name__ == '__main__':
    main(sys.argv[1] if len(sys.argv) > 1 else '../../solutions48.txt')
