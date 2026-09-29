"""Independent exact verification of the solution list printed by semiprime48, and generation of
solutions48.txt.

Usage: python3 verify48.py run48_output.txt [solutions48.txt]

For every set printed by the C++ program (lines '#k OK |T|=48: ...' and '(smaller) OK |T|=..: ...')
this script checks, with its own code:
  * the elements are distinct;
  * each element is p*q with p < q both prime (trial division up to the square root for the
    factorisation, deterministic Miller-Rabin for the primality of both factors);
  * the sum of the reciprocals is exactly 1 (Python fractions).
It also checks that the 47-element sets found along the way are exactly the 23 sets of
solutions47.txt.  With a second argument it writes the list of 48-element solutions.
"""
import sys, re, os
from fractions import Fraction as F


def is_prime(n):
    if n < 2:
        return False
    small = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41)
    for p in small:
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2; s += 1
    for a in small:                      # deterministic for n < 3.3 * 10^24
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    assert n < 3317044064679887385961981
    return True


def split(n):
    """n = p*q with p < q primes, or None"""
    p = 2
    while p * p <= n:
        if n % p == 0:
            q = n // p
            return (p, q) if (q != p and is_prime(p) and is_prime(q)) else None
        p += 1
    return None


def check(T):
    if len(set(T)) != len(T):
        return False, None
    facs = []
    for n in T:
        f = split(n)
        if f is None:
            return False, None
        facs.append(f)
    return sum(F(1, n) for n in T) == 1, facs


def main():
    log = sys.argv[1]
    out = sys.argv[2] if len(sys.argv) > 2 else None
    sols48, smaller = [], []
    for line in open(log):
        m = re.match(r'#\s*\d+\s+(\S+)\s+\|T\|=(\d+):\s*(.*)', line)
        if m:
            sols48.append(list(map(int, m.group(3).split())))
            continue
        m = re.match(r'\(smaller\)\s+(\S+)\s+\|T\|=(\d+):\s*(.*)', line)
        if m:
            smaller.append(list(map(int, m.group(3).split())))
    K = len(sols48[0]) if sols48 else 48
    ok48 = 0; details = []
    for T in sols48:
        good, facs = check(T)
        assert good and len(T) == K, T
        ok48 += 1; details.append((T, facs))
    print("%d-element sets in the log: %d, verified independently: %d" % (K, len(sols48), ok48))
    for T in smaller:
        good, _ = check(T)
        assert good, T
    sizes = {}
    for T in smaller:
        sizes[len(T)] = sizes.get(len(T), 0) + 1
    print("smaller sets in the log (all verified):", dict(sorted(sizes.items())))
    ref = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'solutions47.txt')
    known47 = set()
    for line in open(ref):
        m = re.match(r'#\s*\d+:\s*(.*)', line)
        if m:
            known47.add(tuple(sorted(map(int, m.group(1).split()))))
    found47 = set(tuple(sorted(T)) for T in (smaller if K == 48 else sols48) if len(T) == 47)
    print("47-element sets found = the 23 sets of solutions47.txt:", found47 == known47 and len(known47) == 23)
    assert all(len(T) == 47 for T in smaller) and found47 == known47
    details.sort(key=lambda x: sorted(x[0]))          # lexicographic order of the sorted element lists
    if out:
        big = [len([1 for p, q in facs if q > 73]) > 0 for T, facs in details]
        with open(out, 'w') as f:
            f.write("All %d subsets T of P = {pq : p<q primes} with |T| = %d and sum_{n in T} 1/n = 1.\n" % (len(details), K))
            f.write("Each line: index, the %d elements; then the primes > 73 used (with their neighbours).\n" % K)
            f.write("Verified exactly (C++ BigNat check in semiprime48.cpp and Python fractions in verify48.py):\n")
            f.write("%d distinct squarefree semiprimes, sum = 1.\n" % K)
            f.write("%d of them use only primes <= 73, %d use at least one prime > 73.\n\n" % (big.count(False), big.count(True)))
            for i, (T, facs) in enumerate(details):
                f.write("#%3d: %s\n" % (i + 1, ' '.join(map(str, sorted(T)))))
                nb = {}
                for p, q in facs:
                    if q > 73:
                        nb.setdefault(q, []).append(p)
                    if p > 73:
                        nb.setdefault(p, []).append(q)
                lp = max(q for p, q in facs)
                if nb:
                    desc = '; '.join('%d ~ {%s}' % (P, ', '.join(map(str, sorted(nb[P])))) for P in sorted(nb))
                    f.write("      largest prime %d; primes > 73: %s\n" % (lp, desc))
                else:
                    f.write("      largest prime %d; primes > 73: none (all primes <= 73)\n" % lp)
        print("wrote", out)


if __name__ == '__main__':
    main()
