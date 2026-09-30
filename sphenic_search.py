#!/usr/bin/env python3
"""
Search for a set T of sphenic numbers p*q*r (p<q<r primes), |T| <= 73081,
whose reciprocals sum to an integer (necessarily 1).

EXACT ARITHMETIC ONLY: this file contains no float / double / long double, no
true division '/', no math.log/sqrt, and does not use the `random` module (whose
primary generator returns floats).  Everything is Python int arithmetic; the
pseudo-random choices come from an integer splitmix64 generator.

Method ("top-down repair").
  Local criterion: for squarefree denominators, sum_{n in T} 1/n has p-adic
  valuation >= 0 iff   rho_p := sum_{n in T, p | n} (n/p)^(-1)  ==  0  (mod p).
  * Start with a seed T0 = the k smallest sphenic numbers (sum just below/around 1).
  * Go through the primes p = PMAX, ..., 11, 7 in DECREASING order.  If rho_p != 0,
    toggle (add, or remove if already present) a few terms p*a*b with a<b<p primes
    so that rho_p becomes 0.  Those terms have p as their LARGEST prime, so they
    change rho only at smaller primes (a, b), which are treated later; primes > p
    are untouched.  Hence after the pass rho_p == 0 for every prime p >= 7.
  * Then every prime >= 7 has v_p(sum) >= 0 and every denominator is squarefree,
    so the sum lies in (1/30)Z.  If it equals exactly 1 we are done.
    (|T| <= 73081 => 0 < sum <= H_73081 < 2, so an integral sum is exactly 1.)
  * Otherwise retry with other pseudo-random choices / seeds.
"""
import sys
import time

K_MAX = 73081          # (kept for reference; the bound is now the --bound option)
PMAX = 4000            # every prime factor of a sphenic number <= 23309 is < 3885


# ---------------------------------------------------------------- integer PRNG
class SplitMix64:
    MASK = (1 << 64) - 1

    def __init__(self, seed):
        self.x = seed & self.MASK

    def next(self):
        self.x = (self.x + 0x9E3779B97F4A7C15) & self.MASK
        z = self.x
        z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & self.MASK
        z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & self.MASK
        return z ^ (z >> 31)

    def below(self, n):
        return self.next() % n

    def shuffle(self, lst):
        for i in range(len(lst) - 1, 0, -1):
            j = self.below(i + 1)
            lst[i], lst[j] = lst[j], lst[i]


# --------------------------------------------------------------------- number theory
def primes_upto(n):
    sieve = bytearray([1]) * (n + 1)
    sieve[0:2] = b"\x00\x00"
    i = 2
    while i * i <= n:
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(range(i * i, n + 1, i)))
        i += 1
    return [i for i in range(n + 1) if sieve[i]], sieve


def sphenic_list(limit, primes):
    """Sorted list of (n, (a,b,c)) for all sphenic n <= limit (triple loop over primes)."""
    out = []
    for i, a in enumerate(primes):
        if a * primes[i + 1] * primes[i + 2] > limit:
            break
        for j in range(i + 1, len(primes)):
            b = primes[j]
            if a * b * primes[j + 1] > limit:
                break
            for k in range(j + 1, len(primes)):
                c = primes[k]
                n = a * b * c
                if n > limit:
                    break
                out.append((n, (a, b, c)))
    out.sort()
    return out


def sum_is_one(numbers):
    """Exact test  sum 1/n == 1  using a common denominator L = product of primes involved."""
    L = 1
    seen = set()
    for n in numbers:
        m = n
        d = 2
        while d * d <= m:
            if m % d == 0:
                if d not in seen:
                    seen.add(d)
                    L *= d
                while m % d == 0:
                    m //= d
            d += 1
        if m > 1 and m not in seen:
            seen.add(m)
            L *= m
    return sum(L // n for n in numbers) == L, L


# --------------------------------------------------------------------- one attempt
class Attempt:
    def __init__(self, primes, isprime, terms, rng):
        self.primes = primes
        self.isprime = isprime
        self.rng = rng
        self.T = set(terms)                       # set of sorted triples
        self.nb = {}                              # prime -> set of (x,y) with p*x*y in T
        for t in self.T:
            self._link(t)

    def _link(self, t):
        a, b, c = t
        self.nb.setdefault(a, set()).add((b, c))
        self.nb.setdefault(b, set()).add((a, c))
        self.nb.setdefault(c, set()).add((a, b))

    def _unlink(self, t):
        a, b, c = t
        self.nb[a].discard((b, c))
        self.nb[b].discard((a, c))
        self.nb[c].discard((a, b))

    def toggle(self, a, b, p):
        t = (a, b, p)                             # a < b < p
        if t in self.T:
            self.T.discard(t)
            self._unlink(t)
        else:
            self.T.add(t)
            self._link(t)

    def rho(self, p):
        r = 0
        for (x, y) in self.nb.get(p, ()):
            r += pow(x * y % p, -1, p)
        return r % p

    # -- find a set of toggles (pairs) whose deltas sum to `target` mod p
    def solve(self, p, target):
        pr = self.primes
        below = [q for q in pr if q < p]
        # only terms in which p is the LARGEST prime may be toggled (keeps larger primes untouched)
        cur = {xy for xy in self.nb.get(p, set()) if xy[1] < p}
        inv_t = pow(target, -1, p)
        cands = []
        # size 1, addition:  a*b == inv(target)
        for a in below:
            b = inv_t * pow(a, -1, p) % p
            if b > a and self.isprime[b] and (a, b) not in cur:
                cands.append([(a, b)])
        # size 1, removal:  -inv(ab) == target  <=>  inv(ab) == -target
        for (x, y) in cur:
            if (-pow(x * y % p, -1, p) - target) % p == 0:
                cands.append([(x, y)])
        if cands:
            return cands[self.rng.below(len(cands))]
        # general: BFS over residues with shuffled toggle order (small size first)
        tog = []
        for i, a in enumerate(below):
            for b in below[i + 1:]:
                d = pow(a * b % p, -1, p)
                if (a, b) in cur:
                    d = (-d) % p
                tog.append((a, b, d))
        self.rng.shuffle(tog)
        if len(tog) > 6000:                       # keep BFS cheap for huge p (never needed in practice)
            tog = tog[:6000]
        # size 2 via dictionary
        by_delta = {}
        for idx, (a, b, d) in enumerate(tog):
            by_delta.setdefault(d, []).append(idx)
        cands = []
        for idx, (a, b, d) in enumerate(tog):
            for j in by_delta.get((target - d) % p, ()):
                if j > idx:
                    cands.append([(a, b), (tog[j][0], tog[j][1])])
            if len(cands) > 64:
                break
        if cands:
            return cands[self.rng.below(len(cands))]
        # BFS for larger subsets
        level = {0: []}
        seen = {0}
        for _ in range(8):
            nxt = {}
            for r, sub in level.items():
                for idx, (a, b, d) in enumerate(tog):
                    if idx in sub:
                        continue
                    r2 = (r + d) % p
                    if r2 not in seen:
                        seen.add(r2)
                        nxt[r2] = sub + [idx]
            if target in nxt:
                return [(tog[i][0], tog[i][1]) for i in nxt[target]]
            level = nxt
            if not level:
                break
        return None

    def run(self, pmax, pmin=7):
        pr = self.primes
        for p in reversed([q for q in pr if pmin <= q <= pmax]):
            r = self.rho(p)
            if r == 0:
                continue
            sol = self.solve(p, (-r) % p)
            if sol is None:
                return False
            for (a, b) in sol:
                self.toggle(a, b, p)
            assert self.rho(p) == 0
        return True


def main():
    import argparse
    ap = argparse.ArgumentParser(description="sphenic reciprocal sum = 1, |T| <= BOUND (exact integer arithmetic)")
    ap.add_argument("--bound", type=int, default=6096, help="maximum |T| (default 6096)")
    ap.add_argument("--kmin", type=int, default=4900, help="smallest seed size k")
    ap.add_argument("--kmax", type=int, default=5300, help="seed size k is drawn from [kmin, kmax)")
    ap.add_argument("--tries", type=int, default=100000, help="maximum number of attempts")
    ap.add_argument("--minimize", action="store_true", help="use all tries and keep the smallest |T| found")
    ap.add_argument("--out", default="sphenic_solution.txt")
    ap.add_argument("--seed", type=int, default=20260929, help="integer PRNG seed")
    ap.add_argument("--quiet", action="store_true")
    ap.add_argument("--dump-all", default=None, metavar="FILE",
                    help="also write EVERY set found with sum exactly 1 (regardless of --bound) to FILE, "
                         "as pairs of lines '# attempt=A k=K size=S' and the space-separated numbers")
    args = ap.parse_args()
    dump = open(args.dump_all, "w") if args.dump_all else None
    t0 = time.time_ns()
    primes, isprime = primes_upto(PMAX)
    S = sphenic_list(60000, primes)
    rng = SplitMix64(args.seed)
    attempts = 0
    hist = {}
    best = None
    while attempts < args.tries:
        attempts += 1
        k = args.kmin + rng.below(args.kmax - args.kmin)
        at = Attempt(primes, isprime, [tr for (_, tr) in S[:k]], rng)
        if not at.run(PMAX):
            continue
        nums = sorted(a * b * c for (a, b, c) in at.T)
        one, L = sum_is_one(nums)
        num = sum(L // n for n in nums)
        j30 = (30 * num) // L                     # exact: sum = j30/30
        assert (30 * num) % L == 0, "sum not in (1/30)Z -- repair pass is broken"
        hist[j30] = hist.get(j30, 0) + 1
        if not args.quiet:
            print(f"attempt {attempts}: k={k} |T|={len(nums)} sum = {j30}/30", flush=True)
        if one and dump is not None:
            dump.write(f"# attempt={attempts} k={k} size={len(nums)}\n" + " ".join(map(str, nums)) + "\n")
            dump.flush()
        if one and len(nums) <= args.bound and (best is None or len(nums) < len(best[0])):
            best = (nums, k, attempts)
            if not args.minimize:
                break
    dt = (time.time_ns() - t0) // 1_000_000
    if dump is not None:
        dump.close()
    if best is None:
        print(f"no solution with |T| <= {args.bound} in {attempts} attempts")
    else:
        nums, k, att = best
        with open(args.out, "w") as f:
            f.write(" ".join(map(str, nums)) + "\n")
        print(f"FOUND: |T|={len(nums)} <= {args.bound}, sum == 1 exactly; seed size k={k}, attempt {att}; wrote {args.out}")
    print(f"attempts={attempts}, elapsed {dt // 1000}.{dt % 1000:03d} s, histogram of landed sums j/30: {sorted(hist.items())}")


if __name__ == "__main__":
    main()
