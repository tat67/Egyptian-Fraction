#!/usr/bin/env python3
"""
Smaller sets: sphenic numbers whose reciprocals sum to exactly 1, aiming at |T| <= 5000.

EXACT ARITHMETIC ONLY (no float / double, no true division '/', no math / random modules).

Improvements over sphenic_search.py (same local criterion and same top-down repair idea):

 1. PRIME-CAPPED SEED.  The seed is the k smallest sphenic numbers all of whose prime factors are
    <= CAP.  Every prime of the seed with a nonzero residue costs about one extra term, so dropping
    the terms with the (many) large primes saves most of the ~500 repair terms that the plain
    "k smallest sphenic numbers" seed needs.

 2. PREFER DELETION.  When a single toggle repairs the residue at p, a deletion of an existing term
    p*a*b (which shortens T) is chosen in preference to an addition.

 3. EXHAUSTIVE TAIL.  The random top-down repair only goes down to the prime after TAIL (default 17).
    For the last primes TAIL, ..., 11, 7 *all* combinations of up to MAXSZ toggles are enumerated by
    depth-first search.  Once every prime > TAIL is repaired, the sum is a multiple of 1/P0 with
    P0 = 2*3*5*...*TAIL, so 'sum == 1' is tested exactly as the INTEGER equation  S == P0  with
    S = P0 * sum  tracked incrementally (each toggled term t divides P0, so P0 // t is an integer).
    Among all leaves with S == P0 the one with the fewest terms is kept.  This replaces "hope the
    sum lands on 30/30" by an exact search, so much smaller seeds (sum barely above 1) work.

The result satisfies the p-adic criterion at every prime >= 7 (by construction) and has sum exactly 1
(S == P0); it is re-verified independently by verify_sphenic.py.
"""
import sys
import time
from itertools import combinations

from sphenic_search import SplitMix64, primes_upto, sphenic_list, Attempt, sum_is_one, PMAX


class SmallAttempt(Attempt):
    def __init__(self, primes, isprime, terms, rng, pref_pct):
        Attempt.__init__(self, primes, isprime, terms, rng)
        self.pref_pct = pref_pct                  # probability (percent) of preferring a deletion

    # single-toggle solve with a preference for deletions; falls back to the generic solver
    def solve_pref(self, p, target):
        below = [q for q in self.primes if q < p]
        cur = {xy for xy in self.nb.get(p, set()) if xy[1] < p}
        inv_t = pow(target, -1, p)
        rem = [[(x, y)] for (x, y) in cur if (-pow(x * y % p, -1, p) - target) % p == 0]
        add = []
        for a in below:
            b = inv_t * pow(a, -1, p) % p
            if b > a and self.isprime[b] and (a, b) not in cur:
                add.append([(a, b)])
        if rem and (not add or self.rng.below(100) < self.pref_pct):
            return rem[self.rng.below(len(rem))]
        if add:
            return add[self.rng.below(len(add))]
        return self.solve(p, target)

    def run_top(self, pmax, pmin):
        for p in reversed([q for q in self.primes if pmin <= q <= pmax]):
            r = self.rho(p)
            if r == 0:
                continue
            sol = self.solve_pref(p, (-r) % p)
            if sol is None:
                return False
            for (a, b) in sol:
                self.toggle(a, b, p)
        return True

    def scaled_sum(self, P0):
        """P0 * sum_{n in T} 1/n as an exact integer (asserts divisibility)."""
        L = 1
        for p, s in self.nb.items():
            if s:
                L *= p
        num = 0
        for (a, b, c) in self.T:
            num += L // (a * b * c)
        assert (P0 * num) % L == 0, "sum is not in (1/P0)Z: some prime above the tail is unrepaired"
        return P0 * num // L

    def tail_search(self, tail, P0, maxsz):
        """tail: descending list of primes, e.g. [17, 13, 11, 7].  Returns the best list of toggles
        (a, b, p) making the sum exactly 1, or None."""
        hits = []

        def rec(i, S, chosen):
            if i == len(tail):
                if S == P0:
                    hits.append((len(self.T), list(chosen)))
                return
            p = tail[i]
            target = (-self.rho(p)) % p
            below = [q for q in self.primes if q < p]
            pairs = [(a, b) for ai, a in enumerate(below) for b in below[ai + 1:]]
            deltas = []
            for (a, b) in pairs:
                d = pow(a * b % p, -1, p)
                if (a, b, p) in self.T:
                    d = (-d) % p
                deltas.append(d)
            for s in range(0, maxsz + 1):
                for comb in combinations(range(len(pairs)), s):
                    if sum(deltas[j] for j in comb) % p != target:
                        continue
                    dS = 0
                    for j in comb:
                        a, b = pairs[j]
                        t = P0 // (a * b * p)
                        dS += -t if (a, b, p) in self.T else t
                        self.toggle(a, b, p)
                        chosen.append((a, b, p))
                    rec(i + 1, S + dS, chosen)
                    for j in comb:
                        a, b = pairs[j]
                        self.toggle(a, b, p)
                        chosen.pop()

        rec(0, self.scaled_sum(P0), [])
        if not hits:
            return None
        return min(hits, key=lambda h: h[0])[1]


class TailJoin:
    """Complete meet-in-the-middle solver for the last primes.

    After every prime > TAIL has been repaired, only the sphenic numbers built from the primes
    Q = {2, 3, 5, ..., TAIL} may still change (35 numbers for TAIL = 17).  Let x_t in {0,1} be the FINAL
    presence of such a term t.  Writing 'out' for the terms of T that are not of this kind,

        rho_q(final) = rho_q(out) + sum_t x_t * inv(t/q mod q)        (q = 7, 11, ..., TAIL)
        P0 * sum(final) = S_out + sum_t x_t * (P0 // t),  P0 = product of the primes in Q,

    and we need rho_q(final) = 0 for all q and P0 * sum(final) = P0 (i.e. sum exactly 1).  The
    contributions of a subset of the 35 terms do not depend on the stage, so the two half-tables are
    built once; per stage only the two targets change.  The residues mod 7, 11, 13, 17 are packed into one
    integer mod 17017 by the Chinese remainder theorem (addition-compatible)."""

    def __init__(self, primes, tail):
        self.Q = [p for p in primes if p <= tail]
        self.C = [p for p in self.Q if p >= 7]
        self.M = 1
        for q in self.C:
            self.M *= q
        self.P0 = 1
        for p in self.Q:
            self.P0 *= p
        # CRT idempotents e_q: e_q = 1 mod q, 0 mod the other q'
        self.e = {q: (self.M // q) * pow(self.M // q, -1, q) % self.M for q in self.C}
        self.terms = [(a, b, c) for i, a in enumerate(self.Q) for j, b in enumerate(self.Q) if j > i
                      for c in self.Q if c > b]
        self.key = []
        self.val = []
        for (a, b, c) in self.terms:
            k = 0
            for q, m in ((a, b * c), (b, a * c), (c, a * b)):
                if q in self.e:
                    k = (k + pow(m % q, -1, q) * self.e[q]) % self.M
            self.key.append(k)
            self.val.append(self.P0 // (a * b * c))
        half = len(self.terms) // 2
        self.left = list(range(half))
        self.right = list(range(half, len(self.terms)))
        # tables: for every subset (bitmask over the half) the packed residue key and the value
        self.tabL = self._table(self.left)
        tabR = self._table(self.right)
        best = {}
        for mask, (k, v, pc) in enumerate(tabR):
            kk = (k, v)
            if kk not in best or pc < best[kk][0]:
                best[kk] = (pc, mask)
        self.dictR = best
        self.tail_set = set(self.terms)

    def _table(self, idx):
        ks, vs, pcs = [0], [0], [0]
        for i in idx:
            k, v = self.key[i], self.val[i]
            ks = ks + [(x + k) % self.M for x in ks]
            vs = vs + [x + v for x in vs]
            pcs = pcs + [x + 1 for x in pcs]
        return list(zip(ks, vs, pcs))

    def solve(self, at):
        """at: an Attempt whose primes > TAIL are repaired.  Returns the list of tail terms that must be
        present in the final set (minimising |T|), or None if no completion has sum exactly 1."""
        out = [t for t in at.T if t not in self.tail_set]
        L = 1
        for p, s in at.nb.items():
            if s:
                L *= p
        num = sum(L // (a * b * c) for (a, b, c) in out)
        assert (self.P0 * num) % L == 0
        S_out = self.P0 * num // L
        tval = self.P0 - S_out
        if tval < 0:
            return None
        tkey = 0
        for q in self.C:
            r = 0
            for (x, y) in at.nb.get(q, ()):
                if (min(x, y, q), sorted((x, y, q))[1], max(x, y, q)) not in self.tail_set:
                    r += pow(x * y % q, -1, q)
            tkey = (tkey - r % q * self.e[q]) % self.M
        best = None
        dictR = self.dictR
        M = self.M
        for maskL, (k, v, pc) in enumerate(self.tabL):
            if v > tval:
                continue
            hit = dictR.get(((tkey - k) % M, tval - v))
            if hit is not None and (best is None or pc + hit[0] < best[0]):
                best = (pc + hit[0], maskL, hit[1])
        if best is None:
            return None
        _, mL, mR = best
        chosen = [self.terms[i] for b, i in enumerate(self.left) if (mL >> b) & 1]
        chosen += [self.terms[i] for b, i in enumerate(self.right) if (mR >> b) & 1]
        return chosen, out


def main():
    import argparse
    ap = argparse.ArgumentParser(description="sphenic reciprocal sum = 1 with few terms (exact integer arithmetic)")
    ap.add_argument("--bound", type=int, default=5000, help="maximum |T| (default 5000)")
    ap.add_argument("--cap", type=int, default=2200, help="seed uses only primes <= CAP")
    ap.add_argument("--kmin", type=int, default=4680, help="smallest seed size k")
    ap.add_argument("--kmax", type=int, default=4730, help="seed size k is drawn from [kmin, kmax)")
    ap.add_argument("--tail", type=int, default=17, help="largest prime of the exhaustive tail")
    ap.add_argument("--maxsz", type=int, default=3, help="max toggles per tail prime (tail-mode dfs only)")
    ap.add_argument("--tail-mode", choices=("join", "dfs"), default="join",
                    help="join = complete meet-in-the-middle over all tail terms (default); dfs = bounded DFS")
    ap.add_argument("--pref", type=int, default=90, help="percent preference for deletions")
    ap.add_argument("--tries", type=int, default=100000)
    ap.add_argument("--minimize", action="store_true", help="use all tries and keep the smallest |T|")
    ap.add_argument("--seed", type=int, default=20260930)
    ap.add_argument("--out", default="sphenic_solution_5000.txt")
    ap.add_argument("--dump-all", default=None, metavar="FILE",
                    help="write every set found (sum exactly 1, |T| <= --bound) as '# attempt=A k=K size=S' + numbers")
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args()
    dump = open(args.dump_all, "w") if args.dump_all else None
    t0 = time.time_ns()
    primes, isprime = primes_upto(PMAX)
    S = sphenic_list(120000, primes)
    capped = [tr for (_, tr) in S if tr[2] <= args.cap]
    assert len(capped) >= args.kmax, "seed pool too small; raise the sphenic_list limit"
    tail = [p for p in reversed(primes) if 7 <= p <= args.tail]
    P0 = 1
    for p in primes:
        if p <= args.tail:
            P0 *= p
    rng = SplitMix64(args.seed)
    tj = TailJoin(primes, args.tail) if args.tail_mode == "join" else None
    stats = {"top_fail": 0, "no_leaf": 0, "found": 0}
    best = None
    attempts = 0
    while attempts < args.tries:
        attempts += 1
        k = args.kmin + rng.below(args.kmax - args.kmin)
        at = SmallAttempt(primes, isprime, capped[:k], rng, args.pref)
        if not at.run_top(PMAX, args.tail + 1):
            stats["top_fail"] += 1
            continue
        if tj is None:
            tog = at.tail_search(tail, P0, args.maxsz)
            if tog is None:
                stats["no_leaf"] += 1
                continue
            for (a, b, p) in tog:
                at.toggle(a, b, p)
            final = at.T
        else:
            res = tj.solve(at)
            if res is None:
                stats["no_leaf"] += 1
                continue
            chosen, out = res
            final = set(out) | set(chosen)
        nums = sorted(a * b * c for (a, b, c) in final)
        one, _ = sum_is_one(nums)                 # independent exact re-check with a common denominator
        assert one, "internal error: sum != 1"
        stats["found"] += 1
        if not args.quiet:
            print(f"attempt {attempts}: k={k} |T|={len(nums)}", flush=True)
        if dump is not None and len(nums) <= args.bound:
            dump.write(f"# attempt={attempts} k={k} size={len(nums)}\n" + " ".join(map(str, nums)) + "\n")
            dump.flush()
        if len(nums) <= args.bound and (best is None or len(nums) < len(best[0])):
            best = (nums, k, attempts)
            if not args.minimize:
                break
    if dump is not None:
        dump.close()
    dt = (time.time_ns() - t0) // 1_000_000
    if best is None:
        print(f"no solution with |T| <= {args.bound} in {attempts} attempts")
    else:
        nums, k, att = best
        with open(args.out, "w") as f:
            f.write(" ".join(map(str, nums)) + "\n")
        print(f"FOUND: |T|={len(nums)} <= {args.bound}, sum == 1 exactly; seed size k={k}, cap={args.cap}, attempt {att}; wrote {args.out}")
    print(f"attempts={attempts}, elapsed {dt // 1000}.{dt % 1000:03d} s, {stats}")


if __name__ == "__main__":
    main()
