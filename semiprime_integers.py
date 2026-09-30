#!/usr/bin/env python3
"""
Squarefree semiprimes p*q (p<q primes) whose reciprocals sum to a given INTEGER N >= 1
(Prime Puzzles 897, Q2: "solutions for any integer > 1 using only semiprime denominators").

EXACT ARITHMETIC ONLY: no float / double, no true division '/', no math / random modules
(pseudo-random choices come from the integer splitmix64 generator of sphenic_search.py).

Method (same idea as sphenic_small.py, adapted to two-prime denominators).
  Local criterion.  T is a graph on primes (n = p*q is the edge {p,q}).  sum_{n in T} 1/n is an
  integer iff for EVERY prime p:   rho_p := sum_{q in N(p)} q^(-1)  ==  0  (mod p).
  1. SEED:  the k smallest semiprimes all of whose primes are <= CAP.
  2. TOP-DOWN REPAIR: for the primes p = largest, ..., TAIL+1 in decreasing order, if rho_p != 0 toggle
     (add, or delete when present) one or two edges {q,p} with q < p so that rho_p becomes 0.  Every
     toggled edge has p as its LARGEST prime, so larger primes stay repaired.  A single toggle needs
     q == (-rho_p)^(-1) mod p to be a prime; otherwise two toggles are found by random sampling of q1
     (then q2 is determined).  Deletions are preferred to additions when they suffice.
  3. EXACT TAIL: after all primes > TAIL are repaired, only the C(pi(TAIL),2) semiprimes built from
     Q = {2,3,5,...,TAIL} may still change.  With x_t in {0,1} their final presence, the sum is
     exactly N  iff   rho_q(out) + sum_t x_t*contribution == 0 (mod q) for q in Q, q >= 5   and
     P0*sum(out) + sum_t x_t*(P0/t) == N*P0,   P0 = product of Q.
     The contribution of a subset of these terms is stage-independent, so two half-tables are built once
     and each stage is one dictionary join (meet in the middle, complete for the tail).
The result satisfies the criterion at every prime, so its sum is an integer, and the integer equation
S == N*P0 makes it exactly N.  It is re-verified independently by verify_semiprime_integer.py.
"""
import sys
import time

from sphenic_search import SplitMix64, primes_upto


class SPAttempt:
    def __init__(self, primes, isprime, idx, edges, rng, pref_pct):
        self.primes = primes
        self.isprime = isprime
        self.idx = idx                            # prime -> its index in `primes`
        self.rng = rng
        self.pref = pref_pct
        self.E = set(edges)                       # edges (a, b), a < b
        self.nb = {}
        for (a, b) in self.E:
            self.nb.setdefault(a, set()).add(b)
            self.nb.setdefault(b, set()).add(a)

    def toggle(self, a, b):
        if (a, b) in self.E:
            self.E.discard((a, b))
            self.nb[a].discard(b)
            self.nb[b].discard(a)
        else:
            self.E.add((a, b))
            self.nb.setdefault(a, set()).add(b)
            self.nb.setdefault(b, set()).add(a)

    def rho(self, p):
        return sum(pow(q % p, -1, p) for q in self.nb.get(p, ())) % p

    def solve(self, p, target):
        """list of q < p whose edges {q,p} must be toggled so that the residue changes by `target` mod p."""
        cur = {q for q in self.nb.get(p, ()) if q < p}
        q0 = pow(target, -1, p)                   # single addition: inv(q) == target
        rem = [q for q in cur if (-pow(q, -1, p) - target) % p == 0]
        add = [q0] if (self.isprime[q0] and q0 not in cur) else []
        if rem and (not add or self.rng.below(100) < self.pref):
            return [rem[self.rng.below(len(rem))]]
        if add:
            return add
        ip = self.idx[p]
        if ip >= 40:                              # two toggles by sampling q1 (q2 is then determined)
            for _ in range(4000):
                q1 = self.primes[self.rng.below(ip)]
                d1 = pow(q1, -1, p)
                if q1 in cur:
                    d1 = (-d1) % p
                d2 = (target - d1) % p
                if d2 == 0:
                    continue
                q2 = pow(d2, -1, p)               # addition of q2
                if q2 != q1 and self.isprime[q2] and q2 not in cur:
                    return [q1, q2]
                q2 = pow((-d2) % p, -1, p)        # deletion of q2
                if q2 != q1 and q2 in cur:
                    return [q1, q2]
        # generic BFS over residues (small p, or sampling failed)
        below = list(self.primes[:ip])
        if len(below) > 400:
            self.rng.shuffle(below)
            below = below[:400]
        tog = []
        for q in below:
            d = pow(q, -1, p)
            tog.append((q, (-d) % p if q in cur else d))
        self.rng.shuffle(tog)
        level = {0: []}
        seen = {0}
        for _ in range(10):
            nxt = {}
            for r, sub in level.items():
                for j, (q, d) in enumerate(tog):
                    if j in sub:
                        continue
                    r2 = (r + d) % p
                    if r2 not in seen:
                        seen.add(r2)
                        nxt[r2] = sub + [j]
            if target in nxt:
                return [tog[j][0] for j in nxt[target]]
            level = nxt
            if not level:
                break
        return None

    def run_top(self, pmax, pmin):
        for p in reversed([q for q in self.primes if pmin <= q <= pmax]):
            r = self.rho(p)
            if r == 0:
                continue
            sol = self.solve(p, (-r) % p)
            if sol is None:
                return False
            for q in sol:
                self.toggle(q, p)
        return True


class SPTailJoin:
    def __init__(self, primes, tail):
        self.Q = [p for p in primes if p <= tail]
        self.C = [q for q in self.Q if q >= 5]
        self.M = 1
        for q in self.C:
            self.M *= q
        self.P0 = 1
        for p in self.Q:
            self.P0 *= p
        self.e = {q: (self.M // q) * pow(self.M // q, -1, q) % self.M for q in self.C}
        self.terms = [(a, b) for i, a in enumerate(self.Q) for b in self.Q[i + 1:]]
        self.key = []
        self.val = []
        for (a, b) in self.terms:
            k = 0
            if a in self.e:
                k += pow(b % a, -1, a) * self.e[a]
            if b in self.e:
                k += pow(a % b, -1, b) * self.e[b]
            self.key.append(k % self.M)
            self.val.append(self.P0 // (a * b))
        half = len(self.terms) // 2
        self.left = list(range(half))
        self.right = list(range(half, len(self.terms)))
        self.tabL = self._table(self.left)
        best = {}
        for mask, (k, v, pc) in enumerate(self._table(self.right)):
            if (k, v) not in best or pc < best[(k, v)][0]:
                best[(k, v)] = (pc, mask)
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

    def scaled_sum(self, edges):
        """P0 * sum_{(a,b) in edges} 1/(a*b) as an exact integer.

        Precondition (guaranteed once every prime above the tail is repaired): this quantity is an integer.
        Then, with FP = 2^160 and acc = sum floor(FP/(a*b)), we have  0 <= sum*FP - acc < len(edges),
        hence  S*FP - P0*acc  lies in [0, P0*len(edges)) and P0*len(edges) < FP, so S = ceil(P0*acc / FP).
        (Pure integer arithmetic; avoids a huge common denominator.)"""
        FP = 1 << 160
        assert self.P0 * len(edges) < FP
        acc = 0
        for (a, b) in edges:
            acc += FP // (a * b)
        return (self.P0 * acc + FP - 1) >> 160

    def solve(self, at, N):
        """Returns (chosen tail terms, out edges) giving sum exactly N with the fewest terms, or None."""
        tail_max = self.Q[-1]
        out = [e for e in at.E if e not in self.tail_set]
        S_out = self.scaled_sum(out)
        tval = N * self.P0 - S_out
        if tval < 0:
            return None
        tkey = 0
        for q in self.C:
            r = 0
            for x in at.nb.get(q, ()):
                if x > tail_max:
                    r += pow(x % q, -1, q)
            tkey = (tkey - (r % q) * self.e[q]) % self.M
        best = None
        dictR, M = self.dictR, self.M
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


def exact_sum_is(nums, N):
    """Exact test  sum 1/n == N  (unreduced numerator/denominator pairs, balanced product tree)."""
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


def semiprime_pool(primes, cap, limit):
    ps = [p for p in primes if p <= cap]
    out = []
    for i, a in enumerate(ps):
        if a * ps[i + 1] > limit:
            break
        for b in ps[i + 1:]:
            if a * b > limit:
                break
            out.append((a * b, a, b))
    out.sort()
    return out


def main():
    import argparse
    ap = argparse.ArgumentParser(description="semiprime unit fractions summing to an integer N (exact integer arithmetic)")
    ap.add_argument("--N", type=int, default=2, help="target integer (default 2)")
    ap.add_argument("--cap", type=int, default=1500, help="seed uses only primes <= CAP")
    ap.add_argument("--kmin", type=int, default=2000)
    ap.add_argument("--kmax", type=int, default=2300)
    ap.add_argument("--pool", type=int, default=200000, help="largest semiprime considered for the seed")
    ap.add_argument("--tail", type=int, default=23)
    ap.add_argument("--pref", type=int, default=90)
    ap.add_argument("--tries", type=int, default=1000)
    ap.add_argument("--bound", type=int, default=10 ** 9, help="keep only sets with at most this many terms")
    ap.add_argument("--minimize", action="store_true", help="use all tries and keep the smallest set")
    ap.add_argument("--seed", type=int, default=897)
    ap.add_argument("--out", default="semiprime_sum.txt")
    ap.add_argument("--dump-all", default=None, metavar="FILE")
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args()
    t0 = time.time_ns()
    args.cap = min(args.cap, args.pool // 2)
    pool = semiprime_pool(primes_upto(args.pool // 2 + 2)[0], args.cap, args.pool)
    assert len(pool) >= args.kmax, "seed pool too small; raise --pool or --cap"
    primes, isprime = primes_upto(max(args.cap, args.pool // 2) + 2)
    idx = {p: i for i, p in enumerate(primes)}
    tj = SPTailJoin(primes, args.tail)
    print(f"tables built in {(time.time_ns() - t0) // 1_000_000} ms; tail terms {len(tj.terms)}", flush=True)
    rng = SplitMix64(args.seed)
    dump = open(args.dump_all, "w") if args.dump_all else None
    stats = {"top_fail": 0, "no_leaf": 0, "found": 0}
    best = None
    attempts = 0
    while attempts < args.tries:
        attempts += 1
        k = args.kmin + rng.below(args.kmax - args.kmin)
        seed_edges = [(a, b) for (_, a, b) in pool[:k]]
        at = SPAttempt(primes, isprime, idx, seed_edges, rng, args.pref)
        top = max(p for e in seed_edges for p in e)
        if not at.run_top(top, args.tail + 1):
            stats["top_fail"] += 1
            continue
        res = tj.solve(at, args.N)
        if res is None:
            stats["no_leaf"] += 1
            continue
        chosen, out = res
        final = set(out) | set(chosen)
        nums = sorted(a * b for (a, b) in final)
        assert exact_sum_is(nums, args.N), "internal error: sum != N"
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
        print(f"no solution with <= {args.bound} terms in {attempts} attempts")
    else:
        nums, k, att = best
        with open(args.out, "w") as f:
            f.write("\n".join(map(str, nums)) + "\n")     # one denominator per row
        print(f"FOUND: N={args.N}, |T|={len(nums)}, sum == {args.N} exactly; seed size k={k}, cap={args.cap}, attempt {att}; wrote {args.out}")
    print(f"attempts={attempts}, elapsed {dt // 1000}.{dt % 1000:03d} s, {stats}")


if __name__ == "__main__":
    main()
