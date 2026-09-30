#!/usr/bin/env python3
"""Independent cross-check of semiprime_maxden.cpp (exact arithmetic only).

A different algorithm from the C++ program: it uses only the local congruences (no value
bound), and it searches by primes instead of by edges.

For a bound B, a set T of squarefree semiprimes <= B is a graph on the primes <= B/2.
If sum 1/n over T is an integer (in particular if it is 1), then for every prime q the
residue sum_{p : pq in T} p^{-1} is 0 mod q.

 1. Arc consistency: an edge {p, q} is deleted when no subset of the remaining edges at q
    (or at p) that contains it has residue 0.  This is repeated until nothing changes.
 2. Depth-first search over the primes in decreasing order.  At prime q the edges to larger
    primes are already decided; the search enumerates every subset S of the remaining edges
    to smaller primes with  residue(q) + sum_{p in S} p^{-1} = 0 (mod q).  Each choice
    must leave every smaller neighbour p able to reach residue 0 with the edges still open
    at p.
 3. Every complete assignment satisfies all congruences, so its reciprocal sum is a positive
    integer; it is recomputed with fractions.Fraction and kept if it equals 1.

Run:  python3 crosscheck_maxden.py [B ...]      (default: 588 589)
For B = 588 the search must find no nonempty T at all.  For B = 589 it finds the sets with
integral sum, and exactly those with sum 1 are reported.
"""
import sys
import time
from fractions import Fraction


def primes_upto(n):
    s = bytearray([1]) * (n + 1)
    s[0:2] = b"\x00\x00"
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i :: i] = bytearray(len(s[i * i :: i]))
    return [i for i in range(n + 1) if s[i]]


def reach_sets(q, invs):
    """prefix reachable residue sets as Python int bit masks; pre[k] uses invs[:k]."""
    full = (1 << q) - 1
    pre = [1]
    for a in invs:
        r = pre[-1]
        rot = ((r << a) | (r >> (q - a))) & full
        pre.append(r | rot)
    return pre


def arc_consistency(B):
    ps = primes_upto(B // 2)
    adj = {p: set() for p in ps}
    for i, p in enumerate(ps):
        for q in ps[i + 1 :]:
            if p * q > B:
                break
            adj[p].add(q)
            adj[q].add(p)
    changed = True
    while changed:
        changed = False
        for q in ps:
            nb = sorted(adj[q])
            if not nb:
                continue
            invs = [pow(r, -1, q) for r in nb]
            k = len(nb)
            pre = [{0}]
            for a in invs:
                pre.append(pre[-1] | {(x + a) % q for x in pre[-1]})
            suf = [set() for _ in range(k + 1)]
            suf[k] = {0}
            for i in range(k - 1, -1, -1):
                suf[i] = suf[i + 1] | {(x + invs[i]) % q for x in suf[i + 1]}
            for i in range(k):
                need = (-invs[i]) % q
                if not any(((need - x) % q) in suf[i + 1] for x in pre[i]):
                    adj[q].discard(nb[i])
                    adj[nb[i]].discard(q)
                    changed = True
    return {p: sorted(v) for p, v in adj.items() if v}


def search(B):
    adj = arc_consistency(B)
    ps = sorted(adj)  # primes that still have edges
    idx = {p: i for i, p in enumerate(ps)}
    # for prime r and a threshold t: residues reachable with the neighbours of r below t
    # (neighbours sorted ascending; below[r][j] uses the first j neighbours)
    below = {}
    inv = {}
    for r in ps:
        nb = adj[r]
        inv[r] = [pow(x, -1, r) for x in nb]
        below[r] = reach_sets(r, inv[r])
    pos = {(r, s): j for r in ps for j, s in enumerate(adj[r])}
    rho = {p: 0 for p in ps}
    chosen = []
    found = []
    nodes = [0]

    def ok_at(r, q):
        # r < q: after deciding the edge {r, q}, the neighbours of r still open are those < q
        j = pos[(r, q)]
        return (below[r][j] >> ((-rho[r]) % r)) & 1

    def process(i):
        if i < 0:
            if chosen:
                found.append(sorted(p * q for p, q in chosen))
            return
        q = ps[i]
        lower = [p for p in adj[q] if p < q]
        k = len(lower)
        pre = below[q]  # first k neighbours of q are exactly the lower ones

        def enum(j, need):
            # decide lower[j-1], ..., lower[0]; need = residue still to be added at q
            nodes[0] += 1
            if not (pre[j] >> need) & 1:
                return
            if j == 0:
                process(i - 1)
                return
            p = lower[j - 1]
            a = inv[q][j - 1]
            # include p*q
            old = rho[p]
            rho[p] = (old + pow(q, -1, p)) % p
            if ok_at(p, q):
                chosen.append((p, q))
                enum(j - 1, (need - a) % q)
                chosen.pop()
            rho[p] = old
            # exclude p*q
            if ok_at(p, q):
                enum(j - 1, need)

        enum(k, (-rho[q]) % q)

    process(len(ps) - 1)
    return adj, found, nodes[0]


def main():
    bounds = [int(x) for x in sys.argv[1:]] or [588, 589]
    for B in bounds:
        t0 = time.monotonic_ns()
        adj, found, nodes = search(B)
        ms = (time.monotonic_ns() - t0) // 1_000_000
        edges = sum(len(v) for v in adj.values()) // 2
        print(f"B = {B}: edges left after arc consistency: {edges}, primes: {len(adj)}")
        print(f"  search nodes: {nodes}, sets with integral reciprocal sum: {len(found)}  ({ms} ms)")
        ones = []
        for T in found:
            s = sum(Fraction(1, n) for n in T)
            assert s.denominator == 1 and s >= 1, "congruences hold, so the sum is a positive integer"
            if s == 1:
                ones.append(T)
        print(f"  of these with sum exactly 1: {len(ones)}")
        for T in ones:
            print(f"    |T| = {len(T)}, max T = {max(T)}: {' '.join(map(str, T))}")
        if ones:
            print(f"  smallest max T within the bound: {min(max(T) for T in ones)}")


if __name__ == "__main__":
    main()
