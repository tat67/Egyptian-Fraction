#!/usr/bin/env python3
"""Enumerate every set X of non-semiprime elements <= L that can occur in a solution of shape
   (K - J elements <= L) + (J elements > L),  i.e. every antichain X of integers <= L that are neither prime powers
   nor squarefree semiprimes, with
       sum_X 1/x + top_{K-J-|X|}( semiprimes <= L not dividing an element of X ) + sum_{i=1..J} 1/(L+i)  >=  1.
   (The elements <= L outside X are semiprimes not dividing any x in X; elements > L have reciprocal sum below the tail.)
   Depth-first search over candidates in increasing order.  A branch is cut only if the valid upper bound
       sum_X + max_t [ (t largest remaining candidate reciprocals) + top_{K-J-|X|-t}(semiprimes \\ E(X)) ] + tail
   is below 1.  All reciprocals are integers ceil(2^96/n) (rounded UP), so the test can only keep extra sets, never
   lose one.  Usage: python3 xsets.py K J [L] > xsets_KJ.txt
"""
import sys
K = int(sys.argv[1]); J = int(sys.argv[2]); L = int(sys.argv[3]) if len(sys.argv) > 3 else 1140
ONE = 1 << 96
up = lambda n: -(-ONE // n)
P = [p for p in range(2, L + 1) if all(p % d for d in range(2, int(p ** .5) + 1))]
def fac(n):
    r = {}
    for p in P:
        if p * p > n: break
        while n % p == 0: r[p] = r.get(p, 0) + 1; n //= p
    if n > 1: r[n] = r.get(n, 0) + 1
    return r
S = sorted(p * q for i, p in enumerate(P) for q in P[i + 1:] if p * q <= L)
SV = [up(s) for s in S]
NS = [x for x in range(6, L + 1) if len(fac(x)) >= 2 and not (len(fac(x)) == 2 and all(e == 1 for e in fac(x).values()))]
NV = [up(x) for x in NS]
semdiv = {x: frozenset(i for i, s in enumerate(S) if x % s == 0) for x in NS}
tail = sum(up(L + i) for i in range(1, J + 1))
def toplist(k, E):
    out = []
    if k <= 0: return out
    for i, v in enumerate(SV):
        if i not in E:
            out.append(v)
            if len(out) == k: break
    return out
count = 0
def dfs(i, X, sX, E):
    global count
    k = K - J - len(X)
    if k < 0: return
    tp = toplist(k, E); stp = sum(tp)
    if X and sX + stp + tail >= ONE:
        print(" ".join(map(str, X))); count += 1
    best = sX + stp; acc = 0; s2 = stp
    for t in range(1, k + 1):
        if i + t - 1 >= len(NS): break
        acc += NV[i + t - 1]; s2 -= tp[k - t]
        if sX + acc + s2 > best: best = sX + acc + s2
    if best + tail < ONE: return
    for j in range(i, len(NS)):
        x = NS[j]
        if any(x % y == 0 or y % x == 0 for y in X): continue
        dfs(j + 1, X + [x], sX + NV[j], E | semdiv[x])
dfs(0, [], 0, frozenset())
print("# K=%d J=%d L=%d: %d sets" % (K, J, L, count), file=sys.stderr)
