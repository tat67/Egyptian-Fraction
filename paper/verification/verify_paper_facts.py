#!/usr/bin/env python3
"""Independent exact verification of every numerical statement used in the paper, and
generation of the LaTeX tables in ../tables/ (so that no table entry is typed by hand).

Uses only Python integers and fractions.Fraction (exact).  Input: ../../solutions47.txt.
Primality is decided by trial division (all numbers involved are < 10^6)."""
import re, os, sys, json, itertools
from fractions import Fraction as F
from math import prod

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, '..', '..'))
TAB = os.path.normpath(os.path.join(HERE, '..', 'tables'))

def is_prime(n):
    if n < 2: return False
    d = 2
    while d * d <= n:
        if n % d == 0: return False
        d += 1
    return True

def sp_factor(n):
    """return (p, q) with p < q primes and p*q = n, or None"""
    d = 2
    while d * d <= n:
        if n % d == 0:
            p, q = d, n // d
            return (p, q) if (p != q and is_prime(p) and is_prime(q)) else None
        d += 1
    return None

facts = {}
# ---------------------------------------------------------------- the ordered semiprimes a_k
A = [n for n in range(2, 5000) if sp_factor(n)]
H = lambda k: sum(F(1, a) for a in A[:k])
facts['a_1..a_48'] = A[:48]
for k in (35, 36, 37, 38, 46, 47):
    h = H(k)
    facts['H_%d' % k] = {'num': h.numerator, 'den': h.denominator, 'approx': float(h), 'a_k': A[k - 1]}
assert H(37) < 1 < H(38) and H(46) < 2 and H(47) < 2
assert H(35) < 1 - F(1757, 79000)
# ---------------------------------------------------------------- V(x) and b_k
BIGSP = [n for n in A if max(sp_factor(n)) > 73]
facts['V_terms_first_12'] = BIGSP[:12]
V = lambda x: sum(F(1, n) for n in BIGSP[:x])
facts['V(46)'] = float(V(46)); facts['V(47)'] = float(V(47))
assert V(47) < 1 and V(47) <= F(47, 158)
BIGP = [p for p in range(74, 400) if is_prime(p)]
facts['b_0..b_5'] = BIGP[:6]
S = [p for p in range(2, 74) if is_prime(p)]
assert len(S) == 21 and len(list(itertools.combinations(S, 2))) == 210
facts['sum_1/q_q<=73'] = float(sum(F(1, q) for q in S))
assert sum(F(1, q) for q in S) <= F(1757, 1000)
# ---------------------------------------------------------------- star-size lemma (exact)
def max_star(K):
    best = 0
    for d in range(1, len(S) + 1):
        z = sum(F(1, 79 * q) for q in S[:d])      # the d largest values 1/(79 q)
        h = H(K - d)                               # other <= K-d elements
        if z + h >= 1: best = d
    return best
facts['max_star_K46'] = max_star(46); facts['max_star_K47'] = max_star(47)
assert facts['max_star_K46'] == 10 and facts['max_star_K47'] == 11
# ---------------------------------------------------------------- the 23 solutions
sols = []
for line in open(os.path.join(ROOT, 'solutions47.txt')):
    m = re.match(r'#\s*(\d+):\s*(.*)', line)
    if m: sols.append(sorted(map(int, m.group(2).split())))
assert len(sols) == 23
assert len(set(tuple(s) for s in sols)) == 23, "solutions not distinct"
rows = []; big_rows = []
for idx, T in enumerate(sols, 1):
    assert len(T) == 47 and len(set(T)) == 47
    fac = {n: sp_factor(n) for n in T}
    assert all(fac.values()), "non-squarefree-semiprime element"
    assert sum(F(1, n) for n in T) == 1
    # local criterion (*) at every prime, checked independently
    nbrs = {}
    for n, (p, q) in fac.items():
        nbrs.setdefault(p, []).append(q); nbrs.setdefault(q, []).append(p)
    for p, N in nbrs.items():
        assert sum(pow(q, -1, p) for q in N) % p == 0
    primes = sorted(nbrs)
    big = [P for P in primes if P > 73]
    core = [n for n in T if max(fac[n]) <= 73]
    U = sorted(q for q in S if sum(pow(r, -1, q) for n in core for (a, b) in [fac[n]] if q in (a, b)
                                   for r in [b if a == q else a]) % q)
    info = dict(index=idx, max_prime=max(primes), n_primes=len(primes), core_size=len(core),
                U=U, big=big, elements=T)
    if big:
        assert len(big) == 1
        P = big[0]; Aset = sorted(nbrs[P]); nA = sum(prod(Aset) // q for q in Aset)
        assert all(q <= 73 for q in Aset) and nA % P == 0 and Aset == U
        info.update(P=P, A=Aset, nA=nA, nA_over_P=nA // P, big_elements=sorted(q * P for q in Aset))
        big_rows.append(info)
    rows.append(info)
facts['n_solutions'] = 23
facts['n_all_primes_le_73'] = sum(1 for r in rows if not r['big'])
facts['n_one_big_prime'] = sum(1 for r in rows if r['big'])
facts['big_primes'] = sorted(r['P'] for r in big_rows)
facts['n_primes_le_101_only'] = sum(1 for r in rows if r['max_prime'] <= 101)
facts['min_prime_count'] = min(r['n_primes'] for r in rows); facts['max_prime_count'] = max(r['n_primes'] for r in rows)
common = set(sols[0])
for T in sols: common &= set(T)
facts['common_to_all_23'] = sorted(common)
facts['union_size'] = len(set().union(*map(set, sols)))
# Watanabe-type example quoted in README.md
ex = [6,10,14,15,21,22,26,33,34,35,38,39,46,51,55,57,58,62,65,69,77,82,85,86,87,91,93,94,95,118,119,123,133,145,155,161,187,203,215,287,329,493,517,1247,1357,1363,2537]
facts['readme_example_index'] = [r['index'] for r in rows if r['elements'] == sorted(ex)]
json.dump({k: v for k, v in facts.items()}, open(os.path.join(HERE, 'facts.json'), 'w'), indent=1, default=str)
for k, v in facts.items():
    if not k.startswith('a_1'): print(k, ':', v)
# ---------------------------------------------------------------- LaTeX tables
def tex_int_list(xs): return ', '.join(map(str, xs))
with open(os.path.join(TAB, 'bigprime_table.tex'), 'w') as f:
    f.write('% generated by verification/verify_paper_facts.py -- do not edit by hand\n')
    for r in sorted(big_rows, key=lambda r: r['P']):
        a, b, c = r['A']
        f.write('%d & $\\{%d, %d, %d\\}$ & $%s$ & %s & %s \\\\\n' % (
            r['P'], a, b, c, ('%d = %d\\cdot %d' % (r['nA'], r['nA_over_P'], r['P'])) if r['nA_over_P'] > 1 else '%d' % r['P'],
            tex_int_list(r['big_elements']), r['index']))
with open(os.path.join(TAB, 'solutions_table.tex'), 'w') as f:
    f.write('% generated by verification/verify_paper_facts.py -- do not edit by hand\n')
    base = set(common)
    for r in rows:
        extra = [n for n in r['elements'] if n not in base]
        f.write('%d & %d & %d & %s & %s \\\\\n' % (r['index'], r['max_prime'], r['core_size'],
                (str(r['P']) if r['big'] else '--'), tex_int_list(extra)))
with open(os.path.join(TAB, 'full_solutions.tex'), 'w') as f:
    f.write('% generated by verification/verify_paper_facts.py -- do not edit by hand\n')
    for r in rows:
        f.write('\\solitem{%d}{%s}\n' % (r['index'], tex_int_list(r['elements'])))
with open(os.path.join(TAB, 'hk_table.tex'), 'w') as f:
    f.write('% generated by verification/verify_paper_facts.py -- do not edit by hand\n')
    for k in (35, 37, 38, 46, 47):
        h = facts['H_%d' % k]
        f.write('%d & %d & %.6f & %d \\\\\n' % (k, h['a_k'], h['approx'], len(str(h['den']))))
print("common elements:", len(common))
# exact H_k table (reduced fractions), generated to avoid transcription errors
with open(os.path.join(TAB, 'hk_exact.tex'), 'w') as f:
    f.write('% generated by verification/verify_paper_facts.py -- do not edit by hand\n')
    for k, cmp in ((35, '< 1 - \\tfrac{1757}{79000}'), (37, '< 1'), (38, '> 1'), (46, '< 2'), (47, '< 2')):
        h = facts['H_%d' % k]
        f.write('$H_{%d}$ & $%d$ & %d & %d & $%.6f\\ldots$ & $%s$ \\\\\n' % (
            k, h['a_k'], h['num'], h['den'], int(h['approx'] * 10**6) / 10**6, cmp))
