#!/usr/bin/env python3
"""Compare the re-execution of the budget-47 search with the recorded run.
Inputs : rerun47.log (output of `./semiprime47 4 --dump cores47_rerun.txt`), cores47_rerun.txt.gz,
         ../../../run47_output.txt, ../../../cores47.txt.gz, ../../../solutions47.txt
Output : printed report (saved as rerun47_comparison.txt)."""
import gzip, os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.normpath(os.path.join(HERE, '..', '..', '..'))
def stats(path):
    t = open(path).read(); g = lambda p: int(re.search(p, t).group(1))
    sols = sorted(tuple(map(int, m.group(1).split())) for m in re.finditer(r'OK\s+\|T\|=47:\s*([\d ]+)', t))
    bad = len(re.findall(r'BAD', t))
    return dict(nodes=g(r'search nodes\s*:\s*(\d+)'), cores=g(r'cores passing Step 1\s*:\s*(\d+)'),
                tight=g(r'\|C\|\+\|U\| = 47:\s*(\d+)'), shapes=g(r'completion shapes\s*:\s*(\d+) tried'),
                alive=g(r'(\d+) pass parity'), alive_cores=g(r'\(in (\d+) cores\)'), cand=g(r'(\d+) candidate stars'),
                unresolved=g(r'unresolved cores\s*:\s*(\d+)'), probable=g(r'probable \(not proven\) primes used:\s*(\d+)'),
                search_s=g(r'elapsed:\s*(\d+) s'), solutions=sols, bad=bad)
def dump_lines(path):
    op = gzip.open if path.endswith('.gz') else open
    with op(path, 'rt') as f: return sorted(l.strip() for l in f if l.strip())
old = stats(os.path.join(ROOT, 'run47_output.txt')); new = stats(os.path.join(HERE, 'rerun47.log'))
print('quantity            recorded            re-execution        equal')
for k in ('nodes', 'cores', 'tight', 'shapes', 'alive', 'alive_cores', 'cand', 'unresolved', 'probable', 'bad', 'search_s'):
    print('%-18s %-19s %-19s %s' % (k, old[k], new[k], old[k] == new[k]))
print('solution lists identical:', old['solutions'] == new['solutions'], '(%d / %d)' % (len(old['solutions']), len(new['solutions'])))
ref = sorted(tuple(sorted(map(int, m.group(2).split()))) for m in (re.match(r'#\s*(\d+):\s*(.*)', l) for l in open(os.path.join(ROOT, 'solutions47.txt'))) if m)
print('re-execution solutions == solutions47.txt:', sorted(new['solutions']) == ref)
a = dump_lines(os.path.join(ROOT, 'cores47.txt.gz'))
bpath = os.path.join(HERE, 'cores47_rerun.txt.gz') if os.path.exists(os.path.join(HERE, 'cores47_rerun.txt.gz')) else os.path.join(HERE, 'cores47_rerun.txt')
b = dump_lines(bpath)
print('core dump lines: recorded %d, re-execution %d, identical as sets: %s' % (len(a), len(b), a == b))
ok = all(old[k] == new[k] for k in ('nodes', 'cores', 'tight', 'shapes', 'alive', 'alive_cores', 'cand', 'unresolved', 'probable', 'bad')) \
     and old['solutions'] == new['solutions'] and a == b
print('OVERALL:', 'IDENTICAL (except timing)' if ok else 'DIFFERENCES FOUND')
