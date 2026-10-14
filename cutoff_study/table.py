"""Turn the sweep outputs of cutoff_study.cpp into markdown tables."""
import re, sys
def rows(path):
    out = []
    for line in open(path):
        if line.startswith('SB') and 'SKIPPED' in line:
            out.append({'SB': int(line.split()[1]), 'skipped': line.strip()})
            continue
        if not line.startswith('SB'): continue
        g = lambda pat: re.search(pat, line).group(1)
        r = dict(SB=int(g(r'SB (\d+)')), m=int(g(r' m (\d+)')), b0=int(g(r'b0 (\d+)')), star=int(g(r'maxStar (\d+)')),
                 nodes=int(g(r'nodes (\d+)')), cores=int(g(r'cores (\d+)')), t1=int(g(r'cores \d+ ms (\d+)')),
                 shapes=int(g(r'shapes (\d+)')), alive=int(g(r'alive (\d+)')), b2=int(g(r'b>=2 (\d+)')),
                 stars=int(g(r'stars (\d+)')), unres=int(g(r'unresolved (\d+)')), prob=int(g(r'probable (\d+)')),
                 t2=int(g(r'probable \d+ ms (\d+)')), tot=int(g(r'total ms (\d+)')),
                 sols=re.findall(r'\|T\|=(\d+): (\d+)', line))
        out.append(r)
    return sorted(out, key=lambda r: r['SB'])
for path in sys.argv[1:]:
    print(f'\n{path}\n')
    print('| B | \\|S\\| | b₀ | core elements | Step 1 nodes | cores kept | Step 1 s | shapes (S1–S3) | b=2 shapes | Step 2 s | total s | unresolved | solutions |')
    print('|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|')
    for r in rows(path):
        if 'skipped' in r:
            why = r['skipped'].split('SKIPPED: ')[1]
            print(f"| {r['SB']} | | | | — | — | — | — | — | — | skipped: {why} | | |"); continue
        sol = ', '.join(f'{c} of size {s}' for s, c in r['sols']) or '0'
        # a run with unresolved shapes or probable primes is not a complete search
        tot = f"**{r['tot']/1000:.1f}**" if r['unres'] == 0 and r['prob'] == 0 else f"{r['tot']/1000:.1f} (incomplete)"
        print(f"| {r['SB']} | {r['m']} | {r['b0']} | {r['m']*(r['m']-1)//2} | {r['nodes']:,} | {r['cores']:,} | {r['t1']/1000:.1f} | {r['shapes']:,} | {r['b2']} | {r['t2']/1000:.1f} | {tot} | {r['unres']} | {sol} |")
