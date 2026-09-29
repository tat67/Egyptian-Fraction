"""Print the import closure (module, source root) of the given modules, Lean core excluded."""
import re, os, sys
roots = sys.argv[1:]
M = os.environ.get('M', os.getcwd())   # the Mathlib checkout
srcdirs = [M] + [os.path.join(M, '.lake/packages', p) for p in os.listdir(os.path.join(M, '.lake/packages'))]
def find(mod):
    rel = mod.replace('.', '/') + '.lean'
    for d in srcdirs:
        f = os.path.join(d, rel)
        if os.path.exists(f): return d, f
    return None, None
def header_imports(src):
    # strip block comments (non-nested approx, handles nesting)
    out = []; i = 0; depth = 0; n = len(src)
    while i < n:
        if src.startswith('/-', i): depth += 1; i += 2; continue
        if depth and src.startswith('-/', i): depth -= 1; i += 2; continue
        if depth == 0: out.append(src[i])
        i += 1
    txt = ''.join(out)
    imps = []
    for line in txt.split('\n'):
        s = line.split('--')[0].strip()
        if not s: continue
        if s in ('module', 'prelude') : continue
        mm = re.match(r'^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(.+)$', s)
        if mm: imps += mm.group(1).split(); continue
        break
    return imps
seen = {}
stack = list(roots)
while stack:
    m = stack.pop()
    if m in seen: continue
    top = m.split('.')[0]
    if top in ('Init', 'Std', 'Lean', 'Lake'):
        seen[m] = None; continue
    d, f = find(m)
    if f is None:
        print('MISSING', m, file=sys.stderr); seen[m] = None; continue
    seen[m] = d
    stack += header_imports(open(f, encoding='utf-8').read())
for m, d in sorted(seen.items()):
    if d is not None: print(m, d)
