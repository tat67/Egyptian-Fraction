#!/bin/sh
# run.sh [WORKDIR] : reproduce the analysis of the hvds/seq A101877 solver (see README.md here).
#
# 1. Fetch hvds/seq at a fixed commit. A101877/ there is unchanged since v9.7 + "results" (2015-01-20).
# 2. Build the solver as published (C_int) and with fix_same_prime_carry.patch (C_int_fixed).
# 3. Build the tracer guided.c against both, and follow the a(7) and a(8) witnesses through them.
# 4. Run both solvers for n = 3..7, and check every printed set with exact fractions.
# Needs gcc, libgmp-dev, git, python3. Logs go to stdout.
set -e
here=$(cd "$(dirname "$0")" && pwd)
w=${1:-$(mktemp -d)}
rev=e0b76ebc5cb3503c4b11ae43a8385a9710bbc329
mkdir -p "$w"
if [ ! -d "$w/seq" ]; then
  git init -q "$w/seq"
  git -C "$w/seq" fetch -q --depth 1 https://github.com/hvds/seq "$rev"
  git -C "$w/seq" checkout -q FETCH_HEAD
fi
cd "$w"
rm -rf orig fixed && cp -r seq/A101877 orig && cp -r seq/A101877 fixed
(cd fixed && patch -s -p1 < "$here/fix_same_prime_carry.patch")
for v in orig fixed; do
  (cd $v
   srcs="pp.c walker.c mygmp.c mbh.c prime.c inverse.c"
   cat C_int.c $srcs > all.c
   gcc -O2 -fgnu89-inline -fwhole-program -I. -DALL_C -o C_int all.c -lgmp 2>/dev/null
   sed 's/^int main(/int orig_main(/' C_int.c > C_int_nomain.c
   cat C_int_nomain.c $srcs "$here/guided.c" > all_g.c
   gcc -O2 -fgnu89-inline -I. -DALL_C -o C_guided all_g.c -lgmp 2>/dev/null)
done
W="$here/../witnesses"
for v in orig fixed; do
  echo "################ tracer, solver $v"
  for nk in "7 1243 witness_n7_max1243.txt" "8 3228 witness_n8_max3228.txt" "8 3229 witness_n8_max3228.txt" "8 3230 witness_n8_max3228.txt"; do
    set -- $nk
    ./$v/C_guided $1 $2 "$W/$3" | grep -v '^level .*required [0-9]*$'
    echo
  done
done
for v in orig fixed; do
  echo "################ solver $v: n = 3..7, k increasing from 1 (or from 1240 for n = 7)"
  for n in 3 4 5 6 7; do
    s=1; [ $n = 7 ] && s=1240
    ./$v/C_int $n $s 0 > $v/out_$n.txt 2>&1 || true
    python3 -I - $n $s $v/out_$n.txt <<'EOF'
import re, sys
from fractions import Fraction
n, start = int(sys.argv[1]), int(sys.argv[2]); lines = open(sys.argv[3]).read().split('\n')
failed = [int(m.group(1)) for l in lines for m in [re.search(r'k=(\d+)', l)] if m and 'solution' in l]
k = max(failed) + 1 if failed else start          # the scan stops at the first k reported as a success
nos = [l.split(':')[0] for l in lines if 'no solution found' in l]
i = max(j for j, l in enumerate(lines) if l.startswith('probable solution'))
S = [int(t) for t in lines[i + 1].split(':')[-1].split()]
s = sum(Fraction(1, x) for x in S)
print(f"n={n}: success reported at k={k}; printed set: {len(S)} elements, max {max(S)}, sum 1/x = {s}"
      f" -> {'a genuine solution' if s == n else 'NOT a solution'}"
      + (f"; last 'no solution found': {nos[-1]}" if nos else ""))
EOF
  done
done
