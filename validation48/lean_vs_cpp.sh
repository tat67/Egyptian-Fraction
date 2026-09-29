#!/bin/bash
# Compare the output of the Lean search `Inst.search` (lean/SemiprimeEgypt/Search.lean, proved
# exhaustive in SearchCorrect.lean / SearchReal.lean), compiled to native code, with the cores
# kept by Step 1 of ../semiprime48.cpp (harness dfs48_harness.cpp, Step 2 disabled).
#
# Usage: bash lean_vs_cpp.sh <runG> "SB K" "SB K" ...
#   <runG>: the compiled Lean runner (source: lean_runner/RunG.lean);
#   "SB K": S = primes <= SB, budget K; SB = 73 is the real instance (inst73 K),
#           other SB use the reduced instance `mkInst SB K`.
set -e
RUNG=$1; shift
HERE=$(cd "$(dirname "$0")" && pwd)
TMP=$(mktemp -d)
g++ -O3 -march=native -pthread -o "$TMP/dfs48" "$HERE/dfs48_harness.cpp"
for inst in "$@"; do
  set -- $inst
  SB=$1; K=$2
  "$TMP/dfs48" "$SB" "$K" 1 0 "$TMP/cpp.txt" > "$TMP/cpp.log"
  if [ "$SB" = 73 ]; then "$RUNG" "$K" > "$TMP/lean.txt" 2> "$TMP/lean.log"
  else "$RUNG" "$SB" "$K" > "$TMP/lean.txt" 2> "$TMP/lean.log"; fi
  python3 - "$TMP/cpp.txt" "$TMP/lean.txt" "$SB" "$K" "$(cat "$TMP/cpp.log")" "$(cat "$TMP/lean.log")" <<'EOF'
import sys
cpp_f, lean_f, sb, k, cpp_log, lean_log = sys.argv[1:]
def cpp_cores(f):
    out = []
    for line in open(f):
        t = line.split()
        if 'C' not in t: continue
        out.append(tuple(sorted(int(x) for x in t[t.index('C') + 1:])))
    return out
def lean_cores(f):
    return [tuple(sorted(int(x) for x in line.split())) for line in open(f)]
a, b = cpp_cores(cpp_f), lean_cores(lean_f)
ok = sorted(a) == sorted(b) and len(set(b)) == len(b)
print(f"S = primes <= {sb}, K = {k}: C++ {len(a)} cores, Lean {len(b)} cores, "
      f"{'IDENTICAL' if ok else 'DIFFERENT'}  [C++: {cpp_log.strip()}] [Lean: {lean_log.strip()}]")
if not ok: sys.exit(1)
EOF
done
rm -rf "$TMP"
