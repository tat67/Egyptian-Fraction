#!/bin/bash
# Checks that the new Step 1 (semiprime48.cpp, with the loss bound (P4)) outputs EXACTLY the same
# set of cores as the old Step 1 (semiprime47.cpp), and compares both with a brute-force
# enumeration of all cores on reduced instances.
#   part A: reduced instances S = primes <= 13, 17, 19, 23 (several budgets): old vs new, and
#           brute force (SEG ⊆ D ⊆ FIN, see paper/verification/step1_bruteforce) for S <= 19
#   part B: the real instance S = primes <= 73 with budgets 40..45: old vs new
#   part C: the archived budget-46 and budget-47 dumps of the old program vs new runs
# Usage: bash step1_equivalence.sh [threads]      (about 10 minutes on 4 cores)
set -e
cd "$(dirname "$0")"
T=${1:-4}
ROOT=..
BF=$ROOT/paper/verification/step1_bruteforce
sed -e 's/CompletionResult R = E.complete(U, rhoAll, c, su, zNum);/CompletionResult R;   \/\/ TEST COPY: Step 2 disabled/' \
    $ROOT/semiprime47.cpp > semiprime47_step1only.cpp
g++ -O3 -march=native -pthread -o dfs47 dfs47_harness.cpp
g++ -O3 -march=native -pthread -o dfs48 dfs48_harness.cpp
g++ -O3 -march=native -pthread -o bf $BF/bf.cpp
cmpdumps() {  # label fileA fileB
  if cmp -s <(sort "$2") <(sort "$3"); then echo "$1: IDENTICAL ($(wc -l < "$2") cores)"; else echo "$1: DIFFERENT"; fi
}
echo "== part A: reduced instances =="
for sb in 13 17 19; do ./bf $sb 40 45 50 60 80 > /dev/null; done
for cfg in "13 40" "13 45" "13 50" "13 60" "13 80" "17 40" "17 45" "17 50" "17 60" "19 40" "19 45" "19 50" "23 40" "23 45" "23 50"; do
  set -- $cfg
  ./dfs47 $1 $2 1 2 old.txt
  ./dfs48 $1 $2 1 2 new.txt
  ./dfs48 $1 $2 3 7 new3.txt > /dev/null
  cmpdumps "sb=$1 K=$2 old vs new" old.txt new.txt
  cmpdumps "sb=$1 K=$2 new 1 thread vs 3 threads" new.txt new3.txt
  if [ -f bf_seg_$1_$2.txt ]; then
    cp new.txt d.txt
    (cd . && python3 $BF/compare.py $1 $2 d.txt) | sed "s/^/  brute force: /"
  fi
done
echo "== part B: S = primes <= 73, budgets 40..45 =="
for K in 40 41 42 43 44 45; do
  ./dfs47 73 $K $T 61 old.txt
  ./dfs48 73 $K $T 43 new.txt
  cmpdumps "K=$K old vs new" old.txt new.txt
done
echo "== part C: archived dumps of the old program =="
gunzip -c $ROOT/paper/verification/rerun/cores46.txt.gz > arch46.txt
./dfs48 73 46 $T 43 new46.txt
cmpdumps "K=46 archived (paper/verification/rerun/cores46.txt.gz) vs new" arch46.txt new46.txt
gunzip -c $ROOT/cores47.txt.gz > arch47.txt
./dfs48 73 47 $T 43 new47.txt
cmpdumps "K=47 archived (cores47.txt.gz) vs new" arch47.txt new47.txt
rm -f old.txt new.txt new3.txt d.txt new46.txt new47.txt arch46.txt arch47.txt bf_seg_*.txt bf_fin_*.txt dfs47 dfs48 bf semiprime47_step1only.cpp
