#!/bin/bash
# Brute-force validation of Step 1 (core enumeration) on reduced instances.
# Builds a test copy of ../../../semiprime47.cpp in which (a) Step 2 is disabled and
# (b) the number LOWN of table-driven low primes is a compile-time parameter; the Step-1 code
# itself is unchanged.  For each configuration it checks  SEG ⊆ D ⊆ FIN  (see paper, Sec. 9.4).
set -e
cd "$(dirname "$0")"
SRC=../../../semiprime47.cpp
sed -e 's/CompletionResult R = E.complete(U, rhoAll, c, su, zNum);/CompletionResult R;   \/\/ TEST COPY: Step 2 disabled/' \
    -e 's/int LOWN = 8; /int LOWN = LOWN_VALUE; /' $SRC > semiprime47_step1only.cpp
diff $SRC semiprime47_step1only.cpp > step1only.diff || true
g++ -O2 -pthread -DLOWN_VALUE=8 -o dfs_lown8 dfs_harness.cpp
g++ -O2 -pthread -DLOWN_VALUE=3 -o dfs_lown3 dfs_harness.cpp
g++ -O3 -march=native -pthread -o bf bf.cpp
for sb in 13 17 19; do ./bf $sb 30 35 40 45 50 55 60 70 80; done > bf_sizes.txt
: > results.txt
for cfg in "13 40" "13 45" "13 50" "13 60" "13 80" "17 40" "17 45" "17 50" "17 60" "19 40" "19 45" "19 50"; do
  set -- $cfg
  for v in 8 3; do for th in "1 2" "3 7"; do
    t=($th)
    ./dfs_lown$v $1 $2 ${t[0]} ${t[1]} d.txt >> results.txt
    python3 compare.py $1 $2 d.txt | sed "s/^/LOWN=$v threads=${t[0]}: /" >> results.txt
  done; done
done
# negative control: budget-45 search compared with the budget-50 reference sets (must FAIL)
./dfs_lown8 19 45 1 2 d45.txt > /dev/null
cp bf_seg_19_50.txt bf_seg_19_999.txt; cp bf_fin_19_50.txt bf_fin_19_999.txt
echo "NEGATIVE CONTROL (expected FAIL):" >> results.txt
python3 compare.py 19 999 d45.txt >> results.txt
echo "PASS count: $(grep -c 'RESULT PASS' results.txt)  FAIL count: $(grep -c 'RESULT FAIL' results.txt)" | tee -a results.txt
rm -f d.txt d45.txt bf_seg_*.txt bf_fin_*.txt dfs_lown8 dfs_lown3 bf semiprime47_step1only.cpp
