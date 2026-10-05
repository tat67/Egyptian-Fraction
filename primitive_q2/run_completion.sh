#!/bin/bash
# run_completion.sh DUMP Y PARTS [onlyH]
# Splits a core dump into PARTS interleaved pieces and runs complete_dump on each in parallel.
set -e
DUMP=$1; Y=$2; PARTS=${3:-4}; ONLYH=${4:-0}
base=$(basename "$DUMP" .txt)
for ((i=0; i<PARTS; i++)); do
  awk -v n=$PARTS -v i=$i 'NR % n == i' "$DUMP" > "${base}.part$i"
done
for ((i=0; i<PARTS; i++)); do
  ./complete_dump "${base}.part$i" "$Y" "$ONLYH" > "${base}.part$i.out" 2>&1 &
done
wait
cat ${base}.part*.out
rm -f ${base}.part?
