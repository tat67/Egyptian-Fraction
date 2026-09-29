#!/bin/sh
# find_a.sh n K0 : determine a(n).  Start with "prove n K0" (any set with max <= K0).
#   If a set is found, descend below its maximum until "prove" returns NONE.
#   If the first call returns NONE, step upwards with "witness n K" until a witness exists.
# Every call's output line and timestamps go to log_n<n>.txt; certificates to cert_n<n>_K<K>.txt.
n=$1; K=$2; log=log_n$n.txt
echo "START n=$n $(date +%Y-%m-%dT%H:%M:%S%z)" >> $log
first=1; best=""
while :; do
  out=$(./a101877 prove $n $K cert=cert_n${n}_K${K}.txt 2>>err_n$n.txt)
  echo "$(date +%Y-%m-%dT%H:%M:%S%z) $out" | cut -c1-200 >> $log
  case "$out" in
    *FOUND*) m=$(echo "$out" | sed 's/.*S=//' | tr ',' '\n' | sort -n | tail -1)
             echo "$out" | sed 's/.*S=//' > witness_n${n}_max${m}.txt; best=$m; K=$((m-1)); first=0;;
    *NONE*)  if [ $first = 1 ]; then
               # a(n) > K0: search upwards for the first K with a witness
               K=$((K+1))
               while :; do
                 w=$(./a101877 witness $n $K 2>>err_n$n.txt)
                 echo "$(date +%Y-%m-%dT%H:%M:%S%z) $w" | cut -c1-200 >> $log
                 case "$w" in *FOUND*) echo "$w" | sed 's/.*S=//' > witness_n${n}_max${K}.txt; best=$K; break;; esac
                 K=$((K+1))
               done
             fi
             break;;
    *)       echo "UNDECIDED / error at K=$K" >> $log; break;;
  esac
done
echo "RESULT n=$n a(n)=$best $(date +%Y-%m-%dT%H:%M:%S%z)" >> $log
