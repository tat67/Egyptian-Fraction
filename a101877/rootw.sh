#!/bin/sh
# rootw.sh n K1 K2 : witness-mode (K forced in S) root closure with long optimisation, K1..K2 upward,
# stops at the first K that is not closed at the root.  Certificates: cert_n<n>_K<K>w.txt
n=$1; K=$2; K2=$3
while [ $K -le $K2 ]; do
  out=$(./a101877 witness $n $K maxnodes=1 threads=1 rootiters=30000 noimp=3000 cert=cert_n${n}_K${K}w.txt 2>/dev/null)
  echo "$(date +%Y-%m-%dT%H:%M:%S%z) $out" | cut -c1-190 >> rootw_n$n.txt
  case "$out" in *NONE*) ;; *) break;; esac
  K=$((K+1))
done
