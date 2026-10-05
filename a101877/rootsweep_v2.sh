#!/bin/sh
# rootsweep_v2.sh n K0 OUTDIR : for K = K0, K0+1, ... run  a101877_v2 witness n K maxnodes=1 cert=...
# and stop at the first K that is neither excluded by the candidate filter nor closed at the root.
# Each closed K leaves a certificate OUTDIR/cert_n<n>_K<K>w.txt (check: verify_cert.py FILE --forced-in K).
# The log (one line per K, JST timestamps) goes to OUTDIR/sweep.log.
n=$1; K=$2; d=$3; mkdir -p "$d"
while true; do
  r=$(./a101877_v2 witness $n $K maxnodes=1 cert=$d/cert_n${n}_K${K}w.txt 2>$d/witness_n${n}_K$K.log)
  echo "[$(TZ=Asia/Tokyo date '+%Y-%m-%d %H:%M:%S')] $r" | cut -c1-200 >> $d/sweep.log
  case "$r" in
    *"not a candidate"*) rm -f $d/cert_n${n}_K${K}w.txt ;;
    *"NONE (all nodes closed) nodes=1 "*) ;;
    *) echo "STOP at K=$K (root does not close)" >> $d/sweep.log; break ;;
  esac
  K=$((K+1))
done
