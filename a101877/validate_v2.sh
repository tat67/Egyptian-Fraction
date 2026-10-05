#!/bin/sh
# validate_v2.sh [OUTDIR] : end-to-end validation of the revised solver a101877_v2 on n = 1..9.
# For each n with value A:
#   prove n A-1 with a certificate, which is checked independently (verify_cert.py);
#   witness n A, with the set re-checked by v2's own check mode and with Python Fractions (verify_witness.py).
# Intermediate files go to OUTDIR (default: a fresh temporary directory). The log goes to stdout.
# Build first:  g++ -O2 -march=native -pthread -o a101877_v2 a101877_v2.cpp
d=${1:-$(mktemp -d)}; mkdir -p "$d"
for pair in "1 1" "2 6" "3 24" "4 65" "5 184" "6 469" "7 1243" "8 3228" "9 8498"; do
  set -- $pair; n=$1; A=$2; B=$((A-1))
  t0=$(TZ=Asia/Tokyo date '+%Y-%m-%d %H:%M:%S %Z')
  p=$(./a101877_v2 prove $n $B cert=$d/cert_n${n}_K${B}.txt quiet=1 2>/dev/null)
  if [ -f $d/cert_n${n}_K${B}.txt ]; then c=$(python3 verify_cert.py $d/cert_n${n}_K${B}.txt); else c="(no certificate needed: $(echo "$p" | sed 's/.*NONE: //'))"; fi
  w=$(./a101877_v2 witness $n $A quiet=1 2>/dev/null); echo "$w" | sed 's/.* S=//' > $d/witness_n${n}_max${A}.txt
  k=$(./a101877_v2 check $n $A "$(cat $d/witness_n${n}_max${A}.txt)" 2>/dev/null)
  f=$(python3 verify_witness.py $n $A --S "$(cat $d/witness_n${n}_max${A}.txt)")
  echo "n=$n a(n)=$A   start $t0"
  echo "  $p" | cut -c1-170
  echo "  $c"
  echo "  $w" | sed 's/ S=.*/ S=<in OUTDIR>/'
  echo "  $k"
  echo "  $f"
done
echo "done $(TZ=Asia/Tokyo date '+%Y-%m-%d %H:%M:%S %Z')"
