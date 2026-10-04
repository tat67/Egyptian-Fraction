#!/bin/sh
# validate.sh : n = 1..8.  For each n with claimed value A:
#   prove n A-1 (with certificate), verify the certificate independently (verify_cert.py),
#   witness n A (exact check inside the program and again with Python Fractions),
#   count n A (all witness sets with max A).   Timestamps (ISO 8601) and times per step.
out=validation.txt
: > $out
for pair in "1 1" "2 6" "3 24" "4 65" "5 184" "6 469" "7 1243" "8 3228"; do
  set -- $pair; n=$1; A=$2; B=$((A-1))
  t0=$(date +%Y-%m-%dT%H:%M:%S%z); s0=$(date +%s%N)
  p=$(./a101877 prove $n $B cert=cert_n${n}_K${B}.txt 2>/dev/null)
  c="(no certificate needed: all candidates sum below n)"; [ -f cert_n${n}_K${B}.txt ] && c=$(python3 verify_cert.py cert_n${n}_K${B}.txt)
  w=$(./a101877 witness $n $A 2>/dev/null); echo "$w" | sed 's/.*S=//' > witness_n${n}_max${A}.txt
  f=$(python3 verify_witness.py $n $A --S "$(cat witness_n${n}_max${A}.txt)")
  if [ $n -le 6 ]; then k=$(./a101877 count $n $A 2>/dev/null); else k="(count for n>=7 run separately)"; fi
  s1=$(date +%s%N); t1=$(date +%Y-%m-%dT%H:%M:%S%z)
  {
    echo "n=$n claimed a(n)=$A   start $t0  end $t1  elapsed $(( (s1-s0)/1000000 )) ms"
    echo "  $p" | cut -c1-160
    echo "  $c"
    echo "  $(echo "$w" | cut -c1-110)"
    echo "  $f"
    echo "  $k"
  } >> $out
done
cat $out
