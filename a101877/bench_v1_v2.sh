#!/bin/sh
# bench_v1_v2.sh STREAM : single-core comparison of the previous solver (a101877, "v1") and the
# revised solver (a101877_v2).  Each line of bench/<stream>.txt is one run (program output line).
# Build first:  g++ -O2 -march=native -pthread -o a101877 a101877.cpp
#               g++ -O2 -march=native -pthread -o a101877_v2 a101877_v2.cpp
s=$1; out=bench/$s.txt
run(){ echo "[$(TZ=Asia/Tokyo date '+%Y-%m-%d %H:%M:%S %Z')] $*" >> $out; "$@" 2>/dev/null | sed 's/ S=.*/ S=<omitted>/' >> $out; }
case $s in
  v1_short)
    run ./a101877 prove 8 3227 threads=1
    run ./a101877 prove 9 8496 threads=1
    run ./a101877 witness 9 8497 threads=1
    run ./a101877 witness 7 1243 threads=1
    run ./a101877 witness 6 469 threads=1
    run ./a101877 witness 10 22789 threads=1
    run ./a101877 witness 8 3228 threads=1 ;;
  v1_8500)
    run ./a101877 witness 9 8500 threads=1 maxnodes=5000 ;;
  v1_8498)
    run ./a101877 witness 9 8498 threads=1 maxnodes=3000 ;;
  v2)
    run ./a101877_v2 prove 8 3227 quiet=1
    run ./a101877_v2 prove 9 8496 quiet=1
    run ./a101877_v2 witness 9 8497 quiet=1
    run ./a101877_v2 witness 7 1243 quiet=1
    run ./a101877_v2 witness 6 469 quiet=1
    run ./a101877_v2 witness 10 22789 quiet=1
    run ./a101877_v2 witness 8 3228 quiet=1
    run ./a101877_v2 witness 9 8498 quiet=1
    run ./a101877_v2 witness 9 8500 quiet=1 ;;
esac
echo "[$(TZ=Asia/Tokyo date '+%Y-%m-%d %H:%M:%S %Z')] done" >> $out
