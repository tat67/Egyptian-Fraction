#!/bin/sh
# rootscan.sh n K1 K2 : root-node bound only (maxnodes=1) for K1..K2, 4 processes in parallel
n=$1; K1=$2; K2=$3
seq $K1 $K2 | xargs -P 4 -I{} sh -c "./a101877 prove $n {} maxnodes=1 threads=1 cert=cert_n${n}_K{}.txt 2>/dev/null | cut -c1-150" | sort -t= -k3 -n
