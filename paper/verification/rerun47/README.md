# Re-execution of the budget-47 search (performed for the paper)

The run used the same 4-vCPU container as `../rerun/` (Intel Xeon 2.10 GHz, g++ 13.3.0), with 4 threads:

```
g++ -O3 -march=native -pthread -o semiprime47 ../../../semiprime47.cpp
./semiprime47 4 --dump cores47_rerun.txt        # about 5.4 h wall-clock
gzip cores47_rerun.txt
python3 compare_rerun47.py                      # writes the comparison shown in rerun47_comparison.txt
```

The printed statistics are identical to the recorded `../../../run47_output.txt`:

* nodes 1,795,181,713,099;
* 22,382 cores (11,287 with U ≠ ∅ and |C|+|U| = 47);
* 1,107,702 shapes, of which 8,049 survive, in 7,432 cores;
* 125 candidate stars;
* 0 unresolved cores and 0 probable primes.

The list of 23 solutions is identical, and it equals `solutions47.txt`. The new core dump `cores47_rerun.txt.gz` coincides line by line with `cores47.txt.gz` when both are compared as sets of lines. Only the elapsed time differs: 19,388 s for the search, against 20,898 s in the recorded run.
