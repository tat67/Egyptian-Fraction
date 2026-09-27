# Re-execution of the budget-46 computation (performed for the paper)

Both runs used a cloud container with 4 virtual CPUs (Intel Xeon, 2.10 GHz), Ubuntu 24.04 and g++ 13.3.0.

## 1. Re-execution of the proof program

```
g++ -O3 -march=native -pthread -o semiprime_reciprocals ../../../semiprime_reciprocals.cpp
./semiprime_reciprocals 4
```

The log is `rerun_semiprime_reciprocals_4threads.log`. The output is identical to the recorded `../../../proof_run_output.txt` (including the node count) except for the elapsed time. Other jobs were running on the machine at the same time, which slowed this run.

## 2. Budget-46 core dump through the engine of `semiprime47.cpp`, with a Python Step-2 check

`dump46_harness.cpp` includes the **unmodified** file `semiprime47.cpp`. It runs its engine with budget 46 and writes every core kept by Step 1 to `cores46.txt`, using the same format as `cores47.txt`.

```
g++ -O3 -march=native -pthread -o dump46 dump46_harness.cpp
./dump46 4                                    # writes cores46.txt, prints statistics
gunzip -k cores46.txt.gz                       # the archived dump (if not regenerated)
python3 ../analyze47.py cores46.txt 46 10     # Python Step 2 with budget 46, stars <= 10 leaves
python3 ../../../complete47.py cores46.txt 46 # the original cross-check program
```

The outputs are `dump46.log`, `analyze46_output.txt` and `complete47_budget46_output.txt`. The dump itself is stored compressed as `cores46.txt.gz`.

The Step-1 code of the two programs is the same, so part 2 is not an independent check of Step 1. It does provide the following:

* a second execution of Step 1;
* an independent Step-2 check for budget 46 in Python, with its own shape enumeration, candidate-star factoring and cover search. The README stated that such a check had been done, but no artifact of it was previously archived.
