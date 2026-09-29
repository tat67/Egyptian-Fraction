# Validation of the new Step 1 (`semiprime48.cpp`)

`semiprime48.cpp` differs from `semiprime47.cpp` in Step 1 only by the extra pruning test (P4), the loss bound (see [`../README48.md`](../README48.md), section 3). (P4) is a relaxation of the final Step-1 test, so the new search must output **exactly** the same set of cores as the old one. `step1_equivalence.sh` checks this directly.

Both engines are run in Step-1-only mode through two small harnesses:

* `dfs48_harness.cpp` includes the unmodified `../semiprime48.cpp` and sets its flag `runStep2 = false`.
* `dfs47_harness.cpp` includes a copy of `../semiprime47.cpp` in which the call of Step 2 is removed by a one-line `sed`, as in `../paper/verification/step1_bruteforce`.

The script has three parts.

* **Part A: reduced instances.** `S` = primes `≤ 13, 17, 19, 23`, with several budgets.
  * The old and new dumps are compared.
  * The new dump with 1 thread is compared with the new dump with 3 threads.
  * For `S ≤ 19` the new dump is also compared with the brute-force enumeration of *all* cores (`../paper/verification/step1_bruteforce/bf.cpp`). The check is `SEG ⊆ D ⊆ FIN` and no duplicate cores; see `../paper/verification/step1_bruteforce`.
* **Part B: the real instance** (`S` = primes `≤ 73`) with budgets 40 to 45. The old and new dumps are compared.
* **Part C: the archived dumps of the old program.** `../paper/verification/rerun/cores46.txt.gz` (budget 46) and `../cores47.txt.gz` (budget 47) are compared with new runs.

Run it with `bash step1_equivalence.sh 4`. The recorded output is `step1_equivalence_output.txt`.
