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

Run it with `bash step1_equivalence.sh 4` (about 10 minutes on 4 cores). The recorded output is `step1_equivalence_output.txt`.

**Result.** All 38 dump comparisons are identical, and all 12 brute-force checks pass.

* **Part A.** On all 15 reduced instances the old and new dumps coincide, and so do the new dumps with 1 and 3 threads. Together they contain up to 21,038,736 cores (`S ≤ 23`, `K = 50`).
  * On these small instances the loss bound (P4) prunes nothing; old and new visit the same number of nodes, because their value slack is large.
  * So part A checks the bookkeeping of the new code path (residues, incremental sums, table lookups), not the pruning itself.
* **Part B.** Budgets 40–45 on the real instance: both programs keep no core. The new program visits 4 to 1,166,640 nodes, the old one 28,040 to 10,744,778,486.
* **Part C.** Here (P4) prunes heavily, and the result is still unchanged. The new program reproduces the archived dumps line for line:
  * budget 46: 178 cores, 26,112,391 nodes instead of 1.4·10^11;
  * budget 47: 22,382 cores, 598,305,041 nodes instead of 1.8·10^12.

## Other files

| file | content |
|---|---|
| `run46_output.txt` | `../semiprime48 4 --budget 46`: no set with at most 46 elements (2 s) |
| `run47_output.txt` | `../semiprime48 4 --budget 47`: exactly the 23 known 47-element solutions (65 s) |
| `step2_from_dump.cpp` | runs the C++ Step 2 of `../semiprime48.cpp` on the cores of a dump file. It was used on the 73 budget-48 cores that need the two-big-big-edge solver: 0 completions, 0 unresolved, the same as `../complete48.py`. |
| `cores48_two_bb.txt` | the 73 budget-48 cores whose only surviving shapes have two big-big edges (from the first run, where they were still reported as unresolved) |
| `two_bb_step2_cpp_output.txt`, `two_bb_step2_python_output.txt` | `step2_from_dump` and `../complete48.py` on these 73 cores: no completion, nothing unresolved |
| `lean_vs_cpp.sh`, `lean_vs_cpp_output.txt` | the Lean search `Inst.search` (`../lean/SemiprimeEgypt/Search.lean`, proved exhaustive in Lean), compiled to native code, compared with the Step-1 output of `../semiprime48.cpp`: 12 reduced instances and the real instance with budgets 40–46, identical in every case |
| `lean46_cores.txt` | the 178 cores output by the Lean search for budget 46; the same as the C++ list |
| `lean_runner/` | the native runners of the Lean search (`RunG.lean`, `RunS.lean`, `RunT.lean`, `RunU.lean`), their build steps, and the procedure used for budget 46 |
| `complete48_selftest_output.txt` | `python3 ../complete48.py --selftest`: the planted path and the planted pair of components are recovered. The completion sets (27 and 2) are the same as those printed by `semiprime48 --selftest` in `../run48_output.txt`. |
