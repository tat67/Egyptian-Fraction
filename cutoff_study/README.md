# Choice of the cutoff (core size) and of b₀

**Question.** For each budget K ∈ {46, 47, 48}, choose the parameters that minimise the total cost of the exhaustive search, Step 1 (core enumeration) plus Step 2 (completion with large primes), without losing completeness. The parameters are:

* the set S of small primes, given by a cutoff B (S = primes ≤ B). Its size |S| determines the core size, since the core lives in P_S, which has |S|(|S|−1)/2 possible elements;
* the smallest large prime b₀.

## 1. b₀ is not a free parameter

Every prime must be either small (≤ B) or large (≥ b₀).

* **b₀ larger than the least prime after B is unsound.** A prime p with B < p < b₀ would be neither small nor large. The elements qp would then be missing both from the core and from the bounds for the large part: the value bound V(x) starts at v₁ = 2b₀, the U-edges are bounded by 1/(b₀q), and stars need P ≥ b₀. Admissible cores could then be pruned.
* **b₀ smaller than that prime is sound but strictly weaker.** Larger V(x) and larger 1/(b₀q) mean weaker value and loss bounds, so the search keeps at least as many nodes.

Hence, for every cutoff, **the optimal b₀ is the least prime after B**, and `semiprime48.cpp` sets it that way (`bigMin`). The joint optimisation reduces to the choice of B. Only primes matter: S depends on the largest prime ≤ B.

## 2. Constraints for a complete run

A run counts only if all of the following hold.

* **Step 2 resolves every surviving shape.** That means b ≤ 2, the bound of the b = 2 routine is at most 5·10⁷, at most 20 attachment primes, no 128-bit overflow, and no probable primes.
* **Implementation limits:** ∏_{p≤B} p < 2¹²⁸, so B ≤ 101, and |S| ≥ 9 for the 8-prime leaf table.
* **Cross-check:** the solutions found must be exactly the known ones. That is 0 for K = 46, the 23 sets for K = 47, and 620 + 23 for K = 48.

Every completed run below satisfies all of this: 0 unresolved, 0 probable primes, and exactly the known solutions. This also confirms that the engine is correct for cutoffs other than 73.

## 3. Measurements

The harness `cutoff_study.cpp` includes `../semiprime48.cpp` unmodified.

* Step 1 runs with 4 threads, splitting the work at the 8th prime from the top (43 for B = 73), and dumps the surviving cores.
* Step 2 then runs on those cores with 4 threads.

All runs used the same 4-vCPU cloud container on 2026-10-13. Node counts are machine independent; times are wall-clock. Runs that exceeded 1.3 × the best total so far were stopped, since they cannot be optimal. Raw outputs are in `sweep46.txt`, `sweep47.txt`, `sweep48.txt` and `repeats.txt`.

### K = 46

| B | \|S\| | b₀ | core elements | Step 1 nodes | cores kept | Step 1 s | shapes (S1–S3) | b=2 shapes | Step 2 s | total s | unresolved | solutions |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| 41 | 13 | 43 | 78 | 769,873,068 | 1,191,516 | 150.2 | 11,179,621,773 | 302 | 458.9 | **609.1** | 0 | 0 |
| 43 | 14 | 47 | 91 | 646,488,165 | 289,762 | 137.6 | 1,064,837,672 | 5 | 45.4 | **183.0** | 0 | 0 |
| 47 | 15 | 53 | 105 | 347,275,675 | 46,205 | 68.5 | 87,371,853 | 0 | 3.6 | **72.1** | 0 | 0 |
| 53 | 16 | 59 | 120 | 154,959,475 | 9,436 | 23.8 | 9,917,201 | 0 | 0.5 | **24.2** | 0 | 0 |
| 59 | 17 | 61 | 136 | 104,480,754 | 3,776 | 12.8 | 1,933,878 | 0 | 0.1 | **12.9** | 0 | 0 |
| 61 | 18 | 67 | 153 | 39,892,554 | 1,148 | 4.8 | 260,130 | 0 | 0.0 | **4.8** | 0 | 0 |
| 67 | 19 | 71 | 171 | 26,806,398 | 563 | 2.9 | 62,707 | 0 | 0.0 | **2.9** | 0 | 0 |
| 71 | 20 | 73 | 190 | 25,324,179 | 367 | 2.4 | 18,480 | 0 | 0.0 | **2.4** | 0 | 0 |
| 73 | 21 | 79 | 210 | 26,112,391 | 178 | 2.6 | 3,777 | 0 | 0.0 | **2.6** | 0 | 0 |
| 79 | 22 | 83 | 231 | 28,552,472 | 112 | 2.9 | 1,225 | 0 | 0.0 | **2.9** | 0 | 0 |
| 83 | 23 | 89 | 253 | 31,423,241 | 77 | 3.4 | 1,066 | 0 | 0.0 | **3.4** | 0 | 0 |
| 89 | 24 | 97 | 276 | 35,839,887 | 47 | 4.0 | 527 | 0 | 0.0 | **4.0** | 0 | 0 |
| 97 | 25 | 101 | 300 | 40,354,749 | 44 | 5.5 | 500 | 0 | 0.0 | **5.5** | 0 | 0 |
| 101 | 26 | 103 | 325 | 48,930,298 | 38 | 5.5 | 197 | 0 | 0.0 | **5.5** | 0 | 0 |

Repeated runs, 5 each (`repeats.txt`):

| B | total wall time (median) | CPU time (median) |
|---|---|---|
| 71 | 2.36 s | 9.26 s |
| 73 | 2.41 s | 9.44 s |

### K = 47

| B | \|S\| | b₀ | core elements | Step 1 nodes | cores kept | Step 1 s | shapes (S1–S3) | b=2 shapes | Step 2 s | total s | unresolved | solutions |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| 61 | | | | — | — | — | — | — | — | skipped: exceeded 94s (1.3 x best) | | |
| 67 | 19 | 71 | 171 | 592,564,713 | 59,067 | 80.3 | 12,410,376 | 1 | 1.2 | **81.6** | 0 | 23 of size 47 |
| 71 | 20 | 73 | 190 | 574,619,189 | 40,817 | 68.2 | 3,978,591 | 0 | 0.6 | **68.7** | 0 | 23 of size 47 |
| 73 | 21 | 79 | 210 | 598,305,041 | 22,382 | 70.2 | 1,107,702 | 0 | 0.2 | **70.4** | 0 | 23 of size 47 |
| 79 | 22 | 83 | 231 | 649,571,902 | 15,348 | 77.4 | 397,735 | 0 | 0.2 | **77.6** | 0 | 23 of size 47 |
| 83 | 23 | 89 | 253 | 694,273,194 | 10,169 | 88.1 | 171,727 | 0 | 0.1 | **88.2** | 0 | 23 of size 47 |

Repeated runs, 3 each:

| B | total wall time (median) | CPU time | Step 2 |
|---|---|---|---|
| 71 | 65.5 s | 257–261 s | 0.54–0.61 s |
| 73 | 69.5 s | 267–286 s | 0.24–0.31 s |

### K = 48

| B | \|S\| | b₀ | core elements | Step 1 nodes | cores kept | Step 1 s | shapes (S1–S3) | b=2 shapes | Step 2 s | total s | unresolved | solutions |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| 67 | | | | — | — | — | — | — | — | skipped: not run (at K = 47 already 19% slower than SB = 71; its Step 2 grows faster with K) | | |
| 71 | 20 | 73 | 190 | 12,240,878,620 | 2,510,513 | 1747.0 | 371,828,430 | 138 | 166.9 | **1913.9** | 0 | 23 of size 47, 620 of size 48 |
| 73 | 21 | 79 | 210 | 13,344,629,391 | 1,491,334 | 1823.9 | 116,874,859 | 73 | 34.5 | **1858.4** | 0 | 23 of size 47, 620 of size 48 |
| 79 | | | | — | — | — | — | — | — | skipped: not run (8-9% more Step-1 nodes than SB = 73 at K = 46 and 47) | | |

The B = 73 run took 30 min 58 s of wall time and 121 min 36 s of CPU time. The two K = 48 runs were consecutive on the same machine.

## 4. Result

| budget | optimal cutoff B | \|S\| (possible core elements) | b₀ | Step 1 nodes | Step 2 | total (4 threads) | runner-up |
|---|---|---|---|---|---|---|---|
| 46 | **71** | 20 (190) | **73** | 25,324,179 | 4–5 ms | **2.36 s** (median of 5) | B = 73: 2.41 s (+2%), 3% more nodes |
| 47 | **71** | 20 (190) | **73** | 574,619,189 | 0.55 s | **65.5 s** (median of 3) | B = 73: 69.5 s (+6%), 4% more nodes |
| 48 | **73** | 21 (210) | **79** | 13,344,629,391 | 34.5 s | **1858 s** (31 min) | B = 71: 1914 s (+3%), 8% fewer nodes but 4.8× the Step 2 time |

## 5. Why the optimum lies where it does

**Smaller cutoff.**

* b₀ is smaller, so a large-prime edge can carry much more value: the value bound uses 1/(b₀q) and V(x), whose first term is 1/(2b₀).
* The bounds of Step 1 become weak, and the number of surviving cores explodes. From B = 73 to B = 41 at K = 46 they go from 178 to 1.19 million, and the nodes rise 30-fold.
* Step 2 explodes as well: more shapes, more stars, more b = 1 and b = 2 components. At B = 41 Step 2 alone took 7.6 minutes. At K = 46, shapes with two large–large edges appear for B ≤ 43: 5 at B = 43 and 302 at B = 41. Step 2 handles at most two such edges, so at still smaller cutoffs a run can be expected to leave shapes unresolved. This did not happen in the measured runs, which stopped at B = 41.

**Larger cutoff.**

* Each additional small prime adds a level to the depth-first search, with a branching over its lower neighbours.
* The bounds improve only slightly, because the next large primes (83, 89, …) are close to 79. So the number of nodes grows again: +9% for B = 79 and +16% for B = 83 at K = 47.

**Step 1 alone** is cheapest at B = 71 for all three budgets.

**Step 2** decreases steeply with B, and its share grows with the budget. At B = 71 it is 0.2% of the total at K = 46, 0.8% at K = 47 and 8.7% at K = 48. At B = 73 the shares are 0.1%, 0.3% and 1.9%. At K = 48 the extra Step-2 cost of B = 71 (+132 s) outweighs its Step-1 saving (−77 s), and the optimum moves to B = 73.

## 6. Recommendation for the paper

The paper uses B = 73, b₀ = 79 for all three budgets. That choice is:

* **optimal for K = 48**, the most expensive budget by far;
* **within 2% (K = 46) and 6% (K = 47)** of the optimum B = 71, b₀ = 73. That is a few seconds at most.
* **the only cutoff with a formal proof.** The Lean exhaustiveness proof of Step 1 (`core_mem_search`, instance `inst73`) and the Lean reduction (`Admissible`, `Uset 73`, `V` with the 49 smallest semiprimes with a factor ≥ 79) are stated for B = 73. Switching to B = 71 for K ≤ 47 would require re-instantiating that part of the formalisation, to save at most 4 seconds.

Mathematical completeness holds for every cutoff in the tables. The reduction is valid for any cutoff, and each run resolved every shape. The choice only affects running time.

## 7. Reproducing

```
g++ -O3 -march=native -pthread -o cstudy cutoff_study.cpp
./cstudy 73 48 4 /tmp/dump48.txt     # B = 73, K = 48, 4 threads (about 31 min)
./cstudy 71 47 4 /tmp/dump47.txt     # B = 71, K = 47 (about 1 min)
python3 table.py sweep46.txt sweep47.txt sweep48.txt   # the tables above
```

The arguments are B, K, the number of threads, and the dump file. An optional fifth argument is the split prime; by default it is the 8th prime of S from the top. The dump for K = 48 needs about 260 MB (B = 73) to 450 MB (B = 71).
