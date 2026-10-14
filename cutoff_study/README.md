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

Every completed run below satisfies all of this, with one exception: 0 unresolved, 0 probable primes, and exactly the known solutions. This also confirms that the engine is correct for cutoffs other than 73.

The exception is **B = 67 at K = 48**. Step 2 left 3 shapes unresolved, each with 3 large–large edges (b = 3), which the b = 2 routine cannot handle. That run found the known solutions but does not prove that there are no others, so B = 67 is not admissible for K = 48.

## 3. Measurements

The harness `cutoff_study.cpp` includes `../semiprime48.cpp` unmodified.

* Step 1 runs with 4 threads, splitting the work at the 8th prime from the top (43 for B = 73), and dumps the surviving cores.
* Step 2 then runs on those cores with 4 threads.

The runs in `sweep46.txt`, `sweep47.txt`, `sweep48.txt` and `repeats.txt` used the same 4-vCPU cloud container on 2026-10-13. The runs in `sweep48b.txt` used a second instance on 2026-10-14 (see K = 48). Node counts are machine independent; times are wall-clock, and they can be compared only between runs on the same instance. Runs that exceeded 1.3 × the best total so far were stopped, since they cannot be optimal. The runs of 2026-10-14 had a cap of 1 hour each, which none of them reached.

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

The K = 48 runs were done on two instances of the container. Times can be compared only within one table. The node counts do not depend on the machine: B = 73 explored exactly 13,344,629,391 nodes on both.

**Instance 1 (2026-10-13), `sweep48.txt`.** The two runs were consecutive.

| B | \|S\| | b₀ | core elements | Step 1 nodes | cores kept | Step 1 s | shapes (S1–S3) | b=2 shapes | Step 2 s | total s | unresolved | solutions |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| 71 | 20 | 73 | 190 | 12,240,878,620 | 2,510,513 | 1747.0 | 371,828,430 | 138 | 166.9 | **1913.9** | 0 | 23 of size 47, 620 of size 48 |
| 73 | 21 | 79 | 210 | 13,344,629,391 | 1,491,334 | 1823.9 | 116,874,859 | 73 | 34.5 | **1858.4** | 0 | 23 of size 47, 620 of size 48 |

On instance 1, the B = 73 run took 30 min 58 s of wall time and 121 min 36 s of CPU time.

**Instance 2 (2026-10-14), `sweep48b.txt`.** The three runs were consecutive, each with a cap of 1 hour. B = 73 was rerun here as the reference for B = 67 and B = 79.

| B | \|S\| | b₀ | core elements | Step 1 nodes | cores kept | Step 1 s | shapes (S1–S3) | b=2 shapes | Step 2 s | total s | unresolved | solutions |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| 67 | 19 | 71 | 171 | 11,949,694,254 | 3,360,527 | 1231.3 | 972,393,087 | 273 | 115.7 | 1347.0 (incomplete) | 3 | 23 of size 47, 620 of size 48 |
| 73 | 21 | 79 | 210 | 13,344,629,391 | 1,491,334 | 1273.1 | 116,874,859 | 73 | 17.4 | **1290.5** | 0 | 23 of size 47, 620 of size 48 |
| 79 | 22 | 83 | 231 | 14,815,384,249 | 1,076,241 | 1365.3 | 47,406,803 | 58 | 13.3 | **1378.6** | 0 | 23 of size 47, 620 of size 48 |

The wall and CPU times on instance 2 were as follows:

| B | wall time | CPU time |
|---:|---|---|
| 67 | 22 min 27 s | 87 min 52 s |
| 73 | 21 min 31 s | 84 min 27 s |
| 79 | 22 min 59 s | 90 min 11 s |

Instance 2 is about 1.44× faster than instance 1: the same B = 73 run takes 1290.5 s instead of 1858.4 s.

Relative to B = 73 on the same instance:

| B | K = 48 nodes | K = 48 total | note |
|---:|---:|---:|---|
| 67 | −10.5% | +4.4% | **incomplete**: 3 shapes with b = 3; Step 2 6.7× longer |
| 71 | −8.3% | +3.0% | instance 1; Step 2 4.8× longer |
| 79 | +11.0% | +6.8% | Step 2 slightly shorter (13.3 s vs 17.4 s), but Step 1 7.2% longer |

## 4. Result

| budget | optimal cutoff B | \|S\| (possible core elements) | b₀ | Step 1 nodes | Step 2 | total (4 threads) | runner-up |
|---|---|---|---|---|---|---|---|
| 46 | **71** | 20 (190) | **73** | 25,324,179 | 4–5 ms | **2.36 s** (median of 5) | B = 73: 2.41 s (+2%), 3% more nodes |
| 47 | **71** | 20 (190) | **73** | 574,619,189 | 0.55 s | **65.5 s** (median of 3) | B = 73: 69.5 s (+6%), 4% more nodes |
| 48 | **73** | 21 (210) | **79** | 13,344,629,391 | 34.5 s / 17.4 s | **1858 s** (instance 1) / **1290 s** (instance 2) | B = 71: +3% (instance 1), 8% fewer nodes but 4.8× the Step 2 time. B = 79: +7% (instance 2), 11% more nodes. B = 67: incomplete (3 shapes with b = 3), and +4% anyway |

## 5. Why the optimum lies where it does

**Smaller cutoff.**

* b₀ is smaller, so a large-prime edge can carry much more value: the value bound uses 1/(b₀q) and V(x), whose first term is 1/(2b₀).
* The bounds of Step 1 become weak, and the number of surviving cores explodes. From B = 73 to B = 41 at K = 46 they go from 178 to 1.19 million, and the nodes rise 30-fold.
* Step 2 explodes as well: more shapes, more stars, more b = 1 and b = 2 components. At B = 41 Step 2 alone took 7.6 minutes. At K = 46, shapes with two large–large edges appear for B ≤ 43: 5 at B = 43 and 302 at B = 41. Step 2 handles at most two such edges, so at still smaller cutoffs a run can be expected to leave shapes unresolved. At K = 46 this did not happen in the measured runs, which stopped at B = 41.
* The larger the budget, the larger the cutoff at which this happens. At K = 48, B = 67 has 273 shapes with b ≥ 2, against 73 for B = 73. Three of them have b = 3 and stay unresolved, so B = 67 cannot certify K = 48.

**Larger cutoff.**

* Each additional small prime adds a level to the depth-first search, with a branching over its lower neighbours.
* The bounds improve only slightly, because the next large primes (83, 89, …) are close to 79. So the number of nodes grows again: +9% for B = 79 and +16% for B = 83 at K = 47, and +11% for B = 79 at K = 48.

**Step 1 alone** is cheapest at B = 71 for K = 46 and K = 47. At K = 48, B = 67 explores the fewest nodes (2.4% fewer than B = 71). Relative to B = 73 on the same instance, the Step-1 times of B = 67 and B = 71 are within one percentage point: −3.3% and −4.2%.

**Step 2** decreases steeply with B, and its share grows with the budget. At B = 71 it is 0.2% of the total at K = 46, 0.8% at K = 47 and 8.7% at K = 48. At B = 73 the shares are 0.1%, 0.3% and 1.9%. At K = 48 the extra Step-2 cost of B = 71 (+132 s) outweighs its Step-1 saving (−77 s), and the optimum moves to B = 73. B = 67 has 6.7× the Step-2 time of B = 73 (8.6% of its total). Going up to B = 79 saves only 4 s of Step 2 and costs 92 s of Step 1.

## 6. Recommendation for the paper

The paper uses B = 73, b₀ = 79 for all three budgets. That choice is:

* **optimal for K = 48**, the most expensive budget by far. All its neighbours were measured: B = 71 is 3% slower, B = 79 is 7% slower, and B = 67 does not complete the search;
* **within 2% (K = 46) and 6% (K = 47)** of the optimum B = 71, b₀ = 73. That is a few seconds at most.
* **the only cutoff with a formal proof.** The Lean exhaustiveness proof of Step 1 (`core_mem_search`, instance `inst73`) and the Lean reduction (`Admissible`, `Uset 73`, `V` with the 49 smallest semiprimes with a factor ≥ 79) are stated for B = 73. Switching to B = 71 for K ≤ 47 would require re-instantiating that part of the formalisation, to save at most 4 seconds.

The reduction is valid for any cutoff. Mathematical completeness holds for every run in the tables that resolved every shape, which is all of them except B = 67 at K = 48. Among admissible cutoffs, the choice only affects running time.

## 7. Reproducing

```
g++ -O3 -march=native -pthread -o cstudy cutoff_study.cpp
./cstudy 73 48 4 /tmp/dump48.txt     # B = 73, K = 48, 4 threads (about 31 min)
./cstudy 71 47 4 /tmp/dump47.txt     # B = 71, K = 47 (about 1 min)
python3 table.py sweep46.txt sweep47.txt sweep48.txt sweep48b.txt   # the tables above
```

The arguments are B, K, the number of threads, and the dump file. An optional fifth argument is the split prime; by default it is the 8th prime of S from the top. The dump for K = 48 needs about 260 MB (B = 73) to 450 MB (B = 71). It grows with the number of cores kept (3.4 million for B = 67).
