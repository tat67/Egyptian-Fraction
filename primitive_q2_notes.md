# Q2 (least number of terms of a primitive representation of 1): computational notes

These notes record computations for Q2 that go beyond the rigorous bounds `39 ≤ min |T| ≤ 47`.
The bounds themselves are proved in Lean (`card_bounds`) and checked in C++ (`./primitive_egypt q2`).
Nothing in this file is formally verified. Each item states its status.

* **Compressions of known sets.** Take the 23 semiprime sets with 47 terms and the 620 with 48 terms. No two elements `a, b` of a 47-term set can be replaced by one element `ab/(a+b)` while keeping the set primitive. From the 48-term sets, 23 such replacements give 47-term sets, all of them again semiprime sets. No three elements of any of these 47-term sets can be replaced by two (Egyptian-fraction search over `x ∈ (1/q, 2/q]`).
* **`|T| = 39` (exhaustive C++ search, `q39` variant of the engine).** With the Lagrangian bound at `A = 133`, two elements `≥ 330` would cost more than the slack `H_39 − 1`. Q1 forces an element `≥ 413`. So a 39-term solution has the form `C ∪ {N}` with `C ⊆ [2, 329]`, `|C| = 38`, `N = 1/(1 − Σ_C) ≥ 413`. The search enumerates all primitive cores `C` in the value window `[1 − 1/413, 1)` using the chain bound, and tests `N` exactly. Status: see below.
* **CP-SAT** (OR-Tools 9.15; `primitive_explore/cpsat_q2.py`). These results are evidence, not proofs; they rely on the solver's correctness. The model contains only necessary conditions: primitivity, the congruence modulo `p^{v_p(D)}` at every prime, the value inequalities `Σ ⌈S/n⌉ ≥ S ≥ Σ ⌊S/n⌋`, and `|T| ≤ K`.

  | universe (non-prime-powers) | size | `K` | result |
  |---|---:|---:|---|
  | `≤ 2500`, prime factors `≤ 73` except one prime `≤ 400` (first power) | 1849 | 46 | **INFEASIBLE** |
  | the same universe (sanity check) | 1849 | 47 | feasible (47-term semiprime solution found) |
  | `≤ 1500`, prime factors `≤ 73` except one prime `≤ 700` | 1225 | 46 | **INFEASIBLE** |

  | **all** non-prime-powers `≤ 4000` | 3410 | 46 | **feasible: the 46-term set `T46`**; OPTIMAL 46 (the solver proves no solution with `≤ 45` terms in this universe) |
  | **all** non-prime-powers `≤ 8000` | 6943 | 45 | **INFEASIBLE** |
  | **all** non-prime-powers `≤ 20000` | 17671 | 45 | **feasible: a 44-term set `T44`**; OPTIMAL 44 |
  | **all** non-prime-powers `≤ 40000` | 35714 | 43 | **INFEASIBLE** |

  So inside the first two universes no primitive representation of 1 has fewer than 47 terms. The first two universes exclude `2537 = 43·59`, which `T46` needs. In the full universe `≤ 4000` the solver found `T46` and proved 46 minimal there; `≤ 8000` gives the same minimum. With elements up to 20000 the minimum drops to **44** (`T44`, which uses products of three primes such as `8729 = 7·29·43`). Up to 40000 no set with 43 or fewer terms exists. The minimum over all primitive sets is therefore at most 44. Whether still larger elements allow fewer terms is open; the rigorous lower bound is 39.
