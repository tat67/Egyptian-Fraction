# Q2 (least number of terms of a primitive representation of 1): computational notes

These notes record exploratory computations for Q2. The rigorous bounds are now `42 ≤ min |T| ≤ 44`:

* `39 ≤ min |T|` and the 44-term set `T44` are proved in Lean (`card_bounds`) and checked in C++ (`./primitive_egypt q2`);
* `|T| = 39, 40, 41` are excluded by the exhaustive exact search in [`primitive_q2/`](primitive_q2/README.md). That proof is computer-assisted with exact arithmetic, cross-checked by independent programs, and reproduced on this branch, but it is not formalized in Lean.

Nothing in this file is formally verified. Each item states its status.

* **Compressions of known sets.** Take the 23 semiprime sets with 47 terms and the 620 with 48 terms. No two elements `a, b` of a 47-term set can be replaced by one element `ab/(a+b)` while keeping the set primitive. From the 48-term sets, 23 such replacements give 47-term sets, all of them again semiprime sets. No three elements of any of these 47-term sets can be replaced by two (Egyptian-fraction search over `x ∈ (1/q, 2/q]`).
* **`|T| = 39` (first attempt, superseded).** With the Lagrangian bound at `A = 133`, two elements `≥ 330` would cost more than the slack `H_39 − 1`, so a 39-term solution has the form `C ∪ {N}` with `C ⊆ [2, 329]`, `|C| = 38`, `N = 1/(1 − Σ_C)`. This idea was carried out completely, and extended to `|T| = 40, 41` (up to three large elements), in [`primitive_q2/`](primitive_q2/README.md): no solution exists for `|T| = 39, 40, 41`.
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
  | **all** non-prime-powers `≤ 100000` | 90299 | 43 | **INFEASIBLE** |

  So inside the first two universes no primitive representation of 1 has fewer than 47 terms. The first two universes exclude `2537 = 43·59`, which `T46` needs. In the full universe `≤ 4000` the solver found `T46` and proved 46 minimal there; `≤ 8000` gives the same minimum. With elements up to 20000 the minimum drops to **44** (`T44`, which uses products of three primes such as `8729 = 7·29·43`). Up to 40000, and also up to 100000, the solver finds no set with 43 or fewer terms. The minimum over all primitive sets is therefore at most 44. Whether still larger elements allow 42 or 43 terms is open. The rigorous lower bound is 42 ([`primitive_q2/`](primitive_q2/README.md)), which excludes 39, 40 and 41 terms for elements of any size.

* **All 44-term solutions with bounded elements** (`primitive_explore/enum_q2.py`; CP-SAT with an exact pre-filter, no-good enumeration, every solution re-verified exactly; completeness rests on the solver's INFEASIBLE, uncertified). `T44` is the **only** primitive representation of 1 with 44 terms and all elements `≤ 40 000` (runs for `X = 20 000, 30 000, 40 000`: 9 min, 29 min, 2 h 3 min). The run for `X = 100 000` found no other solution in 7 hours but did not finish; at the observed growth (about ×4 per 10 000) it would need days to weeks. Outputs: `primitive_explore/enum_q2_*_44.txt`.
