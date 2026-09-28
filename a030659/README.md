# OEIS A030659 extended to all terms with a(n) ≤ 1000

**A030659:** a(n) is the smallest possible largest denominator in a representation of 1 as a sum of `n` distinct unit fractions (offset 3).

| n | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | ... |
|---|---|---|---|---|---|---|---|---|---|
| a(n) | 6 | 12 | 15 | 15 | 18 | 20 | 24 | 24 | ... |

**Result.** Every term with `a(n) ≤ 1000` has been computed. These are `a(3), ..., a(473)`, a total of 471 terms.

* The last one is `a(473) = 999`.
* No representation of 1 by 474 distinct unit fractions has all denominators `≤ 1000`, so `a(474) > 1000`.

The terms, in OEIS b-file format, are in [`b030659.txt`](b030659.txt).

All 145 previously known terms (`n = 3..147`, up to `a(147) = 322`) are reproduced exactly. They are compared against the original OEIS b-file in [`oeis_b030659_original.txt`](oeis_b030659_original.txt), and `make_outputs.py` repeats the comparison. The new terms are `n = 148..473`.

```
a(63..)  = 145, 150, 152, 153, 154, 155, 155, 160, 161, 161, 162, 168, 171, 174, 174, 175, ...
a(148..) = 324, 325, 329, 330, 336, 340, 341, 342, 344, 345, 350, 351, 357, 360, 363, 363, ...
a(469..473) = 990, 992, 994, 996, 999
```

The sequence is nondecreasing. At most 3 consecutive terms are equal; the values 371, 402, 413, 511, 535, 649, 685 and 762 each occur three times. `a(n)/n` falls slowly, from 2.28 at `n = 100` to 2.11 at `n = 473`.

## Reformulation

Let `f(M)` be the largest `n` such that 1 is a sum of `n` distinct unit fractions `1/k` with every `k ≤ M`. By definition,

    a(n) = min { M : some representation of 1 by n distinct 1/k has all k ≤ M }.

To establish `a(n) = M`, two things are needed:

* **(witness)** an explicit representation with `n` terms and largest denominator `M`;
* **(bound)** `f(M − 1) < n`.

All witnesses are in [`witnesses.txt`](witnesses.txt), one line per `n`. [`f_table.txt`](f_table.txt) gives `f(M)` for every `M ≤ 1000`.

### Exact integer model

Take `S ⊆ {1, …, M}` and, for each prime `p ≤ M`, let `p^E` be the largest power of `p` that is `≤ M`. Then `Σ_{k∈S} 1/k` is an integer if and only if, for every prime `p ≤ M`,

    Σ_{k ∈ S, p | k}  p^(E − v_p(k)) · (k / p^v_p(k))^(-1)  ≡  0   (mod p^E),

where the inverse is taken mod `p^E`. This says exactly that `v_p` of the sum is at least 0, and only primes `≤ M` can occur in the denominator.

Next, choose a scale `W > 2M` and require

    W − M  ≤  Σ_{k∈S} ⌊W/k⌋  ≤  W.

This forces `0 < Σ 1/k < 2`. An integral sum in that range is exactly 1.

So "`S` is a representation of 1" becomes a set of linear constraints with integer coefficients: one congruence per prime, with an integer multiplier variable, and one bounded sum. There is no floating point anywhere in the model.

### Admissibility prefilter

`admissible.py` removes a number `k ≤ M` when, for some prime `p | k`, no set `K` of multiples of `p` in `[1, M]` containing `k` satisfies the `p`-congruence. This is a subset-sum over residues mod `p^E`.

The filter is sound. For any solution `S`, the set `S ∩ pℤ` is such a `K` for every `p`, so a removed number never occurs in a solution. If `M` itself is removed, then `f(M) = f(M − 1)`.

## Computation

[`compute_f.py`](compute_f.py) works through `M = 1, …, 1000` with the OR-Tools CP-SAT solver (v9.15, 4 workers). At each `M` it decides:

1. whether a representation using `M` with more than `f(M − 1)` terms exists; if so, it maximises the number of terms. The solver must report `OPTIMAL` or `INFEASIBLE` for this; anything else stops the run.
2. for every `n` with `f(M − 1) < n < f(M)`, a separate witness with exactly `n` terms and largest denominator `M`.

The run took 780 s of solver time (about 13 minutes wall time).

| outcome at `M` | count |
|---|---|
| `M` removed by the prefilter | 474 |
| no larger representation using `M` (`INFEASIBLE`) | 132 |
| new maximum found and proved (`OPTIMAL`) | 394 |

In step 2 every `n ≥ 3` had a witness. The only infeasible size was `n = 2`, which lies outside the sequence. So the achievable sizes for each `M` form the interval `3..f(M)`, and `a(n) = min{M : f(M) ≥ n}`.

## Verification

* **Witnesses (exact, no solver involved).** [`verify_witnesses.py`](verify_witnesses.py) checks all 471 representations with Python `Fraction`s. For each `n` it confirms `n` distinct denominators, largest denominator exactly `a(n)`, and a sum of exactly 1.
* **Upper bounds, second model.** [`verify_ub_cpsat2.py`](verify_ub_cpsat2.py) is written separately from `compute_f.py`, and the two share no model-building code. It differs in several ways:
  * it uses no prefilter, so all `k ≤ M` are variables;
  * the congruences go through `AddModuloEquality`;
  * the scaled sum is rounded up, with `W = 2^40`;
  * it is a plain feasibility question, "`|S| ≥ N`?".

  It re-proves every bound actually needed: one claim `f(v − 1) < n_v` for each of the 393 distinct values `v`, where `n_v` is the first `n` with `a(n) = v`, plus `f(1000) < 474`. All 394 claims come back `INFEASIBLE`, in 733 s total ([`ub_cpsat2.txt`](ub_cpsat2.txt)).
* **Upper bounds, third solver.** [`verify_ub_scip.py`](verify_ub_scip.py) states the same exact model, again without the prefilter, for the SCIP 10.0 MIP solver via PySCIPOpt.
  * SCIP was run on the claims in increasing order of `M`: first one at a time with a 600 s limit, then through [`run_scip_parallel.py`](run_scip_parallel.py) with a 900 s limit.
  * Of the 87 claims with `M − 1 ≤ 247`, it proved 84 `INFEASIBLE`. Two hit the time limit, `f(179) < 79` and `f(189) < 83`, and one, `f(245) < 109`, was still running when the check was stopped.
  * It never found a solution that would contradict a claim. Its results are in [`ub_scip.txt`](ub_scip.txt), with columns `M−1`, `N`, status and seconds.
  * SCIP slows down sharply as `M` grows: a single claim at `M = 500` was not settled in 15 minutes, while CP-SAT needs under 15 s even at `M = 1000`. So this check covers only small `M`.
* **Reproducibility.** A second, complete run of `compute_f.py` gave the same `f(M)` for all `M ≤ 1000`; see [`rerun_check.txt`](rerun_check.txt).
* **Known values.** All 145 existing OEIS terms (`n = 3..147`) are reproduced exactly, with no differences.

**What the verification does not cover.** The witnesses are checked exactly, so every `a(n)` is certainly `≤` the listed value. The matching lower bounds `f(a(n) − 1) < n` depend on solver infeasibility proofs: two independent CP-SAT models agree on all 394 claims, and SCIP agrees on the smaller cases. They are not formal certificates.

## Optimal expansions for k = 3..473

[`optimal_expansions.txt`](optimal_expansions.txt) gives one optimal expansion of 1 into `k` distinct unit fractions for every `k = 3..473`, together with the number of tied optimal sets. The same table is also available as [`optimal_expansions.csv`](optimal_expansions.csv) and as a LaTeX `longtable` in [`optimal_expansions.tex`](optimal_expansions.tex).

```
k  | ties | denominators of the optimal expansion
3  | 1    | 2, 3, 6
4  | 1    | 2, 4, 6, 12
5  | 1    | 2, 4, 10, 12, 15
6  | 1    | 3, 4, 6, 10, 12, 15
7  | 1    | 3, 4, 9, 10, 12, 15, 18
8  | 2    | 3, 5, 9, 10, 12, 15, 18, 20
9  | 2    | 4, 5, 8, 9, 10, 15, 18, 20, 24
10 | 1    | 5, 6, 8, 9, 10, 12, 15, 18, 20, 24
11 | 3    | 5, 6, 8, 9, 10, 15, 18, 20, 21, 24, 28
12 | 2    | 4, 8, 9, 10, 12, 15, 18, 20, 21, 24, 28, 30
```

**Criterion.**

1. The largest denominator is as small as possible, namely `a(k)`, the A030659 term above.
2. Among the sets that tie on that, the one listed is the lexicographically smallest denominator list written in increasing order: the smallest `d_1`, then the smallest `d_2`, and so on.

The "ties" column counts every `k`-set with largest denominator `a(k)` and reciprocal sum exactly 1.

**Comparison with the classical table for k ≤ 12.**

* The published table of optimal expansions (Eppstein, MathPages) minimises the largest denominator, and every one of its rows is optimal.
* Its choice among tied sets is not given by any consistent rule. Rows 8, 9 and 11 are the lexicographically smallest sets, but row 12 (`6, 7, 8, 9, 10, 14, 15, 18, 20, 24, 28, 30`) is the other of the two tied sets.
* The table here therefore agrees with the published one for `k = 3..11` and lists the other tied set at `k = 12`.

### How the table was computed

* **Smallest set per row: [`optimal_expansions.py`](optimal_expansions.py).** This uses CP-SAT with the exact model above, fixing the largest denominator at `a(k)` and the size at `k`.
  * Lexicographic order is optimised exactly, window by window. Up to 56 consecutive undecided candidates get weights `2^55, …, 2^0`, with the smaller denominator weighted more, so within a window the weighted objective is exactly lexicographic order.
  * Each window's optimum is fixed before the next window is solved.
  * Every row is re-verified with Python `Fraction`s: `k` distinct denominators, largest `a(k)`, and sum exactly 1.
* **Tie counts: [`count_ties.cpp`](count_ties.cpp).** This is an exact enumerator written independently of the CP-SAT code.
  * **Search.** Multiples of each large prime `p` (`p² > M`) form one block, whose admissible choices are the subsets with residue 0 mod `p`. The remaining candidates are grouped by largest prime factor.
  * **Pruning.** It uses reciprocal-sum bounds, and per-group tables of the least and greatest sum for each (residue, count) pair. At the start of each group, per-prime feasibility tables check the remaining candidates for every smaller prime.
  * **Exactness.** The remaining sum is tracked exactly as an integer multiple of `1/L`, where `L` is the product of the small prime powers (below `2^96`). Floating point is used only for pruning, with a safety margin.
  * **Merging.** Identical states (stage, terms left, exact remaining sum) are counted once through a memo table.
  * **Smallest set.** A second pass also reports the lexicographically smallest set, whenever there are at most `2·10⁷` ties.
* **Tie counts where there are few ties: [`count_ties_cpsat.py`](count_ties_cpsat.py).** This enumerates every solution with CP-SAT. Its count is complete only when the solver reports `OPTIMAL`.

### Checks

* All 471 listed sets pass the exact `Fraction` check.
* Wherever the enumerator or a complete CP-SAT enumeration also produced the smallest set, it equals the listed set exactly; see the output of [`make_table.py`](make_table.py).
* Where both counters finished the same `k`, their counts agree.
* **Validation on known cases.** The counts agree with an exhaustive brute force (`lexmin_bruteforce.cpp`) and with CP-SAT enumeration for `k = 8, 9, 11, 12, 20, 25`. For `k = 61, 62, 101` they agree with CP-SAT enumeration. Every build of the counter gave identical counts on these cases.

### Limits

Counting every tied set becomes very expensive near the top of the range. The number of ties can be astronomically large, for example at least 7,988,637,175 for `k = 232`. Even for the maximal sizes, the search at largest denominators near 1000 is slow.

Where neither counter finished within the time allowed, the table shows a **proven lower bound** `≥ N`. `N` is the number of distinct optimal sets actually found by CP-SAT or accounted for by the C++ counter before its time limit, and it is always at least 1, since the listed set is one of them. See the summary at the top of `optimal_expansions.txt` for which rows are exact.

## Reproducing

    pip install ortools pyscipopt        # OR-Tools 9.15 and SCIP 10.0 were used
    python3 compute_f.py 1000 4          # -> f_values.jsonl (resumable; about 13 min on 4 cores)
    python3 make_outputs.py              # -> b030659.txt, f_table.txt; compares with the OEIS terms
    python3 verify_witnesses.py          # -> witnesses.txt; exact check of every witness
    python3 verify_ub_cpsat2.py          # -> ub_cpsat2.txt; independent upper bounds (about 12 min)
    python3 run_scip_parallel.py 321 900 4   # -> ub_scip.txt; SCIP cross-check
    python3 run_expansions.py 3 473 1 0 4 expansions.jsonl   # table rows (CP-SAT, lexicographic)
    g++ -O2 -march=native -o count_ties count_ties.cpp
    python3 run_ties.py ./count_ties 3 473 4 600 26          # tie counts, 10 min per k
    python3 count_ties_cpsat.py 1800 473                     # CP-SAT enumeration for a few k
    python3 make_table.py                                    # -> optimal_expansions.{txt,csv,tex}

The recorded run is stored compressed as `f_values.jsonl.gz`. The scripts other than `compute_f.py` read the compressed file directly when the plain one is absent.

## Files

| file | contents |
|---|---|
| `b030659.txt` | `n a(n)` for `n = 3..473` |
| `witnesses.txt` | for each `n`, the `n` denominators of a representation of 1 with largest denominator `a(n)` |
| `f_table.txt` | `f(M)` for `M = 1..1000` |
| `oeis_b030659_original.txt` | the existing OEIS b-file (`n = 3..147`), for comparison |
| `f_values.jsonl.gz` | raw per-`M` records of the recorded run: status, time and witnesses |
| `compute_f.log` | progress log of the recorded run |
| `ub_cpsat2.txt`, `ub_scip.txt` | results of the two upper-bound cross-checks |
| `rerun_check.txt` | comparison of the recorded run with a second full run |
| `admissible.py`, `compute_f.py`, `records.py`, `make_outputs.py` | computation |
| `verify_witnesses.py`, `verify_ub_cpsat2.py`, `verify_ub_scip.py`, `run_scip_parallel.py` | verification |
| `optimal_expansions.txt`, `.csv`, `.tex` | the table of optimal expansions for `k = 3..473`, with tie counts |
| `expansions_even.jsonl`, `expansions_odd.jsonl` | raw output of `optimal_expansions.py`: one lexicographically smallest optimal set per `k` |
| `ties_raw.txt`, `ties_partial.txt`, `ties_cpsat.txt` | raw tie counts: exact counts from `count_ties.cpp`, its time-limited lower bounds, and CP-SAT enumerations (`status=OPTIMAL` means complete) |
| `optimal_expansions.py`, `run_expansions.py` | computation of the table rows |
| `count_ties.cpp`, `run_ties.py`, `count_ties_cpsat.py`, `lexmin_bruteforce.cpp`, `make_table.py` | tie counting, brute-force validation and assembly |
