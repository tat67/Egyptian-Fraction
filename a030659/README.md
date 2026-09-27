# OEIS A030659 extended to all terms with a(n) ≤ 1000

**A030659:** a(n) is the smallest possible largest denominator in a representation of 1 as a sum of `n` distinct unit fractions (offset 3).

| n | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | ... |
|---|---|---|---|---|---|---|---|---|---|
| a(n) | 6 | 12 | 15 | 15 | 18 | 20 | 24 | 24 | ... |

**Result.** Every term with `a(n) ≤ 1000` has been computed. These are `a(3), ..., a(473)`, a total of 471 terms.

* The last one is `a(473) = 999`.
* No representation of 1 by 474 distinct unit fractions has all denominators `≤ 1000`, so `a(474) > 1000`.

The terms, in OEIS b-file format, are in [`b030659.txt`](b030659.txt).

The OEIS data section lists `n = 3..62`, and all 60 of those terms are reproduced exactly. The OEIS b-file (by T. Watanabe) goes to `n = 147`, where `a(147) = 322` here. That b-file could not be fetched from this environment, so it has not been compared term by term.

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
* **Known values.** The 60 terms in the OEIS data section (`n = 3..62`) are reproduced exactly.

**What the verification does not cover.** The witnesses are checked exactly, so every `a(n)` is certainly `≤` the listed value. The matching lower bounds `f(a(n) − 1) < n` depend on solver infeasibility proofs: two independent CP-SAT models agree on all 394 claims, and SCIP agrees on the smaller cases. They are not formal certificates.

## Reproducing

    pip install ortools pyscipopt        # OR-Tools 9.15 and SCIP 10.0 were used
    python3 compute_f.py 1000 4          # -> f_values.jsonl (resumable; about 13 min on 4 cores)
    python3 make_outputs.py              # -> b030659.txt, f_table.txt; checks the OEIS data
    python3 verify_witnesses.py          # -> witnesses.txt; exact check of every witness
    python3 verify_ub_cpsat2.py          # -> ub_cpsat2.txt; independent upper bounds (about 12 min)
    python3 run_scip_parallel.py 321 900 4   # -> ub_scip.txt; SCIP cross-check

The recorded run is stored compressed as `f_values.jsonl.gz`. The scripts other than `compute_f.py` read the compressed file directly when the plain one is absent.

## Files

| file | contents |
|---|---|
| `b030659.txt` | `n a(n)` for `n = 3..473` |
| `witnesses.txt` | for each `n`, the `n` denominators of a representation of 1 with largest denominator `a(n)` |
| `f_table.txt` | `f(M)` for `M = 1..1000` |
| `f_values.jsonl.gz` | raw per-`M` records of the recorded run: status, time and witnesses |
| `compute_f.log` | progress log of the recorded run |
| `ub_cpsat2.txt`, `ub_scip.txt` | results of the two upper-bound cross-checks |
| `rerun_check.txt` | comparison of the recorded run with a second full run |
| `admissible.py`, `compute_f.py`, `records.py`, `make_outputs.py` | computation |
| `verify_witnesses.py`, `verify_ub_cpsat2.py`, `verify_ub_scip.py`, `run_scip_parallel.py` | verification |
