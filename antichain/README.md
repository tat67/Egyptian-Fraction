# Antichain Egyptian fractions: `1 = Σ 1/n` with no element dividing another

**Problem (Q1).** Find the smallest size of a finite set `T` of integers `≥ 2` with

    Σ_{n∈T} 1/n = 1      and      m ∤ n for all distinct m, n ∈ T.

(`T = {1}` satisfies the literal statement trivially; as in the problem's own bounds, `1 ∉ T` is understood.)
Known before this work: a 44-element example (upper bound 44) and the lower bound 42 (taken as given, not re-proved here).

## Status

| | |
|---|---|
| **New upper bound** | **43.** Twelve explicit 43-element sets are in [`solutions43.txt`](solutions43.txt); each is verified exactly. |
| Lower bound | 42 (given in the problem statement; not re-verified here). |
| **Hence** | **the minimum is 42 or 43.** |
| 42 elements | **No 42-element set exists except possibly in two shapes** that are not yet searched (see the table below): 41 elements `≤ 1140` plus one larger element, or all 42 elements `≤ 1140` with at least one that is not a squarefree semiprime. |

One of the twelve sets:

    T43 = { 6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62, 65, 69, 74, 77, 82, 85, 86,
            87, 91, 93, 95, 106, 111, 115, 118, 122, 129, 133, 155, 159, 183,
            578495, 869159, 47071321, 180891067 }

with `578495 = 5·37·53·59`, `869159 = 17·29·41·43`, `47071321 = 11·29·41·59·61`, `180891067 = 7·17·23·29·43·53`; the first 39 elements
are squarefree semiprimes, the last four are products of several primes that repair the `p`-adic defects of the first 39.

Verification (exact arithmetic, two independent programs):

    python3 verify_antichain.py solutions43.txt                    # Python fractions
    g++ -O2 -o verify_antichain verify_antichain.cpp && ./verify_antichain solutions43.txt   # 128-bit integers, no floating point

Both check, for every listed set: the elements are distinct and `≥ 2`, no element divides another, and the
reciprocal sum equals `1` exactly.

## How the 43-element sets were found (`plain_search.cpp`)

Write `T = C ∪ F`: `C` consists of `43 − 4 = 39` squarefree semiprimes with reciprocal sum just below 1, and `F` of
four "fixers". Let `r = 1 − Σ_C 1/n = a/D` in lowest terms. If every fixer `n` divides `D`, then with `c = D/n`

    Σ_{n∈F} 1/n = r     ⇔     Σ c = a,   c | D.

So the fixers are four divisors of `D` with sum `a`; the largest is at least `a/4`, the next at least a third of the
rest, and so on. `plain_search.cpp` enumerates all cores (primes `≤ B`, reciprocal sum in `[1 − 1/W, 1)`), and for
each core all such divisor sets whose prime sets are independent in the graph of `C` (no element of `C` divides a
fixer) and not nested. It uses 128-bit integers only.

    g++ -O2 -pthread -o plain_search plain_search.cpp
    ./plain_search 61 43 4 600 4      # 498,825 cores, about 11 minutes on 4 threads: the twelve sets of solutions43.txt
    ./plain_search 47 44 5 400 4      # sanity run: 60 different 44-element sets in 4 seconds

## Exhaustive searches for 42 elements (`complete_search.cpp`)

### Reduction

Let `T` be a 42-element antichain with `Σ 1/n = 1` (`1 ∉ T`). Fix `L = 1140`.

1. **No prime powers.** If `p^k ∈ T`, every other multiple of `p^k` is excluded, so `1/p^k` is the only term with
   `v_p = −k` and `v_p(Σ) = −k < 0`. So every element has at least two prime factors.
2. **Split by size.** `T = M ∪ R`, where `M` consists of the elements `≤ L` and `R` of the `J` elements `> L`.
   `M = X ∪ M'`: `M'` consists of squarefree semiprimes, and `X` of the other elements (neither prime powers nor squarefree semiprimes).
   No semiprime dividing an element of `X` can be in `M'`.
3. **Value bound.** `Σ_X + (largest |M'| reciprocals of semiprimes ≤ L not dividing an element of X) + Σ_{i=1..J} 1/(L+i) ≥ 1`.
   `xsets.py` enumerates every admissible `X` for given `J` (integer upper bounds rounded up, so no set is lost):

   | `J` | admissible `X` (besides `X = ∅`) |
   |---:|---|
   | ≥ 5 | none, and `X = ∅` fails too: **impossible** (the bound decreases in `J`) |
   | 4 | 9 sets: `{4q}` for `q = 53, 59, …, 89` |
   | 3 | 1,421 sets (123 single elements, 1,298 pairs) |
   | 2 | 88,998 sets (sizes 1–4) |
   | 1, 0 | more than 1.1 million each (enumeration not completed) |

4. **`J = 0`, `X = ∅`** (42 semiprimes): impossible by the theorem of this repository (no semiprime set with `≤ 46` elements has an integral reciprocal sum).

### The search

For given `J` and `X`, `complete_search.cpp L K J` enumerates every set `M'` of `K − J − |X|` semiprimes `≤ L`, avoiding the divisors of `X`,
with `1 − J/(L+1) ≤ Σ_M < 1`, and finds **all** completions `R` (any `J` integers `> L`; no assumption on their form).
Everything is exact integer arithmetic (128/256-bit); the only rounding is directed rounding of the pruning bounds.

1. **Classical bound.** If `n_1 < … < n_j` and `Σ 1/n_i = ρ`, then `1/ρ < n_1 ≤ j/ρ`. Used for the first `J − 2` elements of `R`.
2. **Two-term structure.** For `1/y + 1/z = a/D` in lowest terms with `y ≤ z`: there are `w | D` and `y' | w` with
   `gcd(y', D/w) = 1`, `a | y' + D/w`, and `y = h·w`, `z = h·(D/w)·(w/y')`, `h = (y' + D/w)/a`. Consequences used by the program:
   * `z ≥ a/2` (two-term lemma). The admissible `y` form an initial segment, so testing `y_0 = ⌊D/a⌋ + 1` rejects almost every candidate in O(1);
   * `a·y − D = w·y' ≤ gcd(y, D)²`. With `ρ = a·y_0 − D`, the value `y = y_0` works iff `ρ | D·y_0`,
     and a value `y > y_0` needs a divisor `w > √a` of `D` with `w | y`.
3. **Clique rule.** Every prime of the remaining denominator divides a remaining element, and two primes `p, q` with
   `p·q ∈ M` cannot divide the same element. So more pairwise adjacent primes than remaining elements is impossible.
   Exactly as many forces each remaining element to be `≡ q·t (mod q²)` for one clique prime `q`.

Validation: on the cores of the known 43-element sets the program (`K = 43, J = 4`) returns exactly the known completions
and no others, with and without the clique rule. `resolve_two.py` (Python big integers) re-solves every boundary case
and recovers all twelve known solutions from their first 41 elements.

### Results (`K = 42`, `L = 1140`)

| shape | `X` | main sets checked exactly | result |
|---|---|---:|---|
| `J ≥ 5` (`≤ 37` elements `≤ 1140`) | all | — | **impossible** (value bound) |
| 38 + 4 | `∅` | 10,611 | **no solution** ([`runs/run42_J4_L1140.txt`](runs/run42_J4_L1140.txt)); the 4 capped sub-cases were re-run with a larger cap and the last boundary instance was solved exactly ([`runs/run42_J4_subcases.txt`](runs/run42_J4_subcases.txt)) |
| 38 + 4 | 9 sets | 40 | **no solution** ([`runs/run42_J4_X.txt`](runs/run42_J4_X.txt)) |
| 39 + 3 | `∅` | 23,315,868 | **no solution**, nothing unresolved ([`runs/run42_J3_L1140.txt`](runs/run42_J3_L1140.txt)) |
| 39 + 3 | 1,421 sets | 2,777,425 | **no solution** ([`runs/run42_J3_X.txt`](runs/run42_J3_X.txt)) |
| 40 + 2 | `∅` | 987,428,295 | **no solution** ([`runs/run42_J2_L1140.txt`](runs/run42_J2_L1140.txt)); 1,466 sets with a denominator above `2^120` were re-run with the 256-bit path |
| 40 + 2 | 88,998 sets | 1,069,645,282 | **no solution** ([`runs/run42_J2_X.txt`](runs/run42_J2_X.txt)); 81 wide cases re-run in 256 bits and cross-checked with `resolve_two.py` |
| 42 + 0 | `∅` | — | **impossible** (semiprime theorem of this repository) |
| 41 + 1 | all | ~2·10^12 | **not completed** |
| 42 + 0 | `≠ ∅` | — | **not completed** |

"Main sets checked exactly" counts the sets `M` in the value window that pass the small-prime test (at most `J` pairwise adjacent unsatisfied primes among 2, 3, 5, 7, 11, 13); for each of them `1 − Σ_M` is computed exactly and all completions are searched.

Run time: 38+4 13 min (4 threads), 39+3 16 min (3 threads), 40+2 21 min (3 threads), 40+2 with `X` 30 min (4 threads).

## What is not covered (so 42 is not yet excluded)

* **41 + 1**: 41 elements `≤ 1140` and one element `n > 1140`. Here `n = 1/(1 − Σ_M)` is forced: each main set is a single
  candidate, and the condition is purely local (the primes of `n` are exactly the primes at which `M` alone is not
  integral, they must be pairwise non-adjacent, and one congruence per prime). Heuristically a solution is very
  unlikely, but the value window contains about `2·10^12` main sets. With the cover test and the inner clique rule
  (validated on the known 48-term semiprime solutions of shape 47 + 1) the search still needs days on 4 cores.
  A prime-ordered search with a loss bound, as in `semiprime48.cpp`, would be needed.
* **42 + 0 with `X ≠ ∅`**: all 42 elements `≤ 1140`, at least one of them not a squarefree semiprime (more than 10^6 sets `X`).
* The lower bound 42 itself is taken from the problem statement.

## Files

| file | content |
|---|---|
| `solutions43.txt` | twelve 43-element antichains with reciprocal sum 1 (one per line) |
| `verify_antichain.py`, `verify_antichain.cpp` | independent exact verifiers |
| `plain_search.cpp` | constructive search (found the 43-element sets) |
| `complete_search.cpp` | exhaustive search over `M ∪ R` shapes with arbitrary `R`, optional non-semiprime set `X` (`XFILE`) |
| `xsets.py` | enumeration of the admissible non-semiprime sets `X` |
| `resolve_two.py` | exact big-integer solver for two-term boundary cases |
| `runs/` | outputs of the runs quoted above; `xsets_42_J.txt(.gz)` are the `X` lists used |
