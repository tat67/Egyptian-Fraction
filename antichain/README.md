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
| 42 elements | Not found. The searches below exclude every 42-element solution of the stated shapes; they are **not** yet a proof that no 42-element solution exists (see "What is not covered"). |

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

`complete_search.cpp L K J` treats all `T` with `|T| = K` of the shape

    T = M ∪ R,   M = the elements ≤ L, all of them squarefree semiprimes, |M| = K − J;   R = J arbitrary integers > L.

For every antichain `M` with `1 − J/(L+1) ≤ Σ_M 1/n < 1` (a necessary condition, since `J` distinct integers `> L`
have reciprocal sum `< J/(L+1)`) it finds **all** completions `R` — no assumption on the elements of `R`.
Everything is exact integer arithmetic (128/256-bit); the only rounding is directed rounding of the pruning bounds
in the enumeration of `M`.

Ingredients (proofs are short and given in the source comments):

1. **Classical bound.** If `n_1 < … < n_j` and `Σ 1/n_i = ρ` then `1/ρ < n_1 < j/ρ`. Used for the first `J − 2` elements of `R`.
2. **Two-term structure.** For `1/y + 1/z = a/D` in lowest terms with `y ≤ z`: there are `w | D` and `y' | w` with
   `gcd(y', D/w) = 1`, `a | y' + D/w`, and `y = h·w`, `z = h·(D/w)·(w/y')`, `h = (y' + D/w)/a`.
   Consequences used by the program:
   * `z ≥ a/2` (two-term lemma) — rejects almost every candidate pair in O(1);
   * `a·y − D = w·y' ≤ gcd(y, D)²`; with `y_0 = ⌊D/a⌋ + 1`, `ρ = a·y_0 − D`: the value `y = y_0` works iff `ρ | D·y_0`,
     and a value `y > y_0` needs a divisor `w > √a` of `D` with `w | y`.
3. **Clique rule.** Let `V` be the primes dividing the denominator of the remaining sum. Each must divide a remaining
   element; two primes `p, q ∈ V` with `p·q ∈ M` cannot divide the same element. So more pairwise adjacent primes
   than remaining elements is impossible, and exactly as many forces each remaining element to be `≡ q·t (mod q²)`
   for one clique prime `q` (with `t` determined by `a/D`).

Validation: on the cores of known 43-element sets the program (`K = 43, J = 4`) returns exactly the known completions
and no others, with and without the clique rule.

Runs for `K = 42`, `L = 1140` (all squarefree semiprimes `≤ 1140` as possible elements of `M`; 323 of them):

| shape | main sets `M` in the window | result |
|---|---:|---|
| 39 semiprimes + 3 elements `> 1140` (`J = 3`) | 23,315,868 | **no solution**; nothing unresolved ([`runs/run42_J3_L1140.txt`](runs/run42_J3_L1140.txt)) |
| 38 semiprimes + 4 elements `> 1140` (`J = 4`) | 12,446 | run in progress |
| 40 semiprimes + 2 elements `> 1140` (`J = 2`) | about 1.1·10^10 | run in progress |

## What is not covered (so 42 is not yet excluded)

* Sets in which some element `≤ 1140` is not a squarefree semiprime (e.g. `4q`, `9q`, `pqr`).
* Sets with at most one element above 1140 (`J ≤ 1`).
* The lower bound 42 itself is taken from the problem statement.

A full proof that 42 is impossible would need these cases as well, plus a formal (Lean) verification; neither is done here.

## Files

| file | content |
|---|---|
| `solutions43.txt` | twelve 43-element antichains with reciprocal sum 1 (one per line) |
| `verify_antichain.py`, `verify_antichain.cpp` | independent exact verifiers |
| `plain_search.cpp` | constructive search (found the 43-element sets) |
| `complete_search.cpp` | exhaustive search over `M ∪ R` shapes with arbitrary `R` |
| `runs/` | outputs of the runs quoted above |
