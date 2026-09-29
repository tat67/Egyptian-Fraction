# Integral reciprocal sums of sphenic numbers (|T| ≤ 73081)

**Problem.** Let `P = { p·q·r : p < q < r primes } = { 30, 42, 66, 70, … }` (sphenic numbers).
Is there a nonempty `T ⊆ P` with `|T| ≤ 73081` such that `Σ_{n∈T} 1/n` is an integer?

**Answer: YES.** An explicit set with `|T| = 6097` is in [`sphenic_solution.txt`](sphenic_solution.txt)
(one line, 6097 space-separated integers, smallest 30, largest 45117415327,
SHA-256 `edce904da6bb18faf556ef94ac45331abeb2d4f9862194fc7e7d9fafd68a949a`). Its reciprocals sum to **exactly 1**.

Everything is exact integer / rational arithmetic: neither program contains `float`, `double`,
`long double`, `math`, `random`, or a true-division operator (the only `/` characters are in
comments and printed strings; randomness comes from an integer splitmix64 generator).

## Why the value must be 1

Let `a_1 < a_2 < …` be the sphenic numbers and `H_k = Σ_{i≤k} 1/a_i`. Computed exactly
(`sphenic73081.py`, unreduced integer numerator/denominator pair, no rounding):

* `H_4401 < 1 ≤ H_4402` (`a_4402 = 23309`), so at least 4402 terms are needed for a sum of 1;
* `H_73081 = 1.5557763849892871928229026719… < 2` (`a_73081 = 356991`).

If `T` is nonempty with `|T| = k ≤ 73081`, then `0 < Σ_T 1/n ≤ H_k ≤ H_73081 < 2`, so an
*integral* sum is exactly `1`. (Note `H_73081 > 1`, so the bound alone does not exclude an integral
sum; the answer had to be settled by construction.)

## Local criterion

For squarefree denominators, `Σ_{n∈T} 1/n` has `p`-adic valuation `≥ 0` at a prime `p` iff

    ρ_p := Σ_{n∈T, p | n} (n/p)^(-1)  ≡  0  (mod p).

(Write the sum as `(1/p)·Σ 1/m + B` with `m = n/p` prime to `p` and `B` `p`-integral.)
Since every denominator is squarefree, if this holds for all primes `p ≥ 7` the sum lies in `(1/30)ℤ`.

## Construction (`sphenic_search.py`)

1. **Seed**: the `k` smallest sphenic numbers (here `k = 5596`, `a_k = 29379`).
2. **Top-down repair**: for primes `p = 3989, …, 11, 7` in *decreasing* order, if `ρ_p ≠ 0` toggle
   (add, or delete if already present) a few terms `p·a·b` with `a < b < p` prime so that `ρ_p`
   becomes `0`. Because `p` is the *largest* prime in every toggled term, primes larger than `p`
   are unaffected, so once `ρ_p = 0` it stays `0`. (Single toggles are tried first via
   `ab ≡ (−ρ_p)^(-1) mod p`, then pairs, then a BFS over residues for the smallest primes.)
3. After the pass, `ρ_p = 0` for every prime `p ≥ 7`, so the sum is `j/30` for an integer `j`
   (asserted by the program, which reports `j` for each attempt). The repair drifts the sum by about
   `−1/30`, so seeds with sum ≈ 1 land on `29/30` and seeds with sum ≈ 1.03 land on `30/30`.
4. Attempt 2 (`k = 5596`) landed on `30/30`: the sum is `1`.

Concretely `T = (first 5596 sphenic numbers) \ R ∪ A` with `|R| = 128` removed and `|A| = 629`
added terms; `|T| = 5596 − 128 + 629 = 6097`. The added terms involve 547 distinct primes in total.
Run `python3 sphenic_search.py` to reproduce (deterministic; ≈ 0.4 s).

## Verification (`verify_sphenic.py`, independent of the search)

    $ python3 verify_sphenic.py sphenic_solution.txt
    read 6097 numbers from sphenic_solution.txt
    |T| = 6097 <= 73081: OK, all distinct: OK
    every element is a product of exactly 3 distinct primes: OK
    smallest / largest element: 30 / 45117415327
    exact sum of reciprocals = 1/1
    sum of 1/n over T == 1 EXACTLY (Fraction arithmetic): OK
    local criterion (sum of (n/p)^-1 == 0 mod p) holds at all 547 primes occurring in T: OK
    VERIFIED

Three independent exact checks agree that the sum is `1`: `fractions.Fraction` accumulation, the
common-denominator identity `Σ L/n = L` (`L` = product of the primes involved), and an unreduced
integer pair `(N, D)` from a balanced product tree with `N = D`.

## Files

| file | purpose |
|---|---|
| `sphenic73081.py` | exact `H_k` computation (`H_73081 < 2`, crossing `H_4402 ≥ 1`) |
| `sphenic_search.py` | seed + top-down repair search (integer arithmetic only) |
| `sphenic_solution.txt` | the 6097-element set `T` |
| `verify_sphenic.py` | independent exact verifier |
