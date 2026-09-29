# Integral reciprocal sums of sphenic numbers

**Problem.** Let `P = { p·q·r : p < q < r primes } = { 30, 42, 66, 70, … }` (sphenic numbers).
Is there a nonempty `T ⊆ P` with `|T| ≤ B` such that `Σ_{n∈T} 1/n` is an integer?

| bound `B` | answer | explicit example | size |
|---|---|---|---|
| 73081 | **yes** | [`sphenic_solution.txt`](sphenic_solution.txt) | 6097 |
| **6096** | **yes** | [`sphenic_solution_6096.txt`](sphenic_solution_6096.txt) | **5752** |

(The 6097-element set is one element too large for `B = 6096`, so the second bound needed a new set.)

**`B = 6096`: YES.** [`sphenic_solution_6096.txt`](sphenic_solution_6096.txt) is one line of 5752
space-separated sphenic numbers (smallest 30, largest 36563441041; SHA-256
`dbe2bd87f89a3ed7108d9fe885018f40a884ab8fc7996f58b11c023f484883d8`). Their reciprocals sum to **exactly 1**.

Everything is exact integer / rational arithmetic. An AST-level audit of the three scripts finds no float
literal, no `float()`, no true division `/`, and no import of `math`, `random`, `decimal` or `numpy`
(randomness is an integer splitmix64 generator).

## Why an integral sum must be 1

Let `a_1 < a_2 < …` be the sphenic numbers and `H_k = Σ_{i≤k} 1/a_i`. Computed exactly with
`sphenic73081.py` (unreduced integer numerator/denominator pair, no rounding):

* `H_4401 < 1 ≤ H_4402` (`a_4402 = 23309`), so any solution has at least 4402 terms;
* `H_73081 = 1.5557763849892871928229026719… < 2`.

For a nonempty `T` with `|T| = k ≤ 6096` (indeed ≤ 73081): `0 < Σ_T 1/n ≤ H_k < 2`, so an *integral*
sum is exactly `1`. Since `H_6096 > 1`, no size argument excludes it; the answer comes from a construction.

## Local criterion

For squarefree denominators, `Σ_{n∈T} 1/n` has `p`-adic valuation `≥ 0` at a prime `p` iff

    ρ_p := Σ_{n∈T, p | n} (n/p)^(-1)  ≡  0  (mod p).

(Write the sum as `(1/p)·Σ 1/m + B` with `m = n/p` prime to `p` and `B` `p`-integral.)
If this holds for every prime `p ≥ 7`, the sum lies in `(1/30)ℤ`.

## Construction (`sphenic_search.py`)

1. **Seed**: the `k` smallest sphenic numbers.
2. **Top-down repair**: for primes `p = 3989, …, 11, 7` in *decreasing* order, if `ρ_p ≠ 0` toggle
   (add, or delete if already present) a few terms `p·a·b` with `a < b < p` prime so that `ρ_p`
   becomes `0`. `p` is the *largest* prime in every toggled term, so primes larger than `p` are
   unaffected and, once `ρ_p = 0`, it stays `0`. Single toggles are tried first
   (`ab ≡ (−ρ_p)^(-1) mod p`), then pairs, then a BFS over residues for the smallest primes.
3. After the pass, `ρ_p = 0` for every prime `p ≥ 7`, so the sum is `j/30` (asserted by the program,
   which reports `j` for every attempt). The pass drifts the sum by roughly `−1/30`.
   If `j = 30` the sum is `1`; otherwise retry with another random seed / seed size.

For the committed answer: seed `k = 5245` (`a_k = 27646`), attempt 4 landed on `30/30`;
`T = (first 5245 sphenic numbers) \ R ∪ A` with `|R| = 93`, `|A| = 600`, so `|T| = 5245 − 93 + 600 = 5752`.

## Making it fast

The search is *not* a brute-force or exhaustive search; its cost is the number of repair passes times
the cost of one pass. Two measurements drove the speed-up:

* **Where the time goes.** Profiling a pass (~0.19 s) shows ~78 % in `solve`, i.e. in the
  single-toggle candidate scan (one modular inverse per prime below `p`). That is already
  polynomial and cheap, so the lever is the *number of passes*.
* **Seed size vs landed sum.** A 400-attempt scan (`--seed 99`) of seed sizes `k ∈ [4390, 6190)`
  gave (fraction of successful passes landing on `j = 30`):

  | `k` | 4390–4690 | 4690–4990 | 4990–5290 | 5290–5590 | 5590–5890 | 5890–6190 |
  |---|---|---|---|---|---|---|
  | `j = 30` | 1/60 | 14/40 | 28/55 | 44/53 | 31/38 | 19/45 |

  (small `k` lands on `29/30`, large `k` on `31/30`). Larger `k` also means more terms, and
  `|T| ≈ k + 500`, so `k ∈ [4900, 5300)` is the sweet spot: roughly half the passes succeed and
  `|T| ≈ 5400–5800`, comfortably below 6096 (the higher-yield window 5290–5590 would give
  `|T| ≈ 5800–6100`, too close to the bound). This window is now the default.

Results (same machine; all outputs independently verified):

| configuration | passes needed | wall time |
|---|---|---|
| earlier wide window `k ∈ [4390, 6190)`, seed 20260929 | 9 | 1.7 s |
| **tuned default `k ∈ [4900, 5300)`**, seed 20260929 | **4** | **0.65 s** |
| tuned window, 8 other seeds (1–8) | 4, 2, 3, 1, 1, 1, 3, 1 (mean 2.0) | 0.20 – 0.66 s |

Every one of these 9 runs produced a verified set with `|T| ≤ 6096` (sizes 5414 – 5785).
Not claimed: that any of these sets has the minimum possible size.

Reproduce: `python3 sphenic_search.py` (defaults: `--bound 6096 --kmin 4900 --kmax 5300 --seed 20260929`,
writes `sphenic_solution_6096.txt`). The earlier `B = 73081` set is reproduced bit-for-bit by
`python3 sphenic_search.py --bound 73081 --kmin 4390 --kmax 6190 --out sphenic_solution.txt`.

## Verification (`verify_sphenic.py`, independent of the search)

    $ python3 verify_sphenic.py sphenic_solution_6096.txt 6096
    read 5752 numbers from sphenic_solution_6096.txt
    |T| = 5752 <= 6096: OK, all distinct: OK
    every element is a product of exactly 3 distinct primes: OK
    smallest / largest element: 30 / 36563441041
    exact sum of reciprocals = 1/1
    sum of 1/n over T == 1 EXACTLY (Fraction arithmetic): OK
    local criterion (sum of (n/p)^-1 == 0 mod p) holds at all 549 primes occurring in T: OK
    VERIFIED

Independent exact checks agree that the sum is `1`: `fractions.Fraction` accumulation, the
common-denominator identity `Σ L/n = L` (`L` = product of the primes involved, inside the search),
and the per-prime criterion at all 549 primes.

## Files

| file | purpose |
|---|---|
| `sphenic73081.py` | exact `H_k` computation (`H_73081 < 2`, crossing `H_4402 ≥ 1`) |
| `sphenic_search.py` | seed + top-down repair search (integer arithmetic only; options `--bound --kmin --kmax --tries --seed --minimize --out`) |
| `sphenic_solution_6096.txt` | the 5752-element set for `B = 6096` |
| `sphenic_solution.txt` | the 6097-element set for `B = 73081` |
| `verify_sphenic.py` | independent exact verifier (`python3 verify_sphenic.py FILE [BOUND]`) |
