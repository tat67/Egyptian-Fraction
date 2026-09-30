# Integral reciprocal sums of sphenic numbers

**Problem.** Let `P = { p·q·r : p < q < r primes } = { 30, 42, 66, 70, … }` (sphenic numbers).
Is there a nonempty `T ⊆ P` with `|T| ≤ B` such that `Σ_{n∈T} 1/n` is an integer?

| bound `B` | answer | explicit example | size |
|---|---|---|---|
| 73081 | **yes** | [`sphenic_solution.txt`](sphenic_solution.txt) | 6097 |
| 6096 | **yes** | [`sphenic_solution_6096.txt`](sphenic_solution_6096.txt) | 5752 |
| **5000** | **yes** | [`sphenic_solution_5000.txt`](sphenic_solution_5000.txt) | **4978** |

(Each set is too large for the next, smaller bound: the 6097-element set exceeds 6096 by one, and the first
method never produced fewer than 5151 terms, so `B = 5000` needed a new method, `sphenic_small.py`; see
[Getting below 5000](#getting-below-5000-sphenic_smallpy).)

In total **218 examples** have been found and independently verified so far, with **4922 – 6668 terms**
(median 5680); all of them are listed with their term counts, SHA-256 checksums and full contents in
[`sphenic_examples.txt`](sphenic_examples.txt) (see [All examples found so far](#all-examples-found-so-far)).
**68 of the 218 satisfy `|T| ≤ 5000`**, 167 satisfy `|T| ≤ 6096`, and the smallest has **4922 terms**.

**`B = 5000`: YES.** [`sphenic_solution_5000.txt`](sphenic_solution_5000.txt) is one line of 4978
space-separated sphenic numbers (smallest 30, largest 6120074183; SHA-256
`d6f392b82b585311076415252e12e9f8333cfcd4959b5cd34ffab65de41ce3b2`). Their reciprocals sum to **exactly 1**.
`python3 sphenic_small.py` reproduces it (and finds it) in about 1.5 s.

**`B = 6096`: YES.** [`sphenic_solution_6096.txt`](sphenic_solution_6096.txt) is one line of 5752
space-separated sphenic numbers (smallest 30, largest 36563441041; SHA-256
`dbe2bd87f89a3ed7108d9fe885018f40a884ab8fc7996f58b11c023f484883d8`). Their reciprocals sum to **exactly 1**.

Everything is exact integer / rational arithmetic. An AST-level audit of the four scripts finds no float
literal, no `float()`, no true division `/`, and no import of `math`, `random`, `decimal` or `numpy`
(randomness is an integer splitmix64 generator).

## Why an integral sum must be 1

Let `a_1 < a_2 < …` be the sphenic numbers and `H_k = Σ_{i≤k} 1/a_i`. Computed exactly with
`sphenic73081.py` (unreduced integer numerator/denominator pair, no rounding):

* `H_4401 < 1 ≤ H_4402` (`a_4402 = 23309`), so any solution has at least 4402 terms;
* `H_73081 = 1.5557763849892871928229026719… < 2`.

For a nonempty `T` with `|T| = k ≤ 73081` (in particular for the bounds 6096 and 5000): `0 < Σ_T 1/n ≤ H_k < 2`,
so an *integral* sum is exactly `1`. Since `H_k ≥ 1` for every `k ≥ 4402`, no size argument excludes any of
these bounds (`5000 > 4402`); the answer comes from a construction.

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
| earlier wide window `k ∈ [4390, 6190)`, seed 20260929 (this is example E02, 5442 terms) | 9 | 1.7 s |
| **tuned default `k ∈ [4900, 5300)`**, seed 20260929 | **4** | **0.65 s** |
| tuned window, 8 other seeds (1–8) | 4, 2, 3, 1, 1, 1, 3, 1 (mean 2.0) | 0.20 – 0.66 s |

Every one of these 9 runs produced a verified set with `|T| ≤ 6096` (sizes 5414 – 5785).
Not claimed: that any of these sets has the minimum possible size.

Reproduce: `python3 sphenic_search.py` (defaults: `--bound 6096 --kmin 4900 --kmax 5300 --seed 20260929`,
writes `sphenic_solution_6096.txt`). The earlier `B = 73081` set is reproduced bit-for-bit by
`python3 sphenic_search.py --bound 73081 --kmin 4390 --kmax 6190 --out sphenic_solution.txt`, and the
5442-term set (E02) by `python3 sphenic_search.py --bound 6096 --kmin 4390 --kmax 6190 --out FILE`.
The search is deterministic: the same options always give the same file.

## Getting below 5000 (`sphenic_small.py`)

The first method never gave fewer than 5151 terms (best of 137 solutions from a 400-attempt scan, 57 s),
so it cannot answer `B = 5000`. Where the extra terms come from: in the 5151-term set the search **added 521
terms worth only 0.0003 in total** and **removed 26 terms worth 0.0109**. The ≈ 500 added terms are almost
pure parity repair (about one per prime whose residue is nonzero; the seed contains 550 primes), and the
seed has to overshoot 1 by about 1 % to pay for the deletions, which costs roughly another 250 low-value terms.

`sphenic_small.py` changes three things (same local criterion, same top-down repair, still integer arithmetic only):

1. **Prime-capped seed.** The seed is the `k` smallest sphenic numbers *all of whose primes are ≤ CAP*
   (default 2200: 327 primes instead of 550). Terms with a large prime cost a repair term each but carry
   almost no value. A cap sweep (4 attempts for each `k = k0, k0+10, …, k0+320`, where `k0` is the first `k`
   at which the capped seed's sum reaches 1; exploratory runs, sets not saved):

   | cap | primes | `k0` | first hit at `k` | best size | hits / attempts |
   |---|---|---|---|---|---|
   | 1200 | 196 | 4869 | 5129 | 5253 | 5 / 132 |
   | 1600 | 251 | 4618 | 4878 | 5076 | 7 / 132 |
   | 2000 | 303 | 4511 | 4701 | 4943 | 12 / 132 |
   | 2600 | 378 | 4441 | 4641 | 4953 | 18 / 132 |
   | 3200 | 452 | 4412 | 4702 | 4970 | 1 / 132 |
   | no cap (3900) | 539 | 4402 | – | – | 0 / 132 |

   Caps around 2000 – 2600 are best (too small a cap needs too many seed terms; no cap needs too many repairs).
   The first hit comes 190 – 290 terms above `k0` (the seed has to overshoot 1 to pay for the deletions), and the
   repair overhead `|T| − k` of the best set grows with the cap (124, 198, 242, 312, 268 for caps 1200 – 3200),
   as expected since more primes need repairing; for cap 2200 it is 252 – 278 in the 69-set batch below.
2. **Deletion preferred.** When one toggle repairs the residue at `p`, deleting an existing term `p·a·b`
   (which shortens `T`) is chosen in preference to adding one (90 % of the time).
3. **Exact, complete tail (meet in the middle).** The random top-down repair now stops after the prime 19.
   From then on only the 35 sphenic numbers built from `{2, 3, 5, 7, 11, 13, 17}` may still change. Let
   `x_t ∈ {0,1}` be the final presence of such a term `t`, let "out" denote the terms of `T` that are not of
   this kind, and let `P0 = 2·3·5·7·11·13·17 = 510510`. Then `T` is a solution iff

       ρ_q(out) + Σ_t x_t · (t/q)^(-1) ≡ 0 (mod q)   for q = 7, 11, 13, 17,
       P0·Σ_out 1/n + Σ_t x_t · P0/t   =   P0        (sum exactly 1),

   where every `P0/t` is an integer and `P0·Σ_out 1/n` is an integer because all primes above 17 are repaired.
   The residues mod 7, 11, 13, 17 are packed into one integer mod 17017 by the Chinese remainder theorem, so
   the contribution of a subset of the 35 terms is a pair (key, value) that does **not** depend on the stage.
   The two half-tables (2^17 and 2^18 subsets) are therefore built once (≈ 0.5 s); per stage only the two
   targets change, and one dictionary join finds *every* completion and returns the one with the fewest terms.
   (The 35 terms sum to `1651/7854 ≈ 0.21`, which is all the tail can supply; this is why the seed must reach
   a sum of about 1 by itself and why small `k` never hits.) The earlier, bounded depth-first version of this
   tail is kept as `--tail-mode dfs`.

Measurements (same machine):

| method | time per attempt | hits | result |
|---|---|---|---|
| `sphenic_search.py`, 400 attempts (seed 99) | 0.14 s | 137 / 400 (sum = 1) | smallest 5151, **none ≤ 5000** |
| `sphenic_small.py`, DFS tail, window `[4680, 4730)`, 40 attempts | 0.50 s (20.1 s total) | 2 / 40 | – |
| `sphenic_small.py`, join tail, same 40 attempts | **0.074 s (2.9 s total)** | 2 / 40 | **6.8× faster** |
| `sphenic_small.py`, join tail, 1000 attempts | 0.070 s (70 s total) | 69 / 1000, of which 67 have at most 5000 terms | best 4946 |
| `python3 sphenic_small.py` (defaults) | 1.5 s to the first set with at most 5000 terms (attempt 19) | – | **4978** terms |

The smallest set, E149 (**4922 terms**, seed `k = 4648`), came from the DFS-tail version, at attempt 4 of a
wide window (`k ∈ [4100, 4700)`); in that window only 1 attempt in 160 hits, so the tuned window
`k ∈ [4680, 4730)` (about 7 % hits) is what makes the method fast. The command
`python3 sphenic_small.py --tail-mode dfs --bound 5000 --kmin 4100 --kmax 4700` reproduces E149 byte-for-byte.

Still open: the distance between the smallest verified set (4922) and the proved lower bound (4402) is
about 520 terms. A larger tail (primes up to 19 or 23) or a smarter choice of the seed than "the smallest
sphenic numbers below the cap" might close part of it; this has not been tried.

## All examples found so far

Each example is a set `T` of sphenic numbers with `Σ_{n∈T} 1/n = 1` exactly. All **218** were
regenerated by `sphenic_search.py` or `sphenic_small.py`, checked byte-for-byte against the earlier results
where those exist, and verified with `verify_sphenic.py` (Fraction sum `= 1`, every element a product of
exactly 3 distinct primes, `p`-adic criterion at every prime). The complete sets, SHA-256 checksums and
commands are in [`sphenic_examples.txt`](sphenic_examples.txt) (7.4 MB), which was itself re-parsed and
re-checked (218 distinct sets, all sums exactly 1, all checksums match). Three groups:
**A** = E01 – E11 (individual runs of `sphenic_search.py`), **B** = E12 – E148 (its 400-attempt scan),
**C** = E149 – E218 (`sphenic_small.py`).

### Group A: E01 – E11 (individual runs)

| id | terms | seed `k` | pass # | `≤ 6096`? | options for `python3 sphenic_search.py` (`--out FILE` omitted) |
|---|---|---|---|---|---|
| E01 | 6097 | 5596 | 2 | no | `--bound 73081 --kmin 4390 --kmax 6190` (also `sphenic_solution.txt`) |
| E02 | 5442 | 4942 | 9 | yes | `--bound 6096 --kmin 4390 --kmax 6190` |
| E03 | 5752 | 5245 | 4 | yes | *(defaults)* (also `sphenic_solution_6096.txt`) |
| E04 | 5573 | 5070 | 4 | yes | `--seed 1` |
| E05 | **5414** | 4914 | 2 | yes | `--seed 2` |
| E06 | 5683 | 5178 | 3 | yes | `--seed 3` |
| E07 | 5785 | 5278 | 1 | yes | `--seed 4` |
| E08 | 5610 | 5118 | 1 | yes | `--seed 5` |
| E09 | 5590 | 5092 | 1 | yes | `--seed 6` |
| E10 | 5774 | 5270 | 3 | yes | `--seed 7` |
| E11 | 5423 | 4922 | 1 | yes | `--seed 8` |

Rows E04 – E11 use the default options (`--bound 6096`, window `[4900, 5300)`) with the given `--seed`.

### Group B: E12 – E148 (the 400-attempt scan)

The 400-attempt scan behind the seed-size table above (`--seed 99`, window `[4390, 6190)`) produced 137
repair passes that landed on exactly `30/30`. These 137 sets were first only counted (sizes recorded,
sets not saved). They have now been written out with the new `--dump-all` option, and:

* the re-run is deterministic and reproduced the recorded `(attempt, k, size)` of **all 137** exactly
  (same histogram of landed sums: 28/30 × 16, 29/30 × 104, **30/30 × 137**, 31/30 × 34);
* **all 137 were independently verified** with `verify_sphenic.py` and added to `sphenic_examples.txt`
  as E12 – E148, in order of increasing attempt number;
* their sizes run from **5151 to 6668**; 87 of the 137 have `|T| ≤ 6096`.

    python3 sphenic_search.py --bound 73081 --minimize --tries 400 --kmin 4390 --kmax 6190 --seed 99 \
        --dump-all FILE --out BEST

`FILE` receives every set with sum exactly 1 (a `# attempt=A k=K size=S` line followed by the numbers) and
`BEST` the smallest one. Runtime about one minute (400 passes, ≈ 0.15 – 0.2 s each).

The number of primes occurring in a group-B set ranges from 541 to 550.

The five smallest group-B examples:

| id | terms | seed `k` | scan attempt |
|---|---|---|---|
| **E25** | **5151** | 4656 | 46 |
| E58 | 5219 | 4707 | 145 |
| E109 | 5223 | 4716 | 298 |
| E101 | 5266 | 4769 | 277 |
| E98 | 5270 | 4763 | 269 |

Observation from the scan: in each of the 137 sets `|T|` lies between `k + 488` and `k + 515`, so the size
is essentially fixed by the seed size `k`. None of the 56 successful passes with `k < 4650` landed on
`30/30`, and the chance rises with `k` (6 of 21 for `k ∈ [4650, 4800)`, 30 of 58 for `[4950, 5300)`,
44 of 53 for `[5300, 5600)`). The five smallest sets all have `k ∈ [4656, 4769]`, i.e. they come from the
lowest `k` at which a `30/30` landing occurs. None of these 137 sets has 5000 or fewer terms; the prime cap and
exact tail of `sphenic_small.py` (group C) were needed for that.

### Group C: E149 – E218 (`sphenic_small.py`)

* **E149** (4922 terms, seed `k = 4648`, attempt 4): the DFS-tail version, wide window.
  `python3 sphenic_small.py --tail-mode dfs --bound 5000 --kmin 4100 --kmax 4700 --out FILE`
* **E150 – E218** (69 sets): one deterministic batch of the default method (cap 2200, window `[4680, 4730)`,
  join tail, deletion preference 90 %, seed 20260930), in order of increasing attempt number:

      python3 sphenic_small.py --bound 5200 --minimize --tries 1000 --dump-all FILE --out BEST

  1000 attempts in 70 s gave 69 sets with sum exactly 1 (6.9 %); `--bound 5200` only widens what is
  written, it does not change the random choices. Their sizes are 4946 – 5001: 67 have `|T| ≤ 5000` (one
  has exactly 5000) and two have 5001. All use exactly the 327 primes ≤ 2200, and `|T| − k` is 252 – 278.
  **E150** (4978 terms, `k = 4708`, attempt 19) is the first set with `|T| ≤ 5000` and is what
  `python3 sphenic_small.py` writes to `sphenic_solution_5000.txt`.

Group C in total: 70 sets, 68 with `|T| ≤ 5000`, sizes 4922 – 5001 (median 4977).

### Overall

The five smallest examples of all 218:

| id | terms | seed `k` | attempt | how |
|---|---|---|---|---|
| **E149** | **4922** | 4648 | 4 | `sphenic_small.py`, DFS tail |
| E189 | 4946 | 4682 | 549 | `sphenic_small.py` batch |
| E158 | 4950 | 4687 | 125 | `sphenic_small.py` batch |
| E169 | 4951 | 4693 | 280 | `sphenic_small.py` batch |
| E186 | 4951 | 4690 | 478 | `sphenic_small.py` batch |

Distribution of sizes over all 218 examples:

| terms | 4900 – 4999 | 5000 – 5099 | 5100 – 5399 | 5400 – 5699 | 5700 – 5999 | 6000 – 6099 | 6100 – 6399 | 6400 – 6699 |
|---|---|---|---|---|---|---|---|---|
| examples | 67 | 3 | 7 | 35 | 40 | 16 | 32 | 18 |

(The bin 5000 – 5099 holds one set of exactly 5000 terms, which is within the bound `B = 5000`, and two of 5001.)

**What is and is not established.** Existence for `B = 73081`, `B = 6096` and `B = 5000` is settled by the
explicit, exactly verified certificates above (68 of the 218 verified sets have `|T| ≤ 5000`, 167 have
`|T| ≤ 6096`). Minimality is *not* claimed: the only proven lower bound is `|T| ≥ 4402` (because
`H_4401 < 1`), and the smallest verified set has 4922 terms (E149), so the true minimum lies somewhere in
`[4402, 4922]`. Sets found during the exploratory sweeps (cap sweep, window comparisons) were not saved and are
not among the 218.

## Verification (`verify_sphenic.py`, independent of the search)

    $ python3 verify_sphenic.py sphenic_solution_5000.txt 5000
    read 4978 numbers from sphenic_solution_5000.txt
    |T| = 4978 <= 5000: OK, all distinct: OK
    every element is a product of exactly 3 distinct primes: OK
    smallest / largest element: 30 / 6120074183
    exact sum of reciprocals = 1/1
    sum of 1/n over T == 1 EXACTLY (Fraction arithmetic): OK
    local criterion (sum of (n/p)^-1 == 0 mod p) holds at all 327 primes occurring in T: OK
    VERIFIED

`python3 verify_sphenic.py sphenic_solution_6096.txt 6096` and `python3 verify_sphenic.py sphenic_solution.txt 73081`
pass in the same way (549 and 547 primes). Independent exact checks agree that the sum is `1`:
`fractions.Fraction` accumulation, the common-denominator identity `Σ L/n = L` (`L` = product of the primes
involved, inside the searches), and the per-prime criterion at every prime that occurs.

## Files

| file | purpose |
|---|---|
| `sphenic73081.py` | exact `H_k` computation (`H_73081 < 2`, crossing `H_4402 ≥ 1`) |
| `sphenic_search.py` | seed + top-down repair search (integer arithmetic only; options `--bound --kmin --kmax --tries --seed --minimize --dump-all --out`) |
| `sphenic_small.py` | smaller sets: prime-capped seed, deletion preference, exact meet-in-the-middle tail (integer arithmetic only; options `--bound --cap --kmin --kmax --tail --tail-mode --maxsz --pref --tries --seed --minimize --dump-all --out`) |
| `sphenic_solution_5000.txt` | the 4978-element set for `B = 5000` (`python3 sphenic_small.py`) |
| `sphenic_solution_6096.txt` | the 5752-element set for `B = 6096` |
| `sphenic_solution.txt` | the 6097-element set for `B = 73081` |
| `sphenic_examples.txt` | all 218 verified examples (E01 – E218, 4922 – 6668 terms each): overview and size distribution, summary table of term counts, generating commands, SHA-256 checksums, full listings (7.4 MB) |
| `verify_sphenic.py` | independent exact verifier (`python3 verify_sphenic.py FILE [BOUND]`) |
