# Integral reciprocal sums of squarefree semiprimes

**Problem.** Let

    P = { p·q : p < q primes } = { 6, 10, 14, 15, 21, 22, 26, 33, 34, 35, ... }.

Does there exist a nonempty `T ⊆ P` with `|T| ≤ 46` such that `Σ_{n∈T} 1/n` is an integer?

**Answer: No.** No such set exists. The proof below is computer-assisted.
`semiprime_reciprocals.cpp` carries it out exactly, using only integer and rational arithmetic (it contains no `float`, `double` or `long double`).

This bound is sharp. There are 47-element subsets of `P` whose reciprocals sum to 1. Johnson (1978) gave a 48-term example, and Watanabe (arXiv:2009.03275) found 47-term examples. Here is one; the program checks it exactly:

    1 = 1/6 + 1/10 + 1/14 + 1/15 + 1/21 + 1/22 + 1/26 + 1/33 + 1/34 + 1/35 + 1/38 + 1/39
      + 1/46 + 1/51 + 1/55 + 1/57 + 1/58 + 1/62 + 1/65 + 1/69 + 1/77 + 1/82 + 1/85 + 1/86
      + 1/87 + 1/91 + 1/93 + 1/94 + 1/95 + 1/118 + 1/119 + 1/123 + 1/133 + 1/145 + 1/155
      + 1/161 + 1/187 + 1/203 + 1/215 + 1/287 + 1/329 + 1/493 + 1/517 + 1/1247 + 1/1357
      + 1/1363 + 1/2537

Watanabe's searches used only primes `≤ 101`, and he conjectured that 47 is the minimum. The argument here allows every prime, however large, and so proves that the minimum is exactly 47.

Large primes really can occur in such representations, which is why a proof must handle them. The program's self-test finds 47-term representations of 1 that use primes far above 101. One uses the prime `3779 = 29·37 + 29·41 + 37·41` as a "star" joined to 29, 37 and 41:

    1 = 1/6 + 1/10 + 1/14 + 1/15 + 1/21 + 1/22 + 1/26 + 1/33 + 1/34 + 1/35 + 1/38 + 1/39
      + 1/46 + 1/51 + 1/55 + 1/57 + 1/58 + 1/62 + 1/65 + 1/69 + 1/74 + 1/77 + 1/82 + 1/86
      + 1/87 + 1/91 + 1/93 + 1/95 + 1/106 + 1/111 + 1/115 + 1/123 + 1/133 + 1/155 + 1/159
      + 1/161 + 1/185 + 1/203 + 1/215 + 1/253 + 1/265 + 1/583 + 1/667 + 1/731
      + 1/109591 + 1/139823 + 1/154939

Here `109591 = 29·3779`, `139823 = 37·3779` and `154939 = 41·3779`.

---

## Proof

Throughout, `a_1 < a_2 < ...` are the elements of `P`. `H_k = 1/a_1 + ... + 1/a_k` is the largest possible reciprocal sum of a `k`-element subset of `P`.

### 1. The sum must be exactly 1, and 38 ≤ |T| ≤ 46

The program computes the following as exact rationals:

* `H_46 = 1.0577...`, so `H_46 < 2`;
* `H_37 = 0.9936...`, so `H_37 < 1`;
* `H_38 = 1.0014...`, so `H_38 > 1`.

If `|T| = k ≤ 46`, then `0 < Σ_{n∈T} 1/n ≤ H_k ≤ H_46 < 2`. So an integral sum must equal `1`, and `H_k ≥ 1` forces `k ≥ 38`.

### 2. A local criterion

Regard `T` as a graph whose vertices are primes, where `n = pq ∈ T` is the edge `{p, q}`. Let `N(p)` be the set of neighbours of `p`.

**Lemma 1.** `Σ_{n∈T} 1/n ∈ ℤ` holds if and only if, for every prime `p`,

    Σ_{q ∈ N(p)} q^{-1} ≡ 0   (mod p).                                           (*)

*Proof.* Split the sum as `(1/p)·A_p + B_p`, where `A_p = Σ_{q∈N(p)} 1/q` and `B_p` collects the terms not divisible by `p`. The denominators in `A_p` and `B_p` are prime to `p`, so the `p`-adic valuation of the sum is `≥ 0` exactly when `p` divides the numerator of `A_p`, i.e. when (*) holds. A rational number is an integer iff its `p`-adic valuation is `≥ 0` for every `p`. ∎

So the question becomes: is there a graph with at most 46 edges that satisfies (*) at every vertex? If there is, §1 shows its reciprocal sum is exactly `1`. The program uses that value only for pruning.

### 3. Core, big primes, and the unsatisfied set

Let `S = {2, 3, 5, ..., 73}` (21 primes). These are exactly the primes that occur in `a_1, ..., a_46`. Call the primes `≥ 79` *big*. Split `T` into

* `C`, the *core*: the edges with both ends in `S`;
* `G`: the edges with at least one big end.

For `q ∈ S` let `ρ(q) = Σ_{r : qr ∈ C} r^{-1} mod q` be the residue that the core alone contributes to (*) at `q`. Let `U = { q ∈ S : ρ(q) ≠ 0 }` be the unsatisfied set.

**Lemma 2.** `|G| ≥ |U|`, and therefore `|C| + |U| ≤ |T| ≤ 46`.

*Proof.* If `q ∈ U` had no big neighbour, (*) would fail at `q`. So every `q ∈ U` has a big neighbour. An edge of `G` has at most one end in `S`, so these edges are distinct for distinct `q`. ∎

**Lemma 3 (value).** Every edge of `G` has a prime factor `≥ 79`. For each `q ∈ U` choose one edge joining `q` to a big prime; its reciprocal is at most `1/(79q)`. The other edges of `G` are distinct elements of `P` with a factor `≥ 79`. Let `V(x)` be the sum of the `x` largest reciprocals of such elements, so `V(x) = 1/158 + 1/166 + 1/178 + ...`. Since the whole sum is 1,

    1 − Σ_{q∈U} 1/(79q) − V(46 − |C| − |U|)  ≤  Σ_C  ≤  1.

The same argument works with `U` replaced by any subset `U' ⊆ U`: charge `1/(79q)` only for `q ∈ U'` and bound all other edges of `G` by `V`. That gives `1 − Σ_{q∈U'} 1/(79q) − V(46 − |C| − |U'|) ≤ Σ_C`. The search uses this general form (see Step 1).

**Lemma 4 (shape of the big part).** For `q ∈ S` let `d_q` be the number of big neighbours of `q`, and let `b` be the number of edges joining two big primes. Then:

1. `d_q ≥ 1` for `q ∈ U`. For `q ∉ U`, either `d_q = 0` or `d_q ≥ 2`, because a single big neighbour would leave a nonzero residue at `q`.
2. The *excess* satisfies

       E := |G| − |U| = b + Σ_{q∈U} (d_q − 1) + Σ_{q∉U} d_q  ≤  46 − |C| − |U|.

3. *Parity at 2.* Every big prime is odd, so each big neighbour of 2 contributes `1 (mod 2)`. Condition (*) at 2 then gives `ρ(2) + d_2 ≡ 0 (mod 2)`, with `ρ(2) = 0` if `2 ∉ U`.
4. *Value.* The big neighbours of `q` are distinct primes `≥ 79`. If `q ∈ U` has exactly one big neighbour `P`, then (*) forces `P ≡ (−ρ(q))^{-1} (mod q)`, so `P ≥ P_min(q)`, the least prime `> 73` in that residue class. Hence

       1 − Σ_C  =  Σ_G  ≤  Σ_{q∈U, d_q=1} 1/(q·P_min(q)) + Σ_{d_q≥2} Σ_{k<d_q} 1/(q·b_k) + b/(79·83),

   where `b_0 = 79 < b_1 = 83 < ...` are the primes above 73.
5. *Stars.* If `b = 0`, every big prime `P` has all its neighbours in `S`. Write `A = N(P)`; then (*) at `P` reads `P | n(A) := Σ_{q∈A} Π_{r∈A} r / q`, so `P` is one of the finitely many prime factors of `n(A)`.

**Lemma 5 (star size).** A big prime whose neighbours all lie in `S` has at most 10 neighbours. If it had `d` neighbours, its edges would contribute at most `Σ_{i<d} 1/(79·p_i)`, where `p_i` are the smallest primes, and the other `≤ 46 − d` edges at most `H_{46−d}`. For `d ≥ 11` this total is below 1. The program recomputes this bound; for the budget-46 search it prints the maximum, 10.

### 4. The computation

**Step 1: enumerate the cores.** The program enumerates every core `C` (every subset of the 210 elements of `P` with both factors in `S`) such that

* `|C| + |U(C)| ≤ 46`, and
* the inequalities of Lemma 3 hold.

The enumeration is a depth-first search over the primes of `S` in decreasing order. When prime `p` is processed, the search chooses all core edges joining `p` to smaller primes. Every core edge at `p` is then fixed, so the residue `ρ(p)` is known. Either `ρ(p) = 0`, or `p ∈ U`, which costs one unit of the budget 46. Each core is visited exactly once.

A branch is pruned only when one of the following is certain:

* `|C| + |U|` would exceed 46;
* the core sum already exceeds 1;
* even the best completion violates Lemma 3 for the part of `U` decided so far, `U' = U ∩ (p, ∞)`.

The best completion is bounded by the largest remaining core reciprocals plus the allowance `V(·)` for big edges. Primes that join `U` later are not charged `1/(79q)` at that node, so the test is Lemma 3 for the subset `U' ⊆ U`, which is valid (see Lemma 3). Step 1 therefore keeps exactly the cores that satisfy the value bound for **every** upper segment `U ∩ (p, ∞)` of `U`.

*Correction.* An earlier version of this text said the search keeps all cores that satisfy the final Lemma 3 inequality. That is not quite what it does. A prime that joins `U` later adds `1/(79q)` but removes only the smallest `V` term, so the final inequality can hold at a core that was pruned earlier. The pruning is still sound, because it uses the general form of Lemma 3. The Lean formalization in [`lean/`](lean/README.md) states the hypothesis with the corrected condition.

**Step 2: complete each surviving core.** For every core that survives Step 1:

* If `U = ∅`, the core satisfies (*) everywhere. Its sum is then an integer in `(0, 2)`, hence 1, so `T = C` would be a solution.
* Otherwise the program enumerates every shape `(d_q)_{q∈S}, b` allowed by Lemma 4 (1)–(3) and discards those violating the value bound (4). For each remaining shape with `b = 0`, it lists all stars `(P, A)` with `A ⊆ {q : d_q ≥ 1}`, `2 ≤ |A| ≤ 10`, `P > 73` a prime factor of `n(A)`, and `P ≡ (−ρ(q))^{-1} (mod q)` whenever `d_q = 1`. It then searches exactly for a family of distinct stars that covers every `q` exactly `d_q` times with the right residue sums. A surviving shape with `b > 0` would be reported as *unresolved*.

**Result of the run.** The depth-first search visits `1.4·10^11` nodes.

* Exactly 178 cores survive Step 1: 111 with `|C| + |U| = 46` and 67 with `|C| + |U| ≤ 45`. None has `U = ∅`.
* Across these cores, Step 2 enumerates 3777 shapes satisfying Lemma 4 (1)–(3).
* Only 61 shapes also pass the value bound (4). All of them have `b = 0`.
* For none of these 61 shapes does even one admissible star exist.

So no core can be completed, and nothing is left unresolved. I also recomputed the 178 cores independently in Python with exact rationals. That check gives the same numbers: 61 feasible shapes and no star candidates.

So no `T` with `|T| ≤ 46` exists. ∎

### 5. Why the computation is rigorous

* **Exact arithmetic.** Congruences are exact integer arithmetic. `H_k` and the checks of candidate solutions use exact big-integer rationals (`BigNat`).
* **Directed rounding.** Every bound on a sum of reciprocals is a 96-bit fixed-point integer. Upper bounds are rounded up (`⌈2^96/n⌉`) and lower bounds are rounded down (`⌊2^96/n⌋`). A branch is discarded only if the rounded-up best case is still `< 1`, or the rounded-down core sum is already `> 1`.
* **Completeness.** At prime `p` the search goes through every subset of the smaller primes. For the 8 smallest primes it uses a table of all `2^8` subsets, indexed by residue. The explicit include/exclude recursion handles the rest. The parallel version numbers the search nodes at one fixed level and hands each number to exactly one thread through an atomic ticket counter.
* **Self-tests** (`--selftest`):
  * (a) The same engine, without unsatisfied primes and with budget 47, finds all 17 representations of 1 by 47 semiprimes whose primes are all `≤ 73`. It verifies each one exactly. Watanabe also reports 17 examples, from a search with primes `≤ 101`. This test shows that the search is not vacuous.
  * (c) The completion routine is run on the core of the 47-term example above.
    * With `S = primes ≤ 53` (a tight case), it reconstructs the prime 59 and the edges `118, 1357, 2537`.
    * With `S = primes ≤ 43`, it must use a shape with excess: 2 has two big neighbours, 47 and 59. It reconstructs all seven big edges.
  * (b) The whole pipeline, including core enumeration, unsatisfied primes and completion, runs with `S = primes ≤ 53` and budget 47.
    * It finds 21 exactly verified 47-term solutions; 19 of them are completed through big-prime stars.
    * The big primes include 59, 61, ..., 269 and 3779. The example with 3779 above comes from this run.
    * It also reports 2902 cores it cannot settle. Those are expected here and are not errors. This test drops the prime-≤73 set and uses budget 47, so the parity and value bounds do not rule out every shape with big–big edges in that setting. In the real proof the program checks that no such core occurs.

---

## Building and running

    g++ -O3 -march=native -pthread -o semiprime_reciprocals semiprime_reciprocals.cpp
    ./semiprime_reciprocals            # full proof, uses all hardware threads
    ./semiprime_reciprocals 4          # choose the number of threads
    ./semiprime_reciprocals --selftest # proof plus the self-tests above
    ./semiprime_reciprocals --budget 44  # smaller budgets (quick sanity runs)

On 4 cores the proof run takes about 20 minutes and under 300 MB of memory. The self-tests add about 15 minutes. Output of the proof run:

    === Part 1: the smallest squarefree semiprimes ===
    46 smallest elements of P: 6 10 14 15 21 22 26 33 34 35 38 39 46 51 55 57 58 62 65 69 74 77 82 85 86 87 91 93 94 95 106 111 115 118 119 122 123 129 133 134 141 142 143 145 146 155
    H_46 = sum of their reciprocals < 1.057751   (exact check H_46 < 2: yes)
    exact checks: H_37 < 1: yes,  H_38 > 1: yes   => any solution has 38..46 terms and sum exactly 1

    === Part 2: exhaustive search (S = primes <= 73, |C|+|U| <= 46) ===
    threads = 4
    largest possible star (neighbours of one big prime): 10
    search nodes           : 139830520211
    cores passing all tests: 178 (of which |C|+|U| = 46: 111)
    completion shapes      : 3777 tried, 61 pass parity+value (in 61 cores), 0 candidate stars
    unresolved cores       : 0
    solutions found        : 0
    elapsed: 1179 s

    === RESULT ===
    No nonempty set T of squarefree semiprimes with |T| <= 46 has an integral sum of reciprocals.

The count of search nodes depends slightly on the number of threads, because each thread repeats the small part of the tree above the split level.

## Lean formalization

[`lean/`](lean/README.md) formalizes every step of this argument in Lean 4 with Mathlib, except the exhaustive search. That covers the local criterion, the size, value, parity and star-size lemmas, the stars, the component with one big–big edge, and the reduction of an arbitrary solution to the data checked by the search.

The search itself is stated as the explicit hypothesis `Search46`. The theorem `no_integral_sum_le_46` is proved **conditionally** on it, and `Search46` is not verified in Lean. See `lean/README.md` for what is fully proved and what is conditional.

## Files

* `semiprime_reciprocals.cpp`: the complete proof program. It is integer-only, needs C++11 or later and `unsigned __int128` (GCC or Clang).
* `proof_run_output.txt`: output of the proof run (4 threads).
* `selftest_output.txt`: output of `--selftest`, restricted to the self-test part.

## Related results in this repository

* [`README47.md`](README47.md): all 23 subsets `T ⊆ P` with `|T| = 47` and `Σ 1/n = 1`, with a completeness proof (`semiprime47.cpp`).
* [`README48.md`](README48.md): all subsets with `|T| = 48` and `Σ 1/n = 1`, with a completeness proof. `semiprime48.cpp` adds a much stronger pruning bound, which also re-proves the 46-term bound in seconds and the 47-term classification in about a minute.
* [`paper/`](paper/README_PAPER.md): a manuscript that combines this result and the 47-term classification.
* [`README_sphenic.md`](README_sphenic.md): the analogous question for **sphenic numbers** (products of three distinct primes, `30, 42, 66, 70, …`). Here, unlike in the semiprime case above, integral reciprocal sums **do** exist within the bounds asked about (`|T| ≤ 73081`, `|T| ≤ 6096`, and even `|T| ≤ 5000`): **218 independently verified examples** are known, with **4922 – 6668 terms** (167 of them with `|T| ≤ 6096`, 68 with `|T| ≤ 5000`; the smallest has 4922 terms). Every example has reciprocal sum exactly 1, and the only proved lower bound is `|T| ≥ 4402` (because `H_4401 < 1`), so the true minimum lies in `[4402, 4922]` and is unknown.
  * Method 1 (`sphenic_search.py`, integer arithmetic only, about 0.2 s per attempt): take the `k` smallest sphenic numbers and repair the local criterion `Σ_{n ∈ T, p | n} (n/p)^{-1} ≡ 0 (mod p)` at each prime `p` from the top down, using terms in which `p` is the largest prime, so that larger primes stay fixed. Every prime `≥ 7` is then satisfied and the sum lies in `(1/30)ℤ`; it equals 1 when the seed size `k` is chosen so that the repaired sum lands on `30/30`. It never gave fewer than 5151 terms.
  * Method 2 (`sphenic_small.py`, the source of all sets with at most 5000 terms): (i) the seed uses only primes `≤ 2200` (327 primes instead of 550, so far fewer repair terms), (ii) deletions are preferred to additions when one toggle suffices, and (iii) the last primes `≤ 17` are handled *exactly*: only the 35 sphenic numbers built from `{2,…,17}` can still change, each contributes a fixed pair (residues mod 7, 11, 13, 17 packed by CRT; value `P0/t` with `P0 = 510510`), and one meet-in-the-middle join over two precomputed tables (2^17 and 2^18 subsets) finds every completion with sum exactly 1, so the check is the integer equation `S = P0`. This is 6.8× faster per attempt than a bounded DFS over the same tail (0.074 s vs 0.50 s), about 7 % of attempts succeed in the tuned window, and `python3 sphenic_small.py` finds a verified set with `|T| ≤ 5000` in about 1.5 s (`sphenic_solution_5000.txt`, 4978 terms).
  * [`sphenic_examples.txt`](sphenic_examples.txt) lists all 218 examples in full with term counts and SHA-256 checksums; [`verify_sphenic.py`](verify_sphenic.py) checks a set with exact `Fraction` arithmetic and the per-prime criterion; [`sphenic73081.py`](sphenic73081.py) computes the exact bounds (`H_73081 = 1.5557… < 2`, so any integral sum over at most 73081 terms is 1). None of these programs uses floating-point arithmetic.
* **Answers to Prime Puzzles [897](https://www.primepuzzles.net/puzzles/puzz_897.htm) (Q2, Q3) and [899](https://www.primepuzzles.net/puzzles/puzz_899.htm) (Q1, Q2)**, each as a text file with one denominator per row (all verified with exact arithmetic):
  * 899 Q1 (fewer than 48 semiprime terms summing to 1): [`puzzle899_Q1_semiprime_47_terms.txt`](puzzle899_Q1_semiprime_47_terms.txt), 47 terms (the minimum, by the proof above; all 23 such sets are in `solutions47.txt`).
  * 899 Q2 and 897 Q3 (fewer than 73082 terms, each a product of three primes, summing to 1): [`puzzle899_Q2_three_primes_4922_terms.txt`](puzzle899_Q2_three_primes_4922_terms.txt), 4922 terms, all products of three distinct primes (see `README_sphenic.md`).
  * 897 Q2 (semiprime denominators summing to an integer greater than 1): [`puzzle897_Q2_integer2_semiprimes_2250_terms.txt`](puzzle897_Q2_integer2_semiprimes_2250_terms.txt) (sum 2, 2250 terms; 31 verified sets with 2250 – 2552 terms are listed in [`semiprime_integer_examples.txt`](semiprime_integer_examples.txt)) and [`puzzle897_Q2_integer3_semiprimes_708443_terms.txt`](puzzle897_Q2_integer3_semiprimes_708443_terms.txt) (sum 3, 708443 terms). The lower bounds are 1234 terms for the sum 2 and 73736 for the sum 3 (the reciprocals of the 1233, resp. 73736, smallest semiprimes sum to less than 2, resp. 3), so these sets are certificates of existence, not minimal ones; the sum 4 would need more than 600000 terms (the 600177 semiprimes below 3·10^6 have reciprocal sum only about 3.44) and was not attempted. Program: `semiprime_integers.py` (same top-down repair as `sphenic_search.py` with a prime-capped seed and an exact meet-in-the-middle over the 36 semiprimes built from `{2,…,23}`, integer arithmetic only); independent verifier: `verify_semiprime_integer.py FILE N`.
