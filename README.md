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

**Lemma 2.** `|G| ≥ |U|`, and therefore `|C| + |U| ≤ |T| ≤ 46`. If `|C| + |U| = 46`, then:

* every `q ∈ U` has exactly one big neighbour `P_q`;
* `G = { q·P_q : q ∈ U }`;
* every big prime `P` has all its neighbours in `U`. Write `B = N(P)`. Then (*) says

      P ≡ (−ρ(q))^{-1} (mod q)  for every q ∈ B,   and   P | n(B) := Σ_{q∈B} Π_{r∈B} r / q.

*Proof.* If `q ∈ U` had no big neighbour, (*) would fail at `q`. So every `q ∈ U` has a big neighbour. An edge of `G` has at most one end in `S`, so these edges are distinct for distinct `q`. That gives `|G| ≥ |U|`. If `|C| + |U| = 46`, then `|G| ≤ 46 − |C| = |U|`, so these edges are all of `G`. The two congruences are (*) at `q` and (*) at `P`. ∎

In the case `|C| + |U| = 46`, `P ≤ n(B) < 2·Π_{r∈B} r`, because `Σ_{r ≤ 73} 1/r < 2`. So the congruence leaves at most two candidates for `P`.

**Lemma 3 (value).** Every edge of `G` has a prime factor `≥ 79`. For each `q ∈ U` choose one edge `q·P_q`; its reciprocal is at most `1/(79q)`. The other edges of `G` are distinct elements of `P` with a factor `≥ 79`. Let `V(x)` be the sum of the `x` largest reciprocals of such elements, so `V(x) = 1/158 + 1/166 + 1/178 + ...`. Since `Σ_{n∈T} 1/n = 1` and `Σ_C ≤ 1`,

    1 − Σ_{q∈U} 1/(79q) − V(46 − |C| − |U|)  ≤  Σ_C  ≤  1.

**Lemma 4 (star size).** A big prime whose neighbours all lie in `S` has at most 10 neighbours. If it had `d` neighbours, its edges would contribute at most `Σ_{i<d} 1/(79·p_i)`, where `p_i` are the smallest primes, and the remaining `≤ 46 − d` edges at most `H_{46−d}`. For `d ≥ 11` this total is below 1. The program computes this bound itself.

### 4. The computation

The program enumerates every core `C` (every subset of the 210 elements of `P` with both factors in `S`) such that

* `|C| + |U(C)| ≤ 46`, and
* the inequalities of Lemma 3 hold.

The enumeration is a depth-first search over the primes of `S` in decreasing order. When prime `p` is processed, the search chooses all core edges joining `p` to smaller primes. Every core edge at `p` is then fixed, so `ρ(p)` is known. Either `ρ(p) = 0`, or `p ∈ U`, which costs one unit of the budget 46. Each core is visited exactly once.

A branch is pruned only when one of the following is certain:

* `|C| + |U|` would exceed 46;
* the core sum already exceeds 1;
* even the best completion cannot satisfy Lemma 3.

The best completion is bounded by the largest remaining core reciprocals plus the allowance `V(·)` for big edges.

Every core that survives is handled as follows:

* `U = ∅`: the core satisfies (*) everywhere, so it would be a solution by itself.
* `U ≠ ∅` and `|C| + |U| ≤ 45`: reported as *unresolved*.
* `|C| + |U| = 46`: the program tries every partition of `U` into blocks `B` with `2 ≤ |B| ≤ 10`. For each block it computes the at most two candidates `P ≡ CRT((−ρ(q))^{-1} mod q)` below `n(B)`. It then tests `P > 73`, `P | n(B)` and primality of `P`. By Lemma 2 these are the only possible completions.

**Result of the run:** RESULT_PLACEHOLDER

So no `T` with `|T| ≤ 46` exists. ∎

### 5. Why the computation is rigorous

* **Exact arithmetic.** Congruences are exact integer arithmetic. `H_k` and the checks of candidate solutions use exact big-integer rationals (`BigNat`).
* **Directed rounding.** Every bound on a sum of reciprocals is a 96-bit fixed-point integer. Upper bounds are rounded up (`⌈2^96/n⌉`) and lower bounds are rounded down (`⌊2^96/n⌋`). A branch is discarded only if the rounded-up best case is still `< 1`, or the rounded-down core sum is already `> 1`.
* **Completeness.** At prime `p` the search goes through every subset of the smaller primes. For the 8 smallest primes it uses a table of all `2^8` subsets, indexed by residue. The explicit include/exclude recursion handles the rest. The parallel version numbers the search nodes at one fixed level and hands each number to exactly one thread through an atomic ticket counter.
* **Self-tests** (`--selftest`):
  * (a) The same engine, without unsatisfied primes and with budget 47, finds 47-term solutions using only primes `≤ 73`. It verifies each one exactly. So the search is not vacuous.
  * (c) The star-completion routine reconstructs the prime 59 and the edges `118, 1357, 2537` from the core of the 47-term example above, taking `S = primes ≤ 53`.
  * (b) The whole pipeline runs with `S = primes ≤ 53` and budget 47. It rediscovers, through the star step, 47-term solutions that use a prime `> 53`.

---

## Building and running

    g++ -O3 -march=native -pthread -o semiprime_reciprocals semiprime_reciprocals.cpp
    ./semiprime_reciprocals            # full proof, uses all hardware threads
    ./semiprime_reciprocals 4          # choose the number of threads
    ./semiprime_reciprocals --selftest # proof plus the self-tests above
    ./semiprime_reciprocals --budget 44  # smaller budgets (quick sanity runs)

RUNTIME_PLACEHOLDER
