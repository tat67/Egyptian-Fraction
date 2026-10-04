# Problem 2: the fewest terms in a primitive Egyptian fraction of 1

## The problem

The problem is Q2 of `README_PRIMITIVE.md` on branch `claude/nifty-knuth-aj1lt7`, kept exactly as stated there.

A finite set `T` of positive integers is *primitive* if no element divides another. The question asks for the least `|T|` over primitive

    T ⊆ {2, 3, 4, …}   with   Σ_{n∈T} 1/n = 1.

* **No bound on the elements.** The elements may be arbitrarily large.
* **Why 1 is excluded.** `{1}` is the only valid set containing `1`, because 1 divides everything. So the question is about `T ⊆ {2, 3, 4, …}`, as in the original.
* **Known before this work.** `39 ≤ min |T| ≤ 44`.
  * The lower bound is a Lagrangian chain bound, verified in Lean (`card_ge_39`).
  * The upper bound is the 44-term set
    `T44 = {6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62, 65, 69, 74, 77, 82, 85, 86, 87, 91, 93, 94, 95, 111, 115, 119, 123, 133, 141, 143, 145, 287, 8729, 10105, 11687, 14467, 16813}`.
* **Earlier evidence.** CP-SAT found no primitive solution with `|T| ≤ 43` among the integers `≤ 10^5`. This is evidence only: the solver's infeasibility claim is not certified, and larger elements are not covered.

## Result

| `\|T\|` | result | how |
|---|---|---|
| ≤ 38 | impossible | known (Lean, `card_ge_39`) |
| **39** | **impossible** | this work: exhaustive exact search, elements unbounded |
| **40** | **impossible** | this work |
| **41** | **impossible** | this work |
| 42 | **not determined** | see [What remains open](#what-remains-open) |
| 43 | **not determined** | see [What remains open](#what-remains-open) |
| 44 | attained by `T44` | known |

**Consequence.** **42 ≤ min |T| ≤ 44.** Before this work the bound was 39 ≤ min |T| ≤ 44.

The exact minimum is **not** determined. This is the honest outcome of the computation, not a gap in the write-up:

* every step described below is exact;
* every computation whose result is claimed was run to completion and cross-checked;
* a `|T| = 42` run was started and stopped after 20 minutes. It is reported only as a measurement, and no claim is made from it;
* the section [What remains open](#what-remains-open) quantifies why `|T| = 42` and `|T| = 43` are out of reach of this method.

**Method in brief.**
1. A Lagrangian chain bound shows that at most `hmax` elements of `T` exceed a computable `Y`: `hmax = 3` and `Y = 824` for `K = 41`.
2. An exact depth-first search lists every possible *core* `T ∩ [2, Y]`. It tracks exact `p`-adic residues, and the primes left unsatisfied must be covered by the at most `hmax` large elements.
3. For every core, exact Egyptian-fraction algorithms find every set of `h` large elements, of any size, that completes it. Two independent implementations are used.
4. Pruning rules P5 and P6, and the test `δ = 1/b` for one large element, cut the work for `K = 41` from more than an hour (design C was stopped unfinished after 42 minutes) to 2 minutes. They provably lose nothing.

---

## 1. Reductions (all exact)

Fix the size `K = |T|` and an integer threshold `A`. Write `λ = 1/A`.

### Lemma 1 (no prime powers)

**Statement.** `T` contains no prime power `p^j` (`j ≥ 1`).

**Proof.**
* Suppose `p^j ∈ T`.
* Every other `n ∈ T` has `v_p(n) < j`, since otherwise `p^j | n`.
* So `1/p^j` is the only term with `p`-adic valuation `−j`.
* Hence `v_p(Σ) = −j < 0`, and the sum is not an integer.

All elements are therefore non-prime-powers `≥ 6`.

### Lemma 2 (Lagrangian bound)

Let `P_A` be the non-prime-powers in `[6, A)`, and let `W ≥ max_Q Σ_{n∈Q} (1/n − λ)` over antichains `Q ⊆ P_A`.

**Statement.** Every solution satisfies

    Σ_{n∈T, n≥A} (λ − 1/n)  ≤  σ := Kλ + W − 1.

**Proof.**

    1 = Σ_T 1/n = Kλ + Σ_{T∩P_A} (1/n − λ) − Σ_{T, n≥A} (λ − 1/n) ≤ Kλ + W − Σ_{T, n≥A} (λ − 1/n).

**How `W` is computed.** `W` is an upper bound from a chain cover, built as a weighted Dilworth decomposition by maximum flow. The program checks exactly that the chains cover every weight, `Σ_{c∋n} y_c ≥ ⌈2^96/n⌉ − ⌊2^96/A⌋`. An antichain meets each chain at most once, so `2^96·W ≤ Σ_c y_c`.

### Lemma 3 (few large elements)

**Statement.** If `h` elements of `T` exceed `Y`, then `h(λ − 1/(Y+1)) ≤ σ`.

**Proof.** Each such element costs at least `λ − 1/(Y+1)` in Lemma 2.

**Choice of `Y`.** The program takes the smallest `Y` with `hmax(Y) = ⌊σ/λ⌋`:

| K | A | σ ≤ | Y | hmax | non-prime-powers in [6, Y] |
|---|---|---|---|---|---|
| 39 | 133 | 0.008963 | 329 | 1 | 245 |
| 40 | 134 | 0.016426 | 503 | 2 | 387 |
| 41 | 141 | 0.023518 | 824 | 3 | 657 |
| 42 | 142 | 0.030561 | 1075 | 4 | 868 |
| 43 | 145 | 0.037554 | 1568 | 5 | 1292 |

**Core and huge part.** Write `T = C ∪ H` with

* the **core** `C = T ∩ [2, Y]`;
* the **huge part** `H = T ∩ (Y, ∞)`, with `|H| = h ≤ hmax`.

Since every element of `H` is at least `Y + 1`:

    0 ≤ δ := 1 − Σ_C 1/n = Σ_H 1/x ≤ h/(Y+1),    with δ = 0 ⇔ h = 0.        (window)

Define the core's Lagrangian *loss* as `L(C) = W − Σ_{n∈C} (1/n − λ)`. Since `Σ_C 1/n = 1 − δ` and `|C| = K − h`, we get `L(C) = σ − hλ + δ`. So `L(C)` lies in the band `(σ − hλ, σ − hλ + h/(Y+1)]`. A large `h` leaves the core little freedom, and a small `h` leaves it much.

### Lemma 4 (unsatisfied primes)

**Definitions.**
* A prime `p` is *unsatisfied* if `v_p(Σ_C) = −e_p < 0`. Let `U` be the set of unsatisfied primes.
* Two primes `p, q ∈ U` *conflict* if some core element divides `p^{e_p} q^{e_q}`.

**Statement.**
1. The denominator of `δ` is exactly `b = Π_{p∈U} p^{e_p}`.
2. Every `p ∈ U` divides some element of `H` to the power `e_p`.
3. Two conflicting primes cannot share an element of `H`, since that element would be a multiple of a core element.
4. Hence `h ≥ χ(U)`, the chromatic number of the conflict graph.

**Proof.**
* `δ = 1 − Σ_C`, so `v_p(δ) = v_p(Σ_C)` for every `p` with `v_p(Σ_C) < 0`, and `v_p(δ) ≥ 0` otherwise. This gives (1).
* `δ = Σ_H 1/x`, so `v_p(δ) = −e_p` needs some `x ∈ H` with `p^{e_p} | x`. This gives (2).
* (3) and (4) follow directly.

The program also checks the identity `b = Π_{p∈U} p^{e_p}` for every core, as a consistency test of the residue bookkeeping.

### Lemma 5 (clique rule)

**Setting.** Let `C'` be a partial core, and let `D` be a set of primes that pairwise conflict through elements already in `C'` (`pq ∈ C'`), each with nonzero current residue.

**Statement.** `|D| ≤ K − |C'|`.

**Proof.**
* A later core element contains at most one prime of `D`; otherwise it is a multiple of some `pq ∈ C'`.
* After `x` more core elements, at least `|D| − x` primes of `D` are still unsatisfied.
* They pairwise need different elements of `H`, so `K − |C'| − x = h ≥ |D| − x`.

## 2. The algorithm (`q2exact.cpp` + completion)

### Step 1: all cores

The search is a depth-first search over the non-prime-powers `n ≤ Y` in increasing order. Each subset is generated exactly once, by its last element.

**Exact state carried at every node:**
* the count;
* the reciprocal sum, as a lower and an upper `2^96` fixed-point value with directed rounding;
* for every prime `p ≤ Y/2`, the residue `Σ_{n∈C', p|n} p^{E−v_p(n)}·(n/p^{v_p(n)})^{−1} mod p^E`, where `p^E ≤ Y < p^{E+1}`. This residue is `0` iff `v_p(Σ_{C'}) ≥ 0`.

**A node is discarded when any of these holds:**

* **(P1)** the lower-rounded sum exceeds 1;
* **(P2)** no admissible final size `j` with `K − hmax ≤ j ≤ K − χ(U_final)` can still reach the window. The test uses the sum of the `j − |C'|` largest remaining reciprocals that are not comparable to a chosen element;
* **(P3)** the primes whose multiples are all decided and whose residue is nonzero need more than `hmax` colours (Lemma 4);
* **(P4)** the clique rule (Lemma 5), with `D` a maximum clique among the primes `≤ 31`. It is applied when `K − |C'| ≤ 8`.

* **(P5) loop break.** At a node, the candidates `k` for the next element are scanned in increasing order of `n`, i.e. decreasing reciprocal.
  * For candidate `k`, the relaxed bound is: `ub(k, t)` = upper-rounded sum of `C' + {U[k]}` plus the next `t` candidates that are not blocked by the current set.
  * Candidate `k` is *reachable* if `ub(k, t) ≥ 1 − h/(Y+1)` for some `t ≥ 0`, where the final size `j = |C'| + 1 + t` satisfies `h = K − j ≤ hmax`.
  * If `k` is not reachable, the loop stops: neither `k` nor any later candidate is tried.
  * *Why this loses nothing.* The bound ignores the multiples that `U[k]` itself would block, so it is at least the true bound of the child. It is also non-increasing in `k`: `1/U[k]` decreases, and the `t` largest admissible reciprocals after `k` decrease term by term. So no later candidate can reach the window either.
* **(P6) clique test in the parent.** Let `D` be a clique (from P4) of the parent, with `|D| ≥ K − |C'| − 1`. For candidate `k`:
  * let `S` = `D` minus the primes of `U[k]`;
  * extend `S` greedily by every prime `t ≤ 31` of `U[k]` whose residue becomes nonzero and which is adjacent (`tq ∈ C' + {U[k]}`) to all of `S`.

  Then `S` is a clique of the child, because residues change only at the primes of `U[k]` and edges are never removed. So `|S| > K − |C'| − 1` refutes both the child and the core `C' + {U[k]}`, since `χ(U) ≥ |S| > h`. The candidate is then skipped without creating the child.

Each of (P1)–(P6) is a consequence of Lemmas 1–5 for every completion of the node. So the subtree of a discarded node contains no core of a solution. P5 and P6 were added last. On `K = 39` and `K = 40` the dumps with and without them are identical (sorted-dump hashes `f7f5402d…` and `de466a30…`), while the node counts fall by factors of 56 and 86.

**What counts as a core.** A subset of size `j ∈ [K − hmax, K]` is a *core* if all of the following hold, with `h = K − j`:
* the exact value of `δ` lies in the window;
* `U = ∅ ⇔ h = 0`;
* `χ(U) ≤ h`.

**What happens to each core.**
* **`h = 1`.** Completed immediately. A completion needs `δ = 1/b` exactly, with `b = Π_{p∈U} p^{e_p}` known from the residues.
  * Since `sUp ≥ 2^96(1 − δ)`, the core is refuted without GMP whenever `2^96 − sUp > ⌊2^96/b⌋ + 1`.
  * The survivors are checked with GMP.
* **`h = 2`.** Completed inline: with `compl.h`, or with `ind2.h` when `Q2_H2=ind` is set. Alternatively the core is dumped.
* **`h ≥ 3`.** Written to a dump file.

**Parallelism.** The subtrees at depth `splitDepth` are numbered in DFS order and handed out as tickets. A ticket range `[lo, hi)` can be given on the command line. The progress log reports `doneBelow`, the index below which every subtree is finished, so an interrupted run can be resumed exactly. The split into ticket ranges was checked on `K = 40`: two runs over `[0, 200000)` and `[200000, ∞)` gave a byte-identical sorted dump to one full run.

### Step 2: every completion of every core

For a core with `δ = a/b`, all sets `H` are wanted such that:
* `|H| = h`, and every element is `> Y`;
* `Σ_H 1/x = a/b`;
* no element of `H` is a multiple of a core element;
* `H` is primitive.

**`h = 1`.** `x = b/a` must be an integer. Since `gcd(a, b) = 1`, this means `a = 1` and `x = b`.

**`h = 2`.** Every solution has `b/a < x ≤ 2b/a` and `y = bx/(ax − b)`. Equivalently, `d = ax − b` is a divisor of `b²` with `d < b` and `d ≡ −b (mod a)`. Two independent implementations are used:

* **`compl.h` (method M).**
  * Writes `x = g x'`, `y = g y'` with `gcd(x', y') = 1`, `x'y' | b`, `a | x' + y'`, and `g = (b/(x'y'))(x'+y')/a`.
  * Places the prime powers of `b` by meet in the middle on `x'/y' mod a`.
  * Prunes placements that would make `x` or `y` a multiple of a core element.
* **`ind2.h` (method I).** Chooses the cheaper of two scans:
  * **AP:** every integer `x ∈ (max(b/a, Y), 2b/a]`, testing `(ax − b) | bx` in 128-bit arithmetic, or GMP when needed;
  * **DIV:** every divisor `d` of `b²` in the class `−b mod a`, by meet in the middle on `d mod a`.

**`h = 3`.**
* The smallest element satisfies `b/a < x₁ ≤ 3b/a`. Every such `x₁ > Y` is tried, except when:
  * a core element divides `x₁`;
  * `x₁` is a prime power (Lemma 1);
  * the primes `U'` of the new denominator cannot be 2-coloured with respect to `C ∪ {x₁}` (Lemma 4 applied to the core `C ∪ {x₁}`).
* The remaining pair is solved by the `h = 2` method. Both `compl.h` and `complete_ind` (with `ind2.h`) implement this step.

**`h ≥ 4`.** The smallest element is tried in `(b/a, h·b/a]`, and the rest is completed recursively.
* At each level, a candidate is dropped if:
  * an element of `C` or an already chosen element divides it;
  * it is a prime power;
  * the remaining primes cannot be coloured with the number of elements still to choose.
* Both `compl.h` and `complete_ind` implement this. It is not needed for `K ≤ 41`.

Every reported candidate is re-verified with GMP: the exact sum is 1, and the whole set is primitive. A verified solution contains no prime power (Lemma 1), so no primality test is ever needed.

### Completeness

Let `T` be any solution with `|T| = K`.

1. By Lemmas 1 and 3, `C = T ∩ [2, Y]` is a primitive set of non-prime-powers with `|C| = K − h` and `h ≤ hmax`.
2. By Lemmas 2–5 and the arguments given for P5 and P6, no ancestor of `C` in the search tree is discarded, and `C` passes the core tests. So `C` is output with the correct `h`, and its `δ` equals `Σ_H 1/x`.
3. The completion step enumerates all `H` with the stated properties, and `T ∩ (Y, ∞)` is one of them.

Therefore "0 verified solutions" for size `K` proves that no primitive `T` with `|T| = K` and `Σ 1/n = 1` exists, whatever the size of its elements.

### Arithmetic

No floating-point type is used in any decision:

* bounds use `2^96` fixed point with directed rounding (upper bounds rounded up, lower bounds rounded down);
* residues are exact integers modulo `p^E`;
* `δ`, its numerator and denominator, and all completion arithmetic are exact (`unsigned __int128` only where the operands provably fit, GMP otherwise).

GMP is used through the shared library `libgmp.so.10` with a hand-written binding, `gmpz.h`, because no development headers are installed.

## 3. The big-prime decomposition of `semiprime48.cpp`, adapted

`semiprime48.cpp` splits the primes into small primes (`≤ 73`) and big primes (`≥ 79`) and decides, prime by prime from the top, the *star* of each prime.

**What carries over to Problem 2.**

* **Boundary.** Take `B = ⌊√Y⌋`. Then every `n ≤ Y` has at most one prime factor `P > B`, with exponent 1.
* **Stars.** The core elements divisible by `P` are `P·m` with `2 ≤ m ≤ Y/P < P`, where `m` is `B`-smooth. This is the *star* `M(P)`. For `P > B`, all multiples of `P` that are `≤ Y` have largest prime factor `P`.
* **Final residue.** In an order that decides stars by decreasing `P`, the `P`-adic residue is final as soon as the star is chosen. It is `Σ_{m∈M(P)} 1/m mod P`.
* **No big–big elements in the core.** Two big primes never share a core element, because `P·P' > Y`. So elements with several big primes occur only in `H`, and there are at most `hmax` of them.
* **Admissible stars.** When `P` divides no element of `H`, the exact condition is `Σ_{m∈M(P)} 1/m ≡ 0 (mod P)`, and only admissible stars need to be enumerated.

**What does not carry over.**

* In `semiprime48`, every unsatisfied prime costs a whole element, so `|C| + |U| ≤ K`. That is what made the congruences bite there.
* Here an unsatisfied big prime costs nothing extra. Big primes never conflict with each other in the core, so a single huge element can absorb any number of them.
* Typical cores have 10–16 unsatisfied primes, e.g. all of `29, 31, 37, 41, 43, 47, 53, 59, 61, 67`, whose cheapest stars `{2, 3}` or `{2}` have nonzero residue.
* So the admissible-star restriction applies only to the satisfied primes. The unsatisfied option is constrained only through `h ≥ χ(U)`, plus the completion.
* Meanwhile the elements just above `A` (`142 = 2·71`, `145 = 5·29`, `146 = 2·73`, …) cost almost nothing in the Lagrangian sense. They can be combined freely.

**Measured.** The number of star configurations of the big primes whose loss alone fits in the `h = 1` budget, ignoring every other constraint (`count_stars.py`):

| K | B | budget | star configurations |
|---|---|---|---|
| 41 | 28 | 0.017638 | 5.5·10^10 |
| 42 | 32 | 0.024448 | 1.1·10^13 |

**Four designs implemented and compared.**

* **Design A, `q2k.cpp`.**
  * Groups the core universe by largest prime factor and decides the groups for primes in decreasing order. Each group is a star, decided as a block, and each prime's residue becomes final there.
  * Prunes with the chain-cover Lagrangian bound plus `χ(U)·(λ − 1/(Y+1))` for the unsatisfied primes, the exact analogue of `semiprime48`'s loss bound with `g(q)` replaced by the cost of a huge element.
* **Design B, `q2b.cpp`.** Increasing-order DFS with value window and residue pruning.
* **Design C, `q2exact.cpp` (first version).** Design B plus the clique rule (Lemma 5), tighter size bounds `K − hmax ≤ j ≤ K − χ(U)`, and parallel tickets.
* **Design D, `q2exact.cpp` (final).** Design C plus:
  * rules P5 (loop break) and P6 (clique test in the parent);
  * the `h = 1` test `δ = 1/b`;
  * bit-set bookkeeping of the unsatisfied primes.

| K | design | nodes | wall | cores (h=1, h=2) |
|---|---|---|---|---|
| 39 | A `q2k` | 6,015,831 | 0.31 s | 113, – |
| 39 | B `q2b` | 2,060,283 | 0.78 s | 113, – |
| 39 | C `q2exact` (1 thread) | 628,074 | 0.2 s | 113, – |
| 40 | A `q2k` | 17,675,338,036 | 744 s | 65,272, 2,643 |
| 40 | B `q2b` | 911,176,651 | 349 s | 65,272, 2,643 |
| 40 | C `q2exact` (4 threads) | 160,900,759 | 12.2 s | 65,272, 2,643 |
| 39 | D `q2exact` (4 threads) | 11,985 | < 0.1 s | 113, – |
| 40 | D `q2exact` (4 threads) | 1,867,018 | 0.6 s | 65,272, 2,643 |
| 41 | C `q2exact` (4 threads) | not finished: stopped after 42 min at about 41% of its subtrees | – | – |
| 41 | D `q2exact` (4 threads) | 278,925,916 | 108.6 s | 22,083,508, 1,674,415 (and 6,916 with h=3) |

In design D, the `h = 1` cores are counted by `h1RefutedByDeltaTest`; none survives the test.

The prime-by-prime order needs 110 times more nodes than design C at `K = 40`, and 9,500 times more than design D. The increasing order keeps the exact count-limited value bound (P2) at every level. The prime-by-prime order can only use the Lagrangian, count-relaxed chain bound, because the small elements, which carry most of the value, are decided last.

**Where the big-prime structure is still used in designs C and D.**

* The exact per-prime residues: big primes are decided as soon as the DFS passes their last multiple.
* The conflict graph and `χ(U)`.
* The clique rule.
* The completion. For `h = 1`, `H = {b}` contains *all* unsatisfied primes, so every congruence is checked at once by `a = 1`. For `h ≥ 2`, every candidate is filtered by the colourability of `U'`.

## 4. Runs and certificates

**The previous method.** CP-SAT on non-prime-powers `≤ 10^5` with at most 43 terms took 14 min 33 s of wall time and reported INFEASIBLE. That is uncertified and covers bounded elements only; it cannot settle any size here.

The exact search below covers all element sizes.

All runs use 4 threads on a 4-core container. The `nodes` column counts every depth-first-search node, including the shared top of the tree, which each thread traverses.

| K | Y | nodes | cores h=1 | cores h=2 | cores h=3 | completion | solutions | wall |
|---|---|---|---|---|---|---|---|---|
| 39 | 329 | 11,985 | 113 | – | – | `δ = 1/b` test (all 113 refuted) | 0 | < 0.1 s |
| 40 | 503 | 1,867,018 | 65,272 | 2,643 | – | `δ = 1/b` test; `h = 2` by `complete_ind` and `complete_dump` | 0 | 0.6 s |
| 41 | 824 | 278,925,916 | 22,083,508 | 1,674,415 | 6,916 | `δ = 1/b` test; `h = 2, 3` by `complete_ind` (101 s) and `complete_dump` (3 processes, 2,341 s) | 0 | 108.6 s |

**Notes on the `K = 41` row.**
* The first `K = 41` run with P5 and P6 (`runs/K41_q2exact_P5P6_first_run.out`) took 944,398,439 nodes and 236.8 s. It did not have the `δ = 1/b` test and completed all 22,083,508 `h = 1` cores exactly with GMP, with 0 solutions.
* Its dump is identical to the final run's (sorted SHA-256 `f9158e45…`, `runs/dump_fingerprints.txt`).
* The wall times were measured while other processes shared the 4 cores.

Logs are in [`runs/`](runs/). The `K = 41` dump (1,681,331 lines, 294 MB) is not committed. It is regenerated by the commands below in about 2 minutes, and its line counts and the SHA-256 of the sorted dump are in `runs/dump_fingerprints.txt`.

## 5. Validation

1. **Core search against brute force.**
   * `brute_core.cpp` is a plain value-bounded DFS with no residue, colouring or clique pruning.
   * `cmp_cores.py` applies the core tests to its output with Python `Fraction`s and `sympy` factorisations.
   * For `K = 39` (`Y = 329`), the brute force lists 6,768 window sets, of which 113 pass the core tests. These are identical to the 113 cores of `q2exact` (`equal: True`).
2. **Four search designs.**
   * Designs A, B, C and D give the same core counts at `K = 39` and `K = 40`.
   * The full `K = 40` dumps of `q2b` and `q2exact` are identical: 67,915 cores, same sorted hash.
   * With and without P5/P6, the dumps for `K = 39, 40` are identical (`runs/P5P6_equivalence.txt`).
   * For `K = 41`, the dumps of two binaries (P5+P6, and P5+P6+`δ = 1/b` test with bit sets) are identical.
   * Every one of the 1,501,206 cores written by the interrupted run of the older binary without P5/P6 is in the final dump (`runs/K41_old_run_subset_check.txt`).
3. **Two independent completion implementations.**
   * `complete_dump` (`compl.h`, method M) and `complete_ind` (`ind2.h`, method I) share only the GMP binding.
   * Both were run on every `h = 2` and `h = 3` core of `K = 40` and `K = 41`, and both report 0 solutions.
   * `check_completion.py` is a third, Python implementation (divisors of `b²`).
     * It checked all 67,915 `K = 40` cores.
     * For `K = 41` it checked K41_PY.
4. **Planted solutions.**
   * Remove the last `h` elements of `T44` and complete the remaining core.
   * `compl.h` re-finds `T44` for `h = 1, 2, 3, 4` (`h = 4` takes 70 s).
   * `complete_ind` re-finds it for `h = 2, 3, 4` (`h = 4` takes 19 s), see `runs/planted_T44_complete_ind.out`.
5. **Random tests of the completion solvers.**
   * `ind2.h`, against brute force over all `x`:
     * 1,305 random fractions `1/x + 1/y` with 1,434 solutions;
     * 120 random fractions `1/x₁ + 1/x₂ + 1/x₃` with 3,519 solutions, colourability prefilter active;
     * K41_IND4.
   * Each test was run in pure AP mode and in pure DIV mode, with no mismatch.
   * `compl.h`'s two-term solver was compared against brute force on 2,000 random fractions, with no mismatch.
6. **Consistency checks inside every run.**
   * The denominator of `δ` equals `Π_{p∈U} p^{e_p}` for every core; any mismatch aborts.
   * The remainder in every dump line is recomputed from scratch by both completion programs.

## What remains open

The sizes `|T| = 42` and `|T| = 43` are **not decided**. Precisely:

* It is not known whether there is a primitive `T ⊆ {2, 3, …}` with `Σ 1/n = 1` and `|T| = 42` or `|T| = 43`.
* No such `T` has all of its elements `≤ 10^5` (CP-SAT; uncertified).
* No such `T` was found here.

**Why `K = 42` was not completed (measured).** A run of the final program on `K = 42` (`A = 142`, `Y = 1075`, `hmax = 4`), with the `h = 2` cores completed inline by `ind2.h`, was stopped after 20 minutes (`runs/K42_partial_stopped.txt`). In that time:

* not one of its depth-34 subtrees had finished. The first subtrees are the densest ones, and in `K = 41` they also took most of the time;
* about 2.7·10^7 `h = 2` cores were completed inline, with 0 solutions. This count is estimated from the 424,872 cores of the 1/64 hash sample;
* 808,968 `h = 3` cores and 2,737 `h = 4` cores were dumped.

The obstacle is the `h = 4` completion:
* For six of these cores, `complete_ind` needed 2 s, 6 s, 93 s and, for three of them, more than 120 s (stopped).
* Their `b/a` is about 1,000–2,200. The smallest-element search costs roughly `(b/a)^2` exact candidate tests per core.
* The 2,737 `h = 4` cores came from the first 20 minutes, during which no subtree finished. The full run will produce far more. At seconds to minutes per core, the `h = 4` completions alone would take days to weeks on this machine; this is an estimate, not a measurement.

**`K = 43` was not attempted.**
* Its `h = 1` loss budget is 0.0313, against 0.0244 for `K = 42` and 0.0176 for `K = 41`.
* It has up to `h = 5` huge elements.
* A 5-term completion of the single planted core of `T44` did not finish in 37 minutes.

**What `semiprime48`'s decomposition would need here.** Section 3 explains why the big-prime decomposition does not shrink this search:
* unsatisfied big primes are free;
* they are the typical case.

A decisive improvement would have to couple the completion with the core search, e.g. use the congruences that the huge elements must satisfy before the core is complete. For `h = 1` this is possible: `x = b` contains every unsatisfied prime, which the `δ = 1/b` test exploits. For `h ≥ 2`, a free common factor `g = gcd(x, y)` absorbs those congruences.

**A heuristic remark, not a proof.** Solutions, if any, are most likely among cores with many huge elements (`h = 4, 5`), as in `T44`. Those cores have the smallest budgets but the most expensive completions.

## Reproducing

```
cd primitive_q2
make                                   # needs g++ and libgmp.so.10 only
./q2exact 39 133 4 28 -                # K = 39: 0 solutions
./q2exact 40 134 4 30 c40.txt defer2   # K = 40: h=1 completed inline, h=2 cores dumped
./complete_ind c40.txt 503 && ./complete_dump c40.txt 503
./q2exact 41 141 4 34 c41.txt defer2   # K = 41 (about 2 minutes on 4 cores)
./run_completion.sh c41.txt 824 4      # compl.h on all h = 2, 3 cores, 4 processes (about 30-40 minutes)
./complete_ind c41.txt 824             # independent method (about 100 s)
# K = 42 (not completed; for measurements only):
# Q2_H2=ind Q2_H2SAMPLE=c42_h2sample.txt ./q2exact 42 142 4 34 c42_h3.txt.gz defer3
# validation
./brute_core 39 329 1 > b39.txt && ./q2exact 39 133 4 28 d39.txt all && python3 cmp_cores.py 39 329 1 b39.txt d39.txt
./test_compl 1 4                       # planted T44 completions (h = 4 takes about 70 s)
python3 test_ind2.py; python3 test_ind3.py; python3 test_ind4.py   # solver tests vs brute force
python3 count_stars.py 41 141 824 0.023518   # star-configuration count (section 3)
```

The arguments of `q2exact` are `K A [threads] [splitDepth] [dumpfile|-] [nocomplete|deferH|all] [ticketLo] [ticketHi]`.

## Time and tokens

* Task start: 2026-10-04 13:30:27 JST (UTC+09:00).
* Task end: END_TIME JST.
* Elapsed wall-clock time: ELAPSED.
* Token usage: **unavailable**. No authoritative usage data is exposed to this session, so no figure is given.
