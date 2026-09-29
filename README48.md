# All 48-term representations of 1 by squarefree semiprimes

**Problem.** Let `P = { p·q : p < q primes } = { 6, 10, 14, 15, 21, 22, 26, 33, … }`. Find every `T ⊆ P` with `|T| = 48` and `Σ_{n∈T} 1/n = 1`. Verify each one with exact arithmetic, and prove that the list is complete. The program must use no floating point, and it must be much faster than the method used for 47 terms.

**Answer. There are exactly 620 such subsets.**

| structure of the primes `> 73` in `T` | number of sets |
|---|---:|
| none: all primes `≤ 73` | 397 |
| one prime `P > 73`, a *star* (all neighbours of `P` are `≤ 73`) | 187 |
| two primes `> 73`, two separate stars | 18 |
| two primes `P1, P2 > 73` joined by the element `P1·P2` (a two-prime component) | 18 |
| **total** | **620** |

* The largest prime that occurs is `1,210,883`, in `T ∋ 11·1210883, 29·1210883, 37·1210883, 12109·1210883, 17·12109`. The largest element is `12109·1210883 = 14,662,582,247`.
* Twelve elements lie in every solution: `6, 10, 14, 15, 21, 22, 26, 33, 34, 38, 39, 46`.

Every one of the 620 sets was verified with exact rational arithmetic twice. The C++ program uses big-integer fractions, and `verify48.py` uses Python `fractions` with its own factorisation and primality code. The full list, with the primes above 73 and their neighbours, is in [`solutions48.txt`](solutions48.txt).

`semiprime48.cpp` finds the list and proves it complete. It uses only integer and rational arithmetic and contains no `float`, `double` or `long double`.

**Running time (4 threads, one cloud VM).**

| task | method of `semiprime47.cpp` | `semiprime48.cpp` |
|---|---|---|
| 46 terms (no solution) | 1.4·10^11 nodes, ~20 min | 2.6·10^7 nodes, 2 s |
| 47 terms (23 solutions) | 1.8·10^12 nodes, 5 h 48 min | 6.0·10^8 nodes, 65 s |
| 48 terms (620 solutions) | ≈ 2.3·10^13 nodes, ≈ 3 days (extrapolated: ×13 nodes per extra term, 8.6·10^7 nodes/s) | 1.3·10^10 nodes, 29 min 30 s |

---

## Proof of completeness

The framework is that of [`README.md`](README.md) and [`README47.md`](README47.md), with budget 48. Two things are new.

* **Step 1** has a much stronger pruning bound. It outputs exactly the same cores as before, only far faster (section 3).
* **Step 2** can now also solve completions with two big–big edges (section 4). At budget 47 no such shape survived; at budget 48, 73 cores need it.

### 1. Only the local conditions matter

`H_48`, the reciprocal sum of the 48 smallest elements of `P`, is about `1.0704 < 2`; the program checks this exactly. So for `|T| ≤ 48`:

    Σ 1/n = 1   ⇔   Σ 1/n ∈ ℤ   ⇔   for every prime p:  Σ_{q∈N(p)} q^{-1} ≡ 0 (mod p),     (*)

where `T` is read as a graph on primes (`pq ∈ T` is an edge) and `N(p)` is the set of neighbours of `p`.

### 2. Core and big part

* `S` is the set of the 21 primes `≤ 73`; primes `≥ 79` are *big*.
* The core `C` consists of the elements of `T` with both factors in `S`, and the big part `G` is everything else.
* `ρ(q)` is the core residue at `q`, and `U = { q ∈ S : ρ(q) ≠ 0 }`.

Each `q ∈ U` needs its own edge to a big prime, so `|G| ≥ |U|` and `|C| + |U| ≤ 48`. Every element of `G` has a factor `≥ 79`, which gives the value bound

    1 − Σ_{q∈U'} 1/(79q) − V(48 − |C| − |U'|)  ≤  Σ_C  ≤  1        for every U' ⊆ U,

where `V(x)` is the sum of the `x` largest reciprocals of elements of `P` with a factor `≥ 79`.

### 3. Step 1: all cores, with a new pruning bound

**What is enumerated.** Step 1 enumerates exactly what `semiprime47.cpp` enumerates: every core `C` with `|C| + |U(C)| ≤ 48` that satisfies the value bound for every upper segment `U' = U ∩ (p, ∞)`.

* The depth-first search runs over the primes of `S` in decreasing order.
* At prime `p` it chooses `p`'s neighbours among the smaller primes. After that, `ρ(p)` is final, and either `ρ(p) = 0` or `p ∈ U`.

The old pruning tests are kept:

* (P1) the budget `|C| + |U| ≤ 48`;
* (P2) the lower-rounded core sum is at most 1;
* (P3) the value bound, with the rest of the search bounded by the largest remaining reciprocals.

**Why the old search was slow.** Profiling the old search showed the following. With the unsatisfied primes switched off, the same search at budget 45 visits 2.9·10^7 nodes instead of 1.07·10^10, so **99.7% of the nodes come from branches in which some prime is put into `U`**. At such a prime every neighbour set is allowed. The value bound (P3) ignores the congruences (*) that the still undecided primes must satisfy later. These congruences force a loss of value that (P3) cannot see, so the branches died only 5–10 levels further down.

| budget | old search: nodes | old search, `U = ∅` only | new search: nodes |
|---:|---:|---:|---:|
| 43 | 62,440,966 | 1,136,399 | 1,819 |
| 44 | 819,315,334 | 5,807,483 | 57,971 |
| 45 | 10,744,778,486 | 28,873,535 | 1,166,640 |
| 46 | 139,830,520,211 | 141,049,988 | 26,112,391 |
| 47 | 1,795,181,713,099 | 680,505,731 | 598,305,041 |
| 48 | ≈ 2.3·10^13 (extrapolated: ×13 per budget) | – | 13,344,629,391 |

All counts are for 4 threads. The old counts at budgets 43–45 were measured with a profiling copy of `semiprime47.cpp`; those at 46 and 47 are the recorded runs. The column "`U = ∅` only" is the same old search with unsatisfied primes switched off, which is not a valid proof search; it only shows where the old nodes went. The new search, with unsatisfied primes allowed, visits fewer nodes than the old search restricted to `U = ∅`.

**The loss bound (P4).** Fix a number `θ ≥ 0`. The program uses `θ = ⌊2^96/145⌋·2^−96`, just below `1/145`; every `θ ≥ 0` is valid.

The quantity tested at the end of Step 1 is

    Val = Σ_{n∈C} up(1/n) + Σ_{q∈U} up(1/(79q)) + VB(x),     x = 48 − |C| − |U|,

and the core is kept only if `Val ≥ 1`. Here `up` denotes rounding up in 96-bit fixed point, and `VB(x)` is the rounded-up `V(x)`. Put

* `w(n) = up(1/n) − θ` (the *weight* of an edge),
* `g(q) = up(1/(79q)) − θ`,
* `V_θ = max_{0≤x≤48} (VB(x) − x·θ)`.

Since `48 = |C| + |U| + x`,

    Val = 48·θ + Σ_{n∈C} w(n) + Σ_{q∈U} g(q) + (VB(x) − x·θ)  ≤  48·θ + V_θ + Σ_{n∈C} w(n) + Σ_{q∈U} g(q).

At a node of the search, part of `C` and of `U` is already decided and contributes a known amount. The undecided remainder, `F = Σ_{undecided edges of C} w + Σ_{undecided primes of U} g`, is bounded prime by prime.

* **Shares.** For an undecided edge `e = {a, b}` with `a < b`, fix a fraction `σ_a ∈ [0, 1]`.
  * The larger endpoint gets the share `s_b(e) = ⌈σ_a·w(e)⌉` and the smaller endpoint gets `s_a(e) = ⌈(1 − σ_a)·w(e)⌉`, so `s_a + s_b ≥ w(e)`.
  * The program uses `σ_a = 12/12, 11/12, 11/12, 10/12, 10/12, 9/12` for `a = 2, 3, 5, 7, 11, 13`, and `8/12` for larger `a`. These values were tuned on budgets 45–46, and every choice is valid.
* **Local bound.** Let `q` be a prime that still has undecided edges, and let `res(q)` be the residue at `q` of its decided edges. In the final core, either `q ∈ U`, or the set `X` of its undecided neighbours satisfies `res(q) + Σ_{x∈X} x^{-1} ≡ 0 (mod q)`. So the shares at `q`, plus `g(q)` if `q ∈ U`, total at most

      loc(q) = max( g(q) + Σ_x max(s_q({q,x}), 0) ,  max_{X : res(q) + Σ_X x^{-1} ≡ 0 (mod q)} Σ_{x∈X} s_q({q,x}) ).

  * The second maximum is a knapsack over the residues mod `q`.
  * It depends only on the search level and on `res(q)`, so every value of `loc` is a precomputed table entry (`LOC[j][k][r]` and `TOPT[j][i][t]` in the program, about 20,000 entries).
* **Sum.** Every undecided edge is counted through its two shares, so `F ≤ Σ_q loc(q)`.

**(P4)** Prune the node if

    (decided value) + (48 − decided count)·θ + V_θ + Σ_q loc(q)  <  1.

Here "decided value" is the rounded-up sum over the decided core edges and `U`-edges, and "decided count" is the number of decided core edges plus decided `U`-memberships. `Σ_q loc(q)` changes in O(1) when the search adds or rejects an edge. At the table-driven step for the 8 smallest primes, a 256-entry array gives it for every subset at once. All of this is integer arithmetic: `θ` and the fixed-point values are integers, the shares are rounded up, and the tables are exact maxima.

**Why (P4) changes only the speed.** For every core in the subtree of a node, the left-hand side of (P4) is at least `Val`. So (P4) never removes a core that passes the final test `Val ≥ 1`. Tests (P1)–(P3) are unchanged, so Step 1 of `semiprime48.cpp` outputs exactly the same cores as Step 1 of `semiprime47.cpp`. This was also checked directly ([`validation48/`](validation48/README.md)):

* the recorded budget-47 dump (`cores47.txt.gz`, 22,382 cores) and budget-46 dump (178 cores) are reproduced line for line, while the search visits `6.0·10^8` instead of `1.8·10^12` nodes (budget 47);
* at budgets 40–45 on the real instance, both programs keep no core;
* on 15 reduced instances (`S` = primes `≤ 13, 17, 19, 23`, up to 21 million cores), the old and new programs give identical dumps. For `S` = primes `≤ 13, 17, 19`, the new dumps also pass the brute-force check that enumerates all cores. (On these small instances (P4) prunes nothing, so they test the new bookkeeping rather than the pruning.)

### 4. Step 2: every completion of every core

This is Step 2 of `README47.md`, with budget 48. **Shapes** `(d_q)_{q∈S}, b` are filtered by the excess, parity and value tests, where `b` is the number of big–big edges. The surviving shapes are resolved as follows.

* **`b = 0`:** stars `P | n(A)`, and every exact cover is enumerated.
* **`b = 1`:** one two-prime component, solved through the divisor equation

      (tP1 − a1·b2)(tP2 − a2·b1) = b1·b2·(t + a1·a2),    t = Z_K·b1·b2.

  Here `b_i = Π A_i`, `a_i = n(A_i) = Σ_{q∈A_i} b_i/q`, and `Z_K` is the value of the component.
* **`b = 2` (new).** Besides stars, the big part contains either a path `P0 − P1 − P2` or two components `P0 − P1` and `P2 − P3`. The attachment sets `A_i` must be nonempty, except that the middle prime `P1` of a path may have none. The big part of the core must have value `Z_K = 1 − Σ_C − Σ(stars)`.
  * This value is a sum of 5 (path) or 6 (two components) positive terms `a_i/(b_i·P_i)` and `1/(P·P')`. So one term is at least `Z_K/5` (resp. `Z_K/6`). Therefore one of the big primes satisfies `P_i ≤ 5·a_i/(b_i·Z_K)`, or `min(P, P') ≤ √(5/Z_K)` (resp. with 6), and the program computes the largest of these bounds.
  * Every prime `p` up to that bound is tried in every position.
  * If `p` is the middle of the path, both ends are stars on `A0 ∪ {p}` and `A2 ∪ {p}`, so they are prime factors of `p·a0 + b0` and `p·a2 + b2`.
  * If `p` is an end of the path, the other two primes form a one-edge component in which `p` is one more attachment of the middle prime. They are solved by the divisor equation.
  * If `p` lies in one of two components, its partner is a prime factor of `p·a + b`. The other component is then solved by the divisor equation.
  * A candidate is accepted only if its exact value is `Z_K`. This finds every solution, because in every solution some prime is at most the bound.
  * In the run, the bound is at most 1,581.
* **`b ≥ 3`:** reported as unresolved. The run shows that no such shape survives.

Further details:

* A star now has at most `48 − 36 = 12` neighbours; the program computes this bound.
* With 12 neighbours, `n(A)` can exceed `2^64`. All star and component arithmetic is therefore 128-bit with overflow checks, and an overflow would be reported.
* Factorisation uses Pollard's rho. Primality uses Miller–Rabin with the first 13 prime bases, which is deterministic below `3.3·10^24` (Sorenson–Webster). Every number tested lies below that bound, and a larger one would be reported.
* Step 2 finds every completion `G` with `|G| ≤ 48 − |C|`. So the run finds every `T` with `|T| ≤ 48` and reciprocal sum 1, not only those with `|T| = 48`. **In particular it re-finds all 23 sets with `|T| = 47`**, exactly the list of `solutions47.txt`, which is a built-in consistency check.

### 5. Result of the run

The run is recorded in `run48_output.txt`: 4 threads, 29 min 30 s for search and completion together.

* **Step 1** visits 1.33·10^10 nodes and keeps 1,491,334 cores.
  * 702,715 of them have `|C| + |U| = 48`.
  * 414 have `U = ∅`. These are solutions on their own: 397 with 48 elements, and the 17 known 47-element solutions with all primes `≤ 73`.
* **Step 2** examines 116,874,859 shapes. Only 601,685 of them, in 509,055 cores, pass parity and the value bound:
  * 592,627 with `b = 0`;
  * 8,985 with `b = 1`;
  * 73 with `b = 2`, in 73 cores;
  * none with `b ≥ 3`.
* Among the surviving shapes there are 24,065 candidate stars.
* For `b = 2`, the program solves 62,169 component problems (attachment sets times star covers). The largest bound on the enumerated prime is 1,581, and none of the 73 cores can be completed.
* Nothing is unresolved, and no probable prime is used; every primality decision is deterministic.
* The completions give the 223 solutions with 48 elements that use primes `> 73`, and the 6 known 47-element solutions with a prime `> 73`.
* In total the run finds 620 sets with 48 elements, plus exactly the 23 known sets with 47 elements.

**Hence the 620 listed sets are all the 48-element subsets of `P` with reciprocal sum 1.** ∎

### 6. Verification

* **In the program.** Every set is checked for 48 distinct elements `p·q` with `p < q` both proved prime, and its exact sum 1 is computed with big-integer fractions.
* **`verify48.py`.** It independently re-checks every listed set: factorisation by trial division, deterministic Miller–Rabin, and the sum with Python `fractions`. It also checks that the 47-element sets found along the way are exactly the 23 of `solutions47.txt`, and it generates `solutions48.txt`. Output: `verify48_output.txt`.
* **`complete48.py`.** It is an independent Python implementation of Step 2 with exact fractions: its own shape enumeration, uncapped star factoring, covers, divisor equation, and its own code for `b = 2`. It re-solves all 1,491,334 dumped cores and finds the same 643 sets (620 with 48 elements, 23 with 47) and no unresolved core. Output: `run48_python_crosscheck.txt`.
* **Two-edge solver.**
  * Both implementations recover planted examples: a path `167 − 499 − 317` with attachments `{2}, {3}, {5, 7}`, and two components `193 − 191` and `89 − 353`.
  * On those planted instances both find exactly the same completions: 27 and 2 distinct sets, respectively.
  * On the 73 cores that need `b = 2`, both find no completion.
* **Reproducibility.** A first run (before the `b = 2` solver was added, 73 cores reported unresolved) and the final run produce identical core dumps (1,491,334 cores) and the same 620 + 23 solutions.

---

## Lean verification of Step 1

The search of section 3 is formalized in Lean ([`lean/`](lean/README.md)).

* `lean/SemiprimeEgypt/Search.lean` writes it as a Lean function: tests (P1)–(P4), the table-driven step for the 8 smallest primes, the final test, and integer arithmetic throughout.
* Lean proves that the function is exhaustive for every budget `K ≤ 48`. Its output contains every core that passes the exact Step-1 condition (`core_mem_search`), hence the core of every `T` with `|T| ≤ K` and integral reciprocal sum (`core_mem_searchCores`).
* This proof covers the soundness of the loss bound (`loss_bound`) and of the knapsack tables (`mkTables_ok`).
* Compiled to native code, the Lean function reproduces the core lists of `semiprime48.cpp` on 12 reduced instances and on the real instance for budgets 40–46 ([`validation48/lean_vs_cpp_output.txt`](validation48/lean_vs_cpp_output.txt)). It is several hundred to several thousand times slower (budget 46: about 8.5 CPU hours, against 4.6 s for the C++ search with one thread), so budgets 47 and 48 were run only in C++.
* Step 2, including the new case `b = 2`, is not formalized.

## Running

    g++ -O3 -march=native -pthread -o semiprime48 semiprime48.cpp
    ./semiprime48 4 --selftest --dump cores48.txt        # budget 48 (default), 4 threads
    ./semiprime48 4 --budget 47                          # the 47-term classification again (~1 min)
    ./semiprime48 4 --budget 46                          # no solution with <= 46 terms (~2 s)

Independent checks:

    python3 verify48.py run48_output.txt                 # exact check of every listed solution
    gunzip -k cores48.txt.gz
    python3 complete48.py cores48.txt 48 4               # Step 2 again, in Python
    python3 complete48.py --selftest                     # planted two-edge structures
    bash validation48/step1_equivalence.sh 4             # old vs new Step 1, brute force

## Files

| file | content |
|---|---|
| `semiprime48.cpp` | the program: search, completion, verification (integer arithmetic only) |
| `run48_output.txt` | output of `./semiprime48 4 --selftest --dump cores48.txt` |
| `solutions48.txt` | the 620 solutions, with the primes `> 73` and their neighbours |
| `cores48.txt.gz` | the 1,491,334 cores kept by Step 1 (format of `cores47.txt.gz`; SHA-256 of the sorted, uncompressed file: `00ff081ebdedd8a98652c6dedbaa30b44b225661f18f7260d567391299c66cde`) |
| `verify48.py`, `verify48_output.txt` | independent exact verification of the listed solutions |
| `complete48.py`, `run48_python_crosscheck.txt` | independent Python Step 2 on all dumped cores |
| `validation48/` | old-vs-new Step 1 equivalence and brute force (`step1_equivalence.sh`, output in `step1_equivalence_output.txt`), Step 2 on a dump (`step2_from_dump.cpp`), runs of the final program at budgets 46 and 47 (`run46_output.txt`, `run47_output.txt`), and the comparison of the compiled Lean search with Step 1 (`lean_vs_cpp.sh`, `lean_vs_cpp_output.txt`, `lean_runner/`) |
