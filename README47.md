# All 47-term representations of 1 by squarefree semiprimes

**Problem.** Let `P = { p·q : p < q primes }`. Find every `T ⊆ P` with `|T| = 47` and `Σ_{n∈T} 1/n = 1`. Verify each one exactly, and prove that the list is complete.

**Answer. There are exactly 23 such subsets.**

* 17 of them use only primes `≤ 73`. They are also exactly the solutions whose primes are all `≤ 101`, which is consistent with the 17 examples in Watanabe's search (arXiv:2009.03275) restricted to primes `≤ 101`.
* 6 of them use exactly one prime above 73. In each case that prime `P` is joined to exactly three small primes `a, b, c`, and `P` divides `ab + ac + bc`.

  | big prime `P` | neighbours `{a, b, c}` | `ab + ac + bc` |
  |---|---|---|
  | 269 | {5, 11, 47} | 807 = 3·269 |
  | 311 | {3, 5, 37} | 311 |
  | 421 | {29, 43, 47} | 4631 = 11·421 |
  | 433 | {3, 37, 73} | 3031 = 7·433 |
  | 503 | {3, 13, 29} | 503 |
  | 3779 | {29, 37, 41} | 3779 |

Every one of the 23 sets was verified with exact rational arithmetic, in both the C++ program and Python.

The full list is in [`solutions47.txt`](solutions47.txt). The program `semiprime47.cpp` finds the list and proves it complete; it uses no floating point.

---

## Proof of completeness

This uses the same framework as [`README.md`](README.md), with budget 47 in place of 46.

### 1. Only the local conditions matter

`H_47`, the reciprocal sum of the 47 smallest elements of `P`, is about `1.0641 < 2`; the program checks this exactly. So for `|T| = 47`:

    Σ 1/n = 1   ⇔   Σ 1/n ∈ ℤ   ⇔   for every prime p:  Σ_{q∈N(p)} q^{-1} ≡ 0 (mod p),     (*)

where `T` is read as a graph on primes (`pq ∈ T` is an edge) and `N(p)` is the set of neighbours of `p`.

### 2. Core and big part

* `S` is the set of primes `≤ 73`, and primes `≥ 79` are *big*.
* The core `C` consists of the elements of `T` with both factors in `S`. The big part `G` is everything else.
* `ρ(q)` is the core residue at `q`, and `U = { q ∈ S : ρ(q) ≠ 0 }`.

Each `q ∈ U` needs its own edge to a big prime. So `|G| ≥ |U|`, and therefore `|C| + |U| ≤ 47`.

Every element of `G` has a factor `≥ 79`. This gives the value bound

    1 − Σ_{q∈U} 1/(79q) − V(47 − |C| − |U|)  ≤  Σ_C  ≤  1,

where `V(x)` is the sum of the `x` largest reciprocals of elements of `P` that have a factor `≥ 79`.

The bound also holds with `U` replaced by any subset `U' ⊆ U`. The depth-first search of Step 1 applies it to the part of `U` decided so far, `U' = U ∩ (p, ∞)`. So Step 1 keeps exactly the cores that satisfy the bound for every such upper segment, not merely for `U` itself (see [`lean/README.md`](lean/README.md), correction 1).

### 3. Step 1: all cores

A depth-first search over the 21 primes of `S`, in decreasing order, enumerates every core `C` with `|C| + |U(C)| ≤ 47` that satisfies the value bound. It visits each core exactly once, and it prunes only with rigorous, directed-rounding bounds.

### 4. Step 2: every completion of every core

For a core, a completion is a set `G` with `Σ_G = 1 − Σ_C`. Its *shape* consists of `d_q`, the number of big neighbours of `q ∈ S`, and `b`, the number of big–big edges. Every shape satisfies:

* `d_q ≥ 1` on `U`; off `U`, either `d_q = 0` or `d_q ≥ 2`.
* The excess satisfies `b + Σ_U (d_q − 1) + Σ_{∉U} d_q = |G| − |U| ≤ 47 − |C| − |U|`.
* **Parity at 2:** `ρ(2) + d_2` is even, because every big prime is odd.
* **Value:** `1 − Σ_C ≤ Σ_{d_q=1} 1/(q·P_min(q)) + Σ_{d_q≥2} Σ_{k<d_q} 1/(q·b_k) + b/(79·83)`. Here `P_min(q)` is the least prime `> 73` with `P ≡ (−ρ(q))^{-1} (mod q)`, and `b_k` is the `k`-th prime above 73.

Three kinds of shape can survive these tests.

* **`b = 0`.** Every big prime `P` is a *star* whose neighbours `A` all lie in `S`. Then `P | n(A) = Σ_{q∈A} Π A / q`, so `P` is one of finitely many prime factors. Stars have at most 11 neighbours (star-size lemma). The program enumerates every exact cover of the multiplicities `d_q` by distinct stars and keeps the covers whose value equals `1 − Σ_C` exactly.
* **`b = 1`.** There is one component `{P1, P2}` joined by the edge `P1P2`, with attachment sets `A1` and `A2`; all other big primes are stars.
  * Put `b_i = Π A_i`, `a_i = Σ_{q∈A_i} b_i / q`, and `t = Z_K · b1 · b2`, where `Z_K` is the component's value.
  * With this `t`, the identity `(t·P1 − a1·b2)(t·P2 − a2·b1) = b1·b2·(t + a1·a2)` always holds.
  * (*) at `P1` and `P2` is equivalent to `t` being an integer.
  * Both factors on the left are positive, and `A1`, `A2` are nonempty, because a prime cannot have exactly one neighbour.
  * So for fixed `(A1, A2, t)` every solution comes from a positive divisor `X` of `N = b1·b2·(t + a1·a2)`, with `P1 = (X + a1·b2)/t` and `P2 = (N/X + a2·b1)/t`.
  * An earlier version said the equation itself is equivalent to (*). It is the integrality of `t` that is.
* **`b ≥ 2`.** Such a shape would be reported as unresolved.

**Result of the run.** The depth-first search visits `1.8·10^12` nodes.

* Step 1 leaves 22,382 cores: 11,287 with `|C| + |U| = 47`, and 17 with `U = ∅`, which are complete solutions on their own.
* Across these cores, Step 2 examines 1,107,702 shapes. Only 8,049 of them, in 7,432 cores, pass parity and the value bound.
* None of the surviving shapes has `b ≥ 2`, so nothing is unresolved.
* Among the surviving shapes, 125 candidate stars exist in total.
* Every big prime that occurs is below `2^64`, so every primality decision is deterministic (no probable primes).
* The completions yield exactly the 6 big-prime solutions. The cores with `U = ∅` give the 17 solutions with all primes `≤ 73`.

**Hence the 23 listed sets are all 47-element subsets of `P` with reciprocal sum 1.** ∎

### 5. Verification

Every set in the list is checked in two ways:

* it consists of 47 distinct squarefree semiprimes, with deterministic primality tests on the factors;
* the sum of its reciprocals is exactly 1, computed as a big-integer fraction.

There is also an independent Python implementation of Step 2 (`complete47.py`), using exact fractions and its own factoring and cover code. It re-solves all 22,382 cores dumped by Step 1 (`cores47.txt.gz`). It finds the same 23 solutions and 0 unresolved cores; see `run47_python_crosscheck.txt`.

All 21 solutions found in earlier runs are among the 23.

---

## Lean formalization

[`lean/`](lean/README.md) formalizes every step above in Lean 4 with Mathlib, except the exhaustive search. That includes the component equation and its finite divisor enumeration, and an unconditional check that the 23 listed sets are solutions (`Sol23_valid`).

The search is stated as the explicit hypothesis `Search47`. The completeness theorems `solutions47_iff` and `solutions47_ncard` are proved **conditionally** on it, and `Search47` is not verified in Lean.

## Running

    g++ -O3 -march=native -pthread -o semiprime47 semiprime47.cpp
    ./semiprime47 4 --selftest --dump cores47.txt

The recorded run (`run47_output.txt`) took 5 h 48 min wall time on 4 threads, 20,898 s for the search, and needs about 300 MB of memory. To re-check Step 2 without repeating the search:

    gunzip -k cores47.txt.gz && python3 complete47.py cores47.txt 47
