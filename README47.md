# All 47-term representations of 1 by squarefree semiprimes

**Problem.** Let `P = { p·q : p < q primes }`. Find every `T ⊆ P` with `|T| = 47` and `Σ_{n∈T} 1/n = 1`. Verify each one exactly, and prove that the list is complete.

**Answer.** COUNT_PLACEHOLDER

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

### 3. Step 1: all cores

A depth-first search over the 21 primes of `S`, in decreasing order, enumerates every core `C` with `|C| + |U(C)| ≤ 47` that satisfies the value bound. It visits each core exactly once, and it prunes only with rigorous, directed-rounding bounds.

### 4. Step 2: every completion of every core

For a core, a completion is a set `G` with `Σ_G = 1 − Σ_C`. Its *shape* consists of `d_q`, the number of big neighbours of `q ∈ S`, and `b`, the number of big–big edges. Every shape satisfies:

* `d_q ≥ 1` on `U`; off `U`, either `d_q = 0` or `d_q ≥ 2`.
* The excess satisfies `b + Σ_U (d_q − 1) + Σ_{∉U} d_q = |G| − |U| ≤ 47 − |C| − |U|`.
* **Parity at 2:** `ρ(2) + d_2` is even, because every big prime is odd.
* **Value:** `1 − Σ_C ≤ Σ_{d_q=1} 1/(q·P_min(q)) + Σ_{d_q≥2} Σ_{k<d_q} 1/(q·b_k) + b/(79·83)`. Here `P_min(q)` is the least prime `> 73` with `P ≡ (−ρ(q))^{-1} (mod q)`, and `b_k` is the `k`-th prime above 73.

Three kinds of shape can survive these tests.

* **`b = 0`.** Every big prime `P` is a *star* whose neighbours `A` all lie in `S`. Then `P | n(A) = Σ_{q∈A} Π A / q`, so `P` is one of finitely many prime factors. Stars have at most 10 neighbours (star-size lemma). The program enumerates every exact cover of the multiplicities `d_q` by distinct stars and keeps the covers whose value equals `1 − Σ_C` exactly.
* **`b = 1`.** There is one component `{P1, P2}` joined by the edge `P1P2`, with attachment sets `A1` and `A2`; all other big primes are stars.
  * Put `b_i = Π A_i`, `a_i = Σ_{q∈A_i} b_i / q`, and `t = Z_K · b1 · b2`, where `Z_K` is the component's value.
  * Then `t` is a positive integer and `(t·P1 − a1·b2)(t·P2 − a2·b1) = b1·b2·(t + a1·a2)`.
  * This equation is equivalent to (*) at `P1` and `P2`, so every solution comes from a divisor of the right-hand side.
* **`b ≥ 2`.** Such a shape would be reported as unresolved.

**Result of the run:** RUN_PLACEHOLDER

### 5. Verification

Every set in the list is checked in two ways:

* it consists of 47 distinct squarefree semiprimes, with deterministic primality tests on the factors;
* the sum of its reciprocals is exactly 1, computed as a big-integer fraction.

There is also an independent Python implementation of Step 2 (`complete47.py`), using exact fractions. It re-solves every core dumped by Step 1 and reproduces the same list.

---

## Running

    g++ -O3 -march=native -pthread -o semiprime47 semiprime47.cpp
    ./semiprime47 4 --selftest --dump cores47.txt

RUNTIME_PLACEHOLDER
