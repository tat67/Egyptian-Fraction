# Primitive Egyptian fractions of 1

A finite set `T` of positive integers is *primitive* if no element divides another. We ask for primitive `T` with

    Σ_{n∈T} 1/n = 1.

**The set `{1}`.** `T = {1}` satisfies both conditions: its sum is 1, and the divisibility condition is empty for one element. Since `1` divides every integer, `{1}` is also the *only* valid set that contains `1`. Lean proves this as `one_primitive` and `eq_one_of_one_mem`. Taken literally, both minima below would therefore be `1`. The questions are meaningful for `T ⊆ {2, 3, 4, …}`, and that is what is answered here.

The squarefree semiprimes form a primitive set. So the earlier results of this repository already give valid sets with `max T = 589` ([`README_MAXDEN.md`](README_MAXDEN.md)) and with `|T| = 47` ([`README47.md`](README47.md)). Both bounds improve for primitive sets: to `max T = 413` (optimal) and to `|T| = 44`.

| question | result | status |
|---|---|---|
| **Q1** least possible `max T` | **413 = 7·59** | solved; formally verified in Lean (`isLeast_413`) |
| **Q2** least possible `abs(T)` | **39 ≤ min abs(T) ≤ 44** | bounds proved in Lean (`card_bounds`); exact value **not determined** |

The C++ program is `primitive_egypt.cpp`. It uses only integer and big-integer arithmetic, with no `float`, `double` or `long double`. The Lean files are `lean/SemiprimeEgypt/Prim*.lean`. No `sorry` and no `native_decide` are used, and only the standard axioms appear ([`lean_axioms_primitive_output.txt`](lean_axioms_primitive_output.txt)).

---

## Q1: the least possible largest element is 413

### A solution with `max T = 413`

    T = { 6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 57, 58, 62, 65, 69, 77, 82, 85,
          87, 91, 95, 111, 115, 118, 119, 123, 133, 141, 143, 148, 155, 185, 187, 188, 203,
          209, 217, 221, 235, 247, 259, 287, 295, 299, 319, 323, 391, 403, 407, 413 }

* **Size.** `T` has 53 elements.
* **Structure.** All elements are squarefree semiprimes except `148 = 2²·37` and `188 = 2²·47`. These two use the new freedom: two elements at 2-adic level 2 satisfy the 2-adic condition together, because `1/37 + 1/47 ≡ 0 (mod 2)`.
* **Exact check.**
  * `L = lcm(T) = 1687371961521906660` and `Σ_{n∈T} L/n = L`, so the sum is exactly 1.
  * No element divides another (all 53·52 ordered pairs are checked).
  * Lean proves these facts as `T413_sum`, `T413_primitive` and `T413_max`.

**A smaller witness.** Q1 is also attained by a 49-element set. CP-SAT reports 49 as the fewest elements of any primitive solution with `max T ≤ 413`; this optimality claim rests on the solver and is not verified.

    6 10 14 15 21 22 26 33 34 35 38 39 46 51 55 57 58 62 65 69 77 82 85 95 111 115 118 119 123
    133 141 143 145 148 155 185 188 217 221 235 259 287 295 299 319 391 403 407 413

`primitive_explore/verify_sets.py` checks both sets with Python `Fraction`s.

### No valid set has `max T ≤ 412`

**(a) No prime powers.** Suppose `p^k ∈ T` with `k ≥ 1`. Any other element `n` with `v_p(n) ≥ k` would be a multiple of `p^k`, which primitivity forbids. So `1/p^k` is the only term of `p`-adic valuation `−k`. Then the sum has valuation `−k` and cannot be 1. Lean proves this as `no_primePow`, using `padicValRat`. Hence

    T ⊆ U_B = { n ∈ [2, B] : n not a prime power }.

**(b) Scaling.** Let `D = lcm(U_B)`. Then `Σ 1/n = 1 ⇔ Σ D/n = D`.

**(c) Congruence at a prime `p`.** Let `M = gcd(D, p^B) = p^{v_p(D)}`. Then `M` divides `D`, and it divides `D/n` for every `n` with `p ∤ n`. Hence

    Σ_{n∈T, p∣n} (D/n mod M) ≡ 0 (mod M).

**(d) Chain bound.** Take divisibility chains `C` with weights `y_C` that cover every candidate: `Σ_{C∋n} y_C ≥ D/n` for every `n ∈ U_B`. A primitive set meets each chain at most once. So

    Σ_{n∈T} D/n ≤ Σ_{C not entirely excluded} y_C.

The cover comes from a maximum flow (weighted Dilworth theorem). At the start its bound equals the largest reciprocal sum of any primitive subset of `U_B`. For every `B` tested, that maximum is attained by the squarefree semiprimes.

**(e) Search and certificate.**

* A node of the search fixes some elements *in* `T` and some *out*.
* Putting `n` into `T` automatically puts every multiple and every divisor of `n` out.
* A node is closed by one of three tests:
  * `hi`: the elements in `T` already sum to more than 1;
  * `lo`: the chain bound is below 1;
  * `md p`: the congruence (c) cannot be met. This test uses subset sums of residues, stored as a rotated bit mask.

**(f) The scan.** For every `m ∈ U` with `m < 413`, the program searches `U_m` with `m` forced into `T`. That is 312 values of `m`, with `2.09·10^6` nodes in total. All 312 searches fail, and `m = 413` gives the solution above.

**(g) The certificate.** Independently, the program searches `U_412` (312 candidates) with nothing forced. It records the whole tree: **673,645 nodes, 336,823 leaves, and no solution.** Two separate checkers verify it:

* an independent checker inside the C++ program, with exactly the semantics of the Lean function `check`;
* the **Lean kernel**, using `decide +kernel`.

As a further independent cross-check, CP-SAT (OR-Tools, `primitive_explore/cpsat_q2.py 412 206 1000 …`) also reports the model over `U_412` as INFEASIBLE.

For the kernel check, the tree is split into 357 subtree theorems (≤ 3000 nodes each, spread over 16 files, so that `lake` checks them in parallel), assembled by `check_br_of`. This takes about 20 minutes on 4 cores and peaks at about 2.5 GB per process.

### Lean

| file | contents |
|---|---|
| `PrimCheck.lean` | `Primitive`, **`no_primePow`**; the checker (`Cert`, `St`, `Tr` tries, `excl`, `inStep`, `mdAcc`, `mdLeaf`, `check`); `Valid` and the Boolean test `validB`; the chain bound (`cbound`, `cbound_excl`, `sum_le_cbound`); the congruence (`md_congr`, `mdAcc_spec`); **`check_sound`**, **`no_solution`**, `check_br_of` |
| `PrimData412.lean` | generated data for `B = 412`: `D`, candidate and prime masks, 317 weighted chains |
| `PrimCert412_{0,1}.lean` | generated certificate (673,645 nodes) |
| `PrimState412.lean`, `PrimSub412_*.lean`, `PrimRoot412.lean` | generated: the states on the top 1000 nodes, the 357 kernel-checked subtree theorems, and the assembly `C412.cert_ok` |
| `PrimMain.lean` | `data412_valid`; **`no_solution_le_412`**; `exists_ge_413`; `T413`; **`isLeast_413`**; `q1_with_one` (the `{1}` remark) |

```lean
theorem isLeast_413 :
    IsLeast {m : ℕ | ∃ T : Finset ℕ, ∃ h : T.Nonempty,
      (∀ n ∈ T, 2 ≤ n) ∧ Primitive T ∧ recipSum T = 1 ∧ T.max' h = m} 413
```

The C++ program is not trusted. It only produces the certificate, which the kernel checks against the proved soundness theorem `no_solution`. The data are not trusted either: `validB` checks them against the definitions (trial division, prime-power recognition, `n ∣ D`, the chain property and the cover inequalities).

---

## Q2: the least possible number of terms, between 39 and 44

### Upper bound 44: fewer terms than any semiprime representation

    T44 = { 6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62, 65, 69, 74, 77,
            82, 85, 86, 87, 91, 93, 94, 95, 111, 115, 119, 123, 133, 141, 143, 145, 287,
            8729, 10105, 11687, 14467, 16813 }

* **Composition.** The first 39 elements are squarefree semiprimes. The other five are products of three primes:

      8729 = 7·29·43,  10105 = 5·43·47,  11687 = 13·29·31,  14467 = 17·23·37,  16813 = 17·23·43

  Each of these five contributes to the congruences at three primes at once. That is why fewer terms suffice than with semiprimes, where 47 is the proved minimum. Primitivity forces the semiprime divisors of the five large elements, such as `203 = 7·29`, to be absent.
* **Exact check.**
  * `L = lcm(T44) = 614889782588491410` and `Σ L/n = L`.
  * No element divides another.
  * The C++ program (`./primitive_egypt q2`), Python (`primitive_explore/verify_sets.py`) and Lean (`T44_sum`, `T44_primitive`, `T44_card`) all confirm this.

A 46-term set was found first. Among its elements, only `575 = 5²·23` and `925 = 5²·37` are not squarefree semiprimes; they form a pair at 5-adic level 2, because `1/23 + 1/37 ≡ 2 + 3 ≡ 0 (mod 5)`:

    T46 = { 6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62, 65, 69, 74, 77,
            82, 85, 86, 91, 93, 95, 111, 118, 119, 123, 129, 133, 145, 155, 187, 203, 253, 287,
            407, 493, 575, 925, 1357, 2537 }

Both sets were found with the CP-SAT solver (`primitive_explore/cpsat_q2.py`) and then verified exactly.

### Lower bound 39 (Lean: `card_ge_39`)

This is a Lagrangian version of the chain bound. Fix a threshold `A` and write `1/n = 1/A + (1/n − 1/A)`. Take a chain cover of the weights `D/n − D/A` on the candidates `n < A`, with total weight `W`. Then every primitive `T` without prime powers satisfies

    Σ_{n∈T} 1/n  ≤  |T|/A + W/D − (1/A − 1/m)      for each m ∈ T with m ≥ A.

(`lagrange_bound`.) With `A = 129 = a_38`, the 38th squarefree semiprime, the cover has 83 chains and `38/A + W/D − 1 = H_38 − 1 = 0.00144…`, so the bound is tight.

* **`|T| ≤ 37`.** Then `Σ ≤ 37/129 + W/D = 0.99369… < 1`.
* **`|T| = 38`.** An element `m ≥ 159` would give `Σ ≤ 38/129 + W/D − (1/129 − 1/159) < 1`. So `T ⊆ [2, 158]`, which Q1 excludes.

Both inequalities are exact rational comparisons, done in C++ (`./primitive_egypt q2`) and in Lean (`norm_num`). Lean: `card_bounds` states `39 ≤ min |T|` together with the 44-term example.

### What is and is not known about the exact value

For `|T| = k ≥ 39`, the Lagrangian slack `H_k − 1` exceeds the cost `1/a_k − 1/n` of one element, and for larger `k` of several elements. Those elements can be arbitrarily large. For `k = 39` at most one element can exceed 329; for `k = 40, 41, 42, 43` at most 2, 3, 4, 5 elements can exceed 503, 824, 1075, 1363. So no finite search over `[2, B]` settles the question.

`T44` shows the effect: its five large elements are not below `8729`. A proof that 43 or fewer terms are impossible would need an exhaustive treatment of a bounded "core" together with up to five arbitrarily large elements that obey the local congruences. That goes well beyond what the repository needed for semiprimes. It has not been carried out, so **the exact minimum is not determined here**. It lies in `[39, 44]`.

**Computational evidence** (CP-SAT, not formally verified; see [`primitive_q2_notes.md`](primitive_q2_notes.md)): the minimum over primitive sets of non-prime-powers `≤ X` is

| `X` | candidates | fewest terms found | proved by the solver |
|---:|---:|---:|---|
| 4 000 | 3 410 | 46 | optimal |
| 8 000 | 6 943 | 46 | no solution with `≤ 45` terms |
| 20 000 | 17 671 | 44 | optimal |
| 40 000 | 35 714 | 44 | no solution with `≤ 43` terms |
| 100 000 | 90 299 | 44 | no solution with `≤ 43` terms |

So the minimum decreases as larger elements are allowed, reaches 44, and stays at 44 at least up to 100 000. This supports the conjecture that **the answer to Q2 is 44**. It is not a proof: elements beyond `10^5` are not covered, and the solver's infeasibility claims are not certified.

## Running

```
g++ -O2 -std=c++17 -o primitive_egypt primitive_egypt.cpp
./primitive_egypt q1 --cert lean/SemiprimeEgypt   # Q1: scan (≈6 min), solution, certificate + Lean files
./primitive_egypt q2                              # Q2: the bounds 39 and 44
./primitive_egypt all                             # both
./primitive_egypt cert B --cert DIR               # a certificate for any bound B without solutions
./primitive_egypt lag A --cert DIR                # the Lagrangian chain cover for a threshold A
```

Lean (from `lean/`, with Mathlib built):

```
lake build SemiprimeEgypt.PrimCardMain     # ≈ 21 min on 4 cores (most of it: the 412 certificate)
lake env lean AxiomsCheckPrim.lean
```

Outputs: [`primitive_q1_output.txt`](primitive_q1_output.txt) and [`primitive_q2_output.txt`](primitive_q2_output.txt). The regenerated certificate files were checked to be byte-identical to the ones checked by Lean.
