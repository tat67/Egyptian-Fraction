# Lean 4 formalization of the two semiprime results

This directory formalizes, in Lean 4 with Mathlib, the mathematics behind

* [`../README.md`](../README.md): no nonempty set of at most 46 squarefree semiprimes has an integral reciprocal sum;
* [`../README47.md`](../README47.md): there are exactly 23 sets of 47 squarefree semiprimes with reciprocal sum 1.

The exhaustive searches are **not** redone in Lean. Each search result is stated as an explicit hypothesis (`Search46`, `Search47`), and the theorems are proved *from* those hypotheses. There are no `axiom` declarations and no `sorry`, `admit` or `native_decide`. Every theorem depends only on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`); `AxiomsCheck.lean` prints this.

> **Status in one sentence.** Everything *except the exhaustive computer searches* is fully proved in Lean. The two headline results are proved **conditionally** on `Search46` and `Search47`, which state exactly what the C++ programs checked; those two hypotheses are **not** verified in Lean. So these are not complete formal proofs of the original theorems.

## Building

```
lean-toolchain : leanprover/lean4:v4.35.0-rc3
mathlib        : 3cb72cfd416d1b5ec4b930d67648ef036a5df24f   (pinned in lakefile.toml / lake-manifest.json)

lake exe cache get      # optional: download Mathlib binaries
lake build              # builds SemiprimeEgypt (all files)
lake env lean AxiomsCheck.lean   # lists the axioms used by the main theorems
```

Mathlib's binary cache was unreachable in the environment used here, so Mathlib was built from source at the pinned commit. Building this package then takes about a minute, most of it in `Solutions.lean`. The build is warning-free apart from deprecation notices from this Mathlib snapshot and a few unused-variable lints. The options `autoImplicit` and `relaxedAutoImplicit` are off.

## Files

| file | contents |
|---|---|
| `Basic.lean` | `IsSP`, `recipSum`, `resid`, `LocalCond`; **Lemma 1** `integral_iff_localCond` |
| `SumBounds.lean` | exchange lemma; the 47 smallest semiprimes (`A47`, proved complete); `H37 < 1 < H38`, `H46, H47 < 2`, `H35 < 1 - 1757/79000`; "integral ⇒ sum = 1", `38 ≤ |T|` |
| `Core.lean` | core / big part / `U` / `d_q` / big–big count; **Lemma 2**; Lemma 4 (1)–(3); unique-neighbour class; excess identity; stars `P ∣ n(A)`, `|N(P)| ≠ 1` |
| `Values.lean` | `V`, `bigPrime` (= `b_k`), `Pmin`, `shapeVal`; **Lemma 3** (general form); **Lemma 4(4)**; **Lemma 5** (star size) |
| `Decomp.lean` | big part = small edges of big primes ∪ big–big edges; value and multiplicity identities; candidate stars of a solution |
| `Component.lean` | the component with one big–big edge: value identity, local conditions ⇔ integrality, divisor equation, finite enumeration (both directions) |
| `Reduction.lean` | the data checked by the search (`CoreSet`, `Admissible`, `ShapeOK`, `StarCand`) and the proof that every solution produces such data |
| `Solutions.lean` | the 23 sets (`Sol23`), verified unconditionally |
| `Main.lean` | the hypotheses `Search46`, `Search47` and the conditional main theorems |

## What is fully proved (no computational hypothesis)

The notation follows the READMEs: `S` is the set of primes ≤ 73, `C` the core, `G` the big part, `U` the unsatisfied set, `d_q` the number of big neighbours of `q`, `b` the number of big–big edges.

| statement | Lean |
|---|---|
| **Lemma 1.** For a finite set `T` of squarefree semiprimes: `Σ 1/n ∈ ℤ` ⇔ (*) at every prime | `integral_iff_localCond` |
| Exchange lemma: `H_k` is the largest reciprocal sum of `k` semiprimes | `recipSum_le_of_initial`, `recipSum_le_Aupto` |
| `H_37 < 1 < H_38`, `H_46 < 2`, `H_47 < 2`, `H_35 < 1 − 1757/79000` (exact rationals) | `H37_lt_one`, `H38_gt_one`, `H46_lt_two`, `H47_lt_two`, `H35_val` |
| `|T| ≤ 47` and `Σ ∈ ℤ` ⇒ `Σ = 1`; `Σ = 1` ⇒ `|T| ≥ 38` | `recipSum_eq_one_of_integral`, `card_ge_38` |
| **Lemma 2.** `|U| ≤ |G|`, hence `|C| + |U| ≤ |T|` | `card_Uset_le`, `card_core_add_card_Uset_le` |
| **Lemma 3.** `1 ≤ Σ_C + Σ_{q∈U'} 1/(79q) + V(K − |C| − |U'|)` for **every** `U' ⊆ U`; `Σ_C ≤ 1` | `value_lower_subset`, `value_lower`, `core_le_one` |
| **Lemma 4(1).** `d_q ≥ 1` on `U`, `d_q ≠ 1` off `U` | `dcount_pos_of_mem_U`, `dcount_ne_one_of_not_mem_U` |
| **Lemma 4(2).** `|G| = Σ_S d_q + b`; excess `b + Σ_U(d_q−1) + Σ_{S∖U} d_q ≤ K − |C| − |U|` | `card_bigPart_eq`, `excess_le` |
| **Lemma 4(3).** Parity at 2: `ρ(2) + d_2 ≡ 0 (mod 2)` | `parity_two` |
| **Lemma 4(4).** Unique neighbour `P` of `q`: `P⁻¹ = −ρ(q)` in `ZMod q`, `P ≥ P_min(q)`; the shape value bound | `unique_nbr_class`, `Pmin_spec`, `sum_nbr_le`, `shape_value_bound` |
| **Lemma 4(5).** Star: `P ∣ n(A)`, `P ≤ n(A)`, `|A| ≠ 1` | `star_dvd`, `star_le_nA`, `star_card_ne_one` |
| **Lemma 5.** A big prime whose neighbours are all ≤ 73 has `|N(P)| + 36 ≤ |T|`, i.e. at most 10 neighbours for `|T| ≤ 46` and at most 11 for `|T| ≤ 47` | `star_size` |
| `V(x) ≤ x/158`; big–big elements are `≥ 79·83` | `V_le`, `bigbig_elem_ge` |
| `G` = (small edges of the big primes) ∪ (big–big edges); `Σ_G` = star values + big–big part; `d_q` = number of big primes adjacent to `q` | `bigPart_eq`, `recipSum_bigPart_eq`, `dcount_eq_mult` |
| In a solution, a big prime with only small neighbours is a candidate star (prime `> 73`, `A ⊆ S`, `d_q ≥ 1` on `A`, `2 ≤ |A| ≤ |T| − 36`, `P ∣ n(A)`, residue condition when `d_q = 1`) | `starCand_of_real`, `starCand_real` |
| Candidate stars form a finite set | `starCand_finite` |
| **One big–big edge.** `Z·b₁b₂·P₁P₂ = W := a₁b₂P₂ + a₂b₁P₁ + b₁b₂` | `comp_value` |
| (*) at `P₁` and `P₂` ⇔ `P₁P₂ ∣ W` (⇔ `t = Z b₁b₂ ∈ ℤ`) | `comp_local_iff` |
| For `t ≠ 0`: `(tP₁−a₁b₂)(tP₂−a₂b₁) = b₁b₂(t+a₁a₂)` ⇔ `tP₁P₂ = W` | `comp_divisor_eq` |
| If `tP₁P₂ = W`, `t > 0`: `X = tP₁ − a₁b₂` is a **positive** divisor of `N = b₁b₂(t+a₁a₂)` and `P₁ = (X+a₁b₂)/t`, `P₂ = (N/X+a₂b₁)/t` exactly; conversely every such divisor gives `tP₁P₂ = W`; for fixed `(A₁,A₂,t)` there are finitely many pairs | `comp_enum`, `comp_of_divisor`, `comp_pairs_finite` |
| The core and shape of every solution pass the search's tests | `admissible_of_real`, `shapeOK_of_real` |
| **The 23 sets are solutions**: 47 distinct squarefree semiprimes each (explicit factorizations, primality by `norm_num`), reciprocal sum exactly 1; there are 23 distinct sets | `Sol23_valid`, `Sol23_card` |

`Sol23_valid` also proves, unconditionally, that 47 terms are attainable.

## What is proved conditionally

| statement | Lean | hypothesis |
|---|---|---|
| No nonempty `T`, `|T| ≤ 46`, of squarefree semiprimes has `Σ 1/n ∈ ℤ` | `no_integral_sum_le_46` | `Search46` |
| Every `T` with `Σ 1/n ∈ ℤ` has `|T| ≥ 47` | `card_ge_47_of_integral` | `Search46` |
| `T` is a 47-element set of squarefree semiprimes with sum 1 ⇔ `T ∈ Sol23` | `solutions47_iff` (and `solutions47_integral_iff` for "sum ∈ ℤ") | `Search47` |
| The set of all such `T` equals `Sol23` and has exactly 23 elements | `solutions47_eq`, `solutions47_ncard` | `Search47` |

These theorems do **not** prove the original statements. They prove that the original statements follow from `Search46` / `Search47`.

## The computational hypotheses

Both hypotheses are ordinary `Prop`s (`def`s), passed as arguments. They are not asserted anywhere. Here they are verbatim (`Main.lean`):

```lean
def Search46 : Prop :=
  ∀ C : Finset ℕ, CoreSet C → Admissible 46 C →
    (Uset 73 C).Nonempty ∧
      ∀ (d : ℕ → ℕ) (b : ℕ), ShapeOK 46 C d b → b = 0 ∧ ∀ P A, ¬ StarCand 10 C d P A

def Search47 : Prop :=
  (∀ C : Finset ℕ, CoreSet C → Admissible 47 C → Uset 73 C = ∅ → C.Nonempty → C ∈ Sol23) ∧
  (∀ C : Finset ℕ, CoreSet C → Admissible 47 C → (Uset 73 C).Nonempty →
      ∀ (d : ℕ → ℕ) (b : ℕ), ShapeOK 47 C d b → b ≤ 1) ∧
  (∀ (C : Finset ℕ) (d : ℕ → ℕ) (Ps : Finset ℕ) (A : ℕ → Finset ℕ),
      CoreSet C → Admissible 47 C → (Uset 73 C).Nonempty → ShapeOK 47 C d 0 →
      (∀ P ∈ Ps, StarCand 11 C d P (A P)) →
      (∀ q ∈ smallPrimes 73, mult Ps A q = d q) →
      recipSum C + starVal Ps A = 1 →
      C ∪ starEdges Ps A ∈ Sol23) ∧
  (∀ (C : Finset ℕ) (d : ℕ → ℕ) (Ps : Finset ℕ) (A : ℕ → Finset ℕ) (A₁ A₂ : Finset ℕ)
      (t X : ℕ),
      CoreSet C → Admissible 47 C → (Uset 73 C).Nonempty → ShapeOK 47 C d 1 →
      (∀ P ∈ Ps, StarCand 11 C d P (A P)) →
      A₁.Nonempty → A₂.Nonempty → A₁ ⊆ smallPrimes 73 → A₂ ⊆ smallPrimes 73 →
      (∀ q ∈ smallPrimes 73,
        mult Ps A q + (if q ∈ A₁ then 1 else 0) + (if q ∈ A₂ then 1 else 0) = d q) →
      recipSum C + starVal Ps A < 1 →
      0 < t →
      (t : ℚ) = (1 - recipSum C - starVal Ps A) * (∏ q ∈ A₁, (q : ℚ)) * ∏ q ∈ A₂, (q : ℚ) →
      0 < X → X ∣ compN A₁ A₂ t → t ∣ X + nA A₁ * ∏ q ∈ A₂, q →
      t ∣ compN A₁ A₂ t / X + nA A₂ * ∏ q ∈ A₁, q →
      compP₁ A₁ A₂ t X ≠ compP₂ A₁ A₂ t X →
      73 < compP₁ A₁ A₂ t X → 73 < compP₂ A₁ A₂ t X →
      (compP₁ A₁ A₂ t X).Prime → (compP₂ A₁ A₂ t X).Prime →
      compP₁ A₁ A₂ t X ∉ Ps → compP₂ A₁ A₂ t X ∉ Ps →
      C ∪ starEdges Ps A ∪ A₁.image (· * compP₁ A₁ A₂ t X) ∪
          A₂.image (· * compP₂ A₁ A₂ t X) ∪ {compP₁ A₁ A₂ t X * compP₂ A₁ A₂ t X} ∈ Sol23)
```

The notions they use (all in `Reduction.lean`, with exact rational quantities):

* `CoreSet C`: every element of `C` is a squarefree semiprime with both factors `≤ 73`.
* `Admissible K C`: the tests of **Step 1**. These are `|C| + |U| ≤ K`, `Σ_C ≤ 1`, and, for every `p`,
  `1 ≤ Σ_C + Σ_{q∈U, q>p} 1/(79q) + V(K − |C| − |U ∩ (p,∞)|)`
  (see correction 1 below).
* `ShapeOK K C d b`: the tests (i)–(iv) of **Step 2**. These are `d ≥ 1` on `U`, `d ≠ 1` off `U`, the excess bound, parity at 2, and
  `1 − Σ_C ≤ Σ_{q ≤ 73} shapeVal(q, d_q) + b/(79·83)`.
  Here `shapeVal(q, 1) = 1/(q·P_min(q))` and `shapeVal(q, k) = Σ_{i<k} 1/(q·b_i)` otherwise.
* `StarCand m C d P A`: the program's candidate list. `P` is prime, `P > 73`, `A ⊆ S`, `d ≥ 1` on `A`, `2 ≤ |A| ≤ m`, `P ∣ n(A)`, and `P⁻¹ = −ρ(q)` in `ZMod q` when `d_q = 1`.

**How the hypotheses match the programs.**

* **Step 1.** The depth-first search in `semiprime_reciprocals.cpp` and `semiprime47.cpp` reaches every core that satisfies `Admissible`.
  * Its pruning tests are the tests of `Admissible` at the successive upper segments of `U`, computed with upward-rounded bounds.
  * Upward rounding can only keep more cores, so every exactly admissible core survives.
* **`Search46`.** The problem-1 run reports:
  * 0 cores with `U = ∅` and `C ≠ ∅` (these would be listed as solutions). `C = ∅` is not admissible, since `V(46) < 1`.
  * 0 surviving shapes with `b > 0` (these would be reported as unresolved).
  * 0 candidate stars for every surviving shape (`0 candidate stars`).
* **`Search47`.** The problem-2 run reports:
  * **Part 1:** every admissible core with `U = ∅` and `C ≠ ∅` is recorded as a solution.
  * **Part 2:** 0 unresolved shapes, so no surviving shape has `b ≥ 2`.
  * **Part 3:** it enumerates all exact covers by candidate stars with distinct centres and keeps those of exact value `1 − Σ_C`.
  * **Part 4:** it enumerates attachment pairs, covers, the integer `t` and all divisors `X` of `N`.
  * Every recorded set is printed, and the printed list is exactly `Sol23`.
  * The program enumerates unordered pairs `{A₁, A₂}`, while part 4 quantifies over ordered pairs. Swapping `(A₁, P₁) ↔ (A₂, P₂)` replaces `X` by `N/X` and gives the same set, so the program's run covers both orders.

**What is not verified in Lean.** Lean does not check:

* that the C++ programs implement this enumeration correctly, including:
  * the search order and the subset tables;
  * residue bookkeeping;
  * the fixed-point directed rounding;
  * Pollard-rho factorization of `n(A)` and of `t + a₁a₂`;
  * deterministic Miller–Rabin below `2⁶⁴`;
  * the cover and divisor enumeration;
* that the recorded runs produced the stated outputs.

All of this is summarized by `Search46` and `Search47`. The run statistics in the READMEs (numbers of nodes, cores and shapes) are not formalized.

Each hypothesis quantifies over infinite types (`d : ℕ → ℕ`, `A : ℕ → Finset ℕ`), but only finitely many values matter:

* `C` is a subset of the 210 core semiprimes.
* `d` matters only on `S`, and there it is bounded by the excess.
* Candidate stars form a finite set (`starCand_finite`).
* For fixed `(A₁, A₂, t)`, the component pairs are finite (`comp_pairs_finite`), and `t ≤ b₁b₂`.

So each hypothesis is a finite check. Lean is not asked to perform it.

## Corrections to the README arguments found while formalizing

The mathematics was re-checked independently rather than taken from the READMEs. The final conclusions are unaffected, but the following points needed correcting or extra hypotheses.

1. **Step 1 does not enumerate "all cores satisfying Lemma 3" (both READMEs).**
   * The READMEs describe the pruning as "even the best completion cannot satisfy Lemma 3". That is not what the code does.
   * At an intermediate node, the search charges `1/(79q)` only for the primes already placed in `U`. All remaining budget goes to `V`.
   * A prime that joins `U` later, such as `q = 2` at the last level, adds `1/(79q)` but removes only the smallest `V`-term `1/v_r`. This can *increase* the final Lemma-3 quantity.
   * So a core that satisfies the final Lemma-3 test can be pruned earlier. A hypothesis "every core satisfying Lemma 3 is …" would not be what the program checked.
   * **Correction:**
     * Lemma 3 holds for *every* subset `U' ⊆ U`, not just for `U` itself (`value_lower_subset`).
     * The search applies it to the upper segments `U ∩ (p, ∞)`.
     * `Admissible` requires it for every such segment.
   * The pruning is therefore sound, and the hypotheses are stated with the corrected condition.
2. **The component equation (README47, case `b = 1`).**
   * "`t` is a positive integer and `(tP₁ − a₁b₂)(tP₂ − a₂b₁) = b₁b₂(t + a₁a₂)`; this equation is equivalent to (*) at `P₁` and `P₂`" is imprecise.
   * With `t := Z_K b₁b₂` the equation holds identically (`comp_value` + `comp_divisor_eq`). What is equivalent to (*) at `P₁` and `P₂` is the **integrality** of `t` (`comp_local_iff`).
   * Two facts the README uses without proof are now proved:
     * **Both factors are positive:** `tP₁ > a₁b₂` and `tP₂ > a₂b₁`, so only positive divisors are needed (`comp_enum`).
     * **The attachment sets `A₁, A₂` are nonempty:** a prime cannot have exactly one neighbour (`star_card_ne_one`). The program assumes this.
3. **`P_min(q)`.**
   * Its existence would need Dirichlet's theorem, but the argument does not need it: if no prime `> 73` lies in the class, `d_q = 1` is impossible.
   * `Pmin` is defined with the fallback value `0`. `Pmin_spec` gives `P_min ≤ P` for any prime `P > 73` in the class.
   * The program's `pminFor` terminated for every class it met, so its values are the true minima.
4. **Star size.**
   * The README bound is correct.
   * Lean proves `|N(P)| + 36 ≤ |T|` from the cruder estimate `Σ_{q≤73} 1/q ≤ 1.757` and `H_35 < 1 − 1757/79000`. This gives the same maxima, 10 for budget 46 and 11 for budget 47, that the programs computed.
5. **The case `U = ∅`.**
   * "The core satisfies (*) everywhere, hence its sum is 1" needs `C ≠ ∅`. This follows from the value bound, because `V(K) ≤ K/158 < 1`.
   * One also needs `G = ∅`, which follows from `Σ_G = 0`. Both steps are formalized in `case_U_empty`.
6. Lemma 1 needs `T` to consist of squarefree semiprimes, i.e. two distinct prime factors, as `integral_iff_localCond` assumes. The READMEs use it only in that setting.

## Trust base

* Lean's kernel and Mathlib at the pinned commit.
* Numerical facts are checked in the kernel through `decide` (finite-set identities and cardinalities) and `norm_num` (rational sums, primality of the 122 numbers' factors, up to 3779).
* `native_decide` is not used.
