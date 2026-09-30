# Lean 4 formalization of the semiprime results

This directory formalizes, in Lean 4 with Mathlib, the mathematics behind

* [`../README.md`](../README.md): no nonempty set of at most 46 squarefree semiprimes has an integral reciprocal sum;
* [`../README47.md`](../README47.md): there are exactly 23 sets of 47 squarefree semiprimes with reciprocal sum 1;
* [`../README48.md`](../README48.md): the core search (Step 1) of `semiprime48.cpp`, with the loss bound (P4), for every budget `K ≤ 48`.

**The core search is formalized as a Lean function, and Lean proves that it is exhaustive.** `Search.lean` writes Step 1 of `semiprime48.cpp` as the function `Inst.search`: depth-first search over the primes ≤ 73, tests (P1)–(P4), the table-driven leaf step, and the final test, all in exact integer arithmetic. `SearchReal.lean` proves `core_mem_search`: for every `K ≤ 48` the output of `(inst73 K).search (inst73 K).mkTables` contains every admissible core (as its edge set), and in particular the core of every set of at most `K` squarefree semiprimes with an integral reciprocal sum (`core_mem_searchCores` in `MainSearch.lean`).

Step 2 (shapes, stars and components) is **not** redone in Lean. Its outcome is stated as explicit hypotheses, and the theorems are proved *from* those hypotheses:

* `Search46` and `Search47` quantify over all admissible cores.
* The weaker `Search46'` and `Search47'` quantify only over the cores in `searchCores K`, the output of the verified search.

There are no `axiom` declarations and no `sorry`, `admit` or `native_decide`. Every theorem depends only on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`); `AxiomsCheck.lean` prints this.

> **Status in one sentence.** Everything *except Step 2 of the computation* is fully proved in Lean. That includes the reduction, the 23 solutions, and the exhaustiveness of the core search as a Lean function. The headline results are proved **conditionally** on `Search46'` and `Search47'`, which state what the C++ Step 2 checked for the cores output by the search; those hypotheses are **not** verified in Lean. So these are not complete formal proofs of the original theorems.

## Building

```
lean-toolchain : leanprover/lean4:v4.35.0-rc3
mathlib        : 3cb72cfd416d1b5ec4b930d67648ef036a5df24f   (pinned in lakefile.toml / lake-manifest.json)

lake exe cache get      # optional: download Mathlib binaries
lake build              # builds SemiprimeEgypt (all files)
lake env lean AxiomsCheck.lean   # lists the axioms used by the main theorems
```

Mathlib's binary cache was unreachable in the environment used here, so Mathlib was built from source at the pinned commit. Building this package then takes about two minutes, most of it in `Solutions.lean`. The build is warning-free apart from deprecation notices from this Mathlib snapshot and a few unused-variable lints. The options `autoImplicit` and `relaxedAutoImplicit` are off.

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
| `TopSum.lean` | `topSum k L`, the sum of the `k` largest entries of a list, and `le_topSum`; ceiling division `cdiv` |
| `Search.lean` | **the search as a Lean function**: instances (`Inst`), the tests (P1)–(P4) (`nodeOK`, `leafStep`), `Inst.go`, `Inst.search`; the table interface `Tables`, its soundness properties `TablesOK`, and the rounded acceptance condition `IntAdm` |
| `LossBound.lean` | `loss_bound`: the soundness of the loss bound (P4), i.e. the final value is at most the (P4) quantity for every completion |
| `SearchCorrect.lean` | **`mem_search`**: for any tables with `TablesOK`, every edge set with `IntAdm` is in the output of the search |
| `SearchTables.lean` | the concrete tables `mkTables` (residue knapsack `dpRun`, `VB`, `MX`, `BT`, `LOC`, `TOPT`) and test instances `mkInst` |
| `SearchTablesProof.lean` | `mkTables_ok`: the concrete tables satisfy `TablesOK` |
| `SearchReal.lean` | the instance `inst73 K` (primes ≤ 73); cores as edge sets (`edgesOf`, `coreOf`); residues of the search = `resid`; rounding; the 49 smallest big semiprimes (`bigSP_mem_bs73`, `V_le_bs`); **`intAdm_of_admissible`**, **`core_mem_search`** |
| `MainSearch.lean` | `searchCores K`; `core_mem_searchCores`; "integral ⇒ sum = 1" for `|T| ≤ 48`; `Search46'`, `Search47'` and the main theorems under them |
| `SearchSplit.lean` | splitting the search into work items (`items`, `expandItem`, `expandRounds`) with `search_eq_rounds`, used to run the compiled search in several processes |

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

## The search, proved exhaustive (no computational hypothesis)

| statement | Lean |
|---|---|
| For any instance and tables with the soundness properties `TablesOK`, every core satisfying the rounded Step-1 condition `IntAdm` (budget, rounded `Σ_C ≤ 1`, rounded Lemma 3 for every upper segment of `U`) is in the output of `Inst.search` | `mem_search` |
| The loss bound (P4) is sound: for every completion below a node, the final rounded value is at most the (P4) quantity (Lagrange multiplier `θ`, shares rounded up, local knapsack bounds) | `loss_bound`, `cdiv_add_cdiv_ge` |
| The computed tables (`VB`, `MX`, `BT`, `V_θ`, `LOC`, `TOPT`) satisfy `TablesOK` | `mkTables_ok`, `dpRun_ge`, `le_topSum` |
| For `S` = primes ≤ 73 and `K ≤ 48`: `Admissible K C` (exact rationals) ⇒ `IntAdm` for the edge set of `C` | `intAdm_of_admissible` |
| **Every admissible core is found:** `edgesOf C ∈ (inst73 K).search (inst73 K).mkTables` | `core_mem_search`, `mem_searchCores` |
| The core of every nonempty `T` with `|T| ≤ K ≤ 48` and `Σ 1/n ∈ ℤ` is in `searchCores K` | `core_mem_searchCores` |
| `|T| ≤ 48` and `Σ ∈ ℤ` ⇒ `Σ = 1` | `recipSum_eq_one_of_integral_48` |
| The search equals the concatenation of the results of its refined work items (for running it in several processes) | `search_eq_rounds`, `search_eq_evalDeep` |

The search is executable. Compiled to native code, it reproduces the core lists of `semiprime48.cpp` on reduced instances and on the real instance for the budgets that are feasible for it; see `../validation48/lean_vs_cpp_output.txt` and `../validation48/lean_runner/`.

## What is proved conditionally

| statement | Lean | hypothesis |
|---|---|---|
| No nonempty `T`, `|T| ≤ 46`, of squarefree semiprimes has `Σ 1/n ∈ ℤ` | `no_integral_sum_le_46`, `no_integral_sum_le_46'` | `Search46`, resp. `Search46'` |
| Every `T` with `Σ 1/n ∈ ℤ` has `|T| ≥ 47` | `card_ge_47_of_integral`, `card_ge_47_of_integral'` | `Search46`, resp. `Search46'` |
| `T` is a 47-element set of squarefree semiprimes with sum 1 ⇔ `T ∈ Sol23` | `solutions47_iff`, `solutions47_iff'` (and `solutions47_integral_iff`, `solutions47_integral_iff'` for "sum ∈ ℤ") | `Search47`, resp. `Search47'` |
| The set of all such `T` equals `Sol23` and has exactly 23 elements | `solutions47_eq`, `solutions47_ncard`, `solutions47_eq'`, `solutions47_ncard'` | `Search47`, resp. `Search47'` |
| `Search46' → Search46`, `Search47' → Search47` | `search46_of`, `search47_of` | none |

These theorems do **not** prove the original statements. They prove that the original statements follow from `Search46'` / `Search47'`, which only concern the cores in the output of the verified search.

## The computational hypotheses

All hypotheses are ordinary `Prop`s (`def`s), passed as arguments. They are not asserted anywhere. `Search46'` and `Search47'` (`MainSearch.lean`) are `Search46` and `Search47` with every quantifier over cores `C` restricted to `C ∈ searchCores K`, for example

```lean
def searchCores (K : ℕ) : List (Finset ℕ) :=
  ((inst73 K).search (inst73 K).mkTables).map coreOf

def Search46' : Prop :=
  ∀ C ∈ searchCores 46, CoreSet C → Admissible 46 C →
    (Uset 73 C).Nonempty ∧
      ∀ (d : ℕ → ℕ) (b : ℕ), ShapeOK 46 C d b → b = 0 ∧ ∀ P A, ¬ StarCand 10 C d P A
```

and `Search46`, `Search47` are, verbatim (`Main.lean`):

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

* **Step 1.** For the Lean function `Inst.search` this is a theorem (`core_mem_search`). `semiprime48.cpp` implements the same search; `semiprime_reciprocals.cpp` and `semiprime47.cpp` implement it without (P4), which does not change the output. That the C++ code computes the same function as `Inst.search` is not proved. It is supported by the comparison of the outputs (`../validation48/lean_vs_cpp_output.txt`): the primed hypotheses need the C++ Step 1 to output at least the cores of `searchCores K`.
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

* that the C++ Step 1 computes the same function as `Inst.search` (checked only by comparing outputs where the compiled Lean function is fast enough);
* that the C++ Step 2 implements the claims correctly, including:
  * Pollard-rho factorization of `n(A)` and of `t + a₁a₂`;
  * deterministic Miller–Rabin below `2⁶⁴`;
  * the cover and divisor enumeration;
* that the recorded runs produced the stated outputs.

All of this is summarized by `Search46'` and `Search47'`. The run statistics in the READMEs (numbers of nodes, cores and shapes) are not formalized. For 48 terms, Step 2 (including the new case of two big–big edges) and the 620 solutions are not formalized; Lean covers the reduction to the cores of `searchCores 48`.

Each hypothesis quantifies over infinite types (`d : ℕ → ℕ`, `A : ℕ → Finset ℕ`), but only finitely many values matter:

* `C` is a subset of the 210 core semiprimes.
* `d` matters only on `S`, and there it is bounded by the excess.
* Candidate stars form a finite set (`starCand_finite`).
* For fixed `(A₁, A₂, t)`, the component pairs are finite (`comp_pairs_finite`), and `t ≤ b₁b₂`.

So each hypothesis is a finite check. Lean is not asked to perform it.

## Primitive sets (`Prim*.lean`): fully proved

These files formalize [`../README_PRIMITIVE.md`](../README_PRIMITIVE.md). A set is primitive if no element divides another.

* `isLeast_413`: the least possible largest element of a primitive `T ⊆ {2, 3, …}` with `∑ 1/n = 1` is 413.
* `card_bounds`: the least possible number of terms lies between 39 and 47.

| file | contents |
|---|---|
| `PrimCheck.lean` | `no_primePow` (via `padicValRat`); the checker with automatic exclusion of multiples and divisors, the incremental chain bound, the congruence leaves modulo `gcd(D, p^B)`; `check_sound`, `no_solution`, `check_br_of` |
| `PrimData412.lean`, `PrimCert412_*.lean`, `PrimState412.lean`, `PrimSub412_*.lean`, `PrimRoot412.lean` | generated by `primitive_egypt.cpp`: data, the 673,645-node certificate, and 357 kernel-checked subtree theorems with their assembly `C412.cert_ok` |
| `PrimMain.lean` | `no_solution_le_412`, `T413`, `isLeast_413`, the `{1}` remark |
| `PrimCard.lean`, `PrimLag129.lean` | the Lagrangian chain bound `lagrange_bound` and its data for `A = 129` |
| `PrimCardMain.lean` | `card_ge_39`, `T47`, `card_bounds` |

`lake build SemiprimeEgypt.PrimCardMain` takes about 21 minutes on 4 cores, nearly all of it the kernel check of the certificate (about 2.5 GB per process). `lake env lean AxiomsCheckPrim.lean` lists only `propext`, `Classical.choice` and `Quot.sound`.

## The smallest possible largest element (`MaxDen*.lean`): fully proved

These files formalize a separate result, described in [`../README_MAXDEN.md`](../README_MAXDEN.md). Among all nonempty `T ⊆ P` with `Σ_{n∈T} 1/n = 1`, the least possible `max T` is **589**. This result is proved **unconditionally**: there is no computational hypothesis.

| file | contents |
|---|---|
| `MaxDenCheck.lean` | a certificate checker `check` (case splits `n ∈ T` / `n ∉ T`; leaves `lo`, `hi`, `md q` closed by exact natural-number tests, with residue sets as rotated bit masks); data validity `Valid` with the Boolean test `validB` and `valid_of_validB`; **`check_sound`**; **`no_solution`**: valid data plus an accepted certificate imply that no set of squarefree semiprimes `≤ B` has reciprocal sum 1 |
| `MaxDenCert588.lean` | generated by `semiprime_maxden.cpp --cert`: the data for `B = 588` and the 13,201-node certificate |
| `MaxDenMain.lean` | `data588_valid` and `cert588_ok` (both `decide +kernel`); `no_solution_le_588`; `exists_ge_589`; the 53-element solution `T589` (`T589_sp`, `T589_sum`, `T589_max`); **`isLeast_589`** |

`lake build SemiprimeEgypt.MaxDenMain` takes about 25 s once Mathlib is built, most of it the kernel evaluation of the certificate. `lake env lean AxiomsCheckMaxDen.lean` lists only `propext`, `Classical.choice` and `Quot.sound`. It uses no `native_decide` or `Lean.ofReduceBool`.

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
* `native_decide` is not used. The search is never evaluated inside the kernel; its exhaustiveness is proved for the function itself.
