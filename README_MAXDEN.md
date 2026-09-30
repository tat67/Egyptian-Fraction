# The smallest possible largest element

**Problem.** Let `P = { p·q : p < q primes } = { 6, 10, 14, 15, 21, 22, 26, 33, ... }`. Over all nonempty finite `T ⊆ P` with

    Σ_{n∈T} 1/n = 1,

determine the minimum possible value of `max T`.

**Answer: `min max T = 589 = 19·31`.**

* A 53-element set with largest element 589 is given below. Its sum is checked exactly.
* No valid `T` has `max T ≤ 588`. The proof is computer-assisted. The C++ program `semiprime_maxden.cpp` does the search and writes a certificate. The Lean 4 kernel checks that certificate against a formally proved soundness theorem. The main theorem is `SemiprimeEgypt.MaxDen.isLeast_589`, with no `sorry` and no `native_decide`.
* There are exactly **3** sets that reach the minimum. Two independent searches find the same three.

## 1. A solution with `max T = 589`

    T = { 6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 65, 69, 77,
          82, 85, 91, 93, 95, 106, 118, 119, 123, 129, 143, 145, 155, 159, 161, 187, 203,
          213, 247, 265, 287, 295, 299, 341, 355, 403, 413, 473, 493, 497, 559, 583, 589 }

It has 53 elements, and every element is `p·q` with `p < q` primes:

    6=2·3  10=2·5  14=2·7  15=3·5  21=3·7  22=2·11  26=2·13  33=3·11  34=2·17  35=5·7
    38=2·19  39=3·13  46=2·23  51=3·17  55=5·11  57=3·19  58=2·29  65=5·13  69=3·23
    77=7·11  82=2·41  85=5·17  91=7·13  93=3·31  95=5·19  106=2·53  118=2·59  119=7·17
    123=3·41  129=3·43  143=11·13  145=5·29  155=5·31  159=3·53  161=7·23  187=11·17
    203=7·29  213=3·71  247=13·19  265=5·53  287=7·41  295=5·59  299=13·23  341=11·31
    355=5·71  403=13·31  413=7·59  473=11·43  493=17·29  497=7·71  559=13·43  583=11·53
    589=19·31

**Exact check.** The primes used are `2, 3, 5, …, 31, 41, 43, 53, 59, 71` (16 primes). Their product is

    L = 78502578988469866230.

Every element of `T` divides `L`, and

    Σ_{n∈T} L/n = 78502578988469866230 = L,

so `Σ_{n∈T} 1/n = 1` exactly. The C++ program recomputes this with big integers. Lean proves it as `T589_sum`, and the Python cross-check recomputes it with `fractions.Fraction`.

**All optimal sets.** Exactly three sets `T` have `Σ 1/n = 1` and `max T = 589`, with 53, 52 and 51 elements:

    |T|=53: the set above
    |T|=52: 6 10 14 15 21 22 26 33 34 35 38 39 46 51 55 57 62 65 69 77 82 85 87 91 93 95 106 115
            118 119 123 129 145 159 203 217 221 247 265 287 295 299 319 341 377 391 403 413
            473 559 583 589
    |T|=51: 6 10 14 15 21 22 26 33 34 35 38 39 46 51 55 57 58 62 65 69 77 82 85 91 93 95 106 119
            123 129 143 145 159 161 187 203 213 217 247 265 287 299 341 355 403 473 493 497
            559 583 589

## 2. Proof that `max T ≥ 589`

Let `E_B = P ∩ [1, B]` be the candidate elements below a bound `B`. Let `D_B = ∏_{p ≤ B/2} p` be the product of the primes up to `B/2`.

We must show that no `T ⊆ E_588` has `Σ 1/n = 1`. For `B = 588`, `E_588` has 174 elements, there are 62 primes `≤ 294`, and `D_588` has 416 bits.

A size argument alone cannot do this, because `Σ_{n∈E_588} 1/n = 1.4487… > 1`. The first bound where the total reaches 1 is 129.

**Lemma 1 (local criterion).** View `T` as a graph on the primes: `pq ∈ T` is the edge `{p, q}`. If `Σ_{n∈T} 1/n` is an integer, then for every prime `q`

    ρ_q(T) := Σ_{p : pq ∈ T} p⁻¹ ≡ 0   (mod q).

This is Lemma 1 of [`README.md`](README.md). Lean proves it (in both directions) as `integral_iff_localCond`.

**Lemma 2 (scaling).** Every `n = pq ∈ E_B` divides `D_B`, because `2 ≤ p < q` gives `p, q ≤ B/2`. Hence

    Σ_{n∈T} 1/n = 1   ⟺   Σ_{n∈T} D_B/n = D_B,

and every sum below is an exact natural number. (Lean: `sum_scaled_eq`.)

**The certificate.** A certificate is a binary tree. Each node holds a partial assignment: some elements of `E_B` are decided to be *in* `T`, some *out*, and the rest are undecided. A node is either a split `br n` or a closed leaf. A split `br n` has two children, one for `n ∈ T` and one for `n ∉ T`. A closed leaf is closed by one of three exact tests. Each test shows that no `T` consistent with the node can satisfy both Lemma 1 and `Σ = 1`:

| leaf | test | why no `T` survives |
|---|---|---|
| `hi` | `Σ_{in} D/n > D` | `T ⊇ in`, so `Σ_T D/n > D` |
| `lo` | `Σ_{E_B ∖ out} D/n < D` | `T ⊆ E_B ∖ out`, so `Σ_T D/n < D` |
| `md q` | `q` is prime, and `−ρ` is not a subset sum mod `q` of `{p⁻¹ : pq undecided}`, where `ρ = Σ_{pq ∈ in} p⁻¹` | `ρ_q(T) = ρ + (a subset sum of the undecided inverses) ≢ 0`, contradicting Lemma 1 |

The subset sums in `md q` are computed exactly. They form a `q`-bit mask, and each undecided inverse `a` updates it by `R ← R ∪ rot_a(R)`, where `rot_a` rotates the mask by `a` places.

**Soundness.** If every leaf of the tree passes its test, and the root has nothing decided, then no `T ⊆ E_B` has `Σ = 1`. The proof is by induction on the tree: every `T` is consistent with exactly one branch at each split, and the table shows it cannot survive at a leaf. Lean proves this as `check_sound` and `no_solution`. The generic statement holds for every bound `B` and every data set that passes the Boolean test `validB`.

**The computation for `B = 588`.** The search uses the three tests, forced moves and a branching rule. A forced move sets an element whose opposite choice closes at once. The branching rule splits on an edge at the prime whose congruence has the fewest completions. The resulting tree has **13,201 nodes, 6,601 of them leaves, and no solution leaf**. It was checked three times:

1. by the independent tree checker inside `semiprime_maxden.cpp`, which follows the semantics of the Lean `check` exactly;
2. by the Lean 4 kernel, using `decide +kernel` on `check C588.data C588.cert (st0 C588.data) = true` (`cert588_ok`, about 20 s);
3. by the separate Python proof described in §3.

Every solution `T` with `max T < 589` would satisfy `T ⊆ E_588`. So `max T ≥ 589` for every solution. ∎

**Second, independent refutation inside the C++ program.** Every element of `P` below 589 is a candidate value `m` for `max T`. For each such `m`, the program searches `E_m` with `m` forced in, and all 174 searches fail. Most are refuted at the root. The largest search is at `m = 583`, with 5,642 nodes. At `m = 589` the search finds the solution above.

**What the solution structure looks like.** The following is not needed for the proof. Deleting edges that cannot satisfy their congruence at an endpoint leaves 67 elements of `E_588` on 16 primes. Their reciprocals sum to only 1.0775, so a solution may drop at most 0.0775. The large primes can only occur as "stars" with a fixed neighbour set:

* `1/2 + 1/3 + 1/7 = 41/42`;
* `1/3 + 1/11 + 1/13 = 5·43/429`;
* `1/2 + 1/3 + 1/5 + 1/11 = 7·53/330`;
* `1/2 + 1/5 + 1/7 = 59/70`;
* `1/3 + 1/5 + 1/7 = 71/105`.

For example, the prime 41 can occur only with the neighbours 2, 3 and 7, giving the elements 82, 123 and 287. The 53-element solution uses all five of these stars.

## 3. Independent cross-check (`crosscheck_maxden.py`)

This is a different algorithm, in pure Python with exact integers and `Fraction`s:

* It uses only the congruences of Lemma 1, with no value bound.
* It first applies arc consistency to the graph.
* It then enumerates, prime by prime in decreasing order, every neighbour set that satisfies the congruence.

Results:

* `B = 588`: 22.9 million nodes. **No nonempty `T ⊆ E_588` has an integral reciprocal sum at all.** This is equivalent to the result above, because `Σ_{E_588} 1/n < 2`.
* `B = 589`: exactly 3 sets have an integral reciprocal sum. All three have sum exactly 1, and they are the three sets listed in §1.

Output: [`crosscheck_maxden_output.txt`](crosscheck_maxden_output.txt), about 1 minute.

## 4. Lean formalization

These files are in [`lean/SemiprimeEgypt/`](lean/SemiprimeEgypt). They use the same Lean 4 + Mathlib setup as the rest of the repository; [`lean/README.md`](lean/README.md) has the details.

| file | contents |
|---|---|
| `Basic.lean` (existing) | `IsSP`, `recipSum`, `resid`, `LocalCond`; Lemma 1 `integral_iff_localCond` |
| `MaxDenCheck.lean` | the checker (`Cert`, `St`, `rot`, `nbrs`, `modAcc`, `modLeaf`, `check`); data validity (`Valid`, Boolean `validB`, `valid_of_validB`); `rot_testBit`, `mem_nbrs`, `modAcc_spec`, `resid_eq_sig`; **`check_sound`**, `sum_scaled_eq`, **`no_solution`** |
| `MaxDenCert588.lean` | generated by `semiprime_maxden --cert`: the data for `B = 588` and the 13,201-node certificate |
| `MaxDenMain.lean` | `data588_valid`, `cert588_ok` (kernel checks); `no_solution_le_588`, `exists_ge_589`; the solution `T589` (`T589_sp`, `T589_sum`, `T589_max`, `T589_card`); **`isLeast_589`** |

The main theorem:

```lean
theorem isLeast_589 :
    IsLeast {m : ℕ | ∃ T : Finset ℕ, ∃ h : T.Nonempty,
      (∀ n ∈ T, IsSP n) ∧ recipSum T = 1 ∧ T.max' h = m} 589
```

Here `IsSP n` means `∃ p q, p.Prime ∧ q.Prime ∧ p < q ∧ n = p * q`, and `recipSum T = ∑ n ∈ T, (1 : ℚ) / n`.

**What is trusted.** The Lean kernel evaluates the checker on the certificate with `decide +kernel`. It uses no `native_decide` (so no `Lean.ofReduceBool`) and no `sorry`. `lake env lean AxiomsCheckMaxDen.lean` shows that every theorem depends only on `propext`, `Classical.choice` and `Quot.sound` ([`lean_axioms_maxden_output.txt`](lean_axioms_maxden_output.txt)).

The C++ program is not trusted. It only produces the certificate, and a wrong certificate would be rejected by the kernel; replacing a single leaf `md 29` by `md 31` makes `decide` fail. The data (prime list, masks, `D`, initial sum) are not trusted either. The kernel checks them against the mathematical definitions through `validB`/`valid_of_validB`: primality by trial division, every prime `≤ B/2` present, every semiprime `≤ B` present, `n ∣ D`, and the inverse property `p·(p^(q−2) mod q) ≡ 1`.

Build (from `lean/`):

```
lake build SemiprimeEgypt.MaxDenMain     # ~25 s once Mathlib is built
lake env lean AxiomsCheckMaxDen.lean
```

## 5. The C++ program

```
g++ -O2 -std=c++17 -o semiprime_maxden semiprime_maxden.cpp
./semiprime_maxden                        # solve and verify (≈0.5 s)
./semiprime_maxden --cert FILE --count    # also write the Lean certificate, list all optimal sets
```

The program uses only exact arithmetic: machine integers, and a small base-2³² big-natural type for the sums `Σ D/n` and for the final check. It contains no `float`, `double` or `long double`. Timings are integer milliseconds from `std::chrono`.

The program runs in four parts:

1. **Size bound.** It prints the size bound (`max T ≥ 129`).
2. **Scan.** It scans `m ∈ P` upwards, searching exhaustively for a solution with `max T = m`. The first success is at `m = 589`.
3. **Exact verification.** It verifies the solution with big integers: each element is a squarefree semiprime, the elements are distinct, `Σ = 1`, and `max = 589`.
4. **Certificate.** It builds the certificate for `B = 588` and re-checks it independently. It can also write the certificate as Lean.

Output: [`maxden_run_output.txt`](maxden_run_output.txt).

## Files

* `semiprime_maxden.cpp`: solver, verifier and certificate generator.
* `maxden_run_output.txt`: output of `./semiprime_maxden --cert … --count`.
* `crosscheck_maxden.py`, `crosscheck_maxden_output.txt`: independent Python check.
* `lean/SemiprimeEgypt/MaxDenCheck.lean`, `MaxDenCert588.lean`, `MaxDenMain.lean`, `lean/AxiomsCheckMaxDen.lean`, `lean_axioms_maxden_output.txt`: Lean formalization and its axiom report.
