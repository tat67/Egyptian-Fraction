# Audit report for the paper on integral reciprocal sums of squarefree semiprimes

This report records the audit carried out before and during the writing of `main.tex`. It covers `README.md`, `README47.md`, both C++ programs, `complete47.py`, all recorded outputs, `cores47.txt.gz` and the complete `lean/` directory. Every numerical claim in the paper was re-derived from the data or re-executed. The READMEs were not taken at face value.

## 1. Final main theorems

* **Theorem A.** If `T ⊂ P = {pq : p < q primes}` is nonempty and finite and `Σ_{n∈T} 1/n ∈ ℤ`, then `|T| ≥ 47`. The bound is attained.
* **Theorem B.** There are exactly 23 sets `T ⊂ P` with `|T| = 47` and `Σ 1/n = 1`, and equivalently 23 with `Σ 1/n ∈ ℤ`.
  * 17 of them use only primes ≤ 73; in fact all their primes are ≤ 71.
  * 6 of them use exactly one prime `P > 73`, with `P ∈ {269, 311, 421, 433, 503, 3779}`. Each such `P` is joined to three primes `a, b, c ≤ 73` with `P | ab+ac+bc`.

Both theorems are **computer-assisted**. The paper says so in the abstract, in the introduction (Figure 1), and in every proof that uses a computation.

## 2. What is proved analytically

These are proved by hand in Sections 2–5 of the paper and all of them are also proved in Lean:

* the exchange lemma and the exact values of `H_k`, so that an integral sum with at most 47 terms equals 1 and has at least 38 terms;
* the local p-adic criterion;
* `|G| ≥ |U|`;
* the value bound for every `U' ⊆ U` (upper-segment form);
* the shape conditions (S1)–(S4): multiplicities, excess, parity at 2, and the value bound with `P_min` and `b_k`;
* the star lemma `P | n(A)`, `|A| ≥ 2`, and the star-size lemma (≤ 10 leaves for budget 46, ≤ 11 for budget 47);
* the component equation for `b = 1`: value identity, local conditions ⇔ integrality of `t`, the identity `(tP1−a1b2)(tP2−a2b1) = b1b2(t+a1a2)` ⇔ `tP1P2 = W`, positivity of both factors, and finiteness of the divisor enumeration.

## 3. What depends on exhaustive computation

The computational part consists of Computational Claims 6.2 and 7.1 (Lean: `Search46`, `Search47`):

* **Step 1** enumerates the admissible cores by depth-first search, in C++ only.
* **Step 2** enumerates the feasible shapes, candidate stars, exact covers, and the `b = 1` divisor enumeration. It is implemented in C++ and independently in Python.

Recorded results, all re-checked:

| | budget 46 | budget 47 |
|---|---|---|
| search nodes | 139,830,520,211 | 1,795,181,713,099 |
| cores after Step 1 | 178 | 22,382 (17 with U = ∅) |
| shapes (S1)–(S3) | 3,777 | 1,107,702 |
| shapes (S1)–(S4) | 61 (in 61 cores) | 8,049 (in 7,432 cores) |
| … by b = 0 / 1 / ≥2 | 61 / 0 / 0 | 7,981 / 68 / 0 |
| candidate stars | 0 | 125 |
| unresolved | 0 | 0 |
| solutions | 0 | 23 |

## 4. Independent checks

* **Exact verification of the 23 solutions.** Checked in the C++ BigNat code, in Python `Fraction`, in Lean (`Sol23_valid`, `Sol23_card`), and in `verification/verify_paper_facts.py`.
  * All 23 sets are distinct, and each has 47 distinct squarefree semiprimes and reciprocal sum exactly 1.
  * (*) holds at every vertex.
  * The six large primes and their neighbourhoods are recomputed.
* **Python Step 2** (`complete47.py`, and `verification/analyze47.py` with counters) on all 22,382 dumped budget-47 cores.
  * It reproduces the C++ counts exactly: 1,107,702, 8,049, 7,432 and 125. It finds the same 23 solutions and 0 unresolved.
  * Independence is limited: it consumes the C++ Step-1 output and implements the same reduction. It is a second *implementation*, not a second *argument*.
* **Budget-46 re-execution** (`verification/rerun/`).
  * The original program was rerun with 4 threads. Its output is identical to the recorded one, including the node count 139,830,520,211, except for the elapsed time.
  * A second execution through the engine of `semiprime47.cpp` gives identical numbers: 139,830,520,211 nodes, 178 cores, 3,777 and 61 shapes, 0 candidate stars, 0 unresolved, 0 solutions.
  * That run dumped all 178 cores. The Python Step 2 (`analyze47.py` and the original `complete47.py`, both with budget 46) confirms the result: 3,777 shapes, 61 surviving (all with b = 0), 0 candidate stars even without the 10-leaf bound, 0 unresolved and 0 solutions.
* **Brute-force validation of Step 1 on reduced instances** (`verification/step1_bruteforce/`).
  * Every core of `S = primes ≤ 13, 17, 19` was enumerated (2^15, 2^21 and 2^28 cores).
  * In all 48 configurations the check `SEG ⊆ DFS output ⊆ FIN` passes. The configurations cover 12 cutoff/budget pairs, table sizes 8 and 3, and 1 or 3 threads. The DFS output has no duplicates and does not depend on the thread count.
  * A negative control fails, as intended.
* **Overflow audit of the C++ `b = 1` branch.** It uses unchecked 128-bit arithmetic. The largest intermediate value that actually occurred has 59 bits, so no overflow happened.

## 5. Formally verified in Lean, and what remains conditional

* **Unconditional** (no computational hypothesis): all of Section 2 above, the reduction lemmas `admissible_of_real` and `shapeOK_of_real`, the finiteness lemmas, and `Sol23_valid` / `Sol23_card`. So the sharpness part of Theorem A is fully formal.
* **Conditional**: `no_integral_sum_le_46` and `card_ge_47_of_integral` assume `Search46`; `solutions47_iff`, `solutions47_integral_iff`, `solutions47_eq` and `solutions47_ncard` assume `Search47`.
* **Checks performed in this audit:**
  * the development was rebuilt;
  * there are no `sorry`, `admit`, `axiom` or `native_decide`;
  * `#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound` for all 24 checked theorems (`verification/lean_axioms_output.txt`).
* **Not formal:** that the C++ programs implement `Search46` and `Search47`. This rests on the informal argument of Section 7.1 of the paper.

## 6. Discrepancies found and how they were handled

1. **Step-1 pruning description (both READMEs, original versions).** They described the search as keeping all cores that satisfy the final Lemma-3 inequality. The code actually tests Lemma 3 for the *upper segments* of `U` decided so far.
   * This is sound, since Lemma 3 holds for every `U' ⊆ U`, but the description was inaccurate.
   * The brute-force tests show that the difference matters. For example, for `S ≤ 19` and budget 50 there are 1,146,681 "final-test" cores but only 475,652 "upper-segment" cores.
   * This was already corrected in the READMEs and the Lean hypotheses (previous session). The paper uses the corrected form throughout (Definition 4.5, Remark 4.6, Lemma 6.1).
2. **Component equation (README47, original).** The factorization identity was described as equivalent to (*) at `P1` and `P2`. It is the integrality of `t` that is equivalent; the identity holds automatically. This is corrected in README47 and in the paper (Proposition 5.5, Remark 5.6).
3. **"11,287 with |C|+|U| = 47, and 17 with U = ∅" (README47).** The program's counter excludes the 17 cores with `U = ∅`, all of which have `|C| = 47`. The dump contains 11,304 cores with `|C|+|U| = 47` in total. The computation is unaffected; the paper states the numbers precisely.
4. **"I also recomputed the 178 cores independently in Python" (README.md).** No artifact of this existed in the repository. It was reproduced and archived for this paper (`verification/rerun/`), with the same result: 61 feasible shapes and no candidate star.
5. **"needs about 300 MB of memory" (READMEs).** This is the virtual size. The resident memory measured during the rerun was about 4.5 MB.
6. **Watanabe's restriction to primes ≤ 101 (README.md).** The primary source was not accessible because the network policy blocked arXiv. Search snippets describe his search space as 325-dimensional, which equals C(26,2), the number of semiprimes with both factors ≤ 101. This partly corroborates the claim. The paper states it only in a footnote, flagged for checking.
7. **Unchecked 128-bit arithmetic in the `b = 1` branch of `semiprime47.cpp`.** This is a latent weakness that was not triggered (see Section 4), and the Python check uses exact integers.
8. **Probabilistic primality path for n ≥ 2^64 (`isPrime128`).** It was never used: the probable-prime count is 0. Miller–Rabin with the first 12 prime bases is deterministic for n < ψ12 ≈ 3.2·10^23 (Sorenson–Webster), which covers all 64-bit n.

No discrepancy affects the truth of Theorems A and B, subject to the computational claims.

## 7. Answers to the adversarial audit questions

1. **Does the ≤46 search cover arbitrarily large primes?** Yes. Large primes enter only through `G`. The shape analysis covers every `G`. A star centre divides `n(A)`, so it is found by complete factorization. Shapes with a large–large edge would be reported as unresolved, and none survived.
2. **Can any pruning rule discard a valid solution?** Not if the implementation is correct. Every test is a consequence of Lemma 3 for an upper segment, or of `|C|+|U| ≤ K` and `Σ_C ≤ 1`. Rounding is always in the safe direction (Lemma 6.1, Section 10). The brute-force tests support the implementation on reduced instances.
3. **Is the upper-segment correction represented correctly?** Yes: Definition 4.5, Remark 4.6, Lemma 6.1, and the Lean `Admissible`.
4. **Is every possible core enumerated?** Yes, by Lemma 6.1, assuming a correct implementation. This is the least independently checked component: one full-scale implementation, validated on reduced instances and executed three times for budget 46 (the recorded run, a rerun, and a run through the second program's engine).
5. **Is every completion shape enumerated?** Yes. Two independent implementations agree on all counts.
6. **Is the star enumeration finite for a justified reason?** Yes: `P | n(A)` and `n(A) > 0` (Lemma 5.1, `starCand_finite`).
7. **Is the `b = 1` argument correct?** Yes. It is proved in the paper and in Lean, with the corrected equivalence (integrality of `t`) and the positivity of both factors.
8. **Could a `b ≥ 2` case have escaped?** Only through an error in Step 1 or in the shape enumeration. Both Step-2 implementations report 0 feasible shapes with `b ≥ 2`.
9. **Are the 23 solutions distinct?** Yes (Python check, and Lean `Sol23_card`).
10. **Does each contain exactly 47 distinct squarefree semiprimes?** Yes (C++, Python and Lean).
11. **Does each sum equal exactly 1?** Yes, in exact arithmetic (C++, Python and Lean).
12. **Is "exactly 23" supported by exhaustive enumeration?** Yes, conditionally on Claim 7.1, which is the output of the exhaustive search. It does not rest merely on having found 23 examples. Lean derives "exactly 23" from `Search47`.
13. **Does the Lean section separate unconditional from conditional results?** Yes (Section 9, Figure 1, Appendix B).
14. **Were AI-generated arguments accepted without verification?** Every mathematical lemma is machine-checked in Lean, and every number was recomputed. The link between the C++ code and the Lean hypotheses is argued informally; it has been reviewed in this audit, which was itself AI-assisted, but it is not machine-checked. No independent *human* review of the code is documented.
15. **Were historical or novelty claims made without reliable references?** They are phrased cautiously ("to the best of our knowledge"). The literature search was limited to search-engine listings, since direct access to arXiv and Crossref was blocked. The Johnson (1978) citation details and the specifics of Watanabe's search are marked for manual verification (`references.bib`, `README_PAPER.md`).

## 8. Role of generative AI

The project was carried out with Claude Code, an AI coding assistant made by Anthropic, working under the direction of the human user. It developed or wrote the following:

* the mathematical reduction;
* both C++ programs;
* the Python cross-check;
* the Lean formalization;
* the READMEs;
* the verification scripts written for the paper;
* the manuscript draft.

The two corrections in Section 6 (items 1 and 2) were found by the same tool during the formalization and this audit. The paper's disclosure section (Section 12) says this, leaves a bracketed sentence for the authors to describe any human checking, and does not list an AI system as an author or in the acknowledgements.

## 9. Remaining uncertainties

* **Step 1 has a single full-scale implementation.** A bug that affects only large instances (for example, table-driven paths not exercised at small scale) cannot be excluded by the reduced-instance tests. It is mitigated by the soundness proof, careful code review, the reruns, and the consistency of the results: the 17 `U = ∅` solutions agree with a separate self-test run of the engine in a different mode (without unsatisfied primes), and every earlier-found solution is recovered.
* **The correspondence between the C++ code and `Search46`/`Search47` is informal.**
* **Correctness of the compiler and hardware is assumed.**
* **Bibliography.** The Johnson citation and the details of Watanabe's search are unverified. The novelty claim relies on a limited literature search.
* **No documented human review** of the code or the proofs.

## 10. Does the evidence support submission?

**Yes, as a computer-assisted result, with the caveats stated in the paper.**

* The mathematical reduction is fully machine-checked.
* The final list is exactly verified.
* The completion step has two agreeing implementations.
* The core enumeration is proved sound on paper and validated against brute force on reduced instances.

Before submission the authors should:

1. verify the bibliography items marked [MV] and the Watanabe details;
2. have the Step-1 code (`Worker::dfs`/`sub`, tables `BT`, `MX`, `LOWL`) reviewed by a human expert; ideally, obtain an independent reimplementation of Step 1;
3. complete the author, acknowledgement and AI-disclosure fields.
