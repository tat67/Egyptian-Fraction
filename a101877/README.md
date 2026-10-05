# OEIS A101877: the least largest denominator of a sum of distinct unit fractions equal to n

a(n) is the least k such that some finite set S of distinct positive integers with max(S) = k has

    Σ_{x∈S} 1/x = n.

OEIS lists 1, 6, 24, 65, 184, 469, 1243, 3231 for n = 1..8.

This directory contains exact solvers and independent checkers for this problem.
* `a101877_v2.cpp` is the current solver, and `a101877.cpp` (v1) is the earlier one, kept for comparison.
* Neither solver uses floating point anywhere; all arithmetic is on 64/128-bit integers.
* The Python scripts check results independently. They share no code with the solvers and use exact integer or `Fraction` arithmetic.

## Results

| n | a(n) or bounds | status | how | # witness sets (max = a(n)) |
|---|---|---|---|---|
| 1 | 1 | exact | | 1 |
| 2 | 6 | exact | | 1 |
| 3 | 24 | exact | | 1 |
| 4 | 65 | exact | | 1 |
| 5 | 184 | exact | | 16 |
| 6 | 469 | exact | | 224 |
| 7 | 1243 | exact | | not completed (count stopped) |
| 8 | **3228** (the published 3231 is wrong) | exact | witness + certificate | not completed (count stopped) |
| 9 | **8498** | exact | witness + two certificates | not counted |
| 10 | **22792 ≤ a(10) ≤ 22820** | bounds (both certified) | one certificate (`prove 10 22791`) + witness at 22820 | — |
| 11 | **a(11) ≥ 60590** (certified); no upper bound verified | lower bound only | one certificate (`prove 11 60589`) | — |

For n = 4..8 each value is exact: a root certificate for K = a(n) − 1 (`certificates/cert_n*_K*.txt`) together with a witness at a(n) (`witnesses/`). For n = 1..3 no certificate is needed: the candidates in [1..a(n) − 1] already sum to less than n (`runs/validation.txt`). The counts for n ≤ 6 come from complete enumeration and agree with the earlier `a101877_dfs.cpp`.

### a(9) = 8498

The full write-up is [`a101877_a9_verified.txt`](a101877_a9_verified.txt). That report comes from branch `claude/nifty-knuth-aj1lt7`, commits `3fd1c5f` and `6d27103`, and is reproduced unchanged.

* **Upper bound.** `witnesses/witness_n9_max8498.txt` lists 5966 distinct integers with maximum 8498 whose reciprocals sum to exactly 9. This is checked four ways:
  * with `fractions.Fraction`;
  * with the lcm identity Σ L/x = 9L, where L has 384 digits;
  * with sympy;
  * by the residue checks of both C++ solvers.
* **Nothing with maximum ≤ 8496.** Certificate `certificates/cert_n9_K8496_v2.txt`, margin 19,327,643,490 in units of 2^−48. The earlier `cert_n9_K8496.txt` is also valid, with margin 191,468,360.
* **Nothing with maximum 8497.** Certificate `certificates/cert_n9_K8497w.txt`, a root closure with 8497 forced into S, margin 4,008,227,003. It is checked with `verify_cert.py --forced-in 8497`. Before v2, this case rested on a 239-node branch and bound without a certificate.
* **A single certificate also suffices (new on this branch).** `./a101877_v2 prove 9 8497` closes at the root with margin 2,380,067,820. Its certificate `certificates/cert_n9_K8497.txt` shows that no S ⊆ [1..8497] has sum 9, which covers both cases above at once; it passes `verify_cert.py`.
* **One command.** `python3 verify_a9.py` re-checks the witness and the three certificates of the report from scratch in about 2 seconds.
* **How it was found.** v2 found the witness after 67 nodes in about 40 s on one core. v1 had stopped after about 38,300 nodes (82 minutes) without a decision, which left a(9) ∈ {8498, 8500}.

**Re-checked on this branch (2026-10-05).** All of these steps were rerun here:

| check | result |
|---|---|
| `python3 verify_a9.py` | `RESULT: a(9) = 8498 verified` |
| `./a101877_v2 prove 9 8496 cert=…` | root closure, margin 19,327,643,490; the certificate is **byte-identical** to `cert_n9_K8496_v2.txt` |
| `./a101877_v2 witness 9 8497 cert=…` | root closure, margin 4,008,227,003; the certificate is **byte-identical** to `cert_n9_K8497w.txt` |
| `./a101877_v2 witness 9 8498` | FOUND after 67 nodes and 15,847 DP passes; the set is **identical** to `witness_n9_max8498.txt` |
| `./a101877_v2 check 9 8498 …` | `VALID witness` |
| `./a101877_v2 prove 9 8497 cert=…` (new) | root closure, margin 2,380,067,820; `verify_cert.py`: VALID (`certificates/cert_n9_K8497.txt`) |
| `./validate_v2.sh` | n = 1..9 end to end: certificate at a(n) − 1 and witness at a(n), all VALID (`runs/validation_v2.txt`) |

The single-threaded search is deterministic, so identical output is expected.

### a(8) = 3228, not 3231

* **Witness.** `witnesses/witness_n8_max3228.txt` lists 2190 distinct integers with maximum 3228 whose reciprocals sum to exactly 8. It is checked with `fractions.Fraction`, with an lcm integer computation, with sympy, and by the C++ residue check.
* **Lower bound.** Nothing with maximum ≤ 3227 exists. The certificate is `certificates/cert_n8_K3227.txt`, checked by `verify_cert.py`.
* **Consequence.** The published a(8) = 3231 (OEIS) is an overestimate.

### n = 10

* **Certified: a(10) ≥ 22792** (previously ≥ 22790).
  * `certificates/cert_n10_K22791.txt` comes from v2 `prove 10 22791`, a root closure with margin 65,908,006. It shows that no S ⊆ [1..22791] has sum 10, and `verify_cert.py` checks it in about 4 s.
  * This single certificate covers the earlier `cert_n10_K22788.txt` and `cert_n10_K22789w.txt`. It also covers the new per-K root closures for K = 22790 and K = 22791, with margins 2,087,026,847 and 967,621,845. Those were checked too; see `runs/v2_n10/`.
  * Before v2, K = 22790 was undecided: v1's root bound was −6,062,645,272, and it stopped after 1500 nodes.
* **Branch and bound, without an independent certificate.** v2 `witness 10 22792` ends with NONE after 643 nodes (10.2 min, one core). So no S with max(S) = 22792 exists, if one accepts this complete but uncertified search. Its root bound is −2,741,356,479.
* **Upper bound: a(10) ≤ 22820** (new). This confirms the value given with the task.
  * `witnesses/witness_n10_max22820.txt` lists 16,343 distinct integers with maximum 22820 whose reciprocals sum to exactly 10.
  * It is checked with `fractions.Fraction` and with the lcm identity Σ L/x = 10L, where L has 864 digits. It also passes sympy, `verify_witness.py`, and the check modes of both C++ solvers (`runs/v2_n10/verify_witness_n10_max22820.txt`).
  * v2 found it with `witness 10 22820` after 860 nodes (maximum depth 182) in 21.5 min on one core. The root bound was −244,833,989,013. v1 had found no witness at 22820 within its time budget (`runs/log_n10.txt`).
* **Candidate filter.** Of K = 22790..22830, the 16 values 22798, 22799, 22801, 22804, 22805, 22807–22813, 22817, 22818, 22821 and 22822 are excluded by the C++ filter (`runs/v2_n10/candidate_scan_K22790_22830.txt`). None of them is used in the certified bound.

### n = 11

* **Certified: a(11) ≥ 60590** (previously ≥ 60580).
  * `certificates/cert_n11_K60589.txt` comes from v2 `prove 11 60589`, a root closure with margin 324,387,651. It shows that no S ⊆ [1..60589] has sum 11, and `verify_cert.py` checks it in about 16 s.
  * The same bound also follows K by K from a v2 root sweep (`rootsweep_v2.sh`, log `runs/v2_n11/root_sweep_K60581_60590.log`):
    * root certificates for K = 60580, 60581, 60582, 60583, 60585, 60587 and 60588, each checked with `verify_cert.py --forced-in K`;
    * K = 60584, 60586 and 60589 cannot be the maximum. The C++ filter excludes them, and `noncandidates.py` confirms this independently;
    * the earlier certificates for K ≤ 60578 and K = 60579.
  * Before v2, K = 60580 was undecided: v1's root bound was −695,501,196 after 20 minutes. v2 closes it in 42 s with margin 6,370,103,169.
  * K = 60590 is the first case whose root does not close (bound −1,678,478,077), so the sweep stops there.
* **Upper bound.** No witness search was run for n = 11, so the claimed a(11) ≤ 60639 is not verified here.

### The lower bounds given with the task

The task gave lower bounds 8492, 22788 and 60577 for n = 9, 10, 11. All three are confirmed and improved above.

### What is proved how

* **Witnesses (upper bounds).** These are exact: every listed set is verified with `fractions.Fraction`.
* **Root closures (lower bounds).**
  * When the Lagrangian bound closes a case at the root, the weights are written as a certificate in `certificates/`.
  * `verify_cert.py` re-checks every certificate. It shares no code with the C++ programs: it recomputes the candidate set, the residues, Δ and every per-prime minimum with a plain residue DP in integer numpy.
  * Files `cert_n*_K*w.txt` have K forced into S, i.e. they prove "no S with max(S) = K". Check them with `--forced-in K`.
* **Candidate filter.** Some K cannot be the maximum of any set with an integral sum (Rule 2 below), e.g. 8499 and 8501 for n = 9. `verify_witness.py` recomputes the candidate set independently, which confirms this.
* **Multi-node closures.** Branch and bound over several nodes gives NONE results without an independent certificate. Every lower bound stated above rests on root certificates and the candidate filter only. Earlier multi-node results (v1: n = 9 with max 8497, n = 10 with max 22789) have since been re-proved by root certificates.
* **Validation.**
  * v1 (`validate.sh`) was validated on n = 1..8. It reproduces every known value except a(8), where it finds the smaller correct value, and the known witness counts 1, 1, 16 and 224 for n = 3..6.
  * v2 (`validate_v2.sh`) was validated on n = 1..9. For every n it proves a(n) − 1 with an independently checked certificate and finds a witness at a(n) (`runs/validation_v2.txt`).

## Method

Both solvers use the same mathematics. Fix n and K.

**1. Integrality test.** For a prime p ≤ K, let p^E be the largest power of p that is ≤ K. For S ⊆ [1..K], the sum has v_p ≥ 0 exactly when

    res_p(S) = Σ_{x∈S, p|x} p^(E−v_p(x)) · (x/p^v_p(x))^(−1)  ≡ 0  (mod p^E).

**2. Candidates U.** A number x is removed if, for some prime p | x, no set of the remaining multiples of p that contains x has res_p ≡ 0. This is a subset-sum over residues, repeated until nothing changes. Every S with an integral sum lies in U. In particular, K cannot be the maximum when K ∉ U.

**3. Exclusion form.** Let Δ = Σ_U 1/x − n and E = U \ S. Then S has sum n exactly when two things hold:
* res_p(E) ≡ res_p(U) for every p;
* Σ_E 1/x = Δ.

If the residue condition holds, Σ_S is an integer, so Σ_E ≡ Δ (mod 1). The second condition can therefore be replaced by Σ_E < Δ + 1. In particular, every residue-fixing E has Σ_E = Δ or Σ_E ≥ Δ + 1.

**4. Lower bound (Lagrangian decomposition).** Split each ⌊2^48/x⌋ into integer weights λ[p][x], of any sign, over the primes p | x. Then, for every residue-fixing E,

    2^48 · Σ_E 1/x  ≥  Σ_p  min { Σ_{x∈T} λ[p][x] : T ⊆ multiples of p in U, res_p(T) ≡ res_p(U) }.

If the right side exceeds D_hi = Σ_U ⌈2^48/x⌉ − n·2^48 ≥ 2^48·Δ, no S exists.

Each per-prime minimum is an exact dynamic program that exploits the p-adic digit structure. A multiple with v_p(x) = v changes only the top v base-p digits of the residue, so the state at valuation level v has p^v values. The weights only affect how strong the bound is, never whether it is correct.

**5. Branch and bound.** Each node fixes some x into E or into S, and a node is closed when its bound exceeds D_hi.
* **Reduced-cost fixing:** forward and backward DP tables give every free x's bound when it is forced in or out, and any side whose bound exceeds D_hi is fixed the other way.
* **Solutions:** if all primes' optimal sets agree, their union E is residue-fixing. With Σ_E < Δ + 1 it is a solution, which is then verified exactly.
* **Branching:** otherwise the search branches on a number the primes disagree about. The two children fix that number in opposite ways, so they partition the node's search space.

**6. Exact verification of a witness.** A witness passes if every residue res_p(S) ≡ 0, computed exactly for every prime p ≤ K, and the fixed-point enclosure of Σ_S lies inside (n−1, n+1). An integer in that interval equals n. Every witness is also checked independently in Python with `fractions.Fraction`.

**7. Certificates.** When the root bound alone closes a case, `cert=FILE` writes the weights. `verify_cert.py` then re-derives U, the residues, Δ and every per-prime minimum from scratch, using a plain residue DP in numpy int64 rather than the level DP, and checks the bound.

### What v2 changes (`a101877_v2.cpp`)

The mathematics above is unchanged; v2 differs only in how the search is run.
* **Better multipliers.** A Polyak subgradient with an adaptive target: the best bound so far plus δ, with δ halved after 30 non-improving steps. v1 aimed at a fixed target above D_hi and stalled at a weaker bound. Root bound minus D_hi, v1 → v2:
  * `witness 9 8497`: −29,677,051,138 → **+4,008,227,003** (closed at the root);
  * `witness 9 8498`: −491,330,541,200 → −372,349,182,797;
  * `witness 10 22790`: −6,062,645,272 (v1, run of 2026-09-29) → **+2,087,026,847** (closed at the root).
* **In-node propagation.** After reduced-cost fixings, the node is re-probed with the same multipliers until nothing changes. The bound can only rise when options are removed. Then the multipliers are briefly re-optimised. v1 created a new node after every fixing round.
* **Root certificates** for `prove` and `witness` (`cert=FILE`).
* **Options.**
  * `threads=T`; the default `threads=1` is deterministic.
  * `largefirst=1` (branch first on elements with a prime factor > √K).
  * `maxnodes=N`, `quiet=1`.
  * `fixfile=FILE`, which restricts the search to a subproblem. It is only for experiments and is never used for proofs.

**Single-core comparison** (`bench_v1_v2.sh`, outputs in `bench/`). "Nodes" for v1 counts every re-solve after fixings; v2 counts branch-and-bound nodes.

| instance | v1 nodes / time | v2 nodes / time |
|---|---|---|
| `prove 8 3227` (proof) | 1 / 0.20 s | 1 / 0.21 s |
| `prove 9 8496` (proof) | 1 / 1.49 s | 1 / 1.43 s (margin 100× larger) |
| `witness 9 8497` (proof) | 239 / 45.3 s | 1 / 1.75 s (root certificate) |
| `witness 10 22789` (proof) | 2 / 22.6 s | 1 / 6.6 s (root certificate) |
| `witness 6 469` (find) | 19 / 0.11 s | 8 / 0.06 s |
| `witness 7 1243` (find) | 30 / 0.83 s | 14 / 0.72 s |
| `witness 8 3228` (find) | 2722 / 170.4 s | 22 / 4.1 s |
| `witness 9 8500` (find) | 3568 / 593.3 s | 144 / 60.4 s |
| `witness 9 8498` (find) | 3000 / 424.3 s, not found (node cap) | 67 / 37.4 s |

## Files

| file | contents |
|---|---|
| `a101877_v2.cpp` | the current solver: `prove n K`, `witness n K`, `check n K list`, options as above |
| `a101877.cpp` | the earlier solver (v1): `prove`, `witness`, `count`, `check`; still used for counting |
| `a101877_dfs.cpp` | an earlier exact enumerator (depth-first over primes); cross-checks counts for n ≤ 6 |
| `verify_cert.py`, `verify_witness.py` | independent exact checkers |
| `verify_a9.py` | one-shot check of a(9) = 8498 (witness + the three certificates of the report) |
| `verify_bounds.py` | one-shot check of the new bounds: a(9) = 8498 (one certificate), 22792 ≤ a(10) ≤ 22820, a(11) ≥ 60590 (about 20 s) |
| `noncandidates.py` | independent check that a given K cannot be the maximum (K ∉ U, Rule 2) |
| `validate_v2.sh` | v2 end to end for n = 1..9 (certificate at a(n) − 1, witness at a(n)) |
| `rootsweep_v2.sh` | v2 root sweep: `witness n K` for K = K0, K0+1, …, until a root does not close |
| `a101877_a9_verified.txt` | the full report on a(9) = 8498, including the complete witness and the soundness argument for every rule |
| `find_a.sh`, `rootscan.sh`, `rootw.sh`, `validate.sh` | v1 drivers |
| `bench_v1_v2.sh`, `bench/` | the single-core comparison above |
| `witnesses/witness_n*_max*.txt` | witness sets, comma separated |
| `certificates/cert_n*_K*.txt` | lower-bound certificates (root closures); `...w.txt` have K forced into S |
| `runs/` | run logs with timestamps |
| `runs/v2_n10/`, `runs/v2_n11/` | the v2 runs for n = 10 and 11 on this branch (2026-10-05): outputs, logs, certificate checks |
| `runs/validation_v2.txt` | output of `validate_v2.sh` |

## Reproducing

    g++ -O2 -march=native -pthread -o a101877_v2 a101877_v2.cpp
    g++ -O2 -march=native -pthread -o a101877    a101877.cpp          # v1, for comparison / counting

    python3 verify_a9.py                                   # a(9) = 8498, all checks (about 2 s)
    ./a101877_v2 witness 9 8498                            # finds the witness (67 nodes, about 40 s)
    ./a101877_v2 check 9 8498 "$(cat witnesses/witness_n9_max8498.txt)"
    ./a101877_v2 prove 9 8496 cert=c.txt   && python3 verify_cert.py c.txt
    ./a101877_v2 witness 9 8497 cert=w.txt && python3 verify_cert.py w.txt --forced-in 8497
    ./a101877_v2 prove 8 3227 cert=c8.txt  && python3 verify_cert.py c8.txt   # a(8) > 3227
    ./a101877_v2 witness 8 3228                            # a(8) <= 3228 (22 nodes, about 4 s)
    ./validate_v2.sh                                       # v2, n = 1..9 end to end (about 1 min)
    python3 verify_bounds.py                               # all new bounds for n = 9, 10, 11 (about 20 s)
    python3 verify_cert.py certificates/cert_n10_K22791.txt              # a(10) >= 22792
    ./a101877_v2 witness 10 22820                          # a(10) <= 22820 (860 nodes, about 22 min)
    ./a101877_v2 witness 10 22792                          # NONE after 643 nodes (about 10 min)
    ./rootsweep_v2.sh 11 60580 out11                       # n = 11 root closures up to K = 60589
    python3 noncandidates.py 60584 60586 60589             # these K cannot be the maximum
    ./validate.sh                                          # v1, n = 1..8 end to end
    ./bench_v1_v2.sh v2 ; ./bench_v1_v2.sh v1_short        # comparison table

Requirements: g++ (C++17), and Python 3 with numpy (`verify_cert.py`); sympy is only needed for an optional third sum check.
