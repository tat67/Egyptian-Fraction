# OEIS A101877: the least largest denominator of a sum of distinct unit fractions equal to n

a(n) is the least k such that some finite set S of distinct positive integers with max(S) = k has sum_{x in S} 1/x = n.

`a101877.cpp` is a self-contained C++ program for this problem. It uses **no floating point** anywhere; all arithmetic is on 64/128-bit integers. The Python scripts are independent checkers and use exact integer or `Fraction` arithmetic.

## Results

| n | a(n) or bounds | status | # witness sets (max = a(n)) |
|---|---|---|---|
| 1 | 1 | exact | 1 |
| 2 | 6 | exact | 1 |
| 3 | 24 | exact | 1 |
| 4 | 65 | exact | 1 |
| 5 | 184 | exact | 16 |
| 6 | 469 | exact | 224 |
| 7 | 1243 | exact | not completed (count stopped) |
| 8 | **3228** (the published value 3231 is wrong) | exact | not completed (count stopped) |
| 9 | **8498** | exact (`a101877_v2.cpp`, see `../a101877_a9_verified.txt`) | not counted |
| 10 | a(10) ≥ 22790; no upper bound verified here | lower bound only | — |
| 11 | a(11) ≥ 60580; no upper bound verified here | lower bound only | — |

### Key points

**a(9) = 8498** (new; full write-up in [`../a101877_a9_verified.txt`](../a101877_a9_verified.txt)).
* `witnesses/witness_n9_max8498.txt` lists 5966 distinct integers with maximum 8498 whose reciprocals sum to exactly 9. This is checked with `fractions.Fraction`, with the lcm identity Σ L/x = 9L, with sympy, and by both C++ residue checks.
* Nothing with maximum ≤ 8496 exists: `certificates/cert_n9_K8496_v2.txt`, and the earlier `cert_n9_K8496.txt`.
* Nothing with maximum 8497 exists: `certificates/cert_n9_K8497w.txt` (root closure, checked with `verify_cert.py --forced-in 8497`). The earlier result for 8497 was a 239-node branch and bound without a certificate.
* `python3 verify_a9.py` runs all of these checks in about 2 seconds.
* The witness was found by the revised solver `a101877_v2.cpp` after 67 nodes in 37 s on one core. The previous solver stopped after about 38,300 nodes without a decision.

**a(8) = 3228, not 3231.**
* `witnesses/witness_n8_max3228.txt` lists 2190 distinct integers with maximum 3228 whose reciprocals sum to exactly 8. This was checked with `fractions.Fraction`, with an lcm integer computation, with sympy, and by the C++ residue check.
* Nothing with maximum ≤ 3227 exists: see the certificate `certificates/cert_n8_K3227.txt`, checked by `verify_cert.py`.
* The published a(8) = 3231 (OEIS, and as given in the task) is therefore an overestimate.

**n = 9.**
* **Upper bound:** a(9) ≤ 8500, from an exact witness (`witnesses/witness_n9_max8500.txt`). There is also a witness with maximum 8502.
* **Lower bound:**
  * no S ⊆ [1..8496] exists (certificate at 8496, independently verified);
  * no S with max = 8497 exists (branch and bound closed, 239 nodes; no independent certificate);
  * 8499 and 8501 cannot occur in any set with integral sum (independently re-checked).
* **Open:** only whether some S has max = 8498 is undecided. The search was stopped after about 38,000 nodes. So a(9) ∈ {8498, 8500}.

**n = 10.** No S ⊆ [1..22788] exists, and no S with max = 22789 exists, both by independently verified certificates. Hence a(10) ≥ 22790. No witness was found within the time budget, so the previously claimed a(10) ≤ 22820 is not verified here.

**n = 11.** No S ⊆ [1..60578] exists, and no S with max = 60579 exists, both by independently verified certificates. Hence a(11) ≥ 60580. No witness was found, so the claimed a(11) ≤ 60639 is not verified here.

**The given lower bounds.** Those for n = 9, 10, 11 (8492, 22788, 60577) are all confirmed and improved.

### What is proved how

* **Witnesses (upper bounds).** These are exact: every listed set is verified with `fractions.Fraction`.
* **Root closures.** When the Lagrangian bound closes a case at the root, the certificate in `certificates/` is re-checked by `verify_cert.py`. That script shares no code with the C++ program. It recomputes the candidate set, the residues, Δ and every per-prime minimum using a plain residue DP in integer numpy.
* **Multi-node closures.** Two NONE results come from branch and bound over several nodes and have no independent certificate: n = 9 with max = 8497, and n = 10 with max = 22789. The latter was also re-proved at the root with a certificate.
* **Validation.** The program was validated on n = 1..8. It reproduces every known value except a(8), where it finds the smaller correct value, and the known witness counts 1, 1, 16 and 224 for n = 3..6.

## Revised solver `a101877_v2.cpp` (2026-10-04)

It uses the same mathematics as below (residues, candidates, exclusion form, Lagrangian bound, branch and bound), plus three changes:
* **Better multipliers.** A Polyak subgradient with an adaptive target (best bound + δ, with δ halved on stagnation). At K = 8497 the root bound moves from −2.97e10 (open) to +4.0e9, so the case closes at the root.
* **Cheap in-node propagation.** After reduced-cost fixings, the node is re-probed with the same multipliers until a fixpoint is reached, then briefly re-optimized. The previous solver created a new node after every fixing round.
* **Root certificates** in the format of `verify_cert.py`, optional threads (`threads=T`; the default `threads=1` is deterministic), and the experimental options `largefirst=1` and `fixfile=`.

`bench_v1_v2.sh` compares the two solvers on one core; the outputs are in `bench/`. Examples: `witness 9 8497` takes 239 nodes / 45 s with v1 and 1 node / 1.7 s with v2; `witness 8 3228` takes 2722 nodes / 170 s with v1 and 22 nodes / 4.1 s with v2.

## Method

**1. Integrality test.** For a prime p ≤ K, let p^E be the largest power of p that is ≤ K. For S ⊆ [1..K], the sum has v_p ≥ 0 exactly when

    res_p(S) = Σ_{x∈S, p|x} p^(E−v_p(x)) · (x/p^v_p(x))^(−1)  ≡ 0  (mod p^E).

**2. Candidates U.** A number x is removed if, for some prime p | x, no set of the remaining multiples of p that contains x has res_p ≡ 0. This is a subset-sum over residues, repeated until nothing changes. Every S with an integral sum lies in U.

**3. Exclusion form.** Let Δ = Σ_U 1/x − n and E = U \ S. Then S has sum n exactly when two things hold:
* res_p(E) ≡ res_p(U) for every p;
* Σ_E 1/x = Δ.

If the residue condition holds, Σ_S is an integer, so Σ_E ≡ Δ (mod 1). The second condition can therefore be replaced by Σ_E < Δ + 1. In particular, every residue-fixing E has Σ_E = Δ or Σ_E ≥ Δ + 1.

**4. Lower bound (Lagrangian decomposition).** Split each ⌊2^48/x⌋ into integer weights λ[p][x], of any sign, over the primes p | x. Then, for every residue-fixing E,

    2^48 · Σ_E 1/x  ≥  Σ_p  min { Σ_{x∈T} λ[p][x] : T ⊆ multiples of p in U, res_p(T) ≡ res_p(U) }.

If the right side exceeds 2^48·Δ, no S exists. The weights are improved by subgradient ascent.

Each per-prime minimum is an exact dynamic program that exploits the p-adic digit structure. A multiple with v_p(x) = v changes only the top v base-p digits of the residue, so the state at valuation level v has p^v values, and the total work is about E·K per prime. A plain DP would cost (number of multiples)·p^E.

**5. Branch and bound.** Each node fixes some x into E or into S, and a node is closed when its bound exceeds Δ.
* **Reduced-cost fixing:** forward and backward tables give every free x's bound when it is forced in or out, and any side whose bound exceeds Δ is fixed the other way.
* **Solutions:** if all primes' optimal sets agree, their union E is residue-fixing. With Σ_E < Δ + 1 it is a solution, which is then verified exactly.
* **Branching:** otherwise the search branches on a number the primes disagree about.

**6. Exact verification of a witness.** A witness passes if every residue res_p(S) ≡ 0, computed exactly for every prime p ≤ K, and the fixed-point enclosure of Σ_S lies inside (n−1, n+1). An integer in that interval equals n. Every witness is also checked independently in Python with `fractions.Fraction`.

**7. Certificates.** When the root bound alone closes a case, `cert=FILE` writes the weights. `verify_cert.py` then re-derives U, the residues, Δ and every per-prime minimum from scratch, using a plain residue DP in numpy int64 rather than the level DP, and checks the bound.

## Files

| file | contents |
|---|---|
| `a101877.cpp` | the solver: `prove n K`, `witness n K`, `count n K`, `check n K list` |
| `verify_cert.py`, `verify_witness.py` | independent exact checkers |
| `find_a.sh`, `rootscan.sh`, `validate.sh` | drivers |
| `witnesses/witness_n*_max*.txt` | witness sets, comma separated |
| `certificates/cert_n*_K*.txt` | lower-bound certificates (root closures). The `...w.txt` files have K forced into S; check them with `--forced-in K` |
| `runs/` | run logs with timestamps (`validation.txt`, `log_n9..11.txt`, root scans, search outputs) |
| `a101877_dfs.cpp` | an earlier exact enumerator (depth-first over primes); cross-checks counts for n ≤ 6 |

## Reproducing

    g++ -O2 -march=native -pthread -o a101877 a101877.cpp
    ./a101877 prove 8 3227 cert=c.txt && python3 verify_cert.py c.txt   # a(8) > 3227
    ./a101877 witness 8 3228                                           # finds a witness (a few minutes)
    python3 verify_witness.py 8 3228 --S "$(cat witnesses/witness_n8_max3228.txt)"
    ./validate.sh                                                      # n = 1..8 end to end
