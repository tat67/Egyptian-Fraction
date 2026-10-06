# Why hvds/seq A101877 reports a(8) = 3231

The C solver in [hvds/seq/A101877](https://github.com/hvds/seq/tree/master/A101877) (version 9.7, January 2015) reports a(8) = 3231. The value is wrong because one of its pruning rules is unsound. The rule ignores the **carry between powers of the same prime**, so the search discards valid sets.

[`../witnesses/witness_n8_max3228.txt`](../witnesses/witness_n8_max3228.txt) is a valid set with maximum 3228 and sum exactly 8. The solver excludes it, and this folder shows step by step where and why.

## Where 3231 comes from

The `results` file of hvds/seq records two runs:

* `n=8 k=3231 C7: 14.22s`. A set with maximum 3231 was found, which gives the upper bound a(8) ≤ 3231. That bound is correct.
* `n=8 k=3230 C9.7: 69201.09s`. Version 9.7 finished with *"no solution found"*, meaning no S ⊆ {1..3230} sums to 8. This is the step that is false: the 3228 witness is such a set.

## How the solver works

* **Grouping.** For a given k, each x ≤ k goes into a group according to its largest prime-power factor q = p^a:
  G(q) = {x ≤ k : gpp(x) = q}.
  The code calls such a group a "pp structure" (`pp_save_r`, `pp.c`).
* **Kept part and its residue.** Write a member as x = q·m with p ∤ m. The kept part of the group is
  K_q = Σ_{x∈S∩G(q)} 1/x = (1/q)·Σ 1/m.
  Its p^(−a) digit is governed by the residue
  r_q(S) = Σ_{x∈S∩G(q)} m^(−1) mod p.
  The code stores m^(−1) mod p as `pp_value.inv`.
* **Search.** Because Σ_{x∈S} 1/x must be an integer, every p^(−a) digit of the total must vanish.
  * The search visits the groups in a fixed order (`pplist`).
  * At each group it enumerates the subsets to discard, using `walker_findnext`, whose residue matches a target ρ.
  * A group with exactly one non-empty valid choice is collapsed into a single "composite" value, which is moved to the group of its remaining denominator. A group with no valid choice is dropped (`pp_resolve_simple`).

## The error

All line numbers below refer to `A101877/pp.c` at v9.7.

| line | code | effect |
|---|---|---|
| 428 | `if (i == 0 \|\| pp->pp * pplist[i - 1]->pp > k0) {` | q = p^a is classed **independent** when q times the next larger remaining prime power exceeds k |
| 659 | `invsum = pp->invtotal;` | an independent group gets target ρ = 0: its kept part must satisfy v_p(K_q) ≥ −(a−1) **by itself** |
| 127–147, 500 | `pp_listcmp` + `qsort` | independent groups are sorted in ascending order; a dependent D is placed before an independent I whenever D·I > k |
| 647–657 | target of a dependent group | read off the current `spare`, which still counts every later group at its provisional `min_discard` |

### Why the rule is wrong

The test only relates q to other prime powers q′ through products q·q′ ≤ k. That is the right test for **different** primes, where the interaction comes from an element divisible by both q and q′. It is the wrong test for **powers of the same prime**:

* The kept part K_{p^(a+1)} is only required to cancel its own top digit p^(−(a+1)).
* What remains of it generally still has p-adic valuation −a, or even lower. In other words it **carries** into the p^(−a) digit, and G(p^a) has to absorb that carry.

The correct condition, for each prime p and each a ≥ 1, is:

> the p^(−a) digit of K_{p^a} + K_{p^(a+1)} + K_{p^(a+2)} + … (plus terms from other primes' groups) vanishes.

The program instead imposes a **strictly stronger** condition: for every "independent" p^a, the digit of K_{p^a} must vanish on its own. A valid set S can meet the true condition and fail the stronger one, so a "no solution found" verdict is not a proof that no set exists.

The flaw shows up in three ways:

1. **Higher powers classed as independent.** Take p^(a+1) ≤ k but p^a·(next larger prime power) > k. Then p^a is classed independent and forced to ρ = 0, whereas the correct target is minus the carry from p^(a+1), p^(a+2), ….
   * For k = 3230: 64·67, 128·131 and 256·257 all exceed k, so 64, 128 and 256 are all "independent".
   * Yet 128, 256, 512 and 1024 are all ≤ k, so each of those groups sits below a higher power of 2.
2. **Dependent groups visited too early.** When p^a is dependent (32·37 ≤ 3230, so 32 is), it is sorted before every independent group I with 32·I > k. That includes the higher powers of its own prime: 32·128 > 3230. Its target is therefore computed from a `spare` in which the 128, 256 and 512 groups are still at their provisional choices.
3. **The bound is too tight.** The `min_discard` of an independent group is the smallest discard with residue 0 (`pp_resolve_simple`). Under the true condition that is not the smallest possible discard, so `spare` underestimates the slack. The `limit` and `spare < 0` checks in `pp_find` then also prune valid sets.

### The correct test

The author's own earlier programs used the correct test, p^(a+1) ≤ k, and visited the groups in descending order:

* `pp->pp * pp->p <= k`, in v7 `C_int.c` line 846;
* `$pp->{pp} * $pp->{f} <= $limit`, in `H_int`.

The v9 rewrite changed this:

* v9.2 replaced the factor p by the next prime power;
* v9.4 ("reorder pplist") introduced the ascending/merged order.

v9.7 inherits both changes.

## The 3228 witness against the rule (k = 3228, 3229 and 3230 behave the same)

### Static check

The tracer (`runs/run_sh_output.txt`, lines starting `audit:`) finds three independent groups where the witness S breaks the solver's residue-0 rule. In each case S also discards *less* there than the solver's `min_discard`:

| group | residue of S's kept part | solver's rule | S discards less than `min_discard` by |
|---|---|---|---|
| 128 | 1 mod 2 | 0 | 1/3200 |
| 256 | 1 mod 2 | 0 | 1/2816 |
| 243 | 1 mod 3 | 0 | 1/3159 |

In every case the matching carry comes from the higher powers of the same prime. For p = 3:

* G(729) = {729, 1458, 2916}, and S keeps 729 and 1458.
* 1/729 + 1/1458 = 1/486 = 1/(2·3⁵). The 3⁻⁶ digit cancels, but a 3⁻⁵ carry is left.
* S keeps all 9 members of G(243); their sum K₂₄₃ has v₃ = −5, which cancels that carry. The running sum then has v₃ = −3 (`runs/carry_table_p3.txt`).

For p = 2, computed with exact fractions by [`carry_table.py`](carry_table.py) (output in `runs/carry_table_p2.txt`):

| q | G(q) | S keeps | K_q | v₂(K_q) | v₂(running sum from the top) |
|---|---|---|---|---|---|
| 1024 | {1024, 3072} | both | 1/768 | −8 | −8 |
| 512 | {512, 1536, 2560} | 512, 2560 | 3/1280 | −8 | −7 |
| 256 | {256, 768, 1280, 1792, 2304, 2816} | all 6 | 1627/221760 | −6 | −7 |
| 128 | 13 elements | all 13 | 3788707301/214169155200 | −7 | −4 |

Row by row:

* **1024.** The group has a single non-empty valid choice, {1024, 3072}. The solver collapses it into the composite 1/768 = 1/(2⁸·3) and moves it into the 256 group. That step is correct.
* **512.** S keeps 512 and 2560. Their residue is 0, which the solver accepts. But K₅₁₂ = 3/1280 = 3/(2⁸·5) still contains 2⁻⁸: this is a carry.
* **256.** The group now holds its 6 members plus the composite. S keeps all of them:
  1627/221760 + 1/768 = 7663/887040, with v₂ = −8, so the residue is 1.
  * The solver demands residue 0, because 256 is "independent".
  * The true condition holds: adding the carry 3/1280 gives 4871/443520, with v₂ = −7.
* **128.** v₂(K₁₂₈) = −7, so the residue is 1, and the solver demands 0.
  * The true condition holds: this 2⁻⁷ digit cancels the carry from the groups above, and the running sum has v₂ = −4.
  * The remaining 2-power digits are cancelled by elements in groups of other primes, for example 1184 = 32·37, which lies in G(37).

### Dynamic check

In the actual search the witness is cut before the solver reaches any of these groups. The tracer (`runs/run_sh_output.txt`) shows where:

* **Processing order.** The order is 59, 53, 61, 64, 49, 67, 47, 71, 73, 43, 41, 79, 81, 83, 37, 89, 97, **32**, …, 128, …, 256, …, 512, …. The group 32 is level 17; 128, 256 and 512 come at levels 29, 61 and 83.
* **The cut at 32.** At level 17 the solver demands residue 1 for the group 32, while S has residue 0. The walker therefore never produces S's choice there, which is to keep all 34 members.
* **Why the target is off.** The solver's `spare` differs from the true remainder only by the later choices of S, relative to the provisional `min_discard`:
  * 128 group: −1/3200;
  * 256 group: −1/2816;
  * 512 group: +1/3840.

  Each of these denominators is divisible by 32. With S's actual choices put in, the required residue at 32 becomes 0, which is what S has.

So the witness conflicts with the solver in four places, all caused by the same flaw:

* the dynamic cut at 32;
* the static residue rule at 128, 256 and 243.

## The same flaw at n = 7

The a(7) witness [`../witnesses/witness_n7_max1243.txt`](../witnesses/witness_n7_max1243.txt) is rejected at the group 64 (level 14).

* **Why 64 is "independent".** 64·67 > 1243, so the solver forces residue 0 there.
* **What the 64 group holds.** Its 10 members plus the composite 1/192, which comes from G(256) = {256, 768}.
* **What S does there.** S keeps all 11 values, so the residue is 1. The carry that makes this correct comes from the 128 group: S keeps 4 of its 5 members, and K₁₂₈ = 37/2880 has v₂ = −6.
* **A second conflict, at the group 81.** The audit flags 81 as well, with residue 1 mod 3. S keeps all of G(243) = {243, 486, 972, 1215}, whose sum 13/1620 has v₃ = −4: a carry into the 3⁻⁴ digit, which S's choice in G(81) cancels.

v9.7 still prints a(7) = 1243, but only by accident. Its `pp_solution()` stops when the spare is 0 or a unit fraction 1/r, and then prints every element of the groups not yet visited, without checking the result. The set it prints for n = 7 sums to 3550/507, not 7. The sets it prints for n = 4, 5 and 6 are not solutions either. This shortcut can only cause false *successes*; the false "no solution" for n = 8 comes from the rule above.

## Check with the rule corrected

[`fix_same_prime_carry.patch`](fix_same_prime_carry.patch) makes three changes:

* a group counts as independent only if no higher power of the same prime remains;
* lower powers of the same prime are marked dependent;
* the groups are visited in descending order.

Results with the patch:

| check | result |
|---|---|
| tracer, n = 8, k = 3228, 3229, 3230 | the witness passes every level |
| tracer, n = 7, k = 1243 | the witness passes every level |
| solver, n = 3, 5, 6, 7 | reports a(n) = 24, 184, 469, 1243, and the printed sets sum exactly to n |
| solver, n = 4 | reports 65, but the printed set comes from the `pp_solution()` shortcut |
| solver, n = 8 | not run to completion here; the published v9.7 needed 69201 s for k = 3230. For n = 8 the tracer above is the evidence. |

The patch is only a check of the diagnosis. Its descending order is slower, as the author noted when introducing v9.4.

## Files

| file | contents |
|---|---|
| `guided.c` | tracer: appended to the hvds sources, it follows a given set S through the solver's own data structures and walker in the solver's order, and reports the first level where S is excluded |
| `fix_same_prime_carry.patch` | the minimal correction used for the check above |
| `carry_table.py` | independent exact computation of the carry table (no hvds code) |
| `run.sh [WORKDIR]` | fetches hvds/seq at commit `e0b76eb`, builds the solver as published and patched, runs the tracer on the n = 7 and n = 8 witnesses, and runs both solvers for n = 3..7 with every printed set checked by `fractions.Fraction` |
| `runs/run_sh_output.txt` | output of `run.sh` |
| `runs/carry_table_p2.txt` | output of `carry_table.py` for both witnesses |
