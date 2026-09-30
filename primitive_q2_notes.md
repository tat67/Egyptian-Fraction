# Q2 (least number of terms of a primitive representation of 1): computational notes

These notes record computations for Q2 that go beyond the rigorous bounds `39 ≤ min |T| ≤ 47`.
The bounds themselves are proved in Lean (`card_bounds`) and checked in C++ (`./primitive_egypt q2`).
Nothing in this file is formally verified. Each item states its status.

* **Compressions of known sets.** Take the 23 semiprime sets with 47 terms and the 620 with 48 terms. No two elements `a, b` of a 47-term set can be replaced by one element `ab/(a+b)` while keeping the set primitive. From the 48-term sets, 23 such replacements give 47-term sets, all of them again semiprime sets. No three elements of any of these 47-term sets can be replaced by two (Egyptian-fraction search over `x ∈ (1/q, 2/q]`).
* **`|T| = 39` (exhaustive C++ search, `q39` variant of the engine).** With the Lagrangian bound at `A = 133`, two elements `≥ 330` would cost more than the slack `H_39 − 1`. Q1 forces an element `≥ 413`. So a 39-term solution has the form `C ∪ {N}` with `C ⊆ [2, 329]`, `|C| = 38`, `N = 1/(1 − Σ_C) ≥ 413`. The search enumerates all primitive cores `C` in the value window `[1 − 1/413, 1)` using the chain bound, and tests `N` exactly. Status: see below.
* **CP-SAT.** This is a heuristic search, not a proof. The universe is the non-prime-powers `≤ 2500` whose prime factors are `≤ 73`, except for at most one prime `≤ 400`. The model has the congruences at every prime, the value `Σ = 1` and `|T| ≤ 46`. Status: see below.
