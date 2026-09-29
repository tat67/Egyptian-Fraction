/-
The search for `S` = the primes `≤ 73`, and the link to the mathematics of the solutions.

* `inst73 K`: the instance of `semiprime48.cpp` (budget `K ≤ 48`).
* `edgesOf C`: the index pairs of a core `C` (a set of semiprimes with both factors `≤ 73`).
* `intAdm_of_admissible`: the exact Step-1 condition `Admissible K C` of `Reduction.lean` implies
  the rounded condition `IntAdm` for `edgesOf C` (upper rounding of `1/n`, `1/(79q)` and `V`).
* **`core_mem_search`**: every core `C` with `Admissible K C` appears in the output of the
  search, as `edgesOf C`;  **`core_of_solution_mem_search`**: in particular the core of every
  set `T` of squarefree semiprimes with `Σ 1/n = 1` and `|T| ≤ K` does.
-/
import SemiprimeEgypt.SearchTablesProof
import SemiprimeEgypt.Reduction

open Finset

namespace SemiprimeEgypt
namespace Srch

/-- The primes `≤ 73`. -/
def pr73 : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73]

/-- The 49 smallest squarefree semiprimes with a prime factor `> 73`. -/
def bs73 : List ℕ := [158, 166, 178, 194, 202, 206, 214, 218, 226, 237, 249, 254, 262, 267, 274,
  278, 291, 298, 302, 303, 309, 314, 321, 326, 327, 334, 339, 346, 358, 362, 381, 382, 386, 393,
  394, 395, 398, 411, 415, 417, 422, 445, 446, 447, 453, 454, 458, 466, 471]

/-- The instance of `semiprime48.cpp` with budget `K`. -/
def inst73 (K : ℕ) : Inst where
  pr := pr73
  K := K
  big := 79
  bs := bs73
  theta := 145
  AD := 12
  shn := [12, 11, 11, 10, 10, 9]
  lown := 8

lemma inst73_m (K : ℕ) : (inst73 K).m = 21 := rfl

lemma pr73_getD_pos (k : ℕ) : 0 < pr73.getD k 1 := by
  rcases Nat.lt_or_ge k 21 with h | h
  · interval_cases k <;> decide
  · rw [List.getD_eq_default _ _ (by simp [pr73]; omega)]; norm_num

lemma instOK73 (K : ℕ) : InstOK (inst73 K) where
  two_le_m := by rw [inst73_m]; norm_num
  P_pos := fun k => pr73_getD_pos k
  AD_pos := by show 0 < 12; norm_num
  sh_le := fun a => by
    show [12, 11, 11, 10, 10, 9].getD a 8 ≤ 12
    rcases Nat.lt_or_ge a 6 with h | h
    · interval_cases a <;> decide
    · rw [List.getD_eq_default _ _ (by simp; omega)]; norm_num

/-! ### The primes of `S` by index -/

lemma P73 (K k : ℕ) : (inst73 K).P k = pr73.getD k 1 := rfl

lemma P73_prime {k : ℕ} (hk : k < 21) : (pr73.getD k 1).Prime := by
  interval_cases k <;> norm_num [pr73]

lemma P73_le {k : ℕ} (hk : k < 21) : pr73.getD k 1 ≤ 73 := by
  interval_cases k <;> decide

lemma P73_strictMono {a b : ℕ} (hab : a < b) (hb : b < 21) : pr73.getD a 1 < pr73.getD b 1 := by
  interval_cases b <;> interval_cases a <;> decide

lemma P73_inj {a b : ℕ} (ha : a < 21) (hb : b < 21) (h : pr73.getD a 1 = pr73.getD b 1) :
    a = b := by
  rcases lt_trichotomy a b with h' | h' | h'
  · have := P73_strictMono h' hb; omega
  · exact h'
  · have := P73_strictMono h' ha; omega

/-- Every prime `≤ 73` has an index. -/
lemma exists_index {q : ℕ} (hq : q.Prime) (h73 : q ≤ 73) : ∃ k < 21, pr73.getD k 1 = q := by
  have : q ∈ pr73 := by
    interval_cases q <;> first | decide | (norm_num at hq)
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem this
  exact ⟨k, hk, by simp [List.getD_eq_getElem?_getD, hk]⟩

lemma index_of_smallPrime {q : ℕ} (hq : q ∈ smallPrimes 73) : ∃ k < 21, pr73.getD k 1 = q :=
  exists_index (mem_smallPrimes.1 hq).1 (mem_smallPrimes.1 hq).2

end Srch
end SemiprimeEgypt
