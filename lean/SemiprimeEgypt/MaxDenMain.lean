/-
# The smallest possible largest element is 589

Main theorem `isLeast_589`: among all nonempty finite sets `T` of squarefree semiprimes
`p * q` (`p < q` primes) with `∑_{n ∈ T} 1/n = 1`, the least possible value of `max T` is
`589 = 19 · 31`.

* Existence: the explicit 53-element set `T589` (found by `semiprime_maxden.cpp`).
* Minimality: `no_solution_le_588`.  The generic soundness theorem `no_solution`
  (`MaxDenCheck.lean`) is applied to the data and the certificate of `MaxDenCert588.lean`;
  the kernel checks the data (`validB`) and evaluates the checker on the whole certificate
  (13201 nodes) with `decide +kernel`.  No `native_decide`, no `sorry`, no axioms beyond the
  three standard ones (see `AxiomsCheck.lean`).
-/
import SemiprimeEgypt.MaxDenCert588

open Finset

namespace SemiprimeEgypt.MaxDen

/-! ### Minimality: no solution with all elements `≤ 588` -/

/-- The data for `B = 588` pass the Boolean validity test. -/
theorem data588_validB : validB C588.data = true := by decide +kernel

theorem data588_valid : Valid C588.data := valid_of_validB data588_validB

/-- The kernel evaluates the checker on the whole certificate. -/
theorem cert588_ok : check C588.data C588.cert (st0 C588.data) = true := by decide +kernel

/-- **No set of squarefree semiprimes that are all `≤ 588` has reciprocal sum `1`.** -/
theorem no_solution_le_588 (T : Finset ℕ) (hsp : ∀ n ∈ T, IsSP n) (hle : ∀ n ∈ T, n ≤ 588)
    (h1 : recipSum T = 1) : False :=
  no_solution data588_valid cert588_ok T hsp hle h1

/-- Every solution has an element `≥ 589`. -/
theorem exists_ge_589 (T : Finset ℕ) (hsp : ∀ n ∈ T, IsSP n) (h1 : recipSum T = 1) :
    ∃ n ∈ T, 589 ≤ n := by
  by_contra h
  simp only [not_exists, not_and, not_le] at h
  exact no_solution_le_588 T hsp (fun n hn => by have := h n hn; omega) h1

/-! ### Existence: a solution with largest element `589` -/

/-- The 53-element solution. -/
def T589 : Finset ℕ :=
  {6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 65, 69, 77, 82, 85, 91,
   93, 95, 106, 118, 119, 123, 129, 143, 145, 155, 159, 161, 187, 203, 213, 247, 265, 287, 295,
   299, 341, 355, 403, 413, 473, 493, 497, 559, 583, 589}

/-- The factorizations `n = p * q` of the elements of `T589`. -/
def T589pairs : List (ℕ × ℕ) :=
  [(2, 3), (2, 5), (2, 7), (3, 5), (3, 7), (2, 11), (2, 13), (3, 11), (2, 17), (5, 7), (2, 19),
   (3, 13), (2, 23), (3, 17), (5, 11), (3, 19), (2, 29), (5, 13), (3, 23), (7, 11), (2, 41),
   (5, 17), (7, 13), (3, 31), (5, 19), (2, 53), (2, 59), (7, 17), (3, 41), (3, 43), (11, 13),
   (5, 29), (5, 31), (3, 53), (7, 23), (11, 17), (7, 29), (3, 71), (13, 19), (5, 53), (7, 41),
   (5, 59), (13, 23), (11, 31), (5, 71), (13, 31), (7, 59), (11, 43), (17, 29), (7, 71),
   (13, 43), (11, 53), (19, 31)]

theorem T589_eq_pairs : T589 = (T589pairs.map fun x => x.1 * x.2).toFinset := by decide +kernel

theorem T589_card : T589.card = 53 := by decide +kernel

theorem T589_sp : ∀ n ∈ T589, IsSP n := by
  have h : T589pairs.all (fun x => isPrimeB x.1 && isPrimeB x.2 && decide (x.1 < x.2)) = true := by
    decide +kernel
  intro n hn
  rw [T589_eq_pairs, List.mem_toFinset, List.mem_map] at hn
  obtain ⟨⟨p, q⟩, hx, rfl⟩ := hn
  rw [List.all_eq_true] at h
  have hpq := h _ hx
  simp only [Bool.and_eq_true, isPrimeB_iff, decide_eq_true_eq] at hpq
  exact ⟨p, q, hpq.1.1, hpq.1.2, hpq.2, rfl⟩

/-- `∑_{n ∈ T589} 1/n = 1`, checked through the scaled sum with `D = ∏_{p ≤ 294} p`. -/
theorem T589_sum : recipSum T589 = 1 := by
  have hdvd : ∀ n ∈ T589, n ∣ C588.data.D := by decide +kernel
  have hpos : ∀ n ∈ T589, 0 < n := by decide +kernel
  have hs : ∑ n ∈ T589, C588.data.D / n = C588.data.D := by decide +kernel
  have hD : (C588.data.D : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by decide +kernel)
  have h := sum_scaled_eq hpos hdvd
  rw [hs] at h
  apply mul_left_cancel₀ hD
  rw [mul_one]
  exact h.symm

theorem T589_mem : 589 ∈ T589 := by decide +kernel

theorem T589_le : ∀ n ∈ T589, n ≤ 589 := by decide +kernel

theorem T589_max : T589.max' ⟨589, T589_mem⟩ = 589 :=
  le_antisymm (Finset.max'_le _ _ _ T589_le) (Finset.le_max' _ _ T589_mem)

/-! ### The answer -/

/-- **Main theorem.**  The least possible largest element of a nonempty finite set `T` of
squarefree semiprimes with `∑_{n ∈ T} 1/n = 1` is `589`. -/
theorem isLeast_589 :
    IsLeast {m : ℕ | ∃ T : Finset ℕ, ∃ h : T.Nonempty,
      (∀ n ∈ T, IsSP n) ∧ recipSum T = 1 ∧ T.max' h = m} 589 := by
  refine ⟨⟨T589, ⟨589, T589_mem⟩, T589_sp, T589_sum, T589_max⟩, ?_⟩
  rintro m ⟨T, hne, hsp, h1, rfl⟩
  by_contra hlt
  rw [not_le] at hlt
  exact no_solution_le_588 T hsp (fun n hn => by have := T.le_max' n hn; omega) h1

end SemiprimeEgypt.MaxDen
