/-
# Primitive Egyptian fractions of 1: at least 39 terms

`card_ge_39`: every primitive `T ⊆ {2, 3, …}` with `∑ 1/n = 1` has at least 39 elements;
`card_bounds`: the least number of terms lies in `[39, 46]` (a 46-term example `T46`).

* `|T| ≤ 37`: the Lagrangian bound (`lagrange_bound`, chain cover `lag129`) gives
  `∑ 1/n ≤ 37/129 + W/D < 1`.
* `|T| = 38`: an element `m ≥ 159` would cost `1/129 − 1/m ≥ 1/129 − 1/159`, more than the slack
  `38/129 + W/D − 1`; so `T ⊆ [2, 158]`, which `no_solution_le_412` excludes.
-/
import SemiprimeEgypt.PrimMain
import SemiprimeEgypt.PrimLag129

open Finset

namespace SemiprimeEgypt.Prim

theorem lag129_validB : lag129.validB = true := by decide +kernel

theorem lag129_valid : lag129.Valid := LData.valid_of_validB lag129 lag129_validB

theorem lag129_A : lag129.A = 129 := rfl
theorem lag129_D : lag129.D = 591133442051411133755680800 := rfl

/-- The elements of a primitive solution are not prime powers (in the sense of `ppB'`). -/
theorem ppB'_false {T : Finset ℕ} (h2 : ∀ n ∈ T, 2 ≤ n) (hprim : Primitive T)
    (h1 : recipSum T = 1) : ∀ n ∈ T, ppB' lag129.PL n = false := by
  intro n hn
  by_contra h
  rw [Bool.not_eq_false] at h
  obtain ⟨p, k, hp, hk, hpk⟩ := primePow_of_ppB' lag129_valid h
  exact no_primePow (fun m hm => by have := h2 m hm; omega) hprim h1 hp hk (hpk ▸ hn)

/-- **Every primitive `T ⊆ {2, 3, …}` with `∑ 1/n = 1` has at least 39 elements.** -/
theorem card_ge_39 (T : Finset ℕ) (h2 : ∀ n ∈ T, 2 ≤ n) (hprim : Primitive T)
    (h1 : recipSum T = 1) : 39 ≤ T.card := by
  by_contra hlt
  rw [not_le] at hlt
  have hcard : (T.card : ℚ) ≤ 38 := by exact_mod_cast Nat.lt_succ_iff.1 hlt
  have hpp := ppB'_false h2 hprim h1
  by_cases hbig : ∃ m ∈ T, 159 ≤ m
  · obtain ⟨m, hm, hm159⟩ := hbig
    have hb := lagrange_bound lag129_valid hprim h2 hpp m (Or.inl hm)
      (Or.inl (by rw [lag129_A]; omega))
    rw [h1, ite_eq_right (by omega), lag129_A, lag129_D, lag129_W] at hb
    have hm' : 1 / (m : ℚ) ≤ 1 / 159 := by
      have : (159 : ℚ) ≤ m := by exact_mod_cast hm159
      gcongr
    have key : (38 : ℚ) / 129 + (417855082721622096231571545 : ℚ) / 591133442051411133755680800 - (1 / 129 - 1 / 159) < 1 := by norm_num
    have : (T.card : ℚ) / 129 ≤ 38 / 129 := by linarith
    linarith
  · simp only [not_exists, not_and, not_le] at hbig
    exact no_solution_le_412 T h2 (fun n hn => by have := hbig n hn; omega) hprim h1

/-! ### An example with 47 terms (squarefree semiprimes form a primitive set) -/

/-- A 47-term representation by squarefree semiprimes (Watanabe; `solutions47.txt`, #1). -/
def T47 : Finset ℕ :=
  {6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62, 65, 69, 74, 77, 82, 85,
   87, 91, 93, 95, 111, 115, 119, 123, 133, 143, 145, 155, 203, 219, 221, 287, 299, 391, 481,
   1299, 2117, 16021, 31609}

theorem T47_card : T47.card = 47 := by decide +kernel

theorem T47_two : ∀ n ∈ T47, 2 ≤ n := by decide +kernel

theorem T47_primitive : Primitive T47 := by
  unfold Primitive; decide +kernel

theorem T47_sum : recipSum T47 = 1 := by
  have hdvd : ∀ n ∈ T47, n ∣ 9617046579831580890 := by decide +kernel
  have hpos : ∀ n ∈ T47, 0 < n := by decide +kernel
  have hs : ∑ n ∈ T47, 9617046579831580890 / n = 9617046579831580890 := by decide +kernel
  have h := SemiprimeEgypt.MaxDen.sum_scaled_eq hpos hdvd
  rw [hs] at h
  have hD : ((9617046579831580890 : ℕ) : ℚ) ≠ 0 := by norm_num
  apply mul_left_cancel₀ hD
  rw [mul_one]
  exact h.symm

/-! ### An example with 46 terms (primitive, not all squarefree semiprimes) -/

/-- A 46-term primitive representation of `1` (found with CP-SAT; `575 = 5²·23` and
`925 = 5²·37` form a pair at 5-adic level 2, since `1/23 + 1/37 ≡ 0 (mod 5)`). -/
def T46 : Finset ℕ :=
  {6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62, 65, 69, 74, 77, 82, 85,
   86, 91, 93, 95, 111, 118, 119, 123, 129, 133, 145, 155, 187, 203, 253, 287, 407, 493, 575, 925,
   1357, 2537}

theorem T46_card : T46.card = 46 := by decide +kernel

theorem T46_two : ∀ n ∈ T46, 2 ≤ n := by decide +kernel

theorem T46_primitive : Primitive T46 := by
  unfold Primitive; decide +kernel

theorem T46_sum : recipSum T46 = 1 := by
  have hdvd : ∀ n ∈ T46, n ∣ 3859414592842658850 := by decide +kernel
  have hpos : ∀ n ∈ T46, 0 < n := by decide +kernel
  have hs : ∑ n ∈ T46, 3859414592842658850 / n = 3859414592842658850 := by decide +kernel
  have h := SemiprimeEgypt.MaxDen.sum_scaled_eq hpos hdvd
  rw [hs] at h
  have hD : ((3859414592842658850 : ℕ) : ℚ) ≠ 0 := by norm_num
  apply mul_left_cancel₀ hD
  rw [mul_one]
  exact h.symm

/-- **Q2 bounds.**  The least number of terms of a primitive representation of `1` by distinct
unit fractions with denominators `≥ 2` lies between `39` and `46`. -/
theorem card_bounds :
    (∀ T : Finset ℕ, (∀ n ∈ T, 2 ≤ n) → Primitive T → recipSum T = 1 → 39 ≤ T.card) ∧
    (∃ T : Finset ℕ, (∀ n ∈ T, 2 ≤ n) ∧ Primitive T ∧ recipSum T = 1 ∧ T.card = 46) :=
  ⟨card_ge_39, T46, T46_two, T46_primitive, T46_sum, T46_card⟩

end SemiprimeEgypt.Prim
