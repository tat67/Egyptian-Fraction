/-
# Primitive Egyptian fractions of 1: the smallest possible largest element is 413

A finite set `T` of positive integers is *primitive* if no element divides another.

* `one_only`: `{1}` is primitive with `∑ 1/n = 1`, and it is the only such set containing `1`.
  All other sets considered below therefore lie in `{2, 3, …}`.
* `isLeast_413`: among the nonempty primitive `T ⊆ {2, 3, …}` with `∑_{n ∈ T} 1/n = 1`, the least
  possible `max T` is `413 = 7 · 59`.
  - existence: the 53-element set `T413`;
  - minimality: `no_solution_le_412`, from the generic soundness theorem `no_solution`
    (`PrimCheck.lean`) and the certificate of `PrimCert412_*.lean`, checked by the kernel in
    the generated files `PrimSub412_*.lean` and assembled in `PrimRoot412.lean`.
-/
import SemiprimeEgypt.PrimRoot412

open Finset

namespace SemiprimeEgypt.Prim

/-! ### The trivial solution `{1}` -/

theorem one_primitive : Primitive {1} ∧ recipSum {1} = 1 := by
  refine ⟨?_, ?_⟩
  · intro a ha b hb _
    rw [Finset.mem_singleton] at ha hb
    rw [ha, hb]
  · simp [recipSum]

/-- A primitive set containing `1` is `{1}`. -/
theorem eq_one_of_one_mem {T : Finset ℕ} (hprim : Primitive T) (h1 : 1 ∈ T) : T = {1} := by
  ext n
  rw [Finset.mem_singleton]
  constructor
  · intro hn; exact (hprim 1 h1 n hn (one_dvd n)).symm
  · rintro rfl; exact h1

/-! ### Minimality: nothing with all elements `≤ 412` -/

/-- The data for `B = 412` pass the Boolean validity test. -/
theorem data412_validB : validB C412.data = true := by decide +kernel

theorem data412_valid : Valid C412.data := valid_of_validB C412.data data412_validB

/-- **No primitive set of integers in `[2, 412]` has reciprocal sum `1`.** -/
theorem no_solution_le_412 (T : Finset ℕ) (h2 : ∀ n ∈ T, 2 ≤ n) (hle : ∀ n ∈ T, n ≤ 412)
    (hprim : Primitive T) (h1 : recipSum T = 1) : False :=
  no_solution data412_valid C412.cert_ok T h2 hle hprim h1

/-- Every primitive `T ⊆ {2, 3, …}` with `∑ 1/n = 1` has an element `≥ 413`. -/
theorem exists_ge_413 (T : Finset ℕ) (h2 : ∀ n ∈ T, 2 ≤ n) (hprim : Primitive T)
    (h1 : recipSum T = 1) : ∃ n ∈ T, 413 ≤ n := by
  by_contra h
  simp only [not_exists, not_and, not_le] at h
  exact no_solution_le_412 T h2 (fun n hn => by have := h n hn; omega) hprim h1

/-! ### Existence: a primitive set with largest element `413` -/

/-- The 53-element solution (two of its elements, `148 = 4·37` and `188 = 4·47`, are not
squarefree semiprimes). -/
def T413 : Finset ℕ :=
  {6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 57, 58, 62, 65, 69, 77, 82, 85, 87, 91,
   95, 111, 115, 118, 119, 123, 133, 141, 143, 148, 155, 185, 187, 188, 203, 209, 217, 221, 235,
   247, 259, 287, 295, 299, 319, 323, 391, 403, 407, 413}

theorem T413_card : T413.card = 53 := by decide +kernel

theorem T413_two : ∀ n ∈ T413, 2 ≤ n := by decide +kernel

theorem T413_primitive : Primitive T413 := by
  unfold Primitive; decide +kernel

theorem T413_sum : recipSum T413 = 1 := by
  have hdvd : ∀ n ∈ T413, n ∣ C412.data.D := by decide +kernel
  have hpos : ∀ n ∈ T413, 0 < n := by decide +kernel
  have hs : ∑ n ∈ T413, C412.data.D / n = C412.data.D := by decide +kernel
  have hD : (C412.data.D : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by decide +kernel)
  have h := SemiprimeEgypt.MaxDen.sum_scaled_eq hpos hdvd
  rw [hs] at h
  apply mul_left_cancel₀ hD
  rw [mul_one]
  exact h.symm

theorem T413_mem : 413 ∈ T413 := by decide +kernel

theorem T413_le : ∀ n ∈ T413, n ≤ 413 := by decide +kernel

theorem T413_max : T413.max' ⟨413, T413_mem⟩ = 413 :=
  le_antisymm (Finset.max'_le _ _ _ T413_le) (Finset.le_max' _ _ T413_mem)

/-! ### The answer to Q1 -/

/-- **Q1.**  The least possible largest element of a nonempty primitive set `T ⊆ {2, 3, …}`
with `∑_{n ∈ T} 1/n = 1` is `413`. -/
theorem isLeast_413 :
    IsLeast {m : ℕ | ∃ T : Finset ℕ, ∃ h : T.Nonempty,
      (∀ n ∈ T, 2 ≤ n) ∧ Primitive T ∧ recipSum T = 1 ∧ T.max' h = m} 413 := by
  refine ⟨⟨T413, ⟨413, T413_mem⟩, T413_two, T413_primitive, T413_sum, T413_max⟩, ?_⟩
  rintro m ⟨T, hne, h2, hprim, h1, rfl⟩
  by_contra hlt
  rw [not_le] at hlt
  exact no_solution_le_412 T h2 (fun n hn => by have := T.le_max' n hn; omega) hprim h1

/-- Q1 with `1` allowed: then `{1}` is the only set containing `1`, so the question is only
interesting for `T ⊆ {2, 3, …}`; for every other valid set the largest element is `≥ 413`. -/
theorem q1_with_one (T : Finset ℕ) (hpos : ∀ n ∈ T, 0 < n) (hprim : Primitive T)
    (h1 : recipSum T = 1) : T = {1} ∨ ∃ n ∈ T, 413 ≤ n := by
  by_cases h : 1 ∈ T
  · exact Or.inl (eq_one_of_one_mem hprim h)
  · right
    refine exists_ge_413 T (fun n hn => ?_) hprim h1
    have := hpos n hn
    have : n ≠ 1 := fun e => h (e ▸ hn)
    omega

end SemiprimeEgypt.Prim
