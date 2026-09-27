/-
Bounds on reciprocal sums: an exchange lemma, the enumeration of the squarefree semiprimes
up to 158, and the numerical facts H_35 < 1 - 1757/79000, H_37 < 1 < H_38, H_46, H_47 < 2.
-/
import SemiprimeEgypt.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity

open Finset

namespace SemiprimeEgypt

/-! ### Exchange lemma -/

lemma recipSum_nonneg (T : Finset ℕ) : 0 ≤ recipSum T :=
  Finset.sum_nonneg fun n _ => by positivity

lemma recipSum_union {A B : Finset ℕ} (h : Disjoint A B) :
    recipSum (A ∪ B) = recipSum A + recipSum B := by
  simp [recipSum, Finset.sum_union h]

lemma recipSum_mono {A B : Finset ℕ} (h : A ⊆ B) : recipSum A ≤ recipSum B :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun n _ _ => by positivity

lemma recipSum_empty : recipSum ∅ = 0 := by simp [recipSum]

/-- **Exchange lemma.**  Let `A` be a finite set of positive integers `≤ M` containing every
element of `Q` that is `≤ M`.  Then any finite subset `T` of `Q` with `|T| ≤ |A|` has
reciprocal sum at most that of `A`.  (Applied with `A` = the `k` smallest elements of `Q`.) -/
theorem recipSum_le_of_initial (Q : ℕ → Prop) (A T : Finset ℕ) (M : ℕ)
    (hA : ∀ a ∈ A, 0 < a ∧ a ≤ M) (hQA : ∀ n, Q n → n ≤ M → n ∈ A)
    (hT : ∀ n ∈ T, Q n) (hcard : T.card ≤ A.card) : recipSum T ≤ recipSum A := by
  have hT' : recipSum T = recipSum (T \ A) + recipSum (T ∩ A) := by
    rw [← recipSum_union (Finset.disjoint_sdiff_inter T A), Finset.sdiff_union_inter]
  have hA' : recipSum A = recipSum (A \ T) + recipSum (T ∩ A) := by
    rw [Finset.inter_comm, ← recipSum_union (Finset.disjoint_sdiff_inter A T),
      Finset.sdiff_union_inter]
  rw [hT', hA']
  have hc : (T \ A).card ≤ (A \ T).card := by
    have h1 := Finset.card_sdiff_add_card_inter T A
    have h2 := Finset.card_sdiff_add_card_inter A T
    rw [Finset.inter_comm] at h2
    omega
  -- elements of T \ A are > M, elements of A \ T are ≤ M
  rcases (T \ A).eq_empty_or_nonempty with he | hne
  · have h0 : recipSum (T \ A) = 0 := by rw [he, recipSum_empty]
    linarith [recipSum_nonneg (A \ T)]
  have hM : 0 < M := by
    obtain ⟨a, ha⟩ : (A \ T).Nonempty := by
      rw [← Finset.card_pos]; exact lt_of_lt_of_le (Finset.card_pos.2 hne) hc
    have := hA a (Finset.mem_sdiff.1 ha).1
    omega
  have hup : recipSum (T \ A) ≤ (T \ A).card * (1 / (M : ℚ)) := by
    rw [recipSum]
    have := Finset.sum_le_card_nsmul (T \ A) (fun n : ℕ => (1 : ℚ) / n) (1 / (M : ℚ)) ?_
    · simpa [nsmul_eq_mul] using this
    intro n hn
    rw [Finset.mem_sdiff] at hn
    have hnM : M < n := by
      by_contra h
      exact hn.2 (hQA n (hT n hn.1) (by omega))
    have hMq : (0 : ℚ) < M := by exact_mod_cast hM
    exact one_div_le_one_div_of_le hMq (by exact_mod_cast hnM.le)
  have hlo : (A \ T).card * (1 / (M : ℚ)) ≤ recipSum (A \ T) := by
    rw [recipSum]
    have := Finset.card_nsmul_le_sum (A \ T) (fun n : ℕ => (1 : ℚ) / n) (1 / (M : ℚ)) ?_
    · simpa [nsmul_eq_mul] using this
    intro a ha
    have := hA a (Finset.mem_sdiff.1 ha).1
    have ha0 : (0 : ℚ) < a := by exact_mod_cast this.1
    exact one_div_le_one_div_of_le ha0 (by exact_mod_cast this.2)
  have hmid : ((T \ A).card : ℚ) * (1 / (M : ℚ)) ≤ (A \ T).card * (1 / (M : ℚ)) := by
    apply mul_le_mul_of_nonneg_right (by exact_mod_cast hc)
    positivity
  linarith

/-! ### The squarefree semiprimes up to 158 -/

/-- The 47 smallest squarefree semiprimes (all of them `≤ 158`). -/
def A47 : Finset ℕ :=
  {6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62, 65, 69, 74, 77, 82,
   85, 86, 87, 91, 93, 94, 95, 106, 111, 115, 118, 119, 122, 123, 129, 133, 134, 141, 142, 143,
   145, 146, 155, 158}

lemma A47_card : A47.card = 47 := by decide

/-- Every squarefree semiprime `≤ 158` is in `A47`. -/
theorem sp_le_158 {n : ℕ} (h : IsSP n) (hn : n ≤ 158) : n ∈ A47 := by
  obtain ⟨p, q, hp, hq, hpq, rfl⟩ := h
  have hp2 := hp.two_le
  have hp12 : p ≤ 12 := by nlinarith
  have hq79 : q ≤ 79 := by nlinarith
  interval_cases p <;> (try norm_num at hp) <;> interval_cases q <;>
    first | omega | (norm_num at hq; done) | decide

/-- Every element of `A47` is a squarefree semiprime. -/
lemma A47_sp : ∀ n ∈ A47, IsSP n ∧ n ≤ 158 := by
  intro n hn
  simp only [A47, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact ⟨⟨2, 3, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨2, 5, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨2, 7, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨3, 5, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨3, 7, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨2, 11, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨2, 13, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨3, 11, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨2, 17, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨5, 7, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨2, 19, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨3, 13, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨2, 23, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨3, 17, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨5, 11, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨3, 19, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨2, 29, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨2, 31, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨5, 13, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨3, 23, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨2, 37, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨7, 11, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨2, 41, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨5, 17, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨2, 43, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨3, 29, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨7, 13, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨3, 31, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨2, 47, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨5, 19, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨2, 53, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨3, 37, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨5, 23, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨2, 59, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨7, 17, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨2, 61, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨3, 41, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨3, 43, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨7, 19, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨2, 67, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨3, 47, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨2, 71, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨11, 13, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨5, 29, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨2, 73, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨5, 31, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨2, 79, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩

/-- The `k` smallest squarefree semiprimes, for `k ≤ 47`, as the elements of `A47` below a
threshold. -/
def Aupto (M : ℕ) : Finset ℕ := A47.filter (· ≤ M)

lemma Aupto_complete {M : ℕ} (hM : M ≤ 158) {n : ℕ} (h : IsSP n) (hn : n ≤ M) :
    n ∈ Aupto M := by
  rw [Aupto, Finset.mem_filter]; exact ⟨sp_le_158 h (le_trans hn hM), hn⟩

lemma Aupto_bound (M : ℕ) : ∀ a ∈ Aupto M, 0 < a ∧ a ≤ M := by
  intro a ha
  rw [Aupto, Finset.mem_filter] at ha
  exact ⟨(A47_sp a ha.1).1.pos, ha.2⟩

/-- Any finite set of squarefree semiprimes with at most `|Aupto M|` elements has reciprocal
sum at most `recipSum (Aupto M)` (for `M ≤ 158`). -/
theorem recipSum_le_Aupto {M : ℕ} (hM : M ≤ 158) (T : Finset ℕ) (hT : ∀ n ∈ T, IsSP n)
    (hc : T.card ≤ (Aupto M).card) : recipSum T ≤ recipSum (Aupto M) :=
  recipSum_le_of_initial IsSP _ T M (Aupto_bound M) (fun _ h hn => Aupto_complete hM h hn) hT hc

-- the thresholds: a_35 = 119, a_37 = 123, a_38 = 129, a_46 = 155, a_47 = 158
lemma card_Aupto_119 : (Aupto 119).card = 35 := by decide
lemma card_Aupto_123 : (Aupto 123).card = 37 := by decide
lemma card_Aupto_129 : (Aupto 129).card = 38 := by decide
lemma card_Aupto_155 : (Aupto 155).card = 46 := by decide
lemma card_Aupto_158 : (Aupto 158).card = 47 := by decide

lemma Aupto_119_eq : Aupto 119 = {6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57,
    58, 62, 65, 69, 74, 77, 82, 85, 86, 87, 91, 93, 94, 95, 106, 111, 115, 118, 119} := by decide
lemma Aupto_123_eq : Aupto 123 = {6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57,
    58, 62, 65, 69, 74, 77, 82, 85, 86, 87, 91, 93, 94, 95, 106, 111, 115, 118, 119, 122,
    123} := by decide
lemma Aupto_129_eq : Aupto 129 = {6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57,
    58, 62, 65, 69, 74, 77, 82, 85, 86, 87, 91, 93, 94, 95, 106, 111, 115, 118, 119, 122,
    123, 129} := by decide
lemma Aupto_155_eq : Aupto 155 = {6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57,
    58, 62, 65, 69, 74, 77, 82, 85, 86, 87, 91, 93, 94, 95, 106, 111, 115, 118, 119, 122,
    123, 129, 133, 134, 141, 142, 143, 145, 146, 155} := by decide
lemma Aupto_158_eq : Aupto 158 = A47 := by decide

/-- `H_35 < 1 - 1757/79000` (used in the star-size lemma; `H_35 ≈ 0.977366`). -/
lemma H35_val : recipSum (Aupto 119) < 1 - 1757 / 79000 := by
  rw [Aupto_119_eq]; unfold recipSum; norm_num [Finset.sum_insert]
/-- `H_37 < 1` (`H_37 ≈ 0.9936`). -/
lemma H37_lt_one : recipSum (Aupto 123) < 1 := by
  rw [Aupto_123_eq]; unfold recipSum; norm_num [Finset.sum_insert]
/-- `H_38 > 1` (`H_38 ≈ 1.0014`). -/
lemma H38_gt_one : 1 < recipSum (Aupto 129) := by
  rw [Aupto_129_eq]; unfold recipSum; norm_num [Finset.sum_insert]
/-- `H_46 < 2` (`H_46 ≈ 1.0578`). -/
lemma H46_lt_two : recipSum (Aupto 155) < 2 := by
  rw [Aupto_155_eq]; unfold recipSum; norm_num [Finset.sum_insert]
/-- `H_47 < 2` (`H_47 ≈ 1.0641`). -/
lemma H47_lt_two : recipSum (Aupto 158) < 2 := by
  rw [Aupto_158_eq, A47]; unfold recipSum; norm_num [Finset.sum_insert]

/-! ### Consequences -/

lemma recipSum_pos {T : Finset ℕ} (hT : ∀ n ∈ T, IsSP n) (hne : T.Nonempty) :
    0 < recipSum T := by
  obtain ⟨n, hn⟩ := hne
  have hpos : ∀ m ∈ T, (0 : ℚ) ≤ 1 / m := fun m _ => by positivity
  have h1 : (0 : ℚ) < 1 / n := by have := (hT n hn).pos; positivity
  exact lt_of_lt_of_le h1 (Finset.single_le_sum hpos hn)

/-- For at most 47 squarefree semiprimes the reciprocal sum is `< 2`. -/
theorem recipSum_lt_two {T : Finset ℕ} (hT : ∀ n ∈ T, IsSP n) (hc : T.card ≤ 47) :
    recipSum T < 2 := by
  have := recipSum_le_Aupto le_rfl T hT (by rw [card_Aupto_158]; exact hc)
  exact lt_of_le_of_lt this H47_lt_two

/-- An integral reciprocal sum of at most 47 squarefree semiprimes equals `1`. -/
theorem recipSum_eq_one_of_integral {T : Finset ℕ} (hT : ∀ n ∈ T, IsSP n) (hne : T.Nonempty)
    (hc : T.card ≤ 47) (hz : ∃ z : ℤ, recipSum T = z) : recipSum T = 1 := by
  obtain ⟨z, hz⟩ := hz
  have h0 := recipSum_pos hT hne
  have h2 := recipSum_lt_two hT hc
  rw [hz] at h0 h2 ⊢
  have hz1 : 0 < z := by exact_mod_cast h0
  have hz2 : z < 2 := by exact_mod_cast h2
  have : z = 1 := by omega
  rw [this]; norm_num

/-- A set of squarefree semiprimes with reciprocal sum `1` has at least 38 elements. -/
theorem card_ge_38 {T : Finset ℕ} (hT : ∀ n ∈ T, IsSP n) (h1 : recipSum T = 1) :
    38 ≤ T.card := by
  by_contra h
  have := recipSum_le_Aupto (M := 123) (by norm_num) T hT (by rw [card_Aupto_123]; omega)
  linarith [H37_lt_one]

/-- Sharpness of the bound 38: the 38 smallest squarefree semiprimes have sum `> 1`. -/
theorem H38_sharp : 1 < recipSum (Aupto 129) ∧ (Aupto 129).card = 38 :=
  ⟨H38_gt_one, card_Aupto_129⟩

end SemiprimeEgypt
