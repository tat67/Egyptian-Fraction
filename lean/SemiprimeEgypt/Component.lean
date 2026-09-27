/-
The component with one big–big edge (README47 §4, case `b = 1`).

Two big primes `P₁ ≠ P₂` joined by the edge `P₁P₂`, with small attachment sets `A₁, A₂`.
Put `bᵢ = ∏ Aᵢ`, `aᵢ = n(Aᵢ) = Σ_{q∈Aᵢ} bᵢ/q` and let
`Z = Σ_{q∈A₁} 1/(qP₁) + Σ_{q∈A₂} 1/(qP₂) + 1/(P₁P₂)` be the value of the component.

* `comp_value`: `Z · b₁b₂ · P₁P₂ = a₁b₂P₂ + a₂b₁P₁ + b₁b₂ =: W`.
* `comp_local_iff`: (*) at `P₁` and `P₂` (`P₁ ∣ a₁P₂ + b₁`, `P₂ ∣ a₂P₁ + b₂`) iff `P₁P₂ ∣ W`,
  i.e. iff `t = Z b₁ b₂` is an integer.
* `comp_divisor_eq`: for `t ≠ 0`,
  `(tP₁ - a₁b₂)(tP₂ - a₂b₁) = b₁b₂(t + a₁a₂)  ↔  tP₁P₂ = W`.
* `comp_enum`: if `tP₁P₂ = W` with `t > 0`, then `X = tP₁ - a₁b₂` is a positive divisor of
  `N = b₁b₂(t + a₁a₂)`, `P₁ = (X + a₁b₂)/t` and `P₂ = (N/X + a₂b₁)/t`; so for fixed `(A₁,A₂,t)`
  the pair `(P₁,P₂)` is determined by a divisor of `N` (a finite enumeration).
* `comp_of_divisor`: conversely every divisor `X` satisfying the divisibility conditions gives a
  pair with `tP₁P₂ = W`, i.e. a component of value exactly `t / (b₁b₂)`.
-/
import SemiprimeEgypt.Decomp

open Finset

namespace SemiprimeEgypt

/-- `n(A ∪ {P}) = P · n(A) + ∏ A`. -/
lemma nA_insert {A : Finset ℕ} {P : ℕ} (hPA : P ∉ A) (hP : 0 < P) :
    nA (insert P A) = P * nA A + ∏ q ∈ A, q := by
  rw [nA, nA, Finset.prod_insert hPA, Finset.sum_insert hPA, Nat.mul_div_cancel_left _ hP,
    Finset.mul_sum, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun q hq => ?_
  exact Nat.mul_div_assoc P (Finset.dvd_prod_of_mem _ hq)

/-- `Σ_{q∈A} 1/q = n(A) / ∏ A`. -/
lemma sum_inv_eq_nA_div (A : Finset ℕ) (hA : ∀ q ∈ A, 0 < q) :
    ∑ q ∈ A, (1 : ℚ) / q = (nA A : ℚ) / ∏ q ∈ A, (q : ℚ) := by
  have hprod : (∏ q ∈ A, (q : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun q hq => by exact_mod_cast (hA q hq).ne'
  rw [nA, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (hA q hq).ne'
  rw [Nat.cast_div (Finset.dvd_prod_of_mem _ hq) hq0, Nat.cast_prod]
  field_simp

section
variable (A₁ A₂ : Finset ℕ) (P₁ P₂ : ℕ)

/-- The value of the component. -/
def compVal : ℚ :=
  ∑ q ∈ A₁, (1 : ℚ) / (q * P₁) + ∑ q ∈ A₂, (1 : ℚ) / (q * P₂) + 1 / (P₁ * P₂)

/-- `W = a₁b₂P₂ + a₂b₁P₁ + b₁b₂`. -/
def compW : ℕ :=
  nA A₁ * (∏ q ∈ A₂, q) * P₂ + nA A₂ * (∏ q ∈ A₁, q) * P₁ + (∏ q ∈ A₁, q) * ∏ q ∈ A₂, q

/-- `N = b₁b₂(t + a₁a₂)`. -/
def compN (t : ℕ) : ℕ := (∏ q ∈ A₁, q) * (∏ q ∈ A₂, q) * (t + nA A₁ * nA A₂)

end

/-- **Value of the component.**  `Z · b₁ b₂ · P₁ P₂ = W`. -/
theorem comp_value {A₁ A₂ : Finset ℕ} (h₁ : ∀ q ∈ A₁, 0 < q) (h₂ : ∀ q ∈ A₂, 0 < q)
    {P₁ P₂ : ℕ} (hP₁ : 0 < P₁) (hP₂ : 0 < P₂) :
    compVal A₁ A₂ P₁ P₂ * (∏ q ∈ A₁, (q : ℚ)) * (∏ q ∈ A₂, (q : ℚ)) * P₁ * P₂ =
      (compW A₁ A₂ P₁ P₂ : ℚ) := by
  have e₁ : ∑ q ∈ A₁, (1 : ℚ) / (q * P₁) = (1 / (P₁ : ℚ)) * ∑ q ∈ A₁, (1 : ℚ) / q := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [one_div_mul_one_div, mul_comm]
  have e₂ : ∑ q ∈ A₂, (1 : ℚ) / (q * P₂) = (1 / (P₂ : ℚ)) * ∑ q ∈ A₂, (1 : ℚ) / q := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [one_div_mul_one_div, mul_comm]
  have hb₁ : (∏ q ∈ A₁, (q : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun q hq => by exact_mod_cast (h₁ q hq).ne'
  have hb₂ : (∏ q ∈ A₂, (q : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun q hq => by exact_mod_cast (h₂ q hq).ne'
  have hP₁' : (P₁ : ℚ) ≠ 0 := by exact_mod_cast hP₁.ne'
  have hP₂' : (P₂ : ℚ) ≠ 0 := by exact_mod_cast hP₂.ne'
  rw [compVal, e₁, e₂, sum_inv_eq_nA_div A₁ h₁, sum_inv_eq_nA_div A₂ h₂, compW]
  push_cast
  field_simp

/-- **(*) at `P₁`, `P₂` ⟺ `P₁P₂ ∣ W`** (i.e. `t = Z b₁ b₂ ∈ ℤ`), for distinct primes `P₁, P₂`
that divide neither `b₁` nor `b₂`. -/
theorem comp_local_iff {A₁ A₂ : Finset ℕ} {P₁ P₂ : ℕ} (hP₁ : P₁.Prime) (hP₂ : P₂.Prime)
    (hne : P₁ ≠ P₂) (h₁₂ : ¬ P₁ ∣ ∏ q ∈ A₂, q) (h₂₁ : ¬ P₂ ∣ ∏ q ∈ A₁, q) :
    (P₁ ∣ nA A₁ * P₂ + ∏ q ∈ A₁, q ∧ P₂ ∣ nA A₂ * P₁ + ∏ q ∈ A₂, q) ↔
      P₁ * P₂ ∣ compW A₁ A₂ P₁ P₂ := by
  set a₁ := nA A₁; set a₂ := nA A₂; set b₁ := ∏ q ∈ A₁, q; set b₂ := ∏ q ∈ A₂, q
  have eW₁ : compW A₁ A₂ P₁ P₂ = b₂ * (a₁ * P₂ + b₁) + P₁ * (a₂ * b₁) := by
    simp only [compW]; ring
  have eW₂ : compW A₁ A₂ P₁ P₂ = b₁ * (a₂ * P₁ + b₂) + P₂ * (a₁ * b₂) := by
    simp only [compW]; ring
  have hcop : Nat.Coprime P₁ P₂ := (Nat.coprime_primes hP₁ hP₂).2 hne
  constructor
  · rintro ⟨d₁, d₂⟩
    apply hcop.mul_dvd_of_dvd_of_dvd
    · rw [eW₁]; exact dvd_add (dvd_mul_of_dvd_right d₁ _) (dvd_mul_right _ _)
    · rw [eW₂]; exact dvd_add (dvd_mul_of_dvd_right d₂ _) (dvd_mul_right _ _)
  · intro h
    have d₁ : P₁ ∣ compW A₁ A₂ P₁ P₂ := dvd_trans (dvd_mul_right _ _) h
    have d₂ : P₂ ∣ compW A₁ A₂ P₁ P₂ := dvd_trans (dvd_mul_left _ _) h
    rw [eW₁, Nat.dvd_add_left (dvd_mul_right _ _)] at d₁
    rw [eW₂, Nat.dvd_add_left (dvd_mul_right _ _)] at d₂
    refine ⟨?_, ?_⟩
    · rcases (Nat.Prime.dvd_mul hP₁).1 d₁ with h' | h'
      · exact absurd h' h₁₂
      · exact h'
    · rcases (Nat.Prime.dvd_mul hP₂).1 d₂ with h' | h'
      · exact absurd h' h₂₁
      · exact h'

/-- **The divisor equation.**  For `t ≠ 0`:
`(tP₁ - a₁b₂)(tP₂ - a₂b₁) = b₁b₂(t + a₁a₂) ↔ tP₁P₂ = a₁b₂P₂ + a₂b₁P₁ + b₁b₂`. -/
theorem comp_divisor_eq (t P₁ P₂ a₁ a₂ b₁ b₂ : ℤ) (ht : t ≠ 0) :
    (t * P₁ - a₁ * b₂) * (t * P₂ - a₂ * b₁) = b₁ * b₂ * (t + a₁ * a₂) ↔
      t * P₁ * P₂ = a₁ * b₂ * P₂ + a₂ * b₁ * P₁ + b₁ * b₂ := by
  constructor
  · intro h
    have h' : t * (t * P₁ * P₂ - (a₁ * b₂ * P₂ + a₂ * b₁ * P₁ + b₁ * b₂)) = 0 := by
      linear_combination h
    rcases mul_eq_zero.1 h' with h'' | h''
    · exact absurd h'' ht
    · linear_combination h''
  · intro h
    linear_combination t * h

/-- Arithmetic core of `comp_enum`, over plain natural numbers. -/
theorem enum_core {t P₁ P₂ a₁ a₂ b₁ b₂ : ℕ} (ht : 0 < t) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hP₁ : 0 < P₁) (hP₂ : 0 < P₂)
    (hW : t * P₁ * P₂ = a₁ * b₂ * P₂ + a₂ * b₁ * P₁ + b₁ * b₂) :
    0 < t * P₁ - a₁ * b₂ ∧ t * P₁ - a₁ * b₂ ∣ b₁ * b₂ * (t + a₁ * a₂) ∧
      t ∣ (t * P₁ - a₁ * b₂) + a₁ * b₂ ∧
      t ∣ b₁ * b₂ * (t + a₁ * a₂) / (t * P₁ - a₁ * b₂) + a₂ * b₁ ∧
      P₁ = ((t * P₁ - a₁ * b₂) + a₁ * b₂) / t ∧
      P₂ = (b₁ * b₂ * (t + a₁ * a₂) / (t * P₁ - a₁ * b₂) + a₂ * b₁) / t := by
  have hx : a₁ * b₂ < t * P₁ := by
    have : P₂ * (a₁ * b₂) < P₂ * (t * P₁) := by
      have hpos : 0 < a₂ * b₁ * P₁ + b₁ * b₂ := by positivity
      nlinarith
    exact lt_of_mul_lt_mul_left this (Nat.zero_le _)
  have hy : a₂ * b₁ < t * P₂ := by
    have : P₁ * (a₂ * b₁) < P₁ * (t * P₂) := by
      have hpos : 0 < a₁ * b₂ * P₂ + b₁ * b₂ := by positivity
      nlinarith
    exact lt_of_mul_lt_mul_left this (Nat.zero_le _)
  obtain ⟨X, hX⟩ : ∃ X, t * P₁ = X + a₁ * b₂ := ⟨t * P₁ - a₁ * b₂, by omega⟩
  obtain ⟨Y, hY⟩ : ∃ Y, t * P₂ = Y + a₂ * b₁ := ⟨t * P₂ - a₂ * b₁, by omega⟩
  have hXe : t * P₁ - a₁ * b₂ = X := by omega
  rw [hXe]
  have hXY : X * Y = b₁ * b₂ * (t + a₁ * a₂) := by
    have hz := (comp_divisor_eq (t : ℤ) P₁ P₂ a₁ a₂ b₁ b₂ (by exact_mod_cast ht.ne')).2
      (by exact_mod_cast hW)
    have hX' : (X : ℤ) = t * P₁ - a₁ * b₂ := by
      have := congrArg (fun n : ℕ => (n : ℤ)) hX; push_cast at this; linarith
    have hY' : (Y : ℤ) = t * P₂ - a₂ * b₁ := by
      have := congrArg (fun n : ℕ => (n : ℤ)) hY; push_cast at this; linarith
    have : (X : ℤ) * Y = b₁ * b₂ * (t + a₁ * a₂) := by rw [hX', hY']; exact hz
    exact_mod_cast this
  have hXpos : 0 < X := by omega
  have hNX : b₁ * b₂ * (t + a₁ * a₂) / X = Y := by
    rw [← hXY, Nat.mul_div_cancel_left _ hXpos]
  rw [hNX, ← hX, ← hY]
  refine ⟨hXpos, ⟨Y, hXY.symm⟩, dvd_mul_right _ _, dvd_mul_right _ _, ?_, ?_⟩
  · rw [Nat.mul_div_cancel_left _ ht]
  · rw [Nat.mul_div_cancel_left _ ht]

/-- **Finite enumeration.**  If `tP₁P₂ = W` with `t > 0` (and `b₁, b₂ > 0`), then
`X = tP₁ - a₁b₂` is a positive divisor of `N = b₁b₂(t + a₁a₂)`, and
`P₁ = (X + a₁b₂)/t`, `P₂ = (N/X + a₂b₁)/t`, with both divisions exact. -/
theorem comp_enum {A₁ A₂ : Finset ℕ} {P₁ P₂ t : ℕ} (ht : 0 < t)
    (hb₁ : 0 < ∏ q ∈ A₁, q) (hb₂ : 0 < ∏ q ∈ A₂, q) (hP₁ : 0 < P₁) (hP₂ : 0 < P₂)
    (hW : t * P₁ * P₂ = compW A₁ A₂ P₁ P₂) :
    0 < t * P₁ - nA A₁ * ∏ q ∈ A₂, q ∧
      t * P₁ - nA A₁ * ∏ q ∈ A₂, q ∣ compN A₁ A₂ t ∧
      t ∣ (t * P₁ - nA A₁ * ∏ q ∈ A₂, q) + nA A₁ * ∏ q ∈ A₂, q ∧
      t ∣ compN A₁ A₂ t / (t * P₁ - nA A₁ * ∏ q ∈ A₂, q) + nA A₂ * ∏ q ∈ A₁, q ∧
      P₁ = ((t * P₁ - nA A₁ * ∏ q ∈ A₂, q) + nA A₁ * ∏ q ∈ A₂, q) / t ∧
      P₂ = (compN A₁ A₂ t / (t * P₁ - nA A₁ * ∏ q ∈ A₂, q) + nA A₂ * ∏ q ∈ A₁, q) / t :=
  enum_core ht hb₁ hb₂ hP₁ hP₂ hW

/-- Arithmetic core of `comp_of_divisor`. -/
theorem of_divisor_core {t X Y P₁ P₂ a₁ a₂ b₁ b₂ : ℕ} (ht : 0 < t)
    (hXY : X * Y = b₁ * b₂ * (t + a₁ * a₂)) (e₁ : t * P₁ = X + a₁ * b₂)
    (e₂ : t * P₂ = Y + a₂ * b₁) :
    t * P₁ * P₂ = a₁ * b₂ * P₂ + a₂ * b₁ * P₁ + b₁ * b₂ := by
  have key := (comp_divisor_eq (t : ℤ) P₁ P₂ a₁ a₂ b₁ b₂ (by exact_mod_cast ht.ne')).1 (by
    have e₁' : (t : ℤ) * P₁ - a₁ * b₂ = X := by
      have := congrArg (fun n : ℕ => (n : ℤ)) e₁; push_cast at this; linarith
    have e₂' : (t : ℤ) * P₂ - a₂ * b₁ = Y := by
      have := congrArg (fun n : ℕ => (n : ℤ)) e₂; push_cast at this; linarith
    rw [e₁', e₂']; exact_mod_cast hXY)
  exact_mod_cast key

/-- **Soundness of the enumeration.**  Conversely, if `X > 0`, `X ∣ N`, and `t > 0` divides
`X + a₁b₂` and `N/X + a₂b₁`, then `P₁ = (X + a₁b₂)/t`, `P₂ = (N/X + a₂b₁)/t` satisfy
`tP₁P₂ = W`, so the component has value exactly `t/(b₁b₂)`. -/
theorem comp_of_divisor {A₁ A₂ : Finset ℕ} {t X : ℕ} (ht : 0 < t)
    (hXN : X ∣ compN A₁ A₂ t) (h₁ : t ∣ X + nA A₁ * ∏ q ∈ A₂, q)
    (h₂ : t ∣ compN A₁ A₂ t / X + nA A₂ * ∏ q ∈ A₁, q) :
    t * ((X + nA A₁ * ∏ q ∈ A₂, q) / t) * ((compN A₁ A₂ t / X + nA A₂ * ∏ q ∈ A₁, q) / t) =
      compW A₁ A₂ ((X + nA A₁ * ∏ q ∈ A₂, q) / t)
        ((compN A₁ A₂ t / X + nA A₂ * ∏ q ∈ A₁, q) / t) :=
  of_divisor_core ht (Nat.mul_div_cancel' hXN) (Nat.mul_div_cancel' h₁) (Nat.mul_div_cancel' h₂)

/-- **Finiteness of the component enumeration.**  For fixed `A₁, A₂` (sets of positive
integers) and `t > 0`, only finitely many pairs `(P₁, P₂)` of positive integers satisfy
`tP₁P₂ = W`: they satisfy `P₁ ≤ N + a₁b₂` and `P₂ ≤ N + a₂b₁`. -/
theorem comp_pairs_finite {A₁ A₂ : Finset ℕ} (h₁ : ∀ q ∈ A₁, 0 < q) (h₂ : ∀ q ∈ A₂, 0 < q)
    {t : ℕ} (ht : 0 < t) :
    {x : ℕ × ℕ | 0 < x.1 ∧ 0 < x.2 ∧ t * x.1 * x.2 = compW A₁ A₂ x.1 x.2}.Finite := by
  have hb₁ : 0 < ∏ q ∈ A₁, q := Finset.prod_pos h₁
  have hb₂ : 0 < ∏ q ∈ A₂, q := Finset.prod_pos h₂
  have hN : 0 < compN A₁ A₂ t := by
    rw [compN]; exact Nat.mul_pos (Nat.mul_pos hb₁ hb₂) (by omega)
  apply Set.Finite.subset ((Set.finite_Iic (compN A₁ A₂ t + nA A₁ * ∏ q ∈ A₂, q)).prod
    (Set.finite_Iic (compN A₁ A₂ t + nA A₂ * ∏ q ∈ A₁, q)))
  rintro ⟨P₁, P₂⟩ ⟨hP₁, hP₂, hW⟩
  dsimp only at hP₁ hP₂ hW
  obtain ⟨hX, hXN, -, -, e₁, e₂⟩ := comp_enum ht hb₁ hb₂ hP₁ hP₂ hW
  have hXle := Nat.le_of_dvd hN hXN
  refine ⟨?_, ?_⟩
  · change P₁ ≤ _
    rw [e₁]
    exact le_trans (Nat.div_le_self _ _) (by omega)
  · change P₂ ≤ _
    rw [e₂]
    exact le_trans (Nat.div_le_self _ _) (by
      have := Nat.div_le_self (compN A₁ A₂ t) (t * P₁ - nA A₁ * ∏ q ∈ A₂, q)
      omega)

end SemiprimeEgypt
