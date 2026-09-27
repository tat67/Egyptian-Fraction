/-
The two main results, proved *conditionally* on explicit hypotheses that state exactly what
the exhaustive computer searches (`semiprime_reciprocals.cpp`, `semiprime47.cpp`) verified.

No axioms are introduced: `Search46` and `Search47` are ordinary `Prop`s, used as hypotheses.
They are finite statements about the objects enumerated by the programs (cores, shapes,
candidate stars, star covers, divisors of the component equation), and have **not** been
checked in Lean.

* `no_integral_sum_le_46 : Search46 → …` (problem 1),
* `solutions47_iff : Search47 → …`, `solutions47_eq : Search47 → …` (problem 2).
-/
import SemiprimeEgypt.Reduction
import SemiprimeEgypt.Solutions
import Mathlib.Data.Set.Card

open Finset

namespace SemiprimeEgypt

/-! ## Problem 1: no nonempty set of at most 46 squarefree semiprimes has integral sum -/

/-- **The computational assertion for problem 1** (what `semiprime_reciprocals.cpp` checked):
every core passing Step 1 with budget 46 has `U ≠ ∅`, and for each of its shapes passing
Lemma 4 (1)–(4) there are no big–big edges and no candidate star (with at most 10 leaves). -/
def Search46 : Prop :=
  ∀ C : Finset ℕ, CoreSet C → Admissible 46 C →
    (Uset 73 C).Nonempty ∧
      ∀ (d : ℕ → ℕ) (b : ℕ), ShapeOK 46 C d b → b = 0 ∧ ∀ P A, ¬ StarCand 10 C d P A

/-- **Problem 1 (conditional on `Search46`).**  No nonempty set of at most 46 squarefree
semiprimes has an integral reciprocal sum. -/
theorem no_integral_sum_le_46 (hS : Search46) {T : Finset ℕ} (hT : ∀ n ∈ T, IsSP n)
    (hne : T.Nonempty) (hc : T.card ≤ 46) : ¬ ∃ z : ℤ, recipSum T = z := by
  intro hz
  have hloc := (integral_iff_localCond T hT).1 hz
  have h1 := recipSum_eq_one_of_integral hT hne (by omega) hz
  obtain ⟨hU, hsh⟩ := hS _ (coreSet_core hT) (admissible_of_real hT hloc h1 hc)
  obtain ⟨hb, hno⟩ := hsh _ _ (shapeOK_of_real hT hloc h1 hc)
  obtain ⟨q, hq⟩ := hU
  obtain ⟨n, hn, hqn⟩ := exists_big_nbr hT hloc hq
  have hP := bigPrime_of_edge hT hn (Finset.mem_filter.1 hq).1 hqn
  have hbb : bbPart T = ∅ := by
    rw [← Finset.card_eq_zero, ← nbb_eq_card_bbPart]; exact hb
  have hall := nbrs_small_of_bb_empty hT hbb hP
  exact hno _ _ (starCand_real hT hloc h1 hc hP hall)

/-- Equivalent formulation: under `Search46`, every set of squarefree semiprimes with integral
reciprocal sum has at least 47 elements (and 47 is attained, see `Sol23_valid`). -/
theorem card_ge_47_of_integral (hS : Search46) {T : Finset ℕ} (hT : ∀ n ∈ T, IsSP n)
    (hne : T.Nonempty) (hz : ∃ z : ℤ, recipSum T = z) : 47 ≤ T.card := by
  by_contra h
  exact no_integral_sum_le_46 hS hT hne (by omega) hz

/-! ## Problem 2: the 47-element solutions -/

/-- **The computational assertion for problem 2** (what `semiprime47.cpp` checked), in four
parts, all for budget 47:
1. every core passing Step 1 with `U = ∅` and `C ≠ ∅` is one of the 23 listed sets;
2. every shape (of a core with `U ≠ ∅`) passing Lemma 4 (1)–(4) has at most one big–big edge;
3. (`b = 0`) every exact cover of the multiplicities `d` by candidate stars with distinct
   centres whose value is `1 - Σ_C` gives one of the 23 sets;
4. (`b = 1`) for every pair of attachment sets `A₁, A₂`, every cover of the remaining
   multiplicities by candidate stars, the integer `t = (1 - Σ_C - Σ_stars) b₁ b₂`, and every
   positive divisor `X` of `N = b₁ b₂ (t + a₁ a₂)` yielding distinct primes
   `P₁ = (X + a₁ b₂)/t`, `P₂ = (N/X + a₂ b₁)/t` above 73 (and not centres of the stars),
   the resulting set is one of the 23 sets. -/
def Search47 : Prop :=
  (∀ C : Finset ℕ, CoreSet C → Admissible 47 C → Uset 73 C = ∅ → C.Nonempty → C ∈ Sol23) ∧
  (∀ C : Finset ℕ, CoreSet C → Admissible 47 C → (Uset 73 C).Nonempty →
      ∀ (d : ℕ → ℕ) (b : ℕ), ShapeOK 47 C d b → b ≤ 1) ∧
  (∀ (C : Finset ℕ) (d : ℕ → ℕ) (Ps : Finset ℕ) (A : ℕ → Finset ℕ),
      CoreSet C → Admissible 47 C → (Uset 73 C).Nonempty → ShapeOK 47 C d 0 →
      (∀ P ∈ Ps, StarCand 11 C d P (A P)) →
      (∀ q ∈ smallPrimes 73, mult Ps A q = d q) →
      recipSum C + starVal Ps A = 1 →
      C ∪ starEdges Ps A ∈ Sol23) ∧
  (∀ (C : Finset ℕ) (d : ℕ → ℕ) (Ps : Finset ℕ) (A : ℕ → Finset ℕ) (A₁ A₂ : Finset ℕ)
      (t X : ℕ),
      CoreSet C → Admissible 47 C → (Uset 73 C).Nonempty → ShapeOK 47 C d 1 →
      (∀ P ∈ Ps, StarCand 11 C d P (A P)) →
      A₁.Nonempty → A₂.Nonempty → A₁ ⊆ smallPrimes 73 → A₂ ⊆ smallPrimes 73 →
      (∀ q ∈ smallPrimes 73,
        mult Ps A q + (if q ∈ A₁ then 1 else 0) + (if q ∈ A₂ then 1 else 0) = d q) →
      recipSum C + starVal Ps A < 1 →
      0 < t →
      (t : ℚ) = (1 - recipSum C - starVal Ps A) * (∏ q ∈ A₁, (q : ℚ)) * ∏ q ∈ A₂, (q : ℚ) →
      0 < X → X ∣ compN A₁ A₂ t → t ∣ X + nA A₁ * ∏ q ∈ A₂, q →
      t ∣ compN A₁ A₂ t / X + nA A₂ * ∏ q ∈ A₁, q →
      compP₁ A₁ A₂ t X ≠ compP₂ A₁ A₂ t X →
      73 < compP₁ A₁ A₂ t X → 73 < compP₂ A₁ A₂ t X →
      (compP₁ A₁ A₂ t X).Prime → (compP₂ A₁ A₂ t X).Prime →
      compP₁ A₁ A₂ t X ∉ Ps → compP₂ A₁ A₂ t X ∉ Ps →
      C ∪ starEdges Ps A ∪ A₁.image (· * compP₁ A₁ A₂ t X) ∪
          A₂.image (· * compP₂ A₁ A₂ t X) ∪ {compP₁ A₁ A₂ t X * compP₂ A₁ A₂ t X} ∈ Sol23)

section Problem2

variable {T : Finset ℕ}

/-- Case `U = ∅`: the core is the whole solution. -/
lemma case_U_empty (hS1 : ∀ C : Finset ℕ, CoreSet C → Admissible 47 C → Uset 73 C = ∅ →
      C.Nonempty → C ∈ Sol23)
    (hT : ∀ n ∈ T, IsSP n) (hc : T.card = 47) (h1 : recipSum T = 1)
    (hU : Uset 73 (core 73 T) = ∅) : T ∈ Sol23 := by
  have hloc := localCond_of_one hT h1
  have hadm := admissible_of_real hT hloc h1 (le_of_eq hc)
  have hCsp : ∀ n ∈ core 73 T, IsSP n := fun n hn => (coreSet_core hT n hn).1
  -- the core is nonempty (the value bound fails for `C = ∅`)
  have hCne : (core 73 T).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have h3 := hadm.2.2 0
    rw [hU, hne, Finset.filter_empty, recipSum_empty, Finset.sum_empty,
      Finset.card_empty] at h3
    have := V_le 47
    norm_num at h3 this
    linarith
  -- the core alone satisfies (*), so its sum is 1 and the big part is empty
  have hCloc := localCond_core_of_U_empty hT hU
  have hC1 : recipSum (core 73 T) = 1 :=
    recipSum_eq_one_of_integral hCsp hCne
      (le_trans (Finset.card_filter_le _ _) (le_of_eq hc))
      ((integral_iff_localCond _ hCsp).2 hCloc)
  have hG0 : recipSum (bigPart 73 T) = 0 := by
    have := recipSum_core_add_bigPart T; linarith
  have hG : bigPart 73 T = ∅ :=
    (recipSum_eq_zero_iff (fun n hn => hT n (Finset.mem_filter.1 hn).1)).1 hG0
  have hTC : T = core 73 T := by
    conv_lhs => rw [← core_union_bigPart (B := 73) T, hG, Finset.union_empty]
  rw [hTC]
  exact hS1 _ (coreSet_core hT) (hTC ▸ hadm) hU hCne

/-- Case `b = 0`: the big part is a family of stars. -/
lemma case_b0 (hS3 : ∀ (C : Finset ℕ) (d : ℕ → ℕ) (Ps : Finset ℕ) (A : ℕ → Finset ℕ),
      CoreSet C → Admissible 47 C → (Uset 73 C).Nonempty → ShapeOK 47 C d 0 →
      (∀ P ∈ Ps, StarCand 11 C d P (A P)) →
      (∀ q ∈ smallPrimes 73, mult Ps A q = d q) →
      recipSum C + starVal Ps A = 1 → C ∪ starEdges Ps A ∈ Sol23)
    (hT : ∀ n ∈ T, IsSP n) (hc : T.card = 47) (h1 : recipSum T = 1)
    (hU : (Uset 73 (core 73 T)).Nonempty) (hb : nbb 73 (bigPart 73 T) = 0) : T ∈ Sol23 := by
  have hloc := localCond_of_one hT h1
  have hK : T.card ≤ 47 := le_of_eq hc
  have hbb : bbPart T = ∅ := by
    rw [← Finset.card_eq_zero, ← nbb_eq_card_bbPart]; exact hb
  have hshape := shapeOK_of_real hT hloc h1 hK
  rw [hb] at hshape
  have hG : bigPart 73 T = starEdges (bigPrimesOf T) (smallNbrs T) := by
    rw [bigPart_eq hT, hbb, Finset.union_empty]
  have hTeq : T = core 73 T ∪ starEdges (bigPrimesOf T) (smallNbrs T) := by
    rw [← hG]; exact (core_union_bigPart T).symm
  have hval : recipSum (core 73 T) + starVal (bigPrimesOf T) (smallNbrs T) = 1 := by
    have e1 := recipSum_core_add_bigPart T
    have e2 := recipSum_bigPart_eq hT
    rw [hbb, recipSum_empty] at e2
    linarith
  have := hS3 (core 73 T) (dcount (bigPart 73 T)) (bigPrimesOf T) (smallNbrs T)
    (coreSet_core hT) (admissible_of_real hT hloc h1 hK) hU hshape
    (fun P hP => starCand_real hT hloc h1 hK hP (nbrs_small_of_bb_empty hT hbb hP))
    (fun q hq => (dcount_eq_mult hT hq).symm) hval
  rwa [← hTeq] at this

/-- Case `b = 1`: one component `{P₁, P₂}` plus stars. -/
lemma case_b1 (hS4 : ∀ (C : Finset ℕ) (d : ℕ → ℕ) (Ps : Finset ℕ) (A : ℕ → Finset ℕ)
      (A₁ A₂ : Finset ℕ) (t X : ℕ),
      CoreSet C → Admissible 47 C → (Uset 73 C).Nonempty → ShapeOK 47 C d 1 →
      (∀ P ∈ Ps, StarCand 11 C d P (A P)) →
      A₁.Nonempty → A₂.Nonempty → A₁ ⊆ smallPrimes 73 → A₂ ⊆ smallPrimes 73 →
      (∀ q ∈ smallPrimes 73,
        mult Ps A q + (if q ∈ A₁ then 1 else 0) + (if q ∈ A₂ then 1 else 0) = d q) →
      recipSum C + starVal Ps A < 1 →
      0 < t →
      (t : ℚ) = (1 - recipSum C - starVal Ps A) * (∏ q ∈ A₁, (q : ℚ)) * ∏ q ∈ A₂, (q : ℚ) →
      0 < X → X ∣ compN A₁ A₂ t → t ∣ X + nA A₁ * ∏ q ∈ A₂, q →
      t ∣ compN A₁ A₂ t / X + nA A₂ * ∏ q ∈ A₁, q →
      compP₁ A₁ A₂ t X ≠ compP₂ A₁ A₂ t X →
      73 < compP₁ A₁ A₂ t X → 73 < compP₂ A₁ A₂ t X →
      (compP₁ A₁ A₂ t X).Prime → (compP₂ A₁ A₂ t X).Prime →
      compP₁ A₁ A₂ t X ∉ Ps → compP₂ A₁ A₂ t X ∉ Ps →
      C ∪ starEdges Ps A ∪ A₁.image (· * compP₁ A₁ A₂ t X) ∪
          A₂.image (· * compP₂ A₁ A₂ t X) ∪ {compP₁ A₁ A₂ t X * compP₂ A₁ A₂ t X} ∈ Sol23)
    (hT : ∀ n ∈ T, IsSP n) (hc : T.card = 47) (h1 : recipSum T = 1)
    (hU : (Uset 73 (core 73 T)).Nonempty) (hb : nbb 73 (bigPart 73 T) = 1) : T ∈ Sol23 := by
  have hloc := localCond_of_one hT h1
  have hK : T.card ≤ 47 := le_of_eq hc
  have hshape := shapeOK_of_real hT hloc h1 hK
  rw [hb] at hshape
  obtain ⟨P₁, P₂, hP₁, hP₂, hP₁73, hlt, hbb⟩ :=
    bbPart_single hT (by rw [← nbb_eq_card_bbPart]; exact hb)
  have hP₂73 : 73 < P₂ := by omega
  have hne : P₁ ≠ P₂ := by omega
  have hedge : P₁ * P₂ ∈ T := by
    have : P₁ * P₂ ∈ bbPart T := by rw [hbb]; exact Finset.mem_singleton_self _
    exact (Finset.mem_filter.1 (Finset.mem_filter.1 this).1).1
  have hB₁ : P₁ ∈ bigPrimesOf T := mem_bigPrimesOf_of_mem hT hP₁ hP₁73 hedge (dvd_mul_right _ _)
  have hB₂ : P₂ ∈ bigPrimesOf T := mem_bigPrimesOf_of_mem hT hP₂ hP₂73 hedge (dvd_mul_left _ _)
  set A₁ := smallNbrs T P₁ with hA₁
  set A₂ := smallNbrs T P₂ with hA₂
  set Ps := ((bigPrimesOf T).erase P₁).erase P₂ with hPs
  have hA₁S : A₁ ⊆ smallPrimes 73 := smallNbrs_subset hT hP₁
  have hA₂S : A₂ ⊆ smallPrimes 73 := smallNbrs_subset hT hP₂
  have hP₂A₁ : P₂ ∉ A₁ := fun h => by have := (mem_smallPrimes.1 (hA₁S h)).2; omega
  have hP₁A₂ : P₁ ∉ A₂ := fun h => by have := (mem_smallPrimes.1 (hA₂S h)).2; omega
  -- neighbourhoods of P₁ and P₂
  have hN₁ : nbrs T P₁ = insert P₂ A₁ := by
    ext q
    rw [Finset.mem_insert]
    constructor
    · intro hq
      by_cases hq73 : q ≤ 73
      · exact Or.inr (Finset.mem_filter.2 ⟨hq, hq73⟩)
      · rcases big_nbr_eq hT hP₁ hP₂ hbb hB₁ hq (by omega) with h | h
        · exact Or.inl h.2
        · exact absurd h.1 hne
    · rintro (rfl | hq)
      · exact (mem_nbrs hP₁.pos).2 hedge
      · exact (Finset.mem_filter.1 hq).1
  have hN₂ : nbrs T P₂ = insert P₁ A₂ := by
    ext q
    rw [Finset.mem_insert]
    constructor
    · intro hq
      by_cases hq73 : q ≤ 73
      · exact Or.inr (Finset.mem_filter.2 ⟨hq, hq73⟩)
      · rcases big_nbr_eq hT hP₁ hP₂ hbb hB₂ hq (by omega) with h | h
        · exact absurd h.1 hne.symm
        · exact Or.inl h.2
    · rintro (rfl | hq)
      · exact (mem_nbrs hP₂.pos).2 (by rw [mul_comm]; exact hedge)
      · exact (Finset.mem_filter.1 hq).1
  -- A₁, A₂ are nonempty (a prime cannot have exactly one neighbour)
  have hA₁ne : A₁.Nonempty := by
    have := star_card_ne_one hT hloc hP₁
    rw [hN₁, Finset.card_insert_of_notMem hP₂A₁] at this
    exact Finset.card_pos.1 (by omega)
  have hA₂ne : A₂.Nonempty := by
    have := star_card_ne_one hT hloc hP₂
    rw [hN₂, Finset.card_insert_of_notMem hP₁A₂] at this
    exact Finset.card_pos.1 (by omega)
  -- the other big primes are stars
  have hPsB : ∀ P ∈ Ps, P ∈ bigPrimesOf T ∧ P ≠ P₁ ∧ P ≠ P₂ := by
    intro P hP
    rw [hPs, Finset.mem_erase, Finset.mem_erase] at hP
    exact ⟨hP.2.2, hP.2.1, hP.1⟩
  have hPsall : ∀ P ∈ Ps, ∀ q ∈ nbrs T P, q ≤ 73 := by
    intro P hP q hq
    by_contra h
    obtain ⟨hPB, h₁, h₂⟩ := hPsB P hP
    rcases big_nbr_eq hT hP₁ hP₂ hbb hPB hq (by omega) with h' | h'
    · exact h₁ h'.1
    · exact h₂ h'.1
  have hP₁Ps : P₁ ∉ Ps := fun h => (hPsB P₁ h).2.1 rfl
  have hP₂Ps : P₂ ∉ Ps := fun h => (hPsB P₂ h).2.2 rfl
  have hBP : bigPrimesOf T = insert P₁ (insert P₂ Ps) := by
    rw [hPs, Finset.insert_erase (Finset.mem_erase.2 ⟨hne.symm, hB₂⟩),
      Finset.insert_erase hB₁]
  have hP₁ins : P₁ ∉ insert P₂ Ps := by
    rw [Finset.mem_insert]; rintro (h | h)
    · exact hne h
    · exact hP₁Ps h
  -- multiplicities
  have hmult : ∀ q ∈ smallPrimes 73, mult Ps (smallNbrs T) q + (if q ∈ A₁ then 1 else 0) +
      (if q ∈ A₂ then 1 else 0) = dcount (bigPart 73 T) q := by
    intro q hq
    rw [dcount_eq_mult hT hq, hBP, mult_insert hP₁ins, mult_insert hP₂Ps]
    ring
  -- values
  have hval : recipSum (core 73 T) + starVal Ps (smallNbrs T) + compVal A₁ A₂ P₁ P₂ = 1 := by
    have e1 := recipSum_core_add_bigPart T
    have e2 := recipSum_bigPart_eq hT
    rw [hbb, hBP, starVal_insert hP₁ins, starVal_insert hP₂Ps] at e2
    have e3 : recipSum {P₁ * P₂} = 1 / ((P₁ : ℚ) * P₂) := by
      rw [recipSum, Finset.sum_singleton]; push_cast; rfl
    rw [e3] at e2
    rw [compVal]
    linarith
  have hcomp_pos : 0 < compVal A₁ A₂ P₁ P₂ := by
    rw [compVal]
    have h0 : (0 : ℚ) < 1 / ((P₁ : ℚ) * P₂) := by
      have := hP₁.pos; have := hP₂.pos; positivity
    have h1' : (0 : ℚ) ≤ ∑ q ∈ A₁, (1 : ℚ) / (q * P₁) :=
      Finset.sum_nonneg fun _ _ => by positivity
    have h2' : (0 : ℚ) ≤ ∑ q ∈ A₂, (1 : ℚ) / (q * P₂) :=
      Finset.sum_nonneg fun _ _ => by positivity
    linarith
  -- local conditions at P₁, P₂  ⟹  t = W / (P₁ P₂) is an integer
  have hd₁ : P₁ ∣ nA A₁ * P₂ + ∏ q ∈ A₁, q := by
    have := star_dvd hT hloc hP₁
    rwa [hN₁, nA_insert hP₂A₁ hP₂.pos, mul_comm P₂] at this
  have hd₂ : P₂ ∣ nA A₂ * P₁ + ∏ q ∈ A₂, q := by
    have := star_dvd hT hloc hP₂
    rwa [hN₂, nA_insert hP₁A₂ hP₁.pos, mul_comm P₁] at this
  have hW := (comp_local_iff hP₁ hP₂ hne (big_not_dvd_prod hP₁ hP₁73 hA₂S)
    (big_not_dvd_prod hP₂ hP₂73 hA₁S)).1 ⟨hd₁, hd₂⟩
  obtain ⟨t, ht⟩ := hW
  have htW : t * P₁ * P₂ = compW A₁ A₂ P₁ P₂ := by rw [ht]; ring
  have hb₁ := prod_pos_of_primes hA₁S
  have hb₂ := prod_pos_of_primes hA₂S
  have htpos : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · exfalso
      rw [h0, zero_mul, zero_mul, compW] at htW
      have : 0 < (∏ q ∈ A₁, q) * ∏ q ∈ A₂, q := Nat.mul_pos hb₁ hb₂
      omega
    · exact h0
  have htval : (t : ℚ) = (1 - recipSum (core 73 T) - starVal Ps (smallNbrs T)) *
      (∏ q ∈ A₁, (q : ℚ)) * ∏ q ∈ A₂, (q : ℚ) := by
    have hcv := comp_value (A₁ := A₁) (A₂ := A₂)
      (fun q hq => (mem_smallPrimes.1 (hA₁S hq)).1.pos)
      (fun q hq => (mem_smallPrimes.1 (hA₂S hq)).1.pos) hP₁.pos hP₂.pos
    have hW' : ((compW A₁ A₂ P₁ P₂ : ℕ) : ℚ) = (t : ℚ) * P₁ * P₂ := by
      rw [← htW]; push_cast; ring
    have hP₁q : (P₁ : ℚ) ≠ 0 := by exact_mod_cast hP₁.pos.ne'
    have hP₂q : (P₂ : ℚ) ≠ 0 := by exact_mod_cast hP₂.pos.ne'
    have hcomp : compVal A₁ A₂ P₁ P₂ = 1 - recipSum (core 73 T) - starVal Ps (smallNbrs T) := by
      linarith
    have key : (compVal A₁ A₂ P₁ P₂ * (∏ q ∈ A₁, (q : ℚ)) * ∏ q ∈ A₂, (q : ℚ)) *
        ((P₁ : ℚ) * P₂) = (t : ℚ) * ((P₁ : ℚ) * P₂) := by
      rw [← mul_assoc, ← mul_assoc, hcv, hW']
    have := mul_right_cancel₀ (mul_ne_zero hP₁q hP₂q) key
    rw [← hcomp, ← this]
  -- the divisor `X` of the enumeration
  obtain ⟨hX, hXN, htd₁, htd₂, hPe₁, hPe₂⟩ :=
    comp_enum (A₁ := A₁) (A₂ := A₂) htpos hb₁ hb₂ hP₁.pos hP₂.pos htW
  set X := t * P₁ - nA A₁ * ∏ q ∈ A₂, q with hXdef
  have hc₁ : compP₁ A₁ A₂ t X = P₁ := hPe₁.symm
  have hc₂ : compP₂ A₁ A₂ t X = P₂ := hPe₂.symm
  have hmem := hS4 (core 73 T) (dcount (bigPart 73 T)) Ps (smallNbrs T) A₁ A₂ t X
    (coreSet_core hT) (admissible_of_real hT hloc h1 hK) hU hshape
    (fun P hP => starCand_real hT hloc h1 hK (hPsB P hP).1 (hPsall P hP))
    hA₁ne hA₂ne hA₁S hA₂S hmult (by linarith) htpos htval hX hXN htd₁ htd₂
    (by rw [hc₁, hc₂]; exact hne) (by rw [hc₁]; exact hP₁73) (by rw [hc₂]; exact hP₂73)
    (by rw [hc₁]; exact hP₁) (by rw [hc₂]; exact hP₂) (by rw [hc₁]; exact hP₁Ps)
    (by rw [hc₂]; exact hP₂Ps)
  rw [hc₁, hc₂] at hmem
  -- `T` is exactly the set produced by the enumeration
  have hG : bigPart 73 T = A₁.image (· * P₁) ∪ (A₂.image (· * P₂) ∪ starEdges Ps (smallNbrs T))
      ∪ {P₁ * P₂} := by
    rw [bigPart_eq hT, hbb, hBP, starEdges_insert, starEdges_insert]
  have hTeq : T = core 73 T ∪ starEdges Ps (smallNbrs T) ∪ A₁.image (· * P₁) ∪
      A₂.image (· * P₂) ∪ {P₁ * P₂} := by
    conv_lhs => rw [← core_union_bigPart (B := 73) T, hG]
    ac_rfl
  exact (congrArg (fun S => S ∈ Sol23) hTeq).mpr hmem

/-- **Problem 2, completeness (conditional on `Search47`).**  Every set of 47 squarefree
semiprimes with reciprocal sum 1 is one of the 23 listed sets. -/
theorem solutions47_complete (hS : Search47) (hT : ∀ n ∈ T, IsSP n) (hc : T.card = 47)
    (h1 : recipSum T = 1) : T ∈ Sol23 := by
  obtain ⟨hS1, hS2, hS3, hS4⟩ := hS
  have hloc := localCond_of_one hT h1
  rcases (Uset 73 (core 73 T)).eq_empty_or_nonempty with hU | hU
  · exact case_U_empty hS1 hT hc h1 hU
  · have hb := hS2 _ (coreSet_core hT) (admissible_of_real hT hloc h1 (le_of_eq hc)) hU _ _
      (shapeOK_of_real hT hloc h1 (le_of_eq hc))
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with h0 | h0
    · exact case_b0 hS3 hT hc h1 hU h0
    · exact case_b1 hS4 hT hc h1 hU h0

end Problem2

/-- **Problem 2 (conditional on `Search47`).**  A finite set `T` is a 47-element set of
squarefree semiprimes with `Σ 1/n = 1` iff it is one of the 23 listed sets. -/
theorem solutions47_iff (hS : Search47) (T : Finset ℕ) :
    ((∀ n ∈ T, IsSP n) ∧ T.card = 47 ∧ recipSum T = 1) ↔ T ∈ Sol23 :=
  ⟨fun ⟨h1, h2, h3⟩ => solutions47_complete hS h1 h2 h3, Sol23_valid T⟩

/-- Same, with "integral sum" in place of "sum 1" (equivalent for 47 elements, since
`0 < Σ < 2`). -/
theorem solutions47_integral_iff (hS : Search47) (T : Finset ℕ) :
    ((∀ n ∈ T, IsSP n) ∧ T.card = 47 ∧ ∃ z : ℤ, recipSum T = z) ↔ T ∈ Sol23 := by
  rw [← solutions47_iff hS T]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, recipSum_eq_one_of_integral h1 ?_ (le_of_eq h2) h3⟩
    exact Finset.card_pos.1 (by omega)
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, 1, by rw [h3]; norm_num⟩

/-- **Problem 2, the count (conditional on `Search47`).**  The set of all 47-element sets of
squarefree semiprimes with reciprocal sum 1 is exactly `Sol23`, and it has 23 elements. -/
theorem solutions47_eq (hS : Search47) :
    {T : Finset ℕ | (∀ n ∈ T, IsSP n) ∧ T.card = 47 ∧ recipSum T = 1} = (Sol23 : Set _) := by
  ext T
  simp only [Set.mem_ofPred_eq, Finset.mem_coe]
  exact solutions47_iff hS T

theorem solutions47_ncard (hS : Search47) :
    Set.ncard {T : Finset ℕ | (∀ n ∈ T, IsSP n) ∧ T.card = 47 ∧ recipSum T = 1} = 23 := by
  rw [solutions47_eq hS, Set.ncard_coe_finset, Sol23_card]


end SemiprimeEgypt
