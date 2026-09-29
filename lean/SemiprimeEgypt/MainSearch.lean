/-
The main results with Step 1 (the enumeration of cores) replaced by the verified search.

`SearchReal.lean` proves that the Lean function `(inst73 K).search (inst73 K).mkTables` (the
search of `semiprime48.cpp`: depth-first search over the primes `≤ 73` with the budget, value
and loss-bound pruning) outputs every core that passes Step 1 (`core_mem_search`, for every
budget `K ≤ 48`).  Here the computational hypotheses of `Main.lean` are weakened accordingly:

* `Search46'` / `Search47'` are `Search46` / `Search47` with the quantifier over all cores `C`
  restricted to the cores in `searchCores K`, the output of the verified search.  Hence the
  enumeration of cores is no longer an assumption; what remains assumed is Step 2 (shapes,
  stars, components) for the listed cores.
* `search46_of`, `search47_of`: `Search46' → Search46`, `Search47' → Search47`.
* `no_integral_sum_le_46'`, `card_ge_47_of_integral'`, `solutions47_iff'`, `solutions47_eq'`,
  `solutions47_ncard'`: the main theorems under the weaker hypotheses.
* `recipSum_lt_two_48`, `recipSum_eq_one_of_integral_48`: for at most 48 squarefree semiprimes
  an integral reciprocal sum equals `1`;  `core_mem_searchCores`: the core of every set of at
  most 48 squarefree semiprimes with integral reciprocal sum is in the output of the verified
  search with budget 48 (Step 1 of the 48-term classification).
-/
import SemiprimeEgypt.Main
import SemiprimeEgypt.SearchReal

open Finset

namespace SemiprimeEgypt

open Srch

/-- The cores output by the verified Step-1 search with budget `K`. -/
def searchCores (K : ℕ) : List (Finset ℕ) :=
  ((inst73 K).search (inst73 K).mkTables).map coreOf

/-- **Exhaustiveness of Step 1.**  Every core `C` passing Step 1 with budget `K ≤ 48` is in
`searchCores K`. -/
theorem mem_searchCores {K : ℕ} (hK : K ≤ 48) {C : Finset ℕ} (hC : CoreSet C)
    (hA : Admissible K C) : C ∈ searchCores K :=
  List.mem_map.2 ⟨edgesOf C, core_mem_search hK hC hA, coreOf_edgesOf hC⟩

/-! ### At most 48 elements: an integral sum is `1` -/

/-- `H_47 < 3/2` (`H_47 ≈ 1.0641`). -/
lemma H47_lt_three_halves : recipSum (Aupto 158) < 3 / 2 := by
  rw [Aupto_158_eq, A47]; unfold recipSum; norm_num [Finset.sum_insert]

lemma IsSP.ge_six {n : ℕ} (h : IsSP n) : 6 ≤ n := by
  obtain ⟨p, q, hp, hq, hpq, rfl⟩ := h
  have := hp.two_le
  nlinarith

/-- For at most 48 squarefree semiprimes the reciprocal sum is `< 2` (`≤ H_47 + 1/6`). -/
theorem recipSum_lt_two_48 {T : Finset ℕ} (hT : ∀ n ∈ T, IsSP n) (hc : T.card ≤ 48) :
    recipSum T < 2 := by
  rcases T.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · rw [recipSum_empty]; norm_num
  have h1 : recipSum T = recipSum (T.erase x) + 1 / x := by
    unfold recipSum; rw [Finset.sum_erase_add _ _ hx]
  have h2 := recipSum_le_Aupto le_rfl (T.erase x) (fun n hn => hT n (Finset.mem_of_mem_erase hn))
    (by rw [card_Aupto_158, Finset.card_erase_of_mem hx]; omega)
  have h3 := H47_lt_three_halves
  have h6 := (hT x hx).ge_six
  have h4 : (1 : ℚ) / x ≤ 1 / 6 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast h6)
  linarith

/-- An integral reciprocal sum of at most 48 squarefree semiprimes equals `1`. -/
theorem recipSum_eq_one_of_integral_48 {T : Finset ℕ} (hT : ∀ n ∈ T, IsSP n)
    (hne : T.Nonempty) (hc : T.card ≤ 48) (hz : ∃ z : ℤ, recipSum T = z) : recipSum T = 1 := by
  obtain ⟨z, hz⟩ := hz
  have h0 := recipSum_pos hT hne
  have h2 := recipSum_lt_two_48 hT hc
  rw [hz] at h0 h2 ⊢
  have hz1 : 0 < z := by exact_mod_cast h0
  have hz2 : z < 2 := by exact_mod_cast h2
  have : z = 1 := by omega
  rw [this]; norm_num

/-- **Step 1 for every budget `K ≤ 48`.**  The core of every nonempty set `T` of at most `K`
squarefree semiprimes with integral reciprocal sum is in the output of the verified search
with budget `K`. -/
theorem core_mem_searchCores {T : Finset ℕ} (hT : ∀ n ∈ T, IsSP n) (hne : T.Nonempty)
    {K : ℕ} (hK : K ≤ 48) (hc : T.card ≤ K) (hz : ∃ z : ℤ, recipSum T = z) :
    core 73 T ∈ searchCores K := by
  have h1 := recipSum_eq_one_of_integral_48 hT hne (le_trans hc hK) hz
  exact mem_searchCores hK (coreSet_core hT)
    (admissible_of_real hT (localCond_of_one hT h1) h1 hc)

/-! ### Problem 1 -/

/-- **The computational assertion for problem 1, over the verified search**: every core in the
output of the search with budget 46 (which passes Step 1) has `U ≠ ∅`, and for each of its
shapes passing Lemma 4 (1)–(4) there are no big–big edges and no candidate star. -/
def Search46' : Prop :=
  ∀ C ∈ searchCores 46, CoreSet C → Admissible 46 C →
    (Uset 73 C).Nonempty ∧
      ∀ (d : ℕ → ℕ) (b : ℕ), ShapeOK 46 C d b → b = 0 ∧ ∀ P A, ¬ StarCand 10 C d P A

theorem search46_of (hS : Search46') : Search46 :=
  fun C hC hA => hS C (mem_searchCores (by norm_num) hC hA) hC hA

/-- **Problem 1 (conditional on `Search46'`).** -/
theorem no_integral_sum_le_46' (hS : Search46') {T : Finset ℕ} (hT : ∀ n ∈ T, IsSP n)
    (hne : T.Nonempty) (hc : T.card ≤ 46) : ¬ ∃ z : ℤ, recipSum T = z :=
  no_integral_sum_le_46 (search46_of hS) hT hne hc

theorem card_ge_47_of_integral' (hS : Search46') {T : Finset ℕ} (hT : ∀ n ∈ T, IsSP n)
    (hne : T.Nonempty) (hz : ∃ z : ℤ, recipSum T = z) : 47 ≤ T.card :=
  card_ge_47_of_integral (search46_of hS) hT hne hz

/-! ### Problem 2 -/

/-- **The computational assertion for problem 2, over the verified search**: `Search47` with
every quantifier over cores restricted to `searchCores 47`. -/
def Search47' : Prop :=
  (∀ C ∈ searchCores 47, CoreSet C → Admissible 47 C → Uset 73 C = ∅ → C.Nonempty →
      C ∈ Sol23) ∧
  (∀ C ∈ searchCores 47, CoreSet C → Admissible 47 C → (Uset 73 C).Nonempty →
      ∀ (d : ℕ → ℕ) (b : ℕ), ShapeOK 47 C d b → b ≤ 1) ∧
  (∀ C ∈ searchCores 47, ∀ (d : ℕ → ℕ) (Ps : Finset ℕ) (A : ℕ → Finset ℕ),
      CoreSet C → Admissible 47 C → (Uset 73 C).Nonempty → ShapeOK 47 C d 0 →
      (∀ P ∈ Ps, StarCand 11 C d P (A P)) →
      (∀ q ∈ smallPrimes 73, mult Ps A q = d q) →
      recipSum C + starVal Ps A = 1 →
      C ∪ starEdges Ps A ∈ Sol23) ∧
  (∀ C ∈ searchCores 47, ∀ (d : ℕ → ℕ) (Ps : Finset ℕ) (A : ℕ → Finset ℕ) (A₁ A₂ : Finset ℕ)
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

theorem search47_of (hS : Search47') : Search47 := by
  obtain ⟨h1, h2, h3, h4⟩ := hS
  have hm : ∀ {C : Finset ℕ}, CoreSet C → Admissible 47 C → C ∈ searchCores 47 :=
    fun hC hA => mem_searchCores (by norm_num) hC hA
  exact ⟨fun C hC hA => h1 C (hm hC hA) hC hA,
    fun C hC hA => h2 C (hm hC hA) hC hA,
    fun C d Ps A hC hA => h3 C (hm hC hA) d Ps A hC hA,
    fun C d Ps A A₁ A₂ t X hC hA => h4 C (hm hC hA) d Ps A A₁ A₂ t X hC hA⟩

/-- **Problem 2 (conditional on `Search47'`).** -/
theorem solutions47_iff' (hS : Search47') (T : Finset ℕ) :
    ((∀ n ∈ T, IsSP n) ∧ T.card = 47 ∧ recipSum T = 1) ↔ T ∈ Sol23 :=
  solutions47_iff (search47_of hS) T

theorem solutions47_integral_iff' (hS : Search47') (T : Finset ℕ) :
    ((∀ n ∈ T, IsSP n) ∧ T.card = 47 ∧ ∃ z : ℤ, recipSum T = z) ↔ T ∈ Sol23 :=
  solutions47_integral_iff (search47_of hS) T

theorem solutions47_eq' (hS : Search47') :
    {T : Finset ℕ | (∀ n ∈ T, IsSP n) ∧ T.card = 47 ∧ recipSum T = 1} = (Sol23 : Set _) :=
  solutions47_eq (search47_of hS)

theorem solutions47_ncard' (hS : Search47') :
    Set.ncard {T : Finset ℕ | (∀ n ∈ T, IsSP n) ∧ T.card = 47 ∧ recipSum T = 1} = 23 :=
  solutions47_ncard (search47_of hS)

end SemiprimeEgypt
