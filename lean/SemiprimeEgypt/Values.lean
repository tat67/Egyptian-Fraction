/-
Value bounds (README §3, Lemmas 3, 4(4) and 5), for the split point `S = {primes ≤ 73}`.

* `V x`: the sum of the `x` largest reciprocals of squarefree semiprimes having a prime factor
  `> 73` (defined through `Nat.nth`, so no table is needed), and the exchange bound for it.
* `bigPrime k`: the `k`-th prime above 73 (`b_0 = 79, b_1 = 83, ...`).
* `Pmin q r`: the least prime `P > 73` with `P⁻¹ = -r` in `ZMod q` (`0` if there is none).
* Lemma 3 (`value_lower`), the shape bound of Lemma 4(4) (`shape_value_bound`) and the star-size
  lemma (`star_size`).
-/
import SemiprimeEgypt.Core
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.PrimeFin

open Finset

namespace SemiprimeEgypt

/-! ### Exchange bound for an infinite set of positive integers -/

/-- Any `≤ x`-element subset of an infinite set `Q` of positive integers has reciprocal sum at
most `∑_{i<x} 1 / nth Q i` (the sum of the `x` largest reciprocals). -/
theorem recipSum_le_nth (Q : ℕ → Prop) (hinf : {n | Q n}.Infinite) (hpos : ∀ n, Q n → 0 < n)
    (T : Finset ℕ) (hT : ∀ n ∈ T, Q n) {x : ℕ} (hx : T.card ≤ x) :
    recipSum T ≤ ∑ i ∈ range x, (1 : ℚ) / Nat.nth Q i := by
  classical
  rcases Nat.eq_zero_or_pos x with rfl | hx0
  · have : T = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hx)
    subst this; simp [recipSum]
  have hinj := Nat.nth_injective hinf
  set A := (range x).image (Nat.nth Q) with hAdef
  have hA : A.card = x := by rw [Finset.card_image_of_injective _ hinj, card_range]
  have hsum : recipSum A = ∑ i ∈ range x, (1 : ℚ) / Nat.nth Q i := by
    rw [recipSum, Finset.sum_image (fun a _ b _ h => hinj h)]
  rw [← hsum]
  refine recipSum_le_of_initial Q A T (Nat.nth Q (x - 1)) ?_ ?_ hT (by rw [hA]; exact hx)
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
    refine ⟨hpos _ (Nat.nth_mem_of_infinite hinf i), (Nat.nth_le_nth hinf).2 ?_⟩
    rw [Finset.mem_range] at hi; omega
  · intro n hn hle
    rw [Finset.mem_image]
    refine ⟨Nat.count Q n, ?_, Nat.nth_count hn⟩
    rw [Finset.mem_range]
    have h' : Nat.nth Q (Nat.count Q n) ≤ Nat.nth Q (x - 1) := by rw [Nat.nth_count hn]; exact hle
    have := (Nat.nth_le_nth hinf).1 h'
    omega

/-! ### Primes above 73 -/

/-- A *big* prime: a prime `> 73`. -/
def IsBigPrime (P : ℕ) : Prop := P.Prime ∧ 73 < P

/-- `b_k`, the `k`-th prime above 73 (`b_0 = 79`, `b_1 = 83`, ...). -/
noncomputable def bigPrime (k : ℕ) : ℕ := Nat.nth IsBigPrime k

lemma infinite_bigPrime : {P | IsBigPrime P}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨P, hP1, hP2⟩ := Nat.exists_infinite_primes (a + 74)
  exact ⟨P, ⟨hP2, by omega⟩, by omega⟩

lemma ge_79 {P : ℕ} (hP : P.Prime) (h : 73 < P) : 79 ≤ P := by
  by_contra h'
  interval_cases P <;> norm_num at hP

/-- The product of two distinct big primes is at least `79 · 83`. -/
lemma bigbig_ge {P Q : ℕ} (hP : P.Prime) (hQ : Q.Prime) (h1 : 73 < P) (hPQ : P < Q) :
    79 * 83 ≤ P * Q := by
  have h79 := ge_79 hP h1
  have hQ83 : 83 ≤ Q := by
    by_contra h'
    interval_cases Q <;> first | omega | norm_num at hQ
  nlinarith

/-- Sum over `d` distinct big primes: `∑ 1/P ≤ ∑_{k<d} 1/b_k`. -/
lemma recipSum_bigPrimes_le (A : Finset ℕ) (hA : ∀ P ∈ A, IsBigPrime P) :
    recipSum A ≤ ∑ i ∈ range A.card, (1 : ℚ) / bigPrime i :=
  recipSum_le_nth IsBigPrime infinite_bigPrime (fun n h => h.1.pos) A hA le_rfl

/-! ### Semiprimes with a big factor and the function `V` -/

/-- A squarefree semiprime with a prime factor `> 73`. -/
def IsBigSP (n : ℕ) : Prop := IsSP n ∧ ¬ Small 73 n

/-- `V x`: the sum of the `x` largest reciprocals of squarefree semiprimes having a prime factor
`> 73` (`V x = 1/158 + 1/166 + 1/178 + ...`, `x` terms). -/
noncomputable def V (x : ℕ) : ℚ := ∑ i ∈ range x, (1 : ℚ) / Nat.nth IsBigSP i

lemma isSP_mul {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p < q) : IsSP (p * q) :=
  ⟨p, q, hp, hq, h, rfl⟩

lemma infinite_bigSP : {n | IsBigSP n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨P, hP1, hP2⟩ := Nat.exists_infinite_primes (a + 74)
  refine ⟨2 * P, ⟨isSP_mul Nat.prime_two hP2 (by omega), ?_⟩, by omega⟩
  intro hs
  have := hs P (Nat.mem_primeFactors.2 ⟨hP2, dvd_mul_left _ _, by omega⟩)
  omega

lemma IsBigSP.ge_158 {n : ℕ} (h : IsBigSP n) : 158 ≤ n := by
  obtain ⟨⟨p, q, hp, hq, hpq, rfl⟩, hs⟩ := h
  simp only [Small, not_forall] at hs
  obtain ⟨r, hr, hr73⟩ := hs
  rw [primeFactors_sp hp hq (Nat.ne_of_lt hpq)] at hr
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  have hq79 : 79 ≤ q := by
    rcases hr with rfl | rfl
    · exact ge_79 hq (by omega)
    · exact ge_79 hq (by omega)
  have := hp.two_le
  nlinarith

/-- Exchange bound: at most `x` squarefree semiprimes with a big factor have reciprocal sum
`≤ V x`. -/
theorem recipSum_le_V (T : Finset ℕ) (hT : ∀ n ∈ T, IsBigSP n) {x : ℕ} (hx : T.card ≤ x) :
    recipSum T ≤ V x :=
  recipSum_le_nth IsBigSP infinite_bigSP (fun n h => lt_of_lt_of_le (by norm_num) h.ge_158)
    T hT hx

lemma V_le (x : ℕ) : V x ≤ x / 158 := by
  rw [V]
  have : ∀ i ∈ range x, (1 : ℚ) / Nat.nth IsBigSP i ≤ 1 / 158 := by
    intro i _
    have h := (Nat.nth_mem_of_infinite infinite_bigSP i).ge_158
    have h' : (158 : ℚ) ≤ Nat.nth IsBigSP i := by exact_mod_cast h
    exact one_div_le_one_div_of_le (by norm_num) h'
  calc ∑ i ∈ range x, (1 : ℚ) / Nat.nth IsBigSP i ≤ ∑ _i ∈ range x, (1 : ℚ) / 158 :=
        Finset.sum_le_sum this
    _ = x / 158 := by rw [Finset.sum_const, card_range, nsmul_eq_mul]; ring

/-! ### Elements of the big part -/

section BigPart

variable {T : Finset ℕ}

lemma bigPart_isBigSP (hT : ∀ n ∈ T, IsSP n) : ∀ n ∈ bigPart 73 T, IsBigSP n := by
  intro n hn
  have := Finset.mem_filter.1 hn
  exact ⟨hT n this.1, this.2⟩

lemma recipSum_core_add_bigPart (T : Finset ℕ) :
    recipSum T = recipSum (core 73 T) + recipSum (bigPart 73 T) := by
  conv_lhs => rw [← core_union_bigPart (B := 73) T]
  exact recipSum_union (disjoint_core_bigPart T)

/-- A choice of one big edge for every unsatisfied prime (the edges used in Lemma 2). -/
lemma exists_designated (hT : ∀ n ∈ T, IsSP n) (hloc : LocalCond T) :
    ∃ f : ℕ → ℕ, (∀ q ∈ Uset 73 (core 73 T), f q ∈ bigPart 73 T ∧ q ∣ f q) ∧
      Set.InjOn f (Uset 73 (core 73 T)) := by
  classical
  let f : ℕ → ℕ := fun q =>
    if h : ∃ n ∈ bigPart 73 T, q ∣ n then Classical.choose h else 0
  have hf : ∀ q ∈ Uset 73 (core 73 T), f q ∈ bigPart 73 T ∧ q ∣ f q := by
    intro q hq
    have h := exists_big_nbr hT hloc hq
    simp only [f, dif_pos h]
    exact Classical.choose_spec h
  refine ⟨f, hf, ?_⟩
  intro q hq q' hq' hqq'
  have h1 := hf q hq
  have h2 := hf q' hq'
  have hq1 := (mem_smallPrimes.1 (Finset.mem_filter.1 hq).1)
  have hq2 := (mem_smallPrimes.1 (Finset.mem_filter.1 hq').1)
  rw [hqq'] at h1
  have hmem := Finset.mem_filter.1 h2.1
  have hsp := hT _ hmem.1
  exact small_factor_unique hsp hmem.2 hq1.1 hq1.2 h1.2 hq2.1 hq2.2 h2.2

/-- A big element divisible by the small prime `q` is at least `79 q`. -/
lemma big_edge_ge (hT : ∀ n ∈ T, IsSP n) {q n : ℕ} (hq : q.Prime) (hq73 : q ≤ 73)
    (hn : n ∈ bigPart 73 T) (hqn : q ∣ n) : 79 * q ≤ n := by
  have hmem := Finset.mem_filter.1 hn
  obtain ⟨hr, -, hmul⟩ := (hT n hmem.1).cofactor hq hqn
  have hbig := cofactor_big (hT n hmem.1) hmem.2 hq hq73 hqn
  have := ge_79 hr hbig
  rw [← hmul]
  nlinarith

/-- **Lemma 3 (value), general form.**  For a set `T` of squarefree semiprimes with `Σ 1/n = 1`,
`|T| ≤ K` and (*) at every prime, and for **every** subset `U' ⊆ U`:
`1 ≤ Σ_C + Σ_{q ∈ U'} 1/(79 q) + V(K - |C| - |U'|)`.
(Designated big edges are charged `1/(79q)` only for `q ∈ U'`; all other big edges are
bounded by `V`.)  The search uses it for every upper segment `U' = U ∩ (p, ∞)`. -/
theorem value_lower_subset (hT : ∀ n ∈ T, IsSP n) (hloc : LocalCond T) (h1 : recipSum T = 1)
    {K : ℕ} (hK : T.card ≤ K) {U' : Finset ℕ} (hU' : U' ⊆ Uset 73 (core 73 T)) :
    1 ≤ recipSum (core 73 T) + ∑ q ∈ U', (1 : ℚ) / (79 * q) +
      V (K - (core 73 T).card - U'.card) := by
  classical
  obtain ⟨f, hf₀, hinj₀⟩ := exists_designated hT hloc
  have hf : ∀ q ∈ U', f q ∈ bigPart 73 T ∧ q ∣ f q := fun q hq => hf₀ q (hU' hq)
  have hinj : Set.InjOn f U' := hinj₀.mono (by exact_mod_cast hU')
  set G := bigPart 73 T
  set D := U'.image f
  have hDG : D ⊆ G := by
    intro n hn
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hn
    exact (hf q hq).1
  have hDcard : D.card = U'.card := Finset.card_image_of_injOn hinj
  have hG : recipSum G = recipSum D + recipSum (G \ D) := by
    rw [← recipSum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hDG]
  have hDval : recipSum D ≤ ∑ q ∈ U', (1 : ℚ) / (79 * q) := by
    rw [recipSum, Finset.sum_image hinj]
    refine Finset.sum_le_sum fun q hq => ?_
    have hqU : q.Prime ∧ q ≤ 73 := mem_smallPrimes.1 (Finset.mem_filter.1 (hU' hq)).1
    have hge := big_edge_ge hT hqU.1 hqU.2 (hf q hq).1 (hf q hq).2
    have h0 : (0 : ℚ) < 79 * q := by have := hqU.1.pos; positivity
    exact one_div_le_one_div_of_le h0 (by exact_mod_cast hge)
  have hcardG : (G \ D).card ≤ K - (core 73 T).card - U'.card := by
    rw [Finset.card_sdiff_of_subset hDG, hDcard]
    have e1 : (core 73 T).card + G.card = T.card := card_core_add_card_bigPart (B := 73) T
    have e2 : (Uset 73 (core 73 T)).card ≤ G.card := card_Uset_le (B := 73) hT hloc
    have e3 : U'.card ≤ (Uset 73 (core 73 T)).card := Finset.card_le_card hU'
    omega
  have hrest : recipSum (G \ D) ≤ V (K - (core 73 T).card - U'.card) :=
    recipSum_le_V _ (fun n hn => bigPart_isBigSP hT n (Finset.mem_sdiff.1 hn).1) hcardG
  have := recipSum_core_add_bigPart T
  linarith

/-- **Lemma 3 (value).**  The case `U' = U`:
`1 ≤ Σ_C + Σ_{q ∈ U} 1/(79 q) + V(K - |C| - |U|)`. -/
theorem value_lower (hT : ∀ n ∈ T, IsSP n) (hloc : LocalCond T) (h1 : recipSum T = 1)
    {K : ℕ} (hK : T.card ≤ K) :
    1 ≤ recipSum (core 73 T) + ∑ q ∈ Uset 73 (core 73 T), (1 : ℚ) / (79 * q) +
      V (K - (core 73 T).card - (Uset 73 (core 73 T)).card) :=
  value_lower_subset hT hloc h1 hK subset_rfl

/-- The core sum is at most 1. -/
theorem core_le_one (h1 : recipSum T = 1) : recipSum (core 73 T) ≤ 1 := by
  have := recipSum_core_add_bigPart T
  linarith [recipSum_nonneg (bigPart 73 T)]

end BigPart

/-! ### The shape value bound, Lemma 4(4) -/

open Classical in
/-- `Pmin q r`: the least prime `P > 73` with `P⁻¹ = -r` in `ZMod q`, i.e.
`P ≡ (-r)⁻¹ (mod q)`; it is `0` if no such prime exists (then no big prime can be the unique big
neighbour of `q`). -/
noncomputable def Pmin (q : ℕ) (r : ZMod q) : ℕ :=
  if h : ∃ P : ℕ, P.Prime ∧ 73 < P ∧ ((P : ZMod q))⁻¹ = -r then Nat.find h else 0

lemma Pmin_spec {q : ℕ} {r : ZMod q} {P : ℕ} (hP : P.Prime) (hP73 : 73 < P)
    (hr : ((P : ZMod q))⁻¹ = -r) : (Pmin q r).Prime ∧ 73 < Pmin q r ∧ Pmin q r ≤ P := by
  classical
  have h : ∃ P : ℕ, P.Prime ∧ 73 < P ∧ ((P : ZMod q))⁻¹ = -r := ⟨P, hP, hP73, hr⟩
  have hPmin : Pmin q r = Nat.find h := by
    rw [Pmin, dif_pos h]
  rw [hPmin]
  exact ⟨(Nat.find_spec h).1, (Nat.find_spec h).2.1, Nat.find_min' h ⟨hP, hP73, hr⟩⟩

/-- The contribution allowed for the big edges at `q` in the shape bound, when `q` has `k` big
neighbours: `1/(q · Pmin(q))` if `k = 1`, and `Σ_{i<k} 1/(q · b_i)` otherwise. -/
noncomputable def shapeVal (C : Finset ℕ) (q k : ℕ) : ℚ :=
  if k = 1 then 1 / (q * Pmin q (resid C q)) else ∑ i ∈ range k, (1 : ℚ) / (q * bigPrime i)

section Shape

variable {T : Finset ℕ}

lemma nbrs_card_eq (P : ℕ) (hP : 0 < P) (T : Finset ℕ) :
    (nbrs T P).card = (T.filter (fun n => P ∣ n)).card := by
  rw [nbrs, Finset.card_image_of_injOn]
  intro a ha b hb hab
  have ha' := (Finset.mem_filter.1 ha).2
  have hb' := (Finset.mem_filter.1 hb).2
  rw [← Nat.mul_div_cancel' ha', ← Nat.mul_div_cancel' hb']
  exact congrArg (P * ·) hab

lemma recipSum_filter_dvd (P : ℕ) (T : Finset ℕ) :
    recipSum (T.filter (fun n => P ∣ n)) = ∑ q ∈ nbrs T P, (1 : ℚ) / (P * q) := by
  rw [recipSum, nbrs, Finset.sum_image]
  · refine Finset.sum_congr rfl fun n hn => ?_
    have := (Finset.mem_filter.1 hn).2
    rw [← Nat.cast_mul, Nat.mul_div_cancel' this]
  · intro a ha b hb hab
    have ha' := (Finset.mem_filter.1 ha).2
    have hb' := (Finset.mem_filter.1 hb).2
    rw [← Nat.mul_div_cancel' ha', ← Nat.mul_div_cancel' hb']
    exact congrArg (P * ·) hab

/-- The sum over the big neighbours of a small prime `q` is bounded by `shapeVal`. -/
theorem sum_nbr_le (hT : ∀ n ∈ T, IsSP n) (hloc : LocalCond T) {q : ℕ} (hq : q.Prime)
    (hq73 : q ≤ 73) :
    recipSum ((bigPart 73 T).filter (fun n => q ∣ n)) ≤
      shapeVal (core 73 T) q (dcount (bigPart 73 T) q) := by
  set F := (bigPart 73 T).filter (fun n => q ∣ n)
  have hF : ∀ n ∈ F, 73 < n / q ∧ (n / q).Prime ∧ q * (n / q) = n := by
    intro n hn
    obtain ⟨h1, h2, -⟩ := resid_bigPart_eq hT hq hq73 n hn
    exact ⟨h1, h2, Nat.mul_div_cancel' (Finset.mem_filter.1 hn).2⟩
  rw [shapeVal]
  split_ifs with hk
  · -- exactly one big neighbour: it lies in the residue class of `Pmin`
    obtain ⟨n, hn⟩ := Finset.card_eq_one.1 hk
    obtain ⟨hbig, hpr, hcls⟩ := unique_nbr_class hT hloc hq hq73 hn
    obtain ⟨hPp, hP73, hPle⟩ := Pmin_spec hpr hbig hcls
    have hn' : F = {n} := hn
    have hnF : n ∈ F := by rw [hn']; exact Finset.mem_singleton_self n
    rw [hn', recipSum, Finset.sum_singleton]
    rw [← (hF n hnF).2.2]
    have h0 : (0 : ℚ) < q * Pmin q (resid (core 73 T) q) := by
      have := hq.pos; have := hPp.pos; positivity
    apply one_div_le_one_div_of_le h0
    push_cast
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hPle) (by positivity)
  · -- several big neighbours: distinct primes above 73
    set A := F.image (fun n => n / q)
    have hinj : Set.InjOn (fun n => n / q) F := by
      intro a ha b hb hab
      rw [← (hF a ha).2.2, ← (hF b hb).2.2]
      exact congrArg (q * ·) hab
    have hAcard : A.card = dcount (bigPart 73 T) q := Finset.card_image_of_injOn hinj
    have hsum : recipSum F = (1 / (q : ℚ)) * recipSum A := by
      rw [recipSum, recipSum, Finset.sum_image hinj, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n hn => ?_
      conv_lhs => rw [← (hF n hn).2.2]
      have := hq.pos
      have := (hF n hn).2.1.pos
      push_cast
      field_simp
    have hA : ∀ P ∈ A, IsBigPrime P := by
      intro P hP
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hP
      exact ⟨(hF n hn).2.1, (hF n hn).1⟩
    have hle := recipSum_bigPrimes_le A hA
    rw [hAcard] at hle
    rw [hsum]
    have hq0 : (0 : ℚ) < 1 / q := by have := hq.pos; positivity
    calc 1 / (q : ℚ) * recipSum A
        ≤ 1 / (q : ℚ) * ∑ i ∈ range (dcount (bigPart 73 T) q), (1 : ℚ) / bigPrime i :=
          mul_le_mul_of_nonneg_left hle hq0.le
      _ = ∑ i ∈ range (dcount (bigPart 73 T) q), 1 / (q : ℚ) * (1 / bigPrime i) :=
          Finset.mul_sum _ _ _
      _ = ∑ i ∈ range (dcount (bigPart 73 T) q), (1 : ℚ) / (q * bigPrime i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [one_div_mul_one_div]

/-- The big-big elements are at least `79 · 83`. -/
lemma bigbig_elem_ge (hT : ∀ n ∈ T, IsSP n) {n : ℕ}
    (hn : n ∈ (bigPart 73 T).filter (fun n => ∀ q ∈ smallPrimes 73, ¬ q ∣ n)) :
    79 * 83 ≤ n := by
  obtain ⟨hnG, hns⟩ := Finset.mem_filter.1 hn
  obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hT _ (Finset.mem_filter.1 hnG).1
  have hp73 : 73 < p := by
    by_contra h
    exact hns p (mem_smallPrimes.2 ⟨hp, by omega⟩) (dvd_mul_right _ _)
  exact bigbig_ge hp hq hp73 hpq

/-- **Lemma 4(4), the shape value bound.**
`1 - Σ_C ≤ Σ_{q ≤ 73} shapeVal(q, d_q) + b / (79 · 83)`. -/
theorem shape_value_bound (hT : ∀ n ∈ T, IsSP n) (hloc : LocalCond T) (h1 : recipSum T = 1) :
    1 - recipSum (core 73 T) ≤
      ∑ q ∈ smallPrimes 73, shapeVal (core 73 T) q (dcount (bigPart 73 T) q) +
        (nbb 73 (bigPart 73 T) : ℚ) / (79 * 83) := by
  have hsplit := sum_bigPart_split (B := 73) hT (fun n : ℕ => (1 : ℚ) / n)
  have htot := recipSum_core_add_bigPart T
  have hG : 1 - recipSum (core 73 T) = recipSum (bigPart 73 T) := by linarith
  rw [hG, recipSum, hsplit]
  refine add_le_add (Finset.sum_le_sum fun q hq => ?_) ?_
  · have hq' := mem_smallPrimes.1 hq
    exact sum_nbr_le hT hloc hq'.1 hq'.2
  · rw [nbb, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_le_sum fun n hn => ?_
    have := bigbig_elem_ge hT hn
    have h0 : (0 : ℚ) < 79 * 83 := by norm_num
    rw [Nat.cast_one]
    exact one_div_le_one_div_of_le h0 (by exact_mod_cast this)

end Shape

/-! ### The star-size lemma (Lemma 5) -/

lemma smallPrimes_73 : smallPrimes 73 =
    {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73} := by
  decide

lemma card_smallPrimes_73 : (smallPrimes 73).card = 21 := by
  rw [smallPrimes_73]; rfl

/-- `Σ_{q ≤ 73 prime} 1/q ≤ 1.757` (it is `≈ 1.6557`). -/
lemma sum_inv_smallPrimes : ∑ q ∈ smallPrimes 73, (1 : ℚ) / q ≤ 1757 / 1000 := by
  rw [smallPrimes_73]; norm_num [Finset.sum_insert]

/-- **Lemma 5 (star size).**  Let `T` be a set of squarefree semiprimes with `Σ 1/n = 1`, and
let `P > 73` be a prime all of whose neighbours are `≤ 73`.  Then `|N(P)| + 36 ≤ |T|`.
Hence `|N(P)| ≤ 10` if `|T| ≤ 46` and `|N(P)| ≤ 11` if `|T| ≤ 47`. -/
theorem star_size {T : Finset ℕ} (hT : ∀ n ∈ T, IsSP n) (h1 : recipSum T = 1) {P : ℕ}
    (hP : P.Prime) (hP73 : 73 < P) (hA : ∀ q ∈ nbrs T P, q ≤ 73) :
    (nbrs T P).card + 36 ≤ T.card := by
  classical
  by_contra hlt
  set E := T.filter (fun n => P ∣ n)
  have hEcard : E.card = (nbrs T P).card := (nbrs_card_eq P hP.pos T).symm
  have hsplit : recipSum T = recipSum E + recipSum (T \ E) := by
    rw [← recipSum_union Finset.disjoint_sdiff,
      Finset.union_sdiff_of_subset (Finset.filter_subset _ _)]
  have hsub : nbrs T P ⊆ smallPrimes 73 := by
    intro q hq
    exact mem_smallPrimes.2 ⟨(prime_of_mem_nbrs hT hP hq).1, hA q hq⟩
  have hE : recipSum E ≤ 1757 / 79000 := by
    rw [recipSum_filter_dvd]
    calc ∑ q ∈ nbrs T P, (1 : ℚ) / (P * q) ≤ ∑ q ∈ nbrs T P, (1 : ℚ) / 79 * (1 / q) := by
          refine Finset.sum_le_sum fun q hq => ?_
          have hqp := (prime_of_mem_nbrs hT hP hq).1.pos
          have h79 : (79 : ℚ) ≤ P := by exact_mod_cast ge_79 hP hP73
          rw [one_div_mul_one_div]
          have h0 : (0 : ℚ) < 79 * q := by positivity
          apply one_div_le_one_div_of_le h0
          exact mul_le_mul_of_nonneg_right h79 (by positivity)
      _ = 1 / 79 * ∑ q ∈ nbrs T P, (1 : ℚ) / q := (Finset.mul_sum _ _ _).symm
      _ ≤ 1 / 79 * ∑ q ∈ smallPrimes 73, (1 : ℚ) / q := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ ≤ 1 / 79 * (1757 / 1000) := by
          apply mul_le_mul_of_nonneg_left sum_inv_smallPrimes (by norm_num)
      _ = 1757 / 79000 := by norm_num
  have hrest : recipSum (T \ E) ≤ recipSum (Aupto 119) := by
    apply recipSum_le_Aupto (by norm_num) _ (fun n hn => hT n (Finset.mem_sdiff.1 hn).1)
    rw [card_Aupto_119, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), hEcard]
    omega
  linarith [H35_val]

end SemiprimeEgypt
