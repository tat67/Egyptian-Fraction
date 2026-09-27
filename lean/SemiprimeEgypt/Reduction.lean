/-
The finite data checked by the computer search, and the reduction of an arbitrary solution to
that data.

* `CoreSet`, `Admissible` (Step 1), `ShapeOK` (Step 2, Lemma 4 (1)–(4)), `StarCand`
  (candidate stars).
* `admissible_of_real`, `shapeOK_of_real`: the core and the shape of any solution pass the
  tests of the search.
* Structural lemmas for the cases `b = 0` (all big primes are stars) and `b = 1` (one
  component `{P₁, P₂}` plus stars).
-/
import SemiprimeEgypt.Component

open Finset

namespace SemiprimeEgypt

/-! ### The data enumerated by the search -/

/-- A *core set*: squarefree semiprimes with both prime factors `≤ 73`. -/
def CoreSet (C : Finset ℕ) : Prop := ∀ n ∈ C, IsSP n ∧ Small 73 n

/-- **Step 1 (cores).**  The tests that the depth-first search applies to a core `C` with
budget `K`: `|C| + |U| ≤ K` (Lemma 2), `Σ_C ≤ 1`, and the value bound of Lemma 3 for every
*upper segment* `U ∩ (p, ∞)` of `U`,
`1 ≤ Σ_C + Σ_{q ∈ U, q > p} 1/(79q) + V(K - |C| - |U ∩ (p, ∞)|)`.
(The search processes the primes in decreasing order and, at an intermediate node, charges
`1/(79q)` only for the primes already put into `U`; the case `p = 0` is the final test.
Requiring only the final test would *not* describe the set of cores the search visits.) -/
def Admissible (K : ℕ) (C : Finset ℕ) : Prop :=
  C.card + (Uset 73 C).card ≤ K ∧ recipSum C ≤ 1 ∧
    ∀ p : ℕ, 1 ≤ recipSum C + ∑ q ∈ (Uset 73 C).filter (p < ·), (1 : ℚ) / (79 * q) +
      V (K - C.card - ((Uset 73 C).filter (p < ·)).card)

/-- **Step 2 (shapes).**  The tests (i)–(iv) of Lemma 4 for the numbers `d q` of big
neighbours of the small primes `q` and the number `b` of big–big edges. -/
def ShapeOK (K : ℕ) (C : Finset ℕ) (d : ℕ → ℕ) (b : ℕ) : Prop :=
  (∀ q ∈ Uset 73 C, 1 ≤ d q) ∧
  (∀ q ∈ smallPrimes 73, q ∉ Uset 73 C → d q ≠ 1) ∧
  b + ∑ q ∈ Uset 73 C, (d q - 1) + ∑ q ∈ smallPrimes 73 \ Uset 73 C, d q ≤
      K - C.card - (Uset 73 C).card ∧
  resid C 2 + (d 2 : ZMod 2) = 0 ∧
  1 - recipSum C ≤ ∑ q ∈ smallPrimes 73, shapeVal C q (d q) + (b : ℚ) / (79 * 83)

/-- A *candidate star* `(P, A)` for the shape `d` (at most `m` leaves): the list the program
builds before searching for covers. -/
def StarCand (m : ℕ) (C : Finset ℕ) (d : ℕ → ℕ) (P : ℕ) (A : Finset ℕ) : Prop :=
  P.Prime ∧ 73 < P ∧ A ⊆ smallPrimes 73 ∧ (∀ q ∈ A, 1 ≤ d q) ∧ 2 ≤ A.card ∧ A.card ≤ m ∧
    P ∣ nA A ∧ ∀ q ∈ A, d q = 1 → ((P : ZMod q))⁻¹ = - resid C q

/-- The two primes of the component recovered from a divisor `X` (see `comp_enum`). -/
def compP₁ (A₁ A₂ : Finset ℕ) (t X : ℕ) : ℕ := (X + nA A₁ * ∏ q ∈ A₂, q) / t
def compP₂ (A₁ A₂ : Finset ℕ) (t X : ℕ) : ℕ := (compN A₁ A₂ t / X + nA A₂ * ∏ q ∈ A₁, q) / t

/-- `n(A) ≤ |A| · ∏ A`. -/
lemma nA_le (A : Finset ℕ) : nA A ≤ A.card * ∏ q ∈ A, q := by
  rw [nA]
  calc ∑ q ∈ A, (∏ r ∈ A, r) / q ≤ ∑ _q ∈ A, ∏ r ∈ A, r :=
        Finset.sum_le_sum fun q _ => Nat.div_le_self _ _
    _ = A.card * ∏ q ∈ A, q := by rw [Finset.sum_const, smul_eq_mul]

/-- **Finiteness of the star candidates.**  For every shape there are only finitely many
candidate stars: `A ⊆ S` and `P ≤ n(A) ≤ 21 · ∏ S`. -/
theorem starCand_finite (m : ℕ) (C : Finset ℕ) (d : ℕ → ℕ) :
    {x : ℕ × Finset ℕ | StarCand m C d x.1 x.2}.Finite := by
  apply Set.Finite.subset ((Set.finite_Iic (21 * ∏ q ∈ smallPrimes 73, q)).prod
    (smallPrimes 73).powerset.finite_toSet)
  rintro ⟨P, A⟩ ⟨hP, -, hAS, -, h2, -, hdvd, -⟩
  dsimp only at hP hAS h2 hdvd
  refine ⟨?_, by simpa using hAS⟩
  change P ≤ _
  have hApos : ∀ q ∈ A, q.Prime := fun q hq => (mem_smallPrimes.1 (hAS hq)).1
  have hne : A.Nonempty := Finset.card_pos.1 (by omega)
  have h1 := Nat.le_of_dvd (nA_pos hApos hne) hdvd
  have h2' := nA_le A
  have h3 : A.card ≤ 21 := card_smallPrimes_73 ▸ Finset.card_le_card hAS
  have h4 : ∏ q ∈ A, q ≤ ∏ q ∈ smallPrimes 73, q :=
    Finset.prod_le_prod_of_subset_of_one_le hAS fun q hq _ => (mem_smallPrimes.1 hq).1.one_le
  calc P ≤ nA A := h1
    _ ≤ A.card * ∏ q ∈ A, q := h2'
    _ ≤ 21 * ∏ q ∈ smallPrimes 73, q := Nat.mul_le_mul h3 h4

/-! ### Every solution passes the tests -/

section Reduction

variable {T : Finset ℕ}

lemma localCond_of_one (hT : ∀ n ∈ T, IsSP n) (h1 : recipSum T = 1) : LocalCond T :=
  (integral_iff_localCond T hT).1 ⟨1, by rw [h1]; norm_num⟩

lemma coreSet_core (hT : ∀ n ∈ T, IsSP n) : CoreSet (core 73 T) := by
  intro n hn
  have := Finset.mem_filter.1 hn
  exact ⟨hT n this.1, this.2⟩

/-- The core of a solution passes Step 1. -/
theorem admissible_of_real (hT : ∀ n ∈ T, IsSP n) (hloc : LocalCond T) (h1 : recipSum T = 1)
    {K : ℕ} (hK : T.card ≤ K) : Admissible K (core 73 T) :=
  ⟨le_trans (card_core_add_card_Uset_le hT hloc) hK, core_le_one h1,
    fun _ => value_lower_subset hT hloc h1 hK (Finset.filter_subset _ _)⟩

/-- **Lemma 4(2).**  `b + Σ_U (d_q - 1) + Σ_{S∖U} d_q = |G| - |U| ≤ K - |C| - |U|`. -/
theorem excess_le (hT : ∀ n ∈ T, IsSP n) (hloc : LocalCond T) {K : ℕ} (hK : T.card ≤ K) :
    nbb 73 (bigPart 73 T) + ∑ q ∈ Uset 73 (core 73 T), (dcount (bigPart 73 T) q - 1) +
      ∑ q ∈ smallPrimes 73 \ Uset 73 (core 73 T), dcount (bigPart 73 T) q ≤
      K - (core 73 T).card - (Uset 73 (core 73 T)).card := by
  have hUS : Uset 73 (core 73 T) ⊆ smallPrimes 73 := Finset.filter_subset _ _
  have e1 := card_bigPart_eq (B := 73) hT
  have e2 := Finset.sum_sdiff hUS (f := dcount (bigPart 73 T))
  have e3 : ∑ q ∈ Uset 73 (core 73 T), dcount (bigPart 73 T) q =
      ∑ q ∈ Uset 73 (core 73 T), (dcount (bigPart 73 T) q - 1) +
        (Uset 73 (core 73 T)).card := by
    rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q hq => ?_
    have := dcount_pos_of_mem_U hT hloc hq
    omega
  have e4 := card_core_add_card_bigPart (B := 73) T
  omega

/-- The shape of a solution passes Step 2 (Lemma 4 (1)–(4)). -/
theorem shapeOK_of_real (hT : ∀ n ∈ T, IsSP n) (hloc : LocalCond T) (h1 : recipSum T = 1)
    {K : ℕ} (hK : T.card ≤ K) :
    ShapeOK K (core 73 T) (dcount (bigPart 73 T)) (nbb 73 (bigPart 73 T)) :=
  ⟨fun _ hq => dcount_pos_of_mem_U hT hloc hq,
   fun _ hq hU => dcount_ne_one_of_not_mem_U hT hloc (mem_smallPrimes.1 hq).1
     (mem_smallPrimes.1 hq).2 hU,
   excess_le hT hloc hK,
   parity_two hT hloc (by norm_num),
   shape_value_bound hT hloc h1⟩

/-- The cofactor of a small prime in a big element is a big prime of `T`. -/
lemma bigPrime_of_edge (hT : ∀ n ∈ T, IsSP n) {n q : ℕ} (hn : n ∈ bigPart 73 T)
    (hq : q ∈ smallPrimes 73) (hqn : q ∣ n) : n / q ∈ bigPrimesOf T := by
  have hq' := mem_smallPrimes.1 hq
  have hmem := Finset.mem_filter.1 hn
  obtain ⟨hr, -, -⟩ := (hT n hmem.1).cofactor hq'.1 hqn
  have hbig := cofactor_big (hT n hmem.1) hmem.2 hq'.1 hq'.2 hqn
  rw [mem_bigPrimesOf, mem_primesOf]
  exact ⟨⟨n, hmem.1, Nat.mem_primeFactors.2
    ⟨hr, Nat.div_dvd_of_dvd hqn, (hT n hmem.1).pos.ne'⟩⟩, hbig⟩

/-- A candidate star with at most `K - 36` leaves, for a solution with `|T| ≤ K`. -/
theorem starCand_real (hT : ∀ n ∈ T, IsSP n) (hloc : LocalCond T) (h1 : recipSum T = 1)
    {K : ℕ} (hK : T.card ≤ K) {P : ℕ} (hP : P ∈ bigPrimesOf T)
    (hall : ∀ q ∈ nbrs T P, q ≤ 73) :
    StarCand (K - 36) (core 73 T) (dcount (bigPart 73 T)) P (smallNbrs T P) := by
  rw [smallNbrs_eq_nbrs hall]
  obtain ⟨h1', h2', h3', h4', h5', h6', h7', h8'⟩ := starCand_of_real hT hloc h1 hP hall
  exact ⟨h1', h2', h3', h4', h5', by omega, h7', h8'⟩

lemma recipSum_eq_zero_iff (hT : ∀ n ∈ T, IsSP n) : recipSum T = 0 ↔ T = ∅ := by
  constructor
  · intro h
    by_contra hne
    have := recipSum_pos hT (Finset.nonempty_iff_ne_empty.2 hne)
    linarith
  · rintro rfl; exact recipSum_empty

/-- If `U = ∅` then the core alone satisfies (*) at every prime. -/
lemma localCond_core_of_U_empty (hT : ∀ n ∈ T, IsSP n) (hU : Uset 73 (core 73 T) = ∅) :
    LocalCond (core 73 T) := by
  intro p hp
  by_cases hp73 : p ≤ 73
  · by_contra h
    have : p ∈ Uset 73 (core 73 T) :=
      Finset.mem_filter.2 ⟨mem_smallPrimes.2 ⟨hp, hp73⟩, h⟩
    rw [hU] at this
    exact Finset.notMem_empty _ this
  · rw [resid]
    refine Finset.sum_eq_zero fun n hn => ?_
    exfalso
    obtain ⟨hnC, hpn⟩ := Finset.mem_filter.1 hn
    have hC := Finset.mem_filter.1 hnC
    have := hC.2 p (Nat.mem_primeFactors.2 ⟨hp, hpn, (hT n hC.1).pos.ne'⟩)
    omega

/-! #### Stars and the component -/

lemma mult_insert {Ps : Finset ℕ} {A : ℕ → Finset ℕ} {P : ℕ} (hP : P ∉ Ps) (q : ℕ) :
    mult (insert P Ps) A q = mult Ps A q + (if q ∈ A P then 1 else 0) := by
  rw [mult, mult, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem]
    intro h'; exact hP (Finset.mem_filter.1 h').1
  · rfl

lemma starVal_insert {Ps : Finset ℕ} {A : ℕ → Finset ℕ} {P : ℕ} (hP : P ∉ Ps) :
    starVal (insert P Ps) A = ∑ q ∈ A P, (1 : ℚ) / (q * P) + starVal Ps A := by
  rw [starVal, starVal, Finset.sum_insert hP]

lemma starEdges_insert {Ps : Finset ℕ} {A : ℕ → Finset ℕ} {P : ℕ} :
    starEdges (insert P Ps) A = (A P).image (· * P) ∪ starEdges Ps A := by
  rw [starEdges, starEdges, Finset.biUnion_insert]

/-- A prime `> 73` divides no product of primes `≤ 73`. -/
lemma big_not_dvd_prod {P : ℕ} (hP : P.Prime) (hP73 : 73 < P) {A : Finset ℕ}
    (hA : A ⊆ smallPrimes 73) : ¬ P ∣ ∏ q ∈ A, q := by
  intro h
  obtain ⟨q, hq, hPq⟩ := (Prime.dvd_finsetProd_iff hP.prime _).1 h
  have hq' := mem_smallPrimes.1 (hA hq)
  have := Nat.le_of_dvd hq'.1.pos hPq
  omega

lemma prod_pos_of_primes {A : Finset ℕ} (hA : A ⊆ smallPrimes 73) : 0 < ∏ q ∈ A, q :=
  Finset.prod_pos fun q hq => (mem_smallPrimes.1 (hA hq)).1.pos

/-- The unique big-big element of a solution with `b = 1`. -/
lemma bbPart_single (hT : ∀ n ∈ T, IsSP n) (hb : (bbPart T).card = 1) :
    ∃ P₁ P₂, P₁.Prime ∧ P₂.Prime ∧ 73 < P₁ ∧ P₁ < P₂ ∧ bbPart T = {P₁ * P₂} := by
  obtain ⟨n, hn⟩ := Finset.card_eq_one.1 hb
  have hmem : n ∈ bbPart T := by rw [hn]; exact Finset.mem_singleton_self n
  obtain ⟨hnG, hns⟩ := Finset.mem_filter.1 hmem
  obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hT _ (Finset.mem_filter.1 hnG).1
  have hp73 : 73 < p := by
    by_contra h
    exact hns p (mem_smallPrimes.2 ⟨hp, by omega⟩) (dvd_mul_right _ _)
  exact ⟨p, q, hp, hq, hp73, hpq, hn⟩

/-- In a solution with `bbPart = {P₁P₂}`, a big neighbour of a big prime comes from that
edge. -/
lemma big_nbr_eq (hT : ∀ n ∈ T, IsSP n) {P₁ P₂ : ℕ} (hP₁ : P₁.Prime) (hP₂ : P₂.Prime)
    (hbb : bbPart T = {P₁ * P₂}) {P R : ℕ} (hP : P ∈ bigPrimesOf T) (hR : R ∈ nbrs T P)
    (hR73 : 73 < R) : (P = P₁ ∧ R = P₂) ∨ (P = P₂ ∧ R = P₁) := by
  have h := bb_of_big_nbr hT hP hR hR73
  rw [hbb, Finset.mem_singleton] at h
  have hPp := prime_of_mem_bigPrimesOf hP
  rcases prime_dvd_sp hP₁ hP₂ hPp ⟨R, h.symm⟩ with rfl | rfl
  · exact Or.inl ⟨rfl, Nat.eq_of_mul_eq_mul_left hPp.pos h⟩
  · refine Or.inr ⟨rfl, ?_⟩
    rw [mul_comm P₁] at h
    exact Nat.eq_of_mul_eq_mul_left hPp.pos h

lemma mem_bigPrimesOf_of_mem {P n : ℕ} (hT : ∀ n ∈ T, IsSP n) (hP : P.Prime) (hP73 : 73 < P)
    (hn : n ∈ T) (hPn : P ∣ n) : P ∈ bigPrimesOf T := by
  rw [mem_bigPrimesOf, mem_primesOf]
  exact ⟨⟨n, hn, Nat.mem_primeFactors.2 ⟨hP, hPn, (hT n hn).pos.ne'⟩⟩, hP73⟩

end Reduction

end SemiprimeEgypt
