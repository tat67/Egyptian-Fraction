/-
Decomposition of the big part `G` by big primes (README §4, "stars").

Every element of `G` is either `q * P` with `q ≤ 73 < P` (a *small edge* of the big prime `P`)
or a big-big element `P * P'`.  We prove
* `bigPart_eq`: `G = starEdges (big primes of T) (small neighbours) ∪ bbPart T`,
* `recipSum_bigPart_eq`: the corresponding value identity,
* `dcount_eq_mult`: `d_q` = number of big primes adjacent to `q`,
* `starCand_of_real`: a big prime all of whose neighbours are small is a *candidate star*
  (prime `> 73`, neighbours in `S`, `2 ≤ |A| ≤ |T| - 36`, `P ∣ n(A)`, residue condition when
  `d_q = 1`).
-/
import SemiprimeEgypt.Values

open Finset

namespace SemiprimeEgypt

/-- The big primes of `T` (primes `> 73` occurring in some element of `T`). -/
def bigPrimesOf (T : Finset ℕ) : Finset ℕ := (primesOf T).filter (fun P => 73 < P)

/-- The small neighbours (`≤ 73`) of `P`. -/
def smallNbrs (T : Finset ℕ) (P : ℕ) : Finset ℕ := (nbrs T P).filter (· ≤ 73)

/-- The big-big elements of `T`. -/
def bbPart (T : Finset ℕ) : Finset ℕ :=
  (bigPart 73 T).filter (fun n => ∀ q ∈ smallPrimes 73, ¬ q ∣ n)

/-- The edges of a family of stars `P ↦ A P` (`P ∈ Ps`): all products `q * P`, `q ∈ A P`. -/
def starEdges (Ps : Finset ℕ) (A : ℕ → Finset ℕ) : Finset ℕ :=
  Ps.biUnion (fun P => (A P).image (· * P))

/-- The value of a family of stars. -/
def starVal (Ps : Finset ℕ) (A : ℕ → Finset ℕ) : ℚ :=
  ∑ P ∈ Ps, ∑ q ∈ A P, (1 : ℚ) / (q * P)

/-- The number of stars of the family containing `q`. -/
def mult (Ps : Finset ℕ) (A : ℕ → Finset ℕ) (q : ℕ) : ℕ := (Ps.filter (fun P => q ∈ A P)).card

variable {T : Finset ℕ}

lemma nbb_eq_card_bbPart (T : Finset ℕ) : nbb 73 (bigPart 73 T) = (bbPart T).card := rfl

lemma mem_nbrs {P q : ℕ} (hP : 0 < P) : q ∈ nbrs T P ↔ P * q ∈ T := by
  rw [nbrs, Finset.mem_image]
  constructor
  · rintro ⟨n, hn, rfl⟩
    have := Finset.mem_filter.1 hn
    rw [Nat.mul_div_cancel' this.2]; exact this.1
  · intro h
    exact ⟨P * q, Finset.mem_filter.2 ⟨h, dvd_mul_right _ _⟩, Nat.mul_div_cancel_left q hP⟩

lemma mem_bigPrimesOf {P : ℕ} : P ∈ bigPrimesOf T ↔ P ∈ primesOf T ∧ 73 < P :=
  Finset.mem_filter

lemma prime_of_mem_bigPrimesOf {P : ℕ} (h : P ∈ bigPrimesOf T) : P.Prime :=
  prime_of_mem_primesOf T (mem_bigPrimesOf.1 h).1

lemma mem_smallNbrs {P q : ℕ} (hP : 0 < P) : q ∈ smallNbrs T P ↔ P * q ∈ T ∧ q ≤ 73 := by
  rw [smallNbrs, Finset.mem_filter, mem_nbrs hP]

lemma smallNbrs_subset (hT : ∀ n ∈ T, IsSP n) {P : ℕ} (hP : P.Prime) :
    smallNbrs T P ⊆ smallPrimes 73 := by
  intro q hq
  have h := Finset.mem_filter.1 hq
  exact mem_smallPrimes.2 ⟨(prime_of_mem_nbrs hT hP h.1).1, h.2⟩

/-- A product `P * q` with `P` a prime `> 73` is not small. -/
lemma not_small_of_big_factor {P q : ℕ} (hP : P.Prime) (hP73 : 73 < P) (hq : 0 < q) :
    ¬ Small 73 (P * q) := by
  intro hs
  have := hs P (Nat.mem_primeFactors.2 ⟨hP, dvd_mul_right _ _, (Nat.mul_pos hP.pos hq).ne'⟩)
  omega

lemma mem_bigPart_iff (hT : ∀ n ∈ T, IsSP n) {n : ℕ} :
    n ∈ bigPart 73 T ↔ n ∈ starEdges (bigPrimesOf T) (smallNbrs T) ∨ n ∈ bbPart T := by
  constructor
  · intro hn
    by_cases hs : ∀ q ∈ smallPrimes 73, ¬ q ∣ n
    · exact Or.inr (Finset.mem_filter.2 ⟨hn, hs⟩)
    · left
      push Not at hs
      obtain ⟨q, hq, hqn⟩ := hs
      have hq' := mem_smallPrimes.1 hq
      have hmem := Finset.mem_filter.1 hn
      obtain ⟨hr, -, hmul⟩ := (hT n hmem.1).cofactor hq'.1 hqn
      have hbig := cofactor_big (hT n hmem.1) hmem.2 hq'.1 hq'.2 hqn
      rw [starEdges, Finset.mem_biUnion]
      refine ⟨n / q, ?_, ?_⟩
      · rw [mem_bigPrimesOf, mem_primesOf]
        exact ⟨⟨n, hmem.1, Nat.mem_primeFactors.2
          ⟨hr, Nat.div_dvd_of_dvd hqn, (hT n hmem.1).pos.ne'⟩⟩, hbig⟩
      · rw [Finset.mem_image]
        refine ⟨q, (mem_smallNbrs hr.pos).2 ⟨?_, hq'.2⟩, ?_⟩
        · rw [mul_comm, hmul]; exact hmem.1
        · exact hmul
  · rintro (h | h)
    · rw [starEdges, Finset.mem_biUnion] at h
      obtain ⟨P, hP, hn⟩ := h
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hn
      have hP' := mem_bigPrimesOf.1 hP
      have hPp := prime_of_mem_primesOf T hP'.1
      have hq' := (mem_smallNbrs hPp.pos).1 hq
      have hqpos : 0 < q := by
        have := (hT _ hq'.1).pos
        rcases Nat.eq_zero_or_pos q with h0 | h0
        · rw [h0, mul_zero] at this; omega
        · exact h0
      refine Finset.mem_filter.2 ⟨by rw [mul_comm]; exact hq'.1, ?_⟩
      rw [mul_comm]
      exact not_small_of_big_factor hPp hP'.2 hqpos
    · exact (Finset.mem_filter.1 h).1

/-- `G = (small edges of the big primes) ∪ (big-big elements)`. -/
theorem bigPart_eq (hT : ∀ n ∈ T, IsSP n) :
    bigPart 73 T = starEdges (bigPrimesOf T) (smallNbrs T) ∪ bbPart T :=
  Finset.ext fun n => by rw [Finset.mem_union]; exact mem_bigPart_iff hT

lemma disjoint_starEdges_bbPart (hT : ∀ n ∈ T, IsSP n) :
    Disjoint (starEdges (bigPrimesOf T) (smallNbrs T)) (bbPart T) := by
  rw [Finset.disjoint_left]
  intro n hn hbb
  rw [starEdges, Finset.mem_biUnion] at hn
  obtain ⟨P, hP, hn⟩ := hn
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hn
  have hPp := prime_of_mem_bigPrimesOf hP
  have hqS := smallNbrs_subset hT hPp hq
  exact (Finset.mem_filter.1 hbb).2 q hqS (dvd_mul_right _ _)

/-- The value of a star family whose centres are primes `> 73` and whose leaves are positive
integers `≤ 73`: its edges are distinct and `recipSum (starEdges Ps A) = starVal Ps A`. -/
theorem recipSum_starEdges {Ps : Finset ℕ} {A : ℕ → Finset ℕ}
    (hPs : ∀ P ∈ Ps, P.Prime ∧ 73 < P) (hA : ∀ P ∈ Ps, ∀ q ∈ A P, 0 < q ∧ q ≤ 73) :
    recipSum (starEdges Ps A) = starVal Ps A := by
  rw [recipSum, starEdges, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun P hP => ?_
    rw [Finset.sum_image]
    · refine Finset.sum_congr rfl fun q _ => ?_
      push_cast; rfl
    · intro a _ b _ hab
      exact Nat.eq_of_mul_eq_mul_right (hPs P hP).1.pos hab
  · intro P hP P' hP' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro n hn hn'
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hn
    obtain ⟨q', hq', heq⟩ := Finset.mem_image.1 hn'
    have h1 := hPs P hP
    have h2 := hPs P' hP'
    have hdvd : P ∣ q' * P' := by rw [heq]; exact dvd_mul_left _ _
    rcases (Nat.Prime.dvd_mul h1.1).1 hdvd with h | h
    · have := Nat.le_of_dvd (hA P' hP' q' hq').1 h
      have := (hA P' hP' q' hq').2
      omega
    · exact hne ((Nat.prime_dvd_prime_iff_eq h1.1 h2.1).1 h)

lemma smallNbrs_spec (hT : ∀ n ∈ T, IsSP n) :
    ∀ P ∈ bigPrimesOf T, ∀ q ∈ smallNbrs T P, 0 < q ∧ q ≤ 73 := by
  intro P hP q hq
  have hPp := prime_of_mem_bigPrimesOf hP
  have := mem_smallPrimes.1 (smallNbrs_subset hT hPp hq)
  exact ⟨this.1.pos, this.2⟩

/-- **Value identity.**  `Σ_G = Σ_{P big} Σ_{q ∈ N(P), q ≤ 73} 1/(qP) + Σ_{big-big} 1/n`. -/
theorem recipSum_bigPart_eq (hT : ∀ n ∈ T, IsSP n) :
    recipSum (bigPart 73 T) = starVal (bigPrimesOf T) (smallNbrs T) + recipSum (bbPart T) := by
  rw [bigPart_eq hT, recipSum_union (disjoint_starEdges_bbPart hT),
    recipSum_starEdges (fun P hP => ⟨prime_of_mem_bigPrimesOf hP, (mem_bigPrimesOf.1 hP).2⟩)
      (smallNbrs_spec hT)]

/-- `d_q` is the number of big primes adjacent to `q`. -/
theorem dcount_eq_mult (hT : ∀ n ∈ T, IsSP n) {q : ℕ} (hq : q ∈ smallPrimes 73) :
    dcount (bigPart 73 T) q = mult (bigPrimesOf T) (smallNbrs T) q := by
  have hq' := mem_smallPrimes.1 hq
  have key : (bigPart 73 T).filter (fun n => q ∣ n) =
      ((bigPrimesOf T).filter (fun P => q ∈ smallNbrs T P)).image (q * ·) := by
    ext n
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hn, hqn⟩
      have hmem := Finset.mem_filter.1 hn
      obtain ⟨hr, -, hmul⟩ := (hT n hmem.1).cofactor hq'.1 hqn
      have hbig := cofactor_big (hT n hmem.1) hmem.2 hq'.1 hq'.2 hqn
      refine ⟨n / q, Finset.mem_filter.2 ⟨?_, ?_⟩, hmul⟩
      · rw [mem_bigPrimesOf, mem_primesOf]
        exact ⟨⟨n, hmem.1, Nat.mem_primeFactors.2
          ⟨hr, Nat.div_dvd_of_dvd hqn, (hT n hmem.1).pos.ne'⟩⟩, hbig⟩
      · rw [mem_smallNbrs hr.pos, mul_comm, hmul]; exact ⟨hmem.1, hq'.2⟩
    · rintro ⟨P, hP, rfl⟩
      have hP' := Finset.mem_filter.1 hP
      have hPp := prime_of_mem_bigPrimesOf hP'.1
      have hs := (mem_smallNbrs hPp.pos).1 hP'.2
      refine ⟨Finset.mem_filter.2 ⟨by rw [mul_comm]; exact hs.1, ?_⟩, dvd_mul_right _ _⟩
      rw [mul_comm]
      exact not_small_of_big_factor hPp (mem_bigPrimesOf.1 hP'.1).2 hq'.1.pos
  rw [dcount, key, mult, Finset.card_image_of_injective]
  intro a b hab
  exact Nat.eq_of_mul_eq_mul_left hq'.1.pos hab

/-- A big neighbour of a big prime gives a big-big element. -/
lemma bb_of_big_nbr (hT : ∀ n ∈ T, IsSP n) {P R : ℕ} (hP : P ∈ bigPrimesOf T)
    (hR : R ∈ nbrs T P) (hR73 : 73 < R) : P * R ∈ bbPart T := by
  have hPp := prime_of_mem_bigPrimesOf hP
  have hP73 := (mem_bigPrimesOf.1 hP).2
  obtain ⟨hRp, -, hmem⟩ := prime_of_mem_nbrs hT hPp hR
  refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hmem,
    not_small_of_big_factor hPp hP73 hRp.pos⟩, ?_⟩
  intro q hq hqd
  have hq' := mem_smallPrimes.1 hq
  rcases prime_dvd_sp hPp hRp hq'.1 hqd with rfl | rfl <;> omega

/-- If there are no big-big elements, every neighbour of a big prime is small. -/
lemma nbrs_small_of_bb_empty (hT : ∀ n ∈ T, IsSP n) (hbb : bbPart T = ∅) {P : ℕ}
    (hP : P ∈ bigPrimesOf T) : ∀ q ∈ nbrs T P, q ≤ 73 := by
  intro q hq
  by_contra h
  have := bb_of_big_nbr hT hP hq (by omega)
  rw [hbb] at this
  exact Finset.notMem_empty _ this

lemma smallNbrs_eq_nbrs {P : ℕ} (h : ∀ q ∈ nbrs T P, q ≤ 73) : smallNbrs T P = nbrs T P :=
  Finset.filter_true_of_mem h

/-- A big prime of `T` has at least one neighbour. -/
lemma nbrs_nonempty {P : ℕ} (hP : P ∈ bigPrimesOf T) : (nbrs T P).Nonempty := by
  obtain ⟨n, hn, hPn⟩ := (mem_primesOf T).1 (mem_bigPrimesOf.1 hP).1
  have hPn' := Nat.dvd_of_mem_primeFactors hPn
  exact ⟨n / P, Finset.mem_image.2 ⟨n, Finset.mem_filter.2 ⟨hn, hPn'⟩, rfl⟩⟩

/-- **Candidate stars.**  In a set `T` of squarefree semiprimes satisfying (*) everywhere with
`Σ 1/n = 1`, a big prime `P` all of whose neighbours are `≤ 73` gives a candidate star
`(P, A = N(P))`: `P` prime `> 73`, `A ⊆ S`, every `q ∈ A` has `d_q ≥ 1`, `2 ≤ |A|`,
`|A| + 36 ≤ |T|`, `P ∣ n(A)`, and `P⁻¹ = -ρ(q)` in `ZMod q` whenever `d_q = 1`. -/
theorem starCand_of_real (hT : ∀ n ∈ T, IsSP n) (hloc : LocalCond T) (h1 : recipSum T = 1)
    {P : ℕ} (hP : P ∈ bigPrimesOf T) (hall : ∀ q ∈ nbrs T P, q ≤ 73) :
    P.Prime ∧ 73 < P ∧ nbrs T P ⊆ smallPrimes 73 ∧
      (∀ q ∈ nbrs T P, 1 ≤ dcount (bigPart 73 T) q) ∧ 2 ≤ (nbrs T P).card ∧
      (nbrs T P).card + 36 ≤ T.card ∧ P ∣ nA (nbrs T P) ∧
      ∀ q ∈ nbrs T P, dcount (bigPart 73 T) q = 1 →
        ((P : ZMod q))⁻¹ = - resid (core 73 T) q := by
  have hPp := prime_of_mem_bigPrimesOf hP
  have hP73 := (mem_bigPrimesOf.1 hP).2
  have hsub : nbrs T P ⊆ smallPrimes 73 := by
    intro q hq; exact mem_smallPrimes.2 ⟨(prime_of_mem_nbrs hT hPp hq).1, hall q hq⟩
  -- the edge `q * P` lies in `G` and is divisible by `q`
  have hedge : ∀ q ∈ nbrs T P, q * P ∈ (bigPart 73 T).filter (fun n => q ∣ n) := by
    intro q hq
    obtain ⟨hqp, -, hmem⟩ := prime_of_mem_nbrs hT hPp hq
    refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨by rw [mul_comm]; exact hmem, ?_⟩,
      dvd_mul_right _ _⟩
    rw [mul_comm]; exact not_small_of_big_factor hPp hP73 hqp.pos
  refine ⟨hPp, hP73, hsub, ?_, ?_, star_size hT h1 hPp hP73 hall, star_dvd hT hloc hPp, ?_⟩
  · intro q hq
    exact Finset.card_pos.2 ⟨_, hedge q hq⟩
  · have hne := nbrs_nonempty hP
    have h1' := star_card_ne_one hT hloc hPp
    have := Finset.card_pos.2 hne
    omega
  · intro q hq hd
    have hq' := mem_smallPrimes.1 (hsub hq)
    obtain ⟨n, hn⟩ := Finset.card_eq_one.1 hd
    have hmem := hedge q hq
    have hn' : (bigPart 73 T).filter (fun m => q ∣ m) = {n} := hn
    rw [hn', Finset.mem_singleton] at hmem
    rw [← hmem] at hn'
    obtain ⟨-, -, hcls⟩ := unique_nbr_class hT hloc hq'.1 hq'.2 hn'
    rwa [Nat.mul_div_cancel_left P hq'.1.pos] at hcls

end SemiprimeEgypt
