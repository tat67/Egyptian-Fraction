/-
Core / big-part decomposition, the unsatisfied set `U`, and the structural lemmas used by the
completion step: `|U| ≤ |G|`, the excess identity, the conditions on the big-neighbour counts
`d_q` (including parity at 2), the residue class of a unique big neighbour, and the star
divisibility lemma.
-/
import SemiprimeEgypt.SumBounds

open Finset

namespace SemiprimeEgypt

variable (B : ℕ)

/-- `n` is *small* if all its prime factors are `≤ B`. -/
def Small (n : ℕ) : Prop := ∀ r ∈ n.primeFactors, r ≤ B

instance : DecidablePred (Small B) := fun n => by unfold Small; infer_instance

/-- The core: elements of `T` all of whose prime factors are `≤ B`. -/
def core (T : Finset ℕ) : Finset ℕ := T.filter (Small B)

/-- The big part: elements of `T` with a prime factor `> B`. -/
def bigPart (T : Finset ℕ) : Finset ℕ := T.filter (fun n => ¬ Small B n)

/-- The small primes `≤ B`. -/
def smallPrimes : Finset ℕ := (Finset.range (B + 1)).filter Nat.Prime

/-- The unsatisfied set of a core `C`: small primes with nonzero core residue. -/
def Uset (C : Finset ℕ) : Finset ℕ := (smallPrimes B).filter (fun q => resid C q ≠ 0)

/-- `d_q`: the number of elements of `G` divisible by `q`. -/
def dcount (G : Finset ℕ) (q : ℕ) : ℕ := (G.filter (fun n => q ∣ n)).card

/-- The number of big-big edges of `G` (elements with no small prime factor). -/
def nbb (G : Finset ℕ) : ℕ := (G.filter (fun n => ∀ q ∈ smallPrimes B, ¬ q ∣ n)).card

variable {B}

lemma mem_smallPrimes {q : ℕ} : q ∈ smallPrimes B ↔ q.Prime ∧ q ≤ B := by
  simp [smallPrimes, Nat.lt_succ_iff, and_comm]

lemma core_union_bigPart (T : Finset ℕ) : core B T ∪ bigPart B T = T :=
  Finset.filter_union_filter_not_eq (p := Small B) T

lemma disjoint_core_bigPart (T : Finset ℕ) : Disjoint (core B T) (bigPart B T) :=
  Finset.disjoint_filter_filter_not T T (Small B)

lemma card_core_add_card_bigPart (T : Finset ℕ) :
    (core B T).card + (bigPart B T).card = T.card :=
  Finset.card_filter_add_card_filter_not (s := T) (Small B)

lemma resid_union {A A' : Finset ℕ} (h : Disjoint A A') (p : ℕ) :
    resid (A ∪ A') p = resid A p + resid A' p := by
  rw [resid, Finset.filter_union, Finset.sum_union (Finset.disjoint_filter_filter h)]; rfl

lemma resid_split (T : Finset ℕ) (p : ℕ) :
    resid T p = resid (core B T) p + resid (bigPart B T) p := by
  conv_lhs => rw [← core_union_bigPart (B := B) T]
  exact resid_union (disjoint_core_bigPart T) p

/-- For a squarefree semiprime `n = p * q`, the prime factors are exactly `p` and `q`. -/
lemma primeFactors_sp {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (p * q).primeFactors = {p, q} := by
  rw [Nat.primeFactors_mul hp.ne_zero hq.ne_zero, hp.primeFactors, hq.primeFactors]; rfl

/-- In a big element divisible by a small prime `q`, the cofactor is a big prime. -/
lemma cofactor_big {n q : ℕ} (hn : IsSP n) (hbig : ¬ Small B n) (hq : q.Prime) (hqB : q ≤ B)
    (hqn : q ∣ n) : B < n / q := by
  obtain ⟨hr, hrq, hmul⟩ := hn.cofactor hq hqn
  by_contra h
  apply hbig
  intro s hs
  have hs' : s ∈ (q * (n / q)).primeFactors := by rwa [hmul]
  rw [primeFactors_sp hq hr (Ne.symm hrq)] at hs'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs'
  rcases hs' with rfl | rfl <;> omega

/-- A big element has at most one small prime factor. -/
lemma small_factor_unique {n q q' : ℕ} (hn : IsSP n) (hbig : ¬ Small B n)
    (hq : q.Prime) (hqB : q ≤ B) (hqn : q ∣ n) (hq' : q'.Prime) (hq'B : q' ≤ B)
    (hq'n : q' ∣ n) : q = q' := by
  obtain ⟨hr, hrq, hmul⟩ := hn.cofactor hq hqn
  have hbigr := cofactor_big hn hbig hq hqB hqn
  rw [← hmul] at hq'n
  rcases prime_dvd_sp hq hr hq' hq'n with h | h
  · exact h.symm
  · omega

variable {T : Finset ℕ}

/-- The inverse of a prime different from `p` is nonzero in `ZMod p`. -/
lemma inv_prime_ne_zero {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hne : r ≠ p) :
    ((r : ZMod p))⁻¹ ≠ 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Ne, inv_eq_zero, ZMod.natCast_eq_zero_iff]
  intro h
  exact hne ((Nat.prime_dvd_prime_iff_eq hp hr).1 h).symm

/-- Every unsatisfied small prime has a big neighbour. -/
lemma exists_big_nbr (hT : ∀ n ∈ T, IsSP n) (hloc : LocalCond T) {q : ℕ}
    (hq : q ∈ Uset B (core B T)) : ∃ n ∈ bigPart B T, q ∣ n := by
  rw [Uset, Finset.mem_filter, mem_smallPrimes] at hq
  have h0 := hloc q hq.1.1
  rw [resid_split (B := B)] at h0
  by_contra hne
  push Not at hne
  have : resid (bigPart B T) q = 0 := by
    rw [resid]
    refine Finset.sum_eq_zero fun n hn => ?_
    rw [Finset.mem_filter] at hn
    exact absurd hn.2 (hne n hn.1)
  rw [this, add_zero] at h0
  exact hq.2 h0

/-- **Lemma 2.**  `|U| ≤ |G|`. -/
theorem card_Uset_le (hT : ∀ n ∈ T, IsSP n) (hloc : LocalCond T) :
    (Uset B (core B T)).card ≤ (bigPart B T).card := by
  classical
  let f : ℕ → ℕ := fun q =>
    if h : ∃ n ∈ bigPart B T, q ∣ n then Classical.choose h else 0
  have hf : ∀ q ∈ Uset B (core B T), f q ∈ bigPart B T ∧ q ∣ f q := by
    intro q hq
    have h := exists_big_nbr hT hloc hq
    simp only [f, dif_pos h]
    exact Classical.choose_spec h
  apply Finset.card_le_card_of_injOn f (fun q hq => (hf q hq).1)
  intro q hq q' hq' hqq'
  have h1 := hf q hq
  have h2 := hf q' hq'
  have hq1 := (mem_smallPrimes.1 (Finset.mem_filter.1 hq).1)
  have hq2 := (mem_smallPrimes.1 (Finset.mem_filter.1 hq').1)
  rw [hqq'] at h1
  have hmem := Finset.mem_filter.1 h2.1
  have hsp := hT _ hmem.1
  exact small_factor_unique hsp hmem.2 hq1.1 hq1.2 h1.2 hq2.1 hq2.2 h2.2

/-- `|C| + |U| ≤ |T|`. -/
theorem card_core_add_card_Uset_le (hT : ∀ n ∈ T, IsSP n) (hloc : LocalCond T) :
    (core B T).card + (Uset B (core B T)).card ≤ T.card := by
  have := card_Uset_le (B := B) hT hloc
  have := card_core_add_card_bigPart (B := B) T
  omega

/-! ### The big-neighbour counts `d_q` -/

/-- Residue of the big part at a small prime `q`: sum of the inverses of the big neighbours. -/
lemma resid_bigPart_eq (hT : ∀ n ∈ T, IsSP n) {q : ℕ} (hq : q.Prime) (hqB : q ≤ B) :
    ∀ n ∈ (bigPart B T).filter (fun n => q ∣ n), B < n / q ∧ (n / q).Prime ∧ n / q ≠ q := by
  intro n hn
  rw [Finset.mem_filter] at hn
  have hmem := Finset.mem_filter.1 hn.1
  obtain ⟨hr, hrq, -⟩ := (hT n hmem.1).cofactor hq hn.2
  exact ⟨cofactor_big (hT n hmem.1) hmem.2 hq hqB hn.2, hr, hrq⟩

/-- **Lemma 4(1).**  `d_q ≥ 1` for `q ∈ U`, and `d_q ≠ 1` for small primes `q ∉ U`. -/
theorem dcount_pos_of_mem_U (hT : ∀ n ∈ T, IsSP n) (hloc : LocalCond T) {q : ℕ}
    (hq : q ∈ Uset B (core B T)) : 1 ≤ dcount (bigPart B T) q := by
  obtain ⟨n, hn, hqn⟩ := exists_big_nbr hT hloc hq
  exact Finset.card_pos.2 ⟨n, Finset.mem_filter.2 ⟨hn, hqn⟩⟩

theorem dcount_ne_one_of_not_mem_U (hT : ∀ n ∈ T, IsSP n) (hloc : LocalCond T) {q : ℕ}
    (hq : q.Prime) (hqB : q ≤ B) (hU : q ∉ Uset B (core B T)) :
    dcount (bigPart B T) q ≠ 1 := by
  intro h1
  have hC : resid (core B T) q = 0 := by
    by_contra h
    exact hU (Finset.mem_filter.2 ⟨mem_smallPrimes.2 ⟨hq, hqB⟩, h⟩)
  have h0 := hloc q hq
  rw [resid_split (B := B), hC, zero_add] at h0
  obtain ⟨n, hn⟩ := Finset.card_eq_one.1 h1
  rw [resid, hn, Finset.sum_singleton] at h0
  have hmem : n ∈ (bigPart B T).filter (fun n => q ∣ n) := by rw [hn]; simp
  obtain ⟨-, hr, hrq⟩ := resid_bigPart_eq hT hq hqB n hmem
  exact inv_prime_ne_zero hq hr hrq h0

/-- **Lemma 4(3), parity at 2.**  Every big neighbour of 2 is an odd prime, so
`ρ(2) + d_2 ≡ 0 (mod 2)`. -/
theorem parity_two (hT : ∀ n ∈ T, IsSP n) (hloc : LocalCond T) (hB : 2 ≤ B) :
    resid (core B T) 2 + (dcount (bigPart B T) 2 : ZMod 2) = 0 := by
  have h0 := hloc 2 Nat.prime_two
  rw [resid_split (B := B)] at h0
  convert h0 using 2
  rw [resid, dcount, Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  obtain ⟨hbig, hr, -⟩ := resid_bigPart_eq hT Nat.prime_two hB n hn
  have hodd : Odd (n / 2) := hr.odd_of_ne_two (by omega)
  have : ((n / 2 : ℕ) : ZMod 2) = 1 := by
    rw [ZMod.natCast_eq_one_iff_odd]; exact hodd
  rw [this, inv_one, Nat.cast_one]

/-- **Lemma 4(4), residue class of a unique big neighbour.**  If `q ∈ U` has exactly one big
neighbour `P` then `P⁻¹ = -ρ(q)` in `ZMod q`. -/
theorem unique_nbr_class (hT : ∀ n ∈ T, IsSP n) (hloc : LocalCond T) {q : ℕ}
    (hq : q.Prime) (hqB : q ≤ B) {n : ℕ}
    (hn : (bigPart B T).filter (fun m => q ∣ m) = {n}) :
    B < n / q ∧ (n / q).Prime ∧ ((n / q : ℕ) : ZMod q)⁻¹ = - resid (core B T) q := by
  have h0 := hloc q hq
  have hG : resid (bigPart B T) q = ((n / q : ℕ) : ZMod q)⁻¹ := by
    rw [resid, hn, Finset.sum_singleton]
  rw [resid_split (B := B), hG] at h0
  have hmem : n ∈ (bigPart B T).filter (fun m => q ∣ m) := by rw [hn]; simp
  obtain ⟨hbig, hr, -⟩ := resid_bigPart_eq hT hq hqB n hmem
  refine ⟨hbig, hr, ?_⟩
  linear_combination h0

/-! ### The excess identity -/

/-- **Decomposition of the big part.**  Every element of `G` has at most one small prime factor,
so a sum over `G` splits into the sums over the elements divisible by each small prime `q`, plus
the sum over the big-big elements (no small prime factor). -/
theorem sum_bigPart_split (hT : ∀ n ∈ T, IsSP n) {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ n ∈ bigPart B T, f n =
      ∑ q ∈ smallPrimes B, ∑ n ∈ (bigPart B T).filter (fun n => q ∣ n), f n +
      ∑ n ∈ (bigPart B T).filter (fun n => ∀ q ∈ smallPrimes B, ¬ q ∣ n), f n := by
  set G := bigPart B T
  rw [← Finset.sum_filter_add_sum_filter_not G (fun n => ∀ q ∈ smallPrimes B, ¬ q ∣ n),
    add_comm]
  congr 1
  have key : ∀ n ∈ G, (if ¬ (∀ q ∈ smallPrimes B, ¬ q ∣ n) then f n else 0) =
      ∑ q ∈ smallPrimes B, (if q ∣ n then f n else 0) := by
    intro n hn
    have hmem := Finset.mem_filter.1 hn
    have hsp := hT n hmem.1
    by_cases hs : ∀ q ∈ smallPrimes B, ¬ q ∣ n
    · rw [if_neg (not_not.2 hs)]
      exact (Finset.sum_eq_zero fun q hq => if_neg (hs q hq)).symm
    · rw [if_pos hs]
      push Not at hs
      obtain ⟨q, hq, hqn⟩ := hs
      rw [Finset.sum_eq_single q]
      · rw [if_pos hqn]
      · intro q' hq' hne
        rw [if_neg]
        intro hq'n
        have h1 := mem_smallPrimes.1 hq
        have h2 := mem_smallPrimes.1 hq'
        exact hne (small_factor_unique hsp hmem.2 h2.1 h2.2 hq'n h1.1 h1.2 hqn)
      · intro h; exact absurd hq h
  calc ∑ n ∈ G.filter (fun n => ¬ ∀ q ∈ smallPrimes B, ¬ q ∣ n), f n
      = ∑ n ∈ G, (if ¬ (∀ q ∈ smallPrimes B, ¬ q ∣ n) then f n else 0) := Finset.sum_filter _ _
    _ = ∑ n ∈ G, ∑ q ∈ smallPrimes B, (if q ∣ n then f n else 0) := Finset.sum_congr rfl key
    _ = ∑ q ∈ smallPrimes B, ∑ n ∈ G, (if q ∣ n then f n else 0) := Finset.sum_comm
    _ = ∑ q ∈ smallPrimes B, ∑ n ∈ G.filter (fun n => q ∣ n), f n :=
        Finset.sum_congr rfl fun q _ => (Finset.sum_filter _ _).symm

/-- **Lemma 4(2), excess identity.**  `|G| = ∑_{q ≤ B} d_q + (number of big-big edges)`. -/
theorem card_bigPart_eq (hT : ∀ n ∈ T, IsSP n) :
    (bigPart B T).card =
      ∑ q ∈ smallPrimes B, dcount (bigPart B T) q + nbb B (bigPart B T) := by
  simp only [dcount, nbb, Finset.card_eq_sum_ones]
  exact sum_bigPart_split hT (fun _ => 1)

/-! ### Stars -/

/-- `n(A) = ∑_{q ∈ A} ∏_{r ∈ A} r / q`. -/
def nA (A : Finset ℕ) : ℕ := ∑ q ∈ A, (∏ r ∈ A, r) / q

/-- For a finite set `A` of primes not containing the prime `P`:
`∑_{q ∈ A} q⁻¹ = 0` in `ZMod P` iff `P ∣ n(A)`. -/
theorem sum_inv_eq_zero_iff_dvd {A : Finset ℕ} (hA : ∀ q ∈ A, q.Prime) {P : ℕ} (hP : P.Prime)
    (hPA : P ∉ A) : (∑ q ∈ A, ((q : ZMod P))⁻¹ = 0) ↔ P ∣ nA A := by
  haveI : Fact P.Prime := ⟨hP⟩
  have hprod0 : ((∏ r ∈ A, r : ℕ) : ZMod P) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    obtain ⟨r, hr, hPr⟩ := (Prime.dvd_finsetProd_iff hP.prime _).1 h
    have := (Nat.prime_dvd_prime_iff_eq hP (hA r hr)).1 hPr
    exact hPA (this ▸ hr)
  have key : ((nA A : ℕ) : ZMod P) = ((∏ r ∈ A, r : ℕ) : ZMod P) * ∑ q ∈ A, ((q : ZMod P))⁻¹ := by
    rw [nA, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hqdvd : q ∣ ∏ r ∈ A, r := Finset.dvd_prod_of_mem _ hq
    have hq0 : ((q : ℕ) : ZMod P) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro h
      have := (Nat.prime_dvd_prime_iff_eq hP (hA q hq)).1 h
      exact hPA (this ▸ hq)
    have hc : ((∏ r ∈ A, r) / q : ℕ) * q = ∏ r ∈ A, r := Nat.div_mul_cancel hqdvd
    have hc' : (((∏ r ∈ A, r) / q : ℕ) : ZMod P) * (q : ZMod P) = ((∏ r ∈ A, r : ℕ) : ZMod P) := by
      rw [← Nat.cast_mul, hc]
    rw [← hc', mul_assoc, mul_inv_cancel₀ hq0, mul_one]
  rw [← ZMod.natCast_eq_zero_iff, key]
  constructor
  · intro h; rw [h, mul_zero]
  · intro h; exact (mul_eq_zero.1 h).resolve_left hprod0

/-- The neighbours of `p` in `T`. -/
def nbrs (T : Finset ℕ) (p : ℕ) : Finset ℕ := (T.filter (fun n => p ∣ n)).image (· / p)

lemma resid_eq_sum_nbrs {p : ℕ} (hp : 0 < p) :
    resid T p = ∑ q ∈ nbrs T p, ((q : ZMod p))⁻¹ := by
  rw [resid, nbrs, Finset.sum_image]
  intro a ha b hb hab
  have ha' := (Finset.mem_filter.1 ha).2
  have hb' := (Finset.mem_filter.1 hb).2
  rw [← Nat.mul_div_cancel' ha', ← Nat.mul_div_cancel' hb']
  exact congrArg (p * ·) hab

lemma prime_of_mem_nbrs (hT : ∀ n ∈ T, IsSP n) {p q : ℕ} (hp : p.Prime) (hq : q ∈ nbrs T p) :
    q.Prime ∧ q ≠ p ∧ p * q ∈ T := by
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hq
  rw [Finset.mem_filter] at hn
  obtain ⟨h1, h2, h3⟩ := (hT n hn.1).cofactor hp hn.2
  exact ⟨h1, h2, by rw [h3]; exact hn.1⟩

/-- **Star lemma.**  If `P` is a prime occurring in `T` whose neighbours `A = N(P)` are
all `≤ B < P`, then `P ∣ n(A)`, hence `P ≤ n(A)`, and `|A| ≥ 2`. -/
theorem star_dvd (hT : ∀ n ∈ T, IsSP n) (hloc : LocalCond T) {P : ℕ} (hP : P.Prime) :
    P ∣ nA (nbrs T P) := by
  have h0 := hloc P hP
  rw [resid_eq_sum_nbrs hP.pos] at h0
  refine (sum_inv_eq_zero_iff_dvd (fun q hq => (prime_of_mem_nbrs hT hP hq).1) hP ?_).1 h0
  intro hPP
  exact (prime_of_mem_nbrs hT hP hPP).2.1 rfl

theorem star_card_ne_one (hT : ∀ n ∈ T, IsSP n) (hloc : LocalCond T) {P : ℕ} (hP : P.Prime) :
    (nbrs T P).card ≠ 1 := by
  intro h1
  obtain ⟨q, hq⟩ := Finset.card_eq_one.1 h1
  have h0 := hloc P hP
  rw [resid_eq_sum_nbrs hP.pos, hq, Finset.sum_singleton] at h0
  have := prime_of_mem_nbrs hT hP (hq ▸ Finset.mem_singleton_self q)
  exact inv_prime_ne_zero hP this.1 this.2.1 h0

lemma nA_pos {A : Finset ℕ} (hA : ∀ q ∈ A, q.Prime) (hne : A.Nonempty) : 0 < nA A := by
  obtain ⟨q, hq⟩ := hne
  rw [nA]
  have hdvd : q ∣ ∏ r ∈ A, r := Finset.dvd_prod_of_mem _ hq
  have hpos : 0 < (∏ r ∈ A, r) / q :=
    Nat.div_pos (Nat.le_of_dvd (Finset.prod_pos fun r hr => (hA r hr).pos) hdvd) (hA q hq).pos
  exact lt_of_lt_of_le hpos (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hq)

theorem star_le_nA (hT : ∀ n ∈ T, IsSP n) (hloc : LocalCond T) {P : ℕ} (hP : P.Prime)
    (hne : (nbrs T P).Nonempty) : P ≤ nA (nbrs T P) :=
  Nat.le_of_dvd (nA_pos (fun q hq => (prime_of_mem_nbrs hT hP hq).1) hne)
    (star_dvd hT hloc hP)

end SemiprimeEgypt
