/-
Squarefree semiprimes, reciprocal sums, and the local (p-adic) criterion for integrality.

Main result: `integral_iff_localCond`.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Qify
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

open Finset

namespace SemiprimeEgypt

/-- `n` is a squarefree semiprime: `n = p * q` with primes `p < q`. -/
def IsSP (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ n = p * q

/-- The reciprocal sum of a finite set of natural numbers. -/
def recipSum (T : Finset ℕ) : ℚ := ∑ n ∈ T, (1 : ℚ) / n

/-- The local residue of `T` at `p`: `∑_{n ∈ T, p ∣ n} (n / p)⁻¹` in `ZMod p`.  For a set of
squarefree semiprimes this is `∑_{q ∈ N(p)} q⁻¹`, where `N(p) = {q : p * q ∈ T}`. -/
def resid (T : Finset ℕ) (p : ℕ) : ZMod p :=
  ∑ n ∈ T.filter (fun n => p ∣ n), (((n / p : ℕ) : ZMod p))⁻¹

/-- The local conditions `(*)` at every prime. -/
def LocalCond (T : Finset ℕ) : Prop := ∀ p, p.Prime → resid T p = 0

/-! ### Elementary facts about squarefree semiprimes -/

lemma IsSP.pos {n : ℕ} (h : IsSP n) : 0 < n := by
  obtain ⟨p, q, hp, hq, -, rfl⟩ := h
  exact Nat.mul_pos hp.pos hq.pos

/-- If a prime `r` divides the semiprime `p * q` then `r = p` or `r = q`. -/
lemma prime_dvd_sp {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (h : r ∣ p * q) : r = p ∨ r = q := by
  rcases (Nat.Prime.dvd_mul hr).1 h with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr hp).1 h)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr hq).1 h)

/-- For a squarefree semiprime `n` and a prime `r ∣ n`, the cofactor `n / r` is a prime
different from `r`. -/
lemma IsSP.cofactor {n r : ℕ} (h : IsSP n) (hr : r.Prime) (hrn : r ∣ n) :
    (n / r).Prime ∧ n / r ≠ r ∧ r * (n / r) = n := by
  obtain ⟨p, q, hp, hq, hpq, rfl⟩ := h
  rcases prime_dvd_sp hp hq hr hrn with rfl | rfl
  · refine ⟨?_, ?_, ?_⟩
    · rw [Nat.mul_div_cancel_left _ hr.pos]; exact hq
    · rw [Nat.mul_div_cancel_left _ hr.pos]; omega
    · rw [Nat.mul_div_cancel_left _ hr.pos]
  · refine ⟨?_, ?_, ?_⟩
    · rw [Nat.mul_div_cancel _ hr.pos]; exact hp
    · rw [Nat.mul_div_cancel _ hr.pos]; omega
    · rw [Nat.mul_div_cancel _ hr.pos, mul_comm]

/-! ### The local criterion -/

section Criterion

variable (T : Finset ℕ)

/-- The primes occurring in `T`. -/
def primesOf : Finset ℕ := T.biUnion (fun n => n.primeFactors)

/-- The product of the primes occurring in `T` (a common denominator). -/
def denom : ℕ := ∏ r ∈ primesOf T, r

lemma mem_primesOf {r : ℕ} : r ∈ primesOf T ↔ ∃ n ∈ T, r ∈ n.primeFactors := by
  simp [primesOf]

lemma prime_of_mem_primesOf {r : ℕ} (h : r ∈ primesOf T) : r.Prime := by
  obtain ⟨n, -, hn⟩ := (mem_primesOf T).1 h
  exact Nat.prime_of_mem_primeFactors hn

lemma denom_pos : 0 < denom T :=
  Finset.prod_pos fun r hr => (prime_of_mem_primesOf T hr).pos

lemma dvd_denom {n : ℕ} (hT : ∀ m ∈ T, IsSP m) (hn : n ∈ T) : n ∣ denom T := by
  obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hT n hn
  have hsub : ({p, q} : Finset ℕ) ⊆ primesOf T := by
    intro r hr
    rw [mem_primesOf]
    refine ⟨p * q, hn, ?_⟩
    rw [Nat.mem_primeFactors]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact ⟨hp, dvd_mul_right _ _, (Nat.mul_pos hp.pos hq.pos).ne'⟩
    · exact ⟨hq, dvd_mul_left _ _, (Nat.mul_pos hp.pos hq.pos).ne'⟩
  have := Finset.prod_dvd_prod_of_subset _ _ (fun r => r) hsub
  rwa [Finset.prod_pair (Nat.ne_of_lt hpq)] at this

/-- The numerator `N = ∑_{n ∈ T} D / n`. -/
def numer : ℕ := ∑ n ∈ T, denom T / n

lemma recipSum_eq (hT : ∀ m ∈ T, IsSP m) :
    recipSum T = (numer T : ℚ) / denom T := by
  have hD : (denom T : ℚ) ≠ 0 := by exact_mod_cast (denom_pos T).ne'
  rw [eq_div_iff hD, recipSum, Finset.sum_mul, numer, Nat.cast_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (hT n hn).pos.ne'
  rw [Nat.cast_div (dvd_denom T hT hn) hn0]
  field_simp

lemma isInt_iff_dvd (N D : ℕ) (hD : 0 < D) :
    (∃ z : ℤ, (N : ℚ) / D = z) ↔ D ∣ N := by
  constructor
  · rintro ⟨z, hz⟩
    have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
    have h1 : (N : ℚ) = z * D := by rw [div_eq_iff hD'] at hz; exact hz
    have h2 : (N : ℤ) = z * D := by exact_mod_cast h1
    have h3 : (D : ℤ) ∣ (N : ℤ) := ⟨z, by rw [h2, mul_comm]⟩
    exact Int.natCast_dvd_natCast.1 h3
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
    push_cast
    field_simp

/-- `p ∣ N` exactly when the local condition at `p` holds (for `p` occurring in `T`). -/
lemma dvd_numer_iff (hT : ∀ m ∈ T, IsSP m) {p : ℕ} (hpV : p ∈ primesOf T) :
    p ∣ numer T ↔ resid T p = 0 := by
  have hp : p.Prime := prime_of_mem_primesOf T hpV
  haveI : Fact p.Prime := ⟨hp⟩
  -- D = p * D', with p ∤ D'
  set D' : ℕ := ∏ r ∈ (primesOf T).erase p, r with hD'
  have hDD' : denom T = p * D' := by
    rw [denom, hD', Finset.mul_prod_erase (primesOf T) (fun r => r) hpV]
  have hpD' : ¬ p ∣ D' := by
    intro h
    obtain ⟨r, hr, hpr⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 h
    have hr' : r.Prime := prime_of_mem_primesOf T (Finset.mem_of_mem_erase hr)
    have : p = r := (Nat.prime_dvd_prime_iff_eq hp hr').1 hpr
    exact (Finset.ne_of_mem_erase hr) this.symm
  have hD'0 : (D' : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact hpD'
  -- the numerator modulo p
  have key : ((numer T : ℕ) : ZMod p) = (D' : ZMod p) * resid T p := by
    rw [numer, Nat.cast_sum, resid, Finset.mul_sum,
      ← Finset.sum_filter_add_sum_filter_not T (fun n => p ∣ n)]
    have hzero : ∑ n ∈ T.filter (fun n => ¬ p ∣ n), ((denom T / n : ℕ) : ZMod p) = 0 := by
      refine Finset.sum_eq_zero fun n hn => ?_
      rw [Finset.mem_filter] at hn
      rw [ZMod.natCast_eq_zero_iff]
      have hnD := dvd_denom T hT hn.1
      have h1 : denom T = denom T / n * n := (Nat.div_mul_cancel hnD).symm
      have h2 : p ∣ denom T / n * n := by rw [← h1, hDD']; exact dvd_mul_right _ _
      rcases (Nat.Prime.dvd_mul hp).1 h2 with h | h
      · exact h
      · exact absurd h hn.2
    rw [hzero, add_zero]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_filter] at hn
    obtain ⟨hq, hqp, hpn⟩ := (hT n hn.1).cofactor hp hn.2
    set q := n / p
    have hq0 : (q : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro h
      exact hqp ((Nat.prime_dvd_prime_iff_eq hp hq).1 h).symm
    -- denom / n * q = D'
    have hnD := dvd_denom T hT hn.1
    have hmul : denom T / n * q = D' := by
      have h1 : denom T = denom T / n * n := (Nat.div_mul_cancel hnD).symm
      have h2 : p * (denom T / n * q) = p * D' := by
        rw [← hDD']
        calc p * (denom T / n * q) = denom T / n * (p * q) := by ring
          _ = denom T / n * n := by rw [hpn]
          _ = denom T := h1.symm
      exact Nat.eq_of_mul_eq_mul_left hp.pos h2
    have hcast : ((denom T / n : ℕ) : ZMod p) * (q : ZMod p) = (D' : ZMod p) := by
      rw [← Nat.cast_mul, hmul]
    have h1 : (q : ZMod p) * ((q : ZMod p))⁻¹ = 1 := mul_inv_cancel₀ hq0
    rw [← hcast, mul_assoc, h1, mul_one]
  rw [← ZMod.natCast_eq_zero_iff, key]
  constructor
  · intro h; exact (mul_eq_zero.1 h).resolve_left hD'0
  · intro h; rw [h, mul_zero]

lemma resid_eq_zero_of_not_mem (hT : ∀ m ∈ T, IsSP m) {p : ℕ} (hp : p.Prime)
    (hpV : p ∉ primesOf T) : resid T p = 0 := by
  rw [resid]
  refine Finset.sum_eq_zero fun n hn => ?_
  rw [Finset.mem_filter] at hn
  exfalso
  apply hpV
  rw [mem_primesOf]
  exact ⟨n, hn.1, Nat.mem_primeFactors.2 ⟨hp, hn.2, (hT n hn.1).pos.ne'⟩⟩

/-- **Local criterion.**  For a finite set `T` of squarefree semiprimes, the reciprocal sum is
an integer if and only if the congruence `∑_{q ∈ N(p)} q⁻¹ ≡ 0 (mod p)` holds at every prime. -/
theorem integral_iff_localCond (hT : ∀ m ∈ T, IsSP m) :
    (∃ z : ℤ, recipSum T = z) ↔ LocalCond T := by
  rw [recipSum_eq T hT, isInt_iff_dvd _ _ (denom_pos T)]
  constructor
  · intro h p hp
    by_cases hpV : p ∈ primesOf T
    · exact (dvd_numer_iff T hT hpV).1
        (dvd_trans (Finset.dvd_prod_of_mem (fun r => r) hpV) h)
    · exact resid_eq_zero_of_not_mem T hT hp hpV
  · intro h
    refine Finset.prod_primes_dvd _ (fun r hr => (prime_of_mem_primesOf T hr).prime) ?_
    intro r hr
    exact (dvd_numer_iff T hT hr).2 (h r (prime_of_mem_primesOf T hr))

end Criterion

end SemiprimeEgypt
