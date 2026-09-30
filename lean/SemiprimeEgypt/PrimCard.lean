/-
# A Lagrangian bound for the number of terms

For a threshold `A` and a common multiple `D` of the integers below `A`, a *chain cover* is a
list of divisibility chains `C` with weights `y_C ∈ ℕ` such that every candidate `n < A` (not a
prime power) satisfies `∑_{C ∋ n} y_C ≥ D/n − D/A`.  With `W = ∑ y_C`, every primitive set
`T ⊆ {2, 3, …}` without prime powers satisfies

    ∑_{n ∈ T} 1/n  ≤  |T|/A + W/D − (1/A − 1/m)        for every m ∈ T with m ≥ A,

because `1/n = 1/A + (1/n − 1/A)`, a primitive set meets each chain at most once, and the
terms with `n ≥ A` contribute `1/n − 1/A ≤ 0`.  (`lagrange_bound`.)

With `A = 129` (the 38th squarefree semiprime) this gives: a primitive `T` with `∑ 1/n = 1` and
`|T| ≤ 38` has all elements `≤ 158`, which `no_solution_le_412` excludes.  Hence `|T| ≥ 39`
(`card_ge_39` in `PrimMain.lean`).
-/
import SemiprimeEgypt.PrimCheck

open Finset

namespace SemiprimeEgypt.Prim

/-- Data for the Lagrangian bound. -/
structure LData where
  A : ℕ
  D : ℕ
  /-- primes used to recognize prime powers -/
  PL : List ℕ
  /-- chains: (elements, weight) -/
  chains : List (List ℕ × ℕ)

variable (L : LData)

def LData.W : ℕ := (L.chains.map Prod.snd).sum

/-- The cover of `n`: total weight of the chains containing `n`. -/
def LData.cov (n : ℕ) : ℕ := ((L.chains.filter (fun C => n ∈ C.1)).map Prod.snd).sum

def ppB' (PL : List ℕ) (n : ℕ) : Bool := isPrimeB n || PL.any (fun p => isPowOf p n n)

structure LData.Valid : Prop where
  Dpos : 0 < L.D
  Apos : 0 < L.A
  dvdA : L.A ∣ L.D
  dvd : ∀ n, 2 ≤ n → n < L.A → ppB' L.PL n = false → n ∣ L.D
  pl : ∀ p ∈ L.PL, p.Prime
  chain : ∀ C ∈ L.chains, ∀ a ∈ C.1, ∀ b ∈ C.1, a ∣ b ∨ b ∣ a
  cover : ∀ n, 2 ≤ n → n < L.A → ppB' L.PL n = false → L.D / n - L.D / L.A ≤ L.cov n

def LData.validB : Bool :=
  decide (0 < L.D) && decide (0 < L.A) && L.D % L.A == 0 &&
  (List.range L.A).all (fun n => decide (n < 2) || ppB' L.PL n || L.D % n == 0) &&
  L.PL.all isPrimeB &&
  L.chains.all (fun C => C.1.all (fun a => C.1.all (fun b => b % a == 0 || a % b == 0))) &&
  (List.range L.A).all (fun n => decide (n < 2) || ppB' L.PL n ||
    decide (L.D / n - L.D / L.A ≤ L.cov n))

theorem LData.valid_of_validB (h : L.validB = true) : L.Valid := by
  simp only [LData.validB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hD, hA⟩, hdA⟩, hdv⟩, hpl⟩, hch⟩, hcov⟩ := h
  refine ⟨hD, hA, Nat.dvd_of_mod_eq_zero hdA, ?_, fun p hp => (isPrimeB_iff p).1 (hpl p hp),
    ?_, ?_⟩
  · intro n h2 hn hpp
    rcases hdv n hn with (h | h) | h
    · omega
    · rw [hpp] at h; exact absurd h (by decide)
    · exact Nat.dvd_of_mod_eq_zero h
  · intro C hC a ha b hb
    rcases hch C hC a ha b hb with h | h
    · exact Or.inl (Nat.dvd_of_mod_eq_zero h)
    · exact Or.inr (Nat.dvd_of_mod_eq_zero h)
  · intro n h2 hn hpp
    rcases hcov n hn with (h | h) | h
    · omega
    · rw [hpp] at h; exact absurd h (by decide)
    · exact h

variable {L}

/-- `ppB'` recognizes prime powers soundly. -/
theorem primePow_of_ppB' (hv : L.Valid) {n : ℕ} (h : ppB' L.PL n = true) :
    ∃ p k, p.Prime ∧ 0 < k ∧ p ^ k = n := by
  simp only [ppB', Bool.or_eq_true, List.any_eq_true] at h
  rcases h with h | ⟨p, hp, hpow⟩
  · exact ⟨n, 1, (isPrimeB_iff n).1 h, one_pos, pow_one n⟩
  · obtain ⟨k, hk, hpk⟩ := isPowOf_spec n n hpow
    exact ⟨p, k, hv.pl p hp, hk, hpk⟩

/-- The chain cover bounds the small elements of a primitive set. -/
theorem sum_small_le (hv : L.Valid) {T : Finset ℕ} (hprim : Primitive T) (h2 : ∀ n ∈ T, 2 ≤ n)
    (hpp : ∀ n ∈ T, ppB' L.PL n = false) :
    ∑ n ∈ T.filter (· < L.A), (L.D / n - L.D / L.A) ≤ L.W := by
  set S := T.filter (· < L.A)
  have hcov : ∀ n ∈ S, L.D / n - L.D / L.A ≤ L.cov n := by
    intro n hn
    rw [Finset.mem_filter] at hn
    exact hv.cover n (h2 n hn.1) hn.2 (hpp n hn.1)
  -- double counting over the list of chains
  have hdc : ∀ (cs : List (List ℕ × ℕ)), (∀ C ∈ cs, ∀ a ∈ C.1, ∀ b ∈ C.1, a ∣ b ∨ b ∣ a) →
      ∑ n ∈ S, ((cs.filter (fun C => n ∈ C.1)).map Prod.snd).sum ≤ (cs.map Prod.snd).sum := by
    intro cs
    induction cs with
    | nil => intro _; simp
    | cons C cs ih =>
      intro hch
      have ih' := ih (fun C' hC' => hch C' (List.mem_cons_of_mem _ hC'))
      have hsplit : ∀ n, ((( C :: cs).filter (fun C => n ∈ C.1)).map Prod.snd).sum =
          (if n ∈ C.1 then C.2 else 0) + ((cs.filter (fun C => n ∈ C.1)).map Prod.snd).sum := by
        intro n
        by_cases h : n ∈ C.1
        · simp [h]
        · simp [h]
      simp_rw [hsplit]
      rw [Finset.sum_add_distrib, List.map_cons, List.sum_cons]
      refine Nat.add_le_add ?_ ih'
      -- a chain meets the primitive set at most once
      have hone : (S.filter (fun n => n ∈ C.1)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        simp only [Finset.mem_filter, S] at ha hb
        rcases hch C List.mem_cons_self a ha.2 b hb.2 with h | h
        · exact hprim a ha.1.1 b hb.1.1 h
        · exact (hprim b hb.1.1 a ha.1.1 h).symm
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
      calc (S.filter (fun n => n ∈ C.1)).card * C.2 ≤ 1 * C.2 := Nat.mul_le_mul_right _ hone
        _ = C.2 := one_mul _
  exact le_trans (Finset.sum_le_sum hcov) (hdc L.chains hv.chain)

/-- **Lagrangian bound.**  For every `m ∈ T` with `L.A ≤ m`:
`∑ 1/n ≤ |T|/A + W/D − (1/A − 1/m)`; and without such an element `∑ 1/n ≤ |T|/A + W/D`. -/
theorem lagrange_bound (hv : L.Valid) {T : Finset ℕ} (hprim : Primitive T)
    (h2 : ∀ n ∈ T, 2 ≤ n) (hpp : ∀ n ∈ T, ppB' L.PL n = false) (m : ℕ)
    (hm : m ∈ T ∨ m = 0) (hmA : L.A ≤ m ∨ m = 0) :
    recipSum T ≤ T.card / (L.A : ℚ) + L.W / (L.D : ℚ) -
      (if m = 0 then 0 else (1 / (L.A : ℚ) - 1 / m)) := by
  have hA : (0 : ℚ) < L.A := by exact_mod_cast hv.Apos
  have hD : (0 : ℚ) < L.D := by exact_mod_cast hv.Dpos
  -- 1/n = 1/A + (1/n - 1/A)
  have hsplit : recipSum T = T.card / (L.A : ℚ) + ∑ n ∈ T, (1 / (n : ℚ) - 1 / L.A) := by
    rw [recipSum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hsplit]
  rw [← Finset.sum_filter_add_sum_filter_not T (· < L.A)]
  -- the small part
  have hsmall : ∑ n ∈ T.filter (· < L.A), (1 / (n : ℚ) - 1 / L.A) ≤ L.W / (L.D : ℚ) := by
    have h := sum_small_le hv hprim h2 hpp
    have hcast : ∑ n ∈ T.filter (· < L.A), (1 / (n : ℚ) - 1 / L.A) =
        (∑ n ∈ T.filter (· < L.A), ((L.D / n - L.D / L.A : ℕ) : ℚ)) / L.D := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [Finset.mem_filter] at hn
      have hn2 := h2 n hn.1
      have hnD : n ∣ L.D := hv.dvd n hn2 hn.2 (hpp n hn.1)
      have hle : L.D / L.A ≤ L.D / n := Nat.div_le_div_left hn.2.le (by omega)
      rw [Nat.cast_sub hle, Nat.cast_div hnD (by norm_cast; omega),
        Nat.cast_div hv.dvdA (by exact_mod_cast hv.Apos.ne')]
      field_simp
    rw [hcast, div_le_div_iff_of_pos_right hD]
    exact_mod_cast h
  -- the large part
  have hlarge : ∑ n ∈ T.filter (fun n => ¬ n < L.A), (1 / (n : ℚ) - 1 / L.A) ≤
      -(if m = 0 then 0 else (1 / (L.A : ℚ) - 1 / m)) := by
    have hnonpos : ∀ n ∈ T.filter (fun n => ¬ n < L.A), 1 / (n : ℚ) - 1 / L.A ≤ 0 := by
      intro n hn
      rw [Finset.mem_filter, not_lt] at hn
      have : (L.A : ℚ) ≤ n := by exact_mod_cast hn.2
      have : 1 / (n : ℚ) ≤ 1 / L.A := by gcongr
      linarith
    split_ifs with hm0
    · simp only [neg_zero]; exact Finset.sum_nonpos hnonpos
    · have hmT : m ∈ T.filter (fun n => ¬ n < L.A) := by
        rw [Finset.mem_filter, not_lt]
        exact ⟨hm.resolve_right hm0, hmA.resolve_right hm0⟩
      rw [← Finset.add_sum_erase _ _ hmT]
      have := Finset.sum_nonpos (fun n hn => hnonpos n (Finset.mem_of_mem_erase hn))
        (s := (T.filter (fun n => ¬ n < L.A)).erase m)
      linarith
  linarith

end SemiprimeEgypt.Prim
