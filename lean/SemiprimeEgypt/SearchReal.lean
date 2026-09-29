/-
The search for `S` = the primes `≤ 73`, and the link to the mathematics of the solutions.

* `inst73 K`: the instance of `semiprime48.cpp` (budget `K ≤ 48`).
* `edgesOf C`: the index pairs of a core `C` (a set of semiprimes with both factors `≤ 73`).
* `intAdm_of_admissible`: the exact Step-1 condition `Admissible K C` of `Reduction.lean` implies
  the rounded condition `IntAdm` for `edgesOf C` (upper rounding of `1/n`, `1/(79q)` and `V`).
* **`core_mem_search`**: every core `C` with `Admissible K C` appears in the output of the
  search, as `edgesOf C`;  **`core_of_solution_mem_search`**: in particular the core of every
  set `T` of squarefree semiprimes with `Σ 1/n = 1` and `|T| ≤ K` does.
-/
import SemiprimeEgypt.SearchTablesProof
import SemiprimeEgypt.Reduction

open Finset

namespace SemiprimeEgypt
namespace Srch

/-- The primes `≤ 73`. -/
def pr73 : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73]

/-- The 49 smallest squarefree semiprimes with a prime factor `> 73`. -/
def bs73 : List ℕ := [158, 166, 178, 194, 202, 206, 214, 218, 226, 237, 249, 254, 262, 267, 274,
  278, 291, 298, 302, 303, 309, 314, 321, 326, 327, 334, 339, 346, 358, 362, 381, 382, 386, 393,
  394, 395, 398, 411, 415, 417, 422, 445, 446, 447, 453, 454, 458, 466, 471]

/-- The instance of `semiprime48.cpp` with budget `K`. -/
def inst73 (K : ℕ) : Inst where
  pr := pr73
  K := K
  big := 79
  bs := bs73
  theta := 145
  AD := 12
  shn := [12, 11, 11, 10, 10, 9]
  lown := 8

lemma inst73_m (K : ℕ) : (inst73 K).m = 21 := rfl

lemma pr73_getD_pos (k : ℕ) : 0 < pr73.getD k 1 := by
  rcases Nat.lt_or_ge k 21 with h | h
  · interval_cases k <;> decide
  · rw [List.getD_eq_default _ _ (by simp [pr73]; omega)]; norm_num

lemma instOK73 (K : ℕ) : InstOK (inst73 K) where
  two_le_m := by rw [inst73_m]; norm_num
  P_pos := fun k => pr73_getD_pos k
  AD_pos := by show 0 < 12; norm_num
  sh_le := fun a => by
    show [12, 11, 11, 10, 10, 9].getD a 8 ≤ 12
    rcases Nat.lt_or_ge a 6 with h | h
    · interval_cases a <;> decide
    · rw [List.getD_eq_default _ _ (by simp; omega)]; norm_num

/-! ### The primes of `S` by index -/

lemma P73 (K k : ℕ) : (inst73 K).P k = pr73.getD k 1 := rfl

lemma P73_prime {k : ℕ} (hk : k < 21) : (pr73.getD k 1).Prime := by
  interval_cases k <;> norm_num [pr73]

lemma P73_le {k : ℕ} (hk : k < 21) : pr73.getD k 1 ≤ 73 := by
  interval_cases k <;> decide

lemma P73_strictMono {a b : ℕ} (hab : a < b) (hb : b < 21) : pr73.getD a 1 < pr73.getD b 1 := by
  interval_cases b <;> interval_cases a <;> decide

lemma P73_inj {a b : ℕ} (ha : a < 21) (hb : b < 21) (h : pr73.getD a 1 = pr73.getD b 1) :
    a = b := by
  rcases lt_trichotomy a b with h' | h' | h'
  · have := P73_strictMono h' hb; omega
  · exact h'
  · have := P73_strictMono h' ha; omega

/-- Every prime `≤ 73` has an index. -/
lemma exists_index {q : ℕ} (hq : q.Prime) (h73 : q ≤ 73) : ∃ k < 21, pr73.getD k 1 = q := by
  have : q ∈ pr73 := by
    interval_cases q <;> first | decide | (norm_num at hq)
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem this
  exact ⟨k, hk, by simp [List.getD_eq_getElem?_getD, hk]⟩

lemma index_of_smallPrime {q : ℕ} (hq : q ∈ smallPrimes 73) : ∃ k < 21, pr73.getD k 1 = q :=
  exists_index (mem_smallPrimes.1 hq).1 (mem_smallPrimes.1 hq).2

lemma P73_smallPrime {k : ℕ} (hk : k < 21) : pr73.getD k 1 ∈ smallPrimes 73 :=
  mem_smallPrimes.2 ⟨P73_prime hk, P73_le hk⟩

/-! ### Rounding -/

lemma ONE_pos : 0 < ONE := by unfold ONE; positivity

lemma up_ge {n : ℕ} (hn : 0 < n) : (ONE : ℚ) / n ≤ up n := by
  unfold up
  have h3 : ONE ≤ n * ((ONE + n - 1) / n) := by
    have h1 := Nat.div_add_mod (ONE + n - 1) n
    have h2 := Nat.mod_lt (ONE + n - 1) hn
    generalize n * ((ONE + n - 1) / n) = t at h1 ⊢
    generalize (ONE + n - 1) % n = r at h1 h2
    omega
  rw [div_le_iff₀ (by exact_mod_cast hn)]
  have : ((ONE : ℕ) : ℚ) ≤ ((n * ((ONE + n - 1) / n) : ℕ) : ℚ) := by exact_mod_cast h3
  push_cast at this
  linarith

lemma lo_le {n : ℕ} (hn : 0 < n) : (lo n : ℚ) ≤ (ONE : ℚ) / n := by
  unfold lo
  rw [le_div_iff₀ (by exact_mod_cast hn)]
  have : ONE / n * n ≤ ONE := Nat.div_mul_le_self _ _
  exact_mod_cast this

/-! ### The smallest semiprimes with a big factor -/

lemma bs73_len : bs73.length = 49 := rfl

lemma bs73_pairwise : bs73.Pairwise (· < ·) := by decide

lemma bs73_lt {a b : ℕ} (hab : a < b) (hb : b < 49) : bs73.getD a 0 < bs73.getD b 0 := by
  have h := List.pairwise_iff_getElem.1 bs73_pairwise a b (by rw [bs73_len]; omega)
    (by rw [bs73_len]; omega) hab
  simpa [List.getD_eq_getElem?_getD, show a < bs73.length by rw [bs73_len]; omega,
    show b < bs73.length by rw [bs73_len]; omega] using h

lemma bs73_pos {a : ℕ} (ha : a < 49) : 0 < bs73.getD a 0 := by
  interval_cases a <;> decide

/-- Every squarefree semiprime `≤ 471` with a prime factor `> 73` is in `bs73`. -/
theorem bigSP_mem_bs73 {n : ℕ} (h : IsBigSP n) (hn : n ≤ 471) : n ∈ bs73 := by
  obtain ⟨⟨p, q, hp, hq, hpq, rfl⟩, hs⟩ := h
  have hq73 : 73 < q := by
    by_contra hle
    apply hs
    intro r hr
    rw [primeFactors_sp hp hq (Nat.ne_of_lt hpq)] at hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl <;> omega
  have hq79 : 79 ≤ q := ge_79 hq hq73
  have hp2 := hp.two_le
  have hp5 : p ≤ 5 := by nlinarith
  have hq235 : q ≤ 235 := by nlinarith
  interval_cases p <;> (try norm_num at hp) <;> interval_cases q <;>
    first | omega | (norm_num at hq; done) | decide

lemma getD_mem_bs73 {n : ℕ} (h : n ∈ bs73) : ∃ i < 49, bs73.getD i 0 = n := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  exact ⟨i, by rwa [bs73_len] at hi, by simp [List.getD_eq_getElem?_getD, hi]⟩

/-- `V x ≤ Σ_{i<x} 1/bs_i` for `x ≤ 49`. -/
theorem V_le_bs {x : ℕ} (hx : x ≤ 49) :
    V x ≤ ∑ i ∈ range x, (1 : ℚ) / bs73.getD i 0 := by
  rcases Nat.eq_zero_or_pos x with rfl | hx0
  · simp [V]
  have hinj : Set.InjOn (fun i => bs73.getD i 0) (range x) := by
    intro a ha b hb h
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    rcases lt_trichotomy a b with h' | h' | h'
    · have := bs73_lt h' (by omega); simp only at h; omega
    · exact h'
    · have := bs73_lt h' (by omega); simp only at h; omega
  set A := (range x).image (fun i => bs73.getD i 0)
  set S := (range x).image (Nat.nth IsBigSP)
  have hA : recipSum A = ∑ i ∈ range x, (1 : ℚ) / bs73.getD i 0 := by
    rw [recipSum, Finset.sum_image hinj]
  have hS : recipSum S = V x := by
    rw [recipSum, V, Finset.sum_image fun a _ b _ h => Nat.nth_injective infinite_bigSP h]
  rw [← hA, ← hS]
  refine recipSum_le_of_initial IsBigSP A S (bs73.getD (x - 1) 0) ?_ ?_ ?_ ?_
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
    have hi' := Finset.mem_range.1 hi
    refine ⟨bs73_pos (by omega), ?_⟩
    rcases Nat.eq_or_lt_of_le (show i ≤ x - 1 by omega) with h | h
    · rw [h]
    · exact (bs73_lt h (by omega)).le
  · intro n hn hnM
    obtain ⟨i, hi, rfl⟩ := getD_mem_bs73 (bigSP_mem_bs73 hn
      (le_trans hnM (by
        rcases Nat.eq_or_lt_of_le (show x - 1 ≤ 48 by omega) with h | h
        · rw [h]; decide
        · exact (bs73_lt h (by norm_num)).le.trans (by decide))))
    refine Finset.mem_image.2 ⟨i, Finset.mem_range.2 ?_, rfl⟩
    by_contra hge
    have := bs73_lt (show x - 1 < i by omega) hi
    omega
  · intro n hn
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hn
    exact Nat.nth_mem_of_infinite infinite_bigSP i
  · rw [Finset.card_image_of_injOn hinj,
      Finset.card_image_of_injective _ (Nat.nth_injective infinite_bigSP)]

/-! ### Cores as edge sets -/

/-- The element `P a · P b` of the edge `e = (a, b)`. -/
def eprod (e : ℕ × ℕ) : ℕ := pr73.getD e.1 1 * pr73.getD e.2 1

/-- The edge set of a core `C`. -/
def edgesOf (C : Finset ℕ) : Finset (ℕ × ℕ) := (pairsBelow 21).filter (fun e => eprod e ∈ C)

/-- The core of an edge set. -/
def coreOf (E : Finset (ℕ × ℕ)) : Finset ℕ := E.image eprod

lemma mem_pairsBelow' {j : ℕ} {e : ℕ × ℕ} : e ∈ pairsBelow j ↔ e.1 < e.2 ∧ e.2 < j := by
  unfold pairsBelow
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor <;> (intro h; omega)

lemma eprod_pos (e : ℕ × ℕ) : 0 < eprod e := Nat.mul_pos (pr73_getD_pos _) (pr73_getD_pos _)

lemma idx_of_dvd {k a b : ℕ} (hk : k < 21) (ha : a < 21) (hb : b < 21)
    (h : pr73.getD k 1 ∣ pr73.getD a 1 * pr73.getD b 1) : k = a ∨ k = b := by
  rcases (Nat.Prime.dvd_mul (P73_prime hk)).1 h with h | h
  · exact Or.inl (P73_inj hk ha ((Nat.prime_dvd_prime_iff_eq (P73_prime hk) (P73_prime ha)).1 h))
  · exact Or.inr (P73_inj hk hb ((Nat.prime_dvd_prime_iff_eq (P73_prime hk) (P73_prime hb)).1 h))

lemma eprod_injOn : Set.InjOn eprod (pairsBelow 21 : Set (ℕ × ℕ)) := by
  rintro ⟨a, b⟩ he ⟨a', b'⟩ he' h
  rw [Finset.mem_coe, mem_pairsBelow'] at he he'
  simp only [eprod] at h he he'
  have h1 := idx_of_dvd (k := a) (a := a') (b := b') (by omega) (by omega) (by omega)
    (by rw [← h]; exact dvd_mul_right _ _)
  have h2 := idx_of_dvd (k := b) (a := a') (b := b') (by omega) (by omega) (by omega)
    (by rw [← h]; exact dvd_mul_left _ _)
  have h3 := idx_of_dvd (k := a') (a := a) (b := b) (by omega) (by omega) (by omega)
    (by rw [h]; exact dvd_mul_right _ _)
  have h4 := idx_of_dvd (k := b') (a := a) (b := b) (by omega) (by omega) (by omega)
    (by rw [h]; exact dvd_mul_left _ _)
  simp only [Prod.mk.injEq]
  omega

/-- Every element of a core is `P a · P b` for an edge `a < b < 21`. -/
lemma exists_edge {n : ℕ} (hn : IsSP n) (hs : Small 73 n) : ∃ e ∈ pairsBelow 21, eprod e = n := by
  obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hn
  have hfac := primeFactors_sp hp hq (Nat.ne_of_lt hpq)
  have hp73 : p ≤ 73 := hs p (by rw [hfac]; simp)
  have hq73 : q ≤ 73 := hs q (by rw [hfac]; simp)
  obtain ⟨a, ha, rfl⟩ := exists_index hp hp73
  obtain ⟨b, hb, rfl⟩ := exists_index hq hq73
  refine ⟨(a, b), mem_pairsBelow'.2 ⟨show a < b from ?_, hb⟩, rfl⟩
  by_contra hab
  rcases Nat.eq_or_lt_of_le (not_lt.1 hab) with h | h
  · subst h; omega
  · have := P73_strictMono h ha; omega

lemma edgesOf_subset (C : Finset ℕ) : edgesOf C ⊆ pairsBelow 21 := Finset.filter_subset _ _

lemma coreOf_edgesOf {C : Finset ℕ} (hC : CoreSet C) : coreOf (edgesOf C) = C := by
  ext n
  simp only [coreOf, edgesOf, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨e, ⟨-, he⟩, rfl⟩; exact he
  · intro hn
    obtain ⟨e, he, rfl⟩ := exists_edge (hC n hn).1 (hC n hn).2
    exact ⟨e, ⟨he, hn⟩, rfl⟩

lemma edgesOf_injOn (C : Finset ℕ) : Set.InjOn eprod (edgesOf C : Set (ℕ × ℕ)) :=
  eprod_injOn.mono (Finset.coe_subset.2 (edgesOf_subset C))

lemma card_edgesOf {C : Finset ℕ} (hC : CoreSet C) : (edgesOf C).card = C.card := by
  conv_rhs => rw [← coreOf_edgesOf hC]
  rw [coreOf, Finset.card_image_of_injOn (edgesOf_injOn C)]

lemma sum_core {C : Finset ℕ} (hC : CoreSet C) {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ n ∈ C, f n = ∑ e ∈ edgesOf C, f (eprod e) := by
  conv_lhs => rw [← coreOf_edgesOf hC]
  rw [coreOf, Finset.sum_image (edgesOf_injOn C)]

/-! ### Residues and the unsatisfied set -/

lemma cast_inv (K a x : ℕ) (ha : a < 21) :
    (((inst73 K).inv a x : ℕ) : ZMod (pr73.getD a 1)) =
      ((pr73.getD x 1 : ℕ) : ZMod (pr73.getD a 1))⁻¹ := by
  have : NeZero ((inst73 K).P a) := ⟨(P73_prime ha).ne_zero⟩
  exact ZMod.natCast_zmod_val _

/-- The residue computed by the search is the residue `ρ` of the core. -/
lemma resid_eq {K : ℕ} {C : Finset ℕ} (hC : CoreSet C) {k : ℕ} (hk : k < 21) :
    (((inst73 K).res (edgesOf C) k : ℕ) : ZMod (pr73.getD k 1)) = resid C (pr73.getD k 1) := by
  show (((∑ e ∈ edgesOf C, (inst73 K).ctr k e) % pr73.getD k 1 : ℕ) : ZMod (pr73.getD k 1)) = _
  rw [ZMod.natCast_mod, Nat.cast_sum, resid, Finset.sum_filter, sum_core hC]
  refine Finset.sum_congr rfl fun e he => ?_
  obtain ⟨a, b⟩ := e
  obtain ⟨hab, hb⟩ := mem_pairsBelow'.1 (edgesOf_subset C he)
  dsimp only at hab hb
  have hpos := (P73_prime hk).pos
  unfold Inst.ctr eprod
  dsimp only
  by_cases h1 : a = k
  · subst h1
    have hd : pr73.getD a 1 ∣ pr73.getD a 1 * pr73.getD b 1 := dvd_mul_right _ _
    have hba : ¬ b = a := by omega
    simp only [↓reduceIte, hba, hd, Nat.mul_div_cancel_left _ hpos, add_zero]
    exact cast_inv K a b hk
  · by_cases h2 : b = k
    · subst h2
      have hd : pr73.getD b 1 ∣ pr73.getD a 1 * pr73.getD b 1 := dvd_mul_left _ _
      simp only [↓reduceIte, h1, hd, Nat.mul_div_cancel _ hpos, zero_add]
      exact cast_inv K b a hk
    · have hnd : ¬ pr73.getD k 1 ∣ pr73.getD a 1 * pr73.getD b 1 := by
        intro hd
        rcases idx_of_dvd hk (by omega) hb hd with h | h <;> omega
      simp only [↓reduceIte, h1, h2, hnd, add_zero, Nat.cast_zero]

lemma res_eq_zero_iff {K : ℕ} {C : Finset ℕ} (hC : CoreSet C) {k : ℕ} (hk : k < 21) :
    (inst73 K).res (edgesOf C) k = 0 ↔ resid C (pr73.getD k 1) = 0 := by
  rw [← resid_eq (K := K) hC hk]
  have hlt : (inst73 K).res (edgesOf C) k < pr73.getD k 1 := Nat.mod_lt _ (P73_prime hk).pos
  rw [← ZMod.val_eq_zero, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]

lemma mem_UE73 {K : ℕ} {C : Finset ℕ} (hC : CoreSet C) {k : ℕ} :
    k ∈ (inst73 K).UE (edgesOf C) ↔ k < 21 ∧ resid C (pr73.getD k 1) ≠ 0 := by
  unfold Inst.UE
  rw [Finset.mem_filter, Finset.mem_range, inst73_m]
  constructor
  · rintro ⟨hk, h⟩; exact ⟨hk, fun h' => h ((res_eq_zero_iff hC hk).2 h')⟩
  · rintro ⟨hk, h⟩; exact ⟨hk, fun h' => h ((res_eq_zero_iff hC hk).1 h')⟩

/-- The unsatisfied set of the search is the set `U` of the core. -/
lemma Uset_eq {K : ℕ} {C : Finset ℕ} (hC : CoreSet C) :
    Uset 73 C = ((inst73 K).UE (edgesOf C)).image (fun k => pr73.getD k 1) := by
  ext q
  simp only [Uset, Finset.mem_filter, Finset.mem_image, mem_UE73 hC]
  constructor
  · rintro ⟨hq, hr⟩
    obtain ⟨k, hk, rfl⟩ := index_of_smallPrime hq
    exact ⟨k, ⟨hk, hr⟩, rfl⟩
  · rintro ⟨k, ⟨hk, hr⟩, rfl⟩
    exact ⟨P73_smallPrime hk, hr⟩

lemma card_image_P {A : Finset ℕ} (hA : ∀ k ∈ A, k < 21) :
    (A.image (fun k => pr73.getD k 1)).card = A.card :=
  Finset.card_image_of_injOn fun a ha b hb h => P73_inj (hA a ha) (hA b hb) h

lemma sum_image_P {A : Finset ℕ} (hA : ∀ k ∈ A, k < 21) {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) : ∑ q ∈ A.image (fun k => pr73.getD k 1), f q = ∑ k ∈ A, f (pr73.getD k 1) :=
  Finset.sum_image fun a ha b hb h => P73_inj (hA a ha) (hA b hb) h

/-- The prime below the upper segment starting at index `s` (`0` for `s = 0`). -/
def pthr (s : ℕ) : ℕ := if s = 0 then 0 else pr73.getD (s - 1) 1

lemma pthr_lt_iff {s k : ℕ} (hs : s ≤ 21) (hk : k < 21) : pthr s < pr73.getD k 1 ↔ s ≤ k := by
  unfold pthr
  split_ifs with h
  · subst h; exact ⟨fun _ => Nat.zero_le _, fun _ => pr73_getD_pos k⟩
  · constructor
    · intro hlt
      by_contra hsk
      rcases Nat.eq_or_lt_of_le (show k ≤ s - 1 by omega) with h' | h'
      · rw [h'] at hlt; omega
      · have := P73_strictMono h' (by omega); omega
    · intro hsk; exact P73_strictMono (by omega) hk

/-- Upper segments of `U` are upper segments of the unsatisfied set of the search. -/
lemma Useg_eq {K : ℕ} {C : Finset ℕ} (hC : CoreSet C) {s : ℕ} (hs : s ≤ 21) :
    (Uset 73 C).filter (pthr s < ·) =
      (((inst73 K).UE (edgesOf C)).filter (s ≤ ·)).image (fun k => pr73.getD k 1) := by
  ext q
  simp only [Finset.mem_filter, Finset.mem_image, Uset_eq (K := K) hC]
  constructor
  · rintro ⟨⟨k, hk, rfl⟩, hlt⟩
    exact ⟨k, ⟨hk, (pthr_lt_iff hs ((mem_UE73 hC).1 hk).1).1 hlt⟩, rfl⟩
  · rintro ⟨k, ⟨hk, hsk⟩, rfl⟩
    exact ⟨⟨k, hk, rfl⟩, (pthr_lt_iff hs ((mem_UE73 hC).1 hk).1).2 hsk⟩

/-! ### Exhaustiveness for the real problem -/

/-- **Rounding.**  The exact Step-1 condition implies its integer form. -/
theorem intAdm_of_admissible {K : ℕ} (hK : K ≤ 48) {C : Finset ℕ} (hC : CoreSet C)
    (hA : Admissible K C) : IntAdm (inst73 K) (inst73 K).mkTables (edgesOf C) := by
  obtain ⟨hbud, hle1, hval⟩ := hA
  have hEC : (edgesOf C).card = C.card := card_edgesOf hC
  have hUlt : ∀ k ∈ (inst73 K).UE (edgesOf C), k < 21 := fun k hk => ((mem_UE73 hC).1 hk).1
  have hUc : (Uset 73 C).card = ((inst73 K).UE (edgesOf C)).card := by
    rw [Uset_eq (K := K) hC, card_image_P hUlt]
  have hONE : (0 : ℚ) ≤ ONE := Nat.cast_nonneg _
  have hsu : (ONE : ℚ) * recipSum C ≤ (inst73 K).su (edgesOf C) := by
    rw [recipSum, sum_core hC, Finset.mul_sum, Inst.su, Nat.cast_sum]
    refine Finset.sum_le_sum fun e _ => ?_
    have h := up_ge (eprod_pos e)
    simp only [mul_one_div]
    exact h
  have hsl : ((inst73 K).sl (edgesOf C) : ℚ) ≤ ONE * recipSum C := by
    rw [recipSum, sum_core hC, Finset.mul_sum, Inst.sl, Nat.cast_sum]
    refine Finset.sum_le_sum fun e _ => ?_
    have h := lo_le (eprod_pos e)
    simp only [mul_one_div]
    exact h
  have hVB : ∀ x ≤ K, (ONE : ℚ) * V x ≤ ((inst73 K).mkTables.VB x : ℕ) := by
    intro x hx
    rw [Inst.mk_VB (by show x < K + 2; omega), Inst.VBspec, Nat.cast_sum]
    calc (ONE : ℚ) * V x ≤ ONE * ∑ i ∈ range x, (1 : ℚ) / bs73.getD i 0 :=
          mul_le_mul_of_nonneg_left (V_le_bs (by omega)) hONE
      _ ≤ _ := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun i hi => ?_
          have h := up_ge (bs73_pos (show i < 49 by rw [Finset.mem_range] at hi; omega))
          simp only [mul_one_div]
          exact h
  refine ⟨edgesOf_subset C, ?_, ?_, ?_⟩
  · show (edgesOf C).card + ((inst73 K).UE (edgesOf C)).card ≤ K
    rw [hEC, ← hUc]; exact hbud
  · have : ((inst73 K).sl (edgesOf C) : ℚ) ≤ ONE :=
      hsl.trans (mul_le_of_le_one_right hONE hle1)
    exact_mod_cast this
  · intro s hs
    rw [inst73_m] at hs
    set Us := ((inst73 K).UE (edgesOf C)).filter (s ≤ ·) with hUs
    have hUslt : ∀ k ∈ Us, k < 21 := fun k hk => hUlt k (Finset.mem_filter.1 hk).1
    have h1 := hval (pthr s)
    rw [Useg_eq (K := K) hC hs, card_image_P hUslt, sum_image_P hUslt] at h1
    have hgz : (ONE : ℚ) * ∑ k ∈ Us, (1 : ℚ) / (79 * ((pr73.getD k 1 : ℕ) : ℚ)) ≤
        (inst73 K).gz Us := by
      rw [Finset.mul_sum, Inst.gz, Nat.cast_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      have h := up_ge (n := 79 * pr73.getD k 1) (by have := pr73_getD_pos k; omega)
      rw [mul_one_div]
      push_cast at h
      exact h
    have hV := hVB (K - C.card - Us.card) (by omega)
    have key : (ONE : ℚ) ≤ (((inst73 K).su (edgesOf C) + (inst73 K).gz Us +
        (inst73 K).mkTables.VB (K - C.card - Us.card) : ℕ) : ℚ) := by
      push_cast
      have := mul_le_mul_of_nonneg_left h1 hONE
      rw [mul_one, mul_add, mul_add] at this
      linarith
    show ONE ≤ (inst73 K).su (edgesOf C) + (inst73 K).gz Us +
      (inst73 K).mkTables.VB (K - (edgesOf C).card - Us.card)
    rw [hEC]
    exact_mod_cast key

/-- **Exhaustiveness of the search (Step 1).**  Every core `C` with `Admissible K C`
(`K ≤ 48`) is found by the search, as the edge set `edgesOf C`. -/
theorem core_mem_search {K : ℕ} (hK : K ≤ 48) {C : Finset ℕ} (hC : CoreSet C)
    (hA : Admissible K C) : edgesOf C ∈ (inst73 K).search (inst73 K).mkTables :=
  mem_search (instOK73 K) (Inst.mkTables_ok (instOK73 K)) (intAdm_of_admissible hK hC hA)

/-- Every admissible core is `coreOf E` for an edge set `E` in the output of the search. -/
theorem exists_mem_search {K : ℕ} (hK : K ≤ 48) {C : Finset ℕ} (hC : CoreSet C)
    (hA : Admissible K C) :
    ∃ E ∈ (inst73 K).search (inst73 K).mkTables, coreOf E = C :=
  ⟨edgesOf C, core_mem_search hK hC hA, coreOf_edgesOf hC⟩

/-- The core of every set `T` of squarefree semiprimes with `Σ 1/n = 1` and `|T| ≤ K ≤ 48` is
found by the search. -/
theorem core_of_solution_mem_search {T : Finset ℕ} (hT : ∀ n ∈ T, IsSP n)
    (h1 : recipSum T = 1) {K : ℕ} (hK : K ≤ 48) (hTK : T.card ≤ K) :
    edgesOf (core 73 T) ∈ (inst73 K).search (inst73 K).mkTables :=
  core_mem_search hK (coreSet_core hT) (admissible_of_real hT (localCond_of_one hT h1) h1 hTK)

end Srch
end SemiprimeEgypt
