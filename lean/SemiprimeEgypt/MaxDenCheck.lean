/-
# The smallest possible largest element: a certificate checker and its soundness

Problem: among the nonempty finite sets `T` of squarefree semiprimes with `∑_{n ∈ T} 1/n = 1`,
minimize `max T`.  The answer is `589 = 19 · 31` (`MaxDenMain.lean`).

This file contains the *method*, independent of the concrete numbers:

* `Cert`, `check`: a certificate is a binary tree of case splits "`n ∈ T` / `n ∉ T`" on the
  semiprimes `n ≤ B`; each leaf is closed by one of three exact tests
  - `lo`   : even all undecided elements together cannot bring the sum up to `1`,
  - `hi`   : the elements put into `T` already sum to more than `1`,
  - `md q` : the local condition at the prime `q` (Lemma 1, `integral_iff_localCond`) can no
             longer be met: `-ρ` is not a subset sum mod `q` of the inverses of the undecided
             neighbours of `q` (computed by a residue bit mask `R` and rotations `rot`).
  All arithmetic is on natural numbers: sums are scaled by a common multiple `D` of all
  elements, and residue sets are bit masks.
* `Valid`: the properties of the input data (`B`, the list of primes `≤ B/2`, `D`, the bit
  masks of the semiprimes `≤ B` and of the primes, the initial sum) that the soundness proof
  uses; `validB` is a Boolean test and `valid_of_validB` proves that it implies `Valid`.
* `no_solution`: if the data are valid and `check` accepts a certificate, then no set `T` of
  squarefree semiprimes, all `≤ B`, has `recipSum T = 1`.

The concrete certificate (`MaxDenCert588.lean`, written by `semiprime_maxden.cpp --cert`) is
checked by the kernel with `decide +kernel` in `MaxDenMain.lean`.
-/
import SemiprimeEgypt.Basic
import Mathlib.Tactic.IntervalCases

open Finset

namespace SemiprimeEgypt.MaxDen

/-! ### The checker -/

/-- A certificate: a tree of case splits on elements, with refutation leaves. -/
inductive Cert where
  /-- sum of all elements that are still possible `< 1` -/
  | lo : Cert
  /-- sum of the elements already in `T` `> 1` -/
  | hi : Cert
  /-- the local condition at the prime `q` cannot be met -/
  | md : ℕ → Cert
  /-- split on `n`: first child `n ∈ T`, second child `n ∉ T` -/
  | br : ℕ → Cert → Cert → Cert

/-- The input data for a bound `Bd`. -/
structure Data where
  /-- the bound: all elements of `T` are `≤ Bd` -/
  Bd : ℕ
  /-- the primes `≤ Bd / 2`, increasing -/
  PL : List ℕ
  /-- a common multiple of all squarefree semiprimes `≤ Bd` -/
  D : ℕ
  /-- bit mask of the squarefree semiprimes `≤ Bd` -/
  EM : ℕ
  /-- bit mask of the primes `≤ Bd / 2` -/
  PM : ℕ
  /-- `∑_{n ≤ Bd, bit n of EM} D / n` -/
  S0 : ℕ

/-- A search state: the bit masks of the elements decided in / out, the scaled sum of the
elements in, and the scaled sum of all elements not out. -/
structure St where
  inn : ℕ
  out : ℕ
  sIn : ℕ
  sAll : ℕ

/-- Rotation of a `q`-bit residue mask by `a`: bit `x` goes to bit `(x + a) % q`. -/
def rot (q a R : ℕ) : ℕ := ((R <<< a) ||| (R >>> (q - a))) &&& (2 ^ q - 1)

/-- The primes `p ≠ q` of the (increasing) list with `p * q ≤ Bd`. -/
def nbrs (Bd q : ℕ) : List ℕ → List ℕ
  | [] => []
  | p :: ps => if Bd < p * q then [] else if p = q then nbrs Bd q ps else p :: nbrs Bd q ps

/-- Walk the neighbours `p` of `q`: `rho` collects the inverses `p⁻¹ = p ^ (q - 2) mod q` of the
edges that are in, `R` the subset sums of the inverses of the undecided edges. -/
def modAcc (q : ℕ) (s : St) : List ℕ → ℕ → ℕ → ℕ × ℕ
  | [], rho, R => (rho, R)
  | p :: L, rho, R =>
    if s.inn.testBit (p * q) then modAcc q s L ((rho + p ^ (q - 2) % q) % q) R
    else if s.out.testBit (p * q) then modAcc q s L rho R
    else modAcc q s L rho (R ||| rot q (p ^ (q - 2) % q) R)

/-- The test `md q`: `q` is prime and `-rho` is not reachable. -/
def modLeaf (d : Data) (q : ℕ) (s : St) : Bool :=
  d.PM.testBit q && (match modAcc q s (nbrs d.Bd q d.PL) 0 1 with
    | (rho, R) => !(R.testBit ((q - rho) % q)))

/-- The certificate checker. -/
def check (d : Data) : Cert → St → Bool
  | .lo, s => Nat.blt s.sAll d.D
  | .hi, s => Nat.blt d.D s.sIn
  | .md q, s => modLeaf d q s
  | .br n c1 c2, s => Nat.ble n d.Bd && d.EM.testBit n && !(s.inn.testBit n) &&
      !(s.out.testBit n) &&
      check d c1 ⟨s.inn ||| 2 ^ n, s.out, s.sIn + d.D / n, s.sAll⟩ &&
      check d c2 ⟨s.inn, s.out ||| 2 ^ n, s.sIn, s.sAll - d.D / n⟩

/-- The initial state: nothing decided. -/
def st0 (d : Data) : St := ⟨0, 0, 0, d.S0⟩

/-! ### Validity of the data -/

/-- The elements `n ≤ Bd` whose bit is set in `EM`. -/
def edgeSet (d : Data) : Finset ℕ := (range (d.Bd + 1)).filter (fun n => d.EM.testBit n = true)

/-- What the soundness proof needs to know about the data. -/
structure Valid (d : Data) : Prop where
  sorted : d.PL.Pairwise (· < ·)
  complete : ∀ m, m.Prime → 2 * m ≤ d.Bd → m ∈ d.PL
  pm : ∀ q, d.PM.testBit q = true → q.Prime
  inv : ∀ q, d.PM.testBit q = true → ∀ p ∈ nbrs d.Bd q d.PL, p * (p ^ (q - 2) % q) % q = 1
  em : ∀ p ∈ d.PL, ∀ q ∈ d.PL, p < q → p * q ≤ d.Bd → d.EM.testBit (p * q) = true
  dvd : ∀ n ∈ edgeSet d, n ∣ d.D
  s0 : ∑ n ∈ edgeSet d, d.D / n ≤ d.S0

/-- Trial division. -/
def isPrimeB (m : ℕ) : Bool := decide (2 ≤ m) && (List.range m).all (fun k => decide (k < 2) || m % k != 0)

theorem isPrimeB_iff (m : ℕ) : isPrimeB m = true ↔ m.Prime := by
  rw [Nat.prime_def_lt']
  simp only [isPrimeB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun k hk hkm hdvd => ?_⟩
    rcases h k hkm with h' | h'
    · omega
    · exact h' (Nat.mod_eq_zero_of_dvd hdvd)
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun k hkm => ?_⟩
    by_cases hk : k < 2
    · exact Or.inl hk
    · exact Or.inr fun h0 => h k (by omega) hkm (Nat.dvd_of_mod_eq_zero h0)

/-- `∑_{i < n} f i`, by plain recursion (cheap for the kernel). -/
def sumTo (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => sumTo f k + f k

theorem sumTo_eq (f : ℕ → ℕ) (n : ℕ) : sumTo f n = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp [sumTo]
  | succ k ih => rw [sumTo, ih, Finset.sum_range_succ]

/-- The Boolean validity test. -/
def validB (d : Data) : Bool :=
  decide (d.PL.Pairwise (· < ·)) &&
  (List.range (d.Bd / 2 + 1)).all (fun m => !isPrimeB m || d.PL.contains m) &&
  decide (d.PM < 2 ^ (d.Bd + 1)) &&
  (List.range (d.Bd + 1)).all (fun q => !d.PM.testBit q ||
    (isPrimeB q && (nbrs d.Bd q d.PL).all (fun p => p * (p ^ (q - 2) % q) % q == 1))) &&
  d.PL.all (fun p => d.PL.all (fun q =>
    !(decide (p < q) && decide (p * q ≤ d.Bd)) || d.EM.testBit (p * q))) &&
  (List.range (d.Bd + 1)).all (fun n => !d.EM.testBit n || d.D % n == 0) &&
  decide (sumTo (fun n => if d.EM.testBit n = true then d.D / n else 0) (d.Bd + 1) ≤ d.S0)

theorem valid_of_validB {d : Data} (h : validB d = true) : Valid d := by
  simp only [validB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hs, hc⟩, hpm⟩, hq⟩, hem⟩, hdv⟩, hS⟩ := h
  -- bits of `PM` above `Bd` are clear
  have hbit : ∀ q, d.PM.testBit q = true → q < d.Bd + 1 := by
    intro q hq'
    by_contra hlt
    have : d.PM < 2 ^ q := lt_of_lt_of_le hpm (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_lt_two_pow this] at hq'
    exact Bool.false_ne_true hq'
  refine ⟨hs, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m hm h2m
    rcases hc m (by omega) with h' | h'
    · rw [(isPrimeB_iff m).2 hm] at h'; exact absurd h' (by decide)
    · exact List.contains_iff_mem.1 h'
  · intro q hq'
    rcases hq q (hbit q hq') with h' | h'
    · rw [hq'] at h'; exact absurd h' (by decide)
    · exact (isPrimeB_iff q).1 h'.1
  · intro q hq' p hp
    rcases hq q (hbit q hq') with h' | h'
    · rw [hq'] at h'; exact absurd h' (by decide)
    · exact h'.2 p hp
  · intro p hp q hq' hpq hle
    rcases hem p hp q hq' with h' | h'
    · simp [hpq, hle] at h'
    · exact h'
  · intro n hn
    simp only [edgeSet, Finset.mem_filter, Finset.mem_range] at hn
    rcases hdv n hn.1 with h' | h'
    · rw [hn.2] at h'; exact absurd h' (by decide)
    · exact Nat.dvd_of_mod_eq_zero h'
  · rw [sumTo_eq] at hS
    rw [edgeSet, Finset.sum_filter]
    exact hS

/-! ### Semantics -/

/-- A set `T` that would contradict the claim: squarefree semiprimes `≤ Bd`, all local
conditions, and scaled sum `D` (i.e. reciprocal sum `1`). -/
structure Sol (d : Data) (T : Finset ℕ) : Prop where
  sp : ∀ n ∈ T, IsSP n
  le : ∀ n ∈ T, n ≤ d.Bd
  loc : LocalCond T
  sum : ∑ n ∈ T, d.D / n = d.D

/-- `T` is consistent with the state `s`. -/
structure Good (d : Data) (T : Finset ℕ) (s : St) : Prop where
  hin : ∀ n, s.inn.testBit n = true → n ∈ T
  hout : ∀ n, s.out.testBit n = true → n ∉ T
  hsIn : s.sIn ≤ ∑ n ∈ T.filter (fun n => s.inn.testBit n = true), d.D / n
  hsAll : ∑ n ∈ (edgeSet d).filter (fun n => s.out.testBit n = false), d.D / n ≤ s.sAll

variable {d : Data}

theorem mem_edgeSet_of_sp (hv : Valid d) {n : ℕ} (hn : IsSP n) (hle : n ≤ d.Bd) :
    n ∈ edgeSet d := by
  obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hn
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have h1 : 2 * p ≤ p * q := by rw [mul_comm]; exact Nat.mul_le_mul_left p hq2
  have h2 : 2 * q ≤ p * q := Nat.mul_le_mul_right q hp2
  simp only [edgeSet, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hv.em p (hv.complete p hp (by omega)) q (hv.complete q hq (by omega)) hpq hle⟩

theorem rot_testBit {q a R x : ℕ} (ha : a < q) (hx : x < q) (hR : R.testBit x = true) :
    (rot q a R).testBit ((x + a) % q) = true := by
  unfold rot
  rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  by_cases h : x + a < q
  · rw [Nat.mod_eq_of_lt h]
    have e : x + a - a = x := by omega
    simp [e, hR, h]
  · have h1 : (x + a) % q = x + a - q := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [h1]
    have e : q - a + (x + a - q) = x := by omega
    have e2 : x + a - q < q := by omega
    simp [e, hR, e2]

theorem nbrs_sublist (Bd q : ℕ) : ∀ L : List ℕ, (nbrs Bd q L).Sublist L
  | [] => by simp [nbrs]
  | p :: L => by
    unfold nbrs
    split_ifs
    · exact List.nil_sublist _
    · exact (nbrs_sublist Bd q L).cons p
    · exact (nbrs_sublist Bd q L).cons_cons p

theorem mem_nbrs {Bd q : ℕ} : ∀ {L : List ℕ}, L.Pairwise (· < ·) → ∀ {p : ℕ},
    p ∈ nbrs Bd q L ↔ p ∈ L ∧ p ≠ q ∧ p * q ≤ Bd
  | [], _, p => by simp [nbrs]
  | r :: L, hL, p => by
    rw [List.pairwise_cons] at hL
    have ih := @mem_nbrs Bd q L hL.2 p
    unfold nbrs
    by_cases h1 : Bd < r * q
    · rw [ite_eq_left h1]
      simp only [List.not_mem_nil, false_iff, List.mem_cons, not_and]
      rintro (rfl | hp) _ hle
      · omega
      · have : r * q ≤ p * q := Nat.mul_le_mul_right q (hL.1 p hp).le
        omega
    · rw [ite_eq_right h1]
      by_cases h2 : r = q
      · rw [ite_eq_left h2, ih]
        simp only [List.mem_cons]
        constructor
        · rintro ⟨h, h', h''⟩; exact ⟨Or.inr h, h', h''⟩
        · rintro ⟨rfl | h, h', h''⟩
          · exact absurd h2 h'
          · exact ⟨h, h', h''⟩
      · rw [ite_eq_right h2]
        simp only [List.mem_cons, ih]
        constructor
        · rintro (rfl | ⟨h, h', h''⟩)
          · exact ⟨Or.inl rfl, h2, by omega⟩
          · exact ⟨Or.inr h, h', h''⟩
        · rintro ⟨rfl | h, h', h''⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨h, h', h''⟩

/-- The sum of the inverses `p ^ (q - 2) % q` of the `p ∈ L` with `p * q ∈ T`. -/
def sig (T : Finset ℕ) (q : ℕ) (L : List ℕ) : ℕ :=
  (L.map (fun p => if p * q ∈ T then p ^ (q - 2) % q else 0)).sum

theorem modAcc_spec {T : Finset ℕ} {s : St} {q : ℕ} (hq : 0 < q)
    (hin : ∀ n, s.inn.testBit n = true → n ∈ T) (hout : ∀ n, s.out.testBit n = true → n ∉ T) :
    ∀ (L : List ℕ) (rho R σ : ℕ), rho < q →
      (∃ x < q, R.testBit x = true ∧ (rho + x) % q = σ % q) →
      (modAcc q s L rho R).1 < q ∧ ∃ x < q, (modAcc q s L rho R).2.testBit x = true ∧
        ((modAcc q s L rho R).1 + x) % q = (σ + sig T q L) % q
  | [], rho, R, σ, hrho, hx => by
    simpa [modAcc, sig] using ⟨hrho, hx⟩
  | p :: L, rho, R, σ, hrho, ⟨x, hxq, hxR, hxe⟩ => by
    set a := p ^ (q - 2) % q with ha_def
    have ha : a < q := Nat.mod_lt _ hq
    have hsig : sig T q (p :: L) = (if p * q ∈ T then a else 0) + sig T q L := by
      simp [sig, ha_def]
    rw [hsig]
    unfold modAcc
    by_cases h1 : s.inn.testBit (p * q) = true
    · rw [ite_eq_left h1, ite_eq_left (hin _ h1)]
      have := modAcc_spec hq hin hout L ((rho + a) % q) R (σ + a) (Nat.mod_lt _ hq)
        ⟨x, hxq, hxR, by rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_right_comm,
          Nat.add_mod, hxe, ← Nat.add_mod]⟩
      have e : σ + (a + sig T q L) = σ + a + sig T q L := by omega
      rw [e]
      exact this
    · rw [ite_eq_right h1]
      by_cases h2 : s.out.testBit (p * q) = true
      · rw [ite_eq_left h2, ite_eq_right (hout _ h2)]
        simpa using modAcc_spec hq hin hout L rho R σ hrho ⟨x, hxq, hxR, hxe⟩
      · rw [ite_eq_right h2]
        by_cases hT : p * q ∈ T
        · rw [ite_eq_left hT]
          have := modAcc_spec hq hin hout L rho (R ||| rot q a R) (σ + a) hrho
            ⟨(x + a) % q, Nat.mod_lt _ hq, by
              rw [Nat.testBit_or, rot_testBit ha hxq hxR, Bool.or_true], by
              rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, ← Nat.add_assoc, Nat.add_mod,
                hxe, ← Nat.add_mod]⟩
          simpa [Nat.add_assoc] using this
        · rw [ite_eq_right hT]
          simpa using modAcc_spec hq hin hout L rho (R ||| rot q a R) σ hrho
            ⟨x, hxq, by rw [Nat.testBit_or, hxR, Bool.true_or], hxe⟩

/-- The local residue at a prime `q` of a set of semiprimes `≤ Bd`, computed along
`nbrs Bd q PL`. -/
theorem resid_eq_sig (hv : Valid d) {T : Finset ℕ} (hsp : ∀ n ∈ T, IsSP n)
    (hle : ∀ n ∈ T, n ≤ d.Bd) {q : ℕ} (hq : d.PM.testBit q = true) :
    resid T q = ((sig T q (nbrs d.Bd q d.PL) : ℕ) : ZMod q) := by
  have hqp : q.Prime := hv.pm q hq
  have : Fact q.Prime := ⟨hqp⟩
  have hnd : (nbrs d.Bd q d.PL).Nodup := (nbrs_sublist _ _ _).nodup hv.sorted.nodup
  set N := nbrs d.Bd q d.PL with hN
  -- the right-hand side as a finset sum over the neighbours `p` with `p * q ∈ T`
  have hrhs : ((sig T q N : ℕ) : ZMod q) =
      ∑ p ∈ N.toFinset.filter (fun p => p * q ∈ T), ((p : ℕ) : ZMod q)⁻¹ := by
    rw [sig, Nat.cast_list_sum, List.map_map, ← List.sum_toFinset _ hnd, Finset.sum_filter]
    refine Finset.sum_congr rfl fun p hp => ?_
    simp only [Function.comp_apply]
    split_ifs with hpT
    · have h1 := hv.inv q hq p (List.mem_toFinset.1 hp)
      have h2 : (p : ZMod q) * ((p ^ (q - 2) % q : ℕ) : ZMod q) = 1 := by
        rw [← Nat.cast_mul, ← ZMod.natCast_mod, h1, Nat.cast_one]
      exact (inv_eq_of_mul_eq_one_right h2).symm
    · simp
  rw [hrhs, resid]
  -- `{n ∈ T : q ∣ n}` is the image of `{p ∈ N : p * q ∈ T}` under `p ↦ p * q`
  have himg : T.filter (fun n => q ∣ n) =
      (N.toFinset.filter (fun p => p * q ∈ T)).image (fun p => p * q) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_image, List.mem_toFinset]
    constructor
    · rintro ⟨hnT, hqn⟩
      obtain ⟨hpr, hne, hmul⟩ := (hsp n hnT).cofactor hqp hqn
      have hq2 := hqp.two_le
      have hmul' : n / q * q = n := by rw [mul_comm]; exact hmul
      refine ⟨n / q, ⟨?_, by rw [hmul']; exact hnT⟩, hmul'⟩
      rw [hN, mem_nbrs hv.sorted]
      have h2 : 2 * (n / q) ≤ n / q * q := by rw [mul_comm 2]; exact Nat.mul_le_mul_left _ hq2
      refine ⟨hv.complete _ hpr ?_, hne, ?_⟩
      · have := hle n hnT; omega
      · rw [hmul']; exact hle n hnT
    · rintro ⟨p, ⟨-, hpT⟩, rfl⟩
      exact ⟨hpT, dvd_mul_left q p⟩
  rw [himg, Finset.sum_image]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [Nat.mul_div_cancel p hqp.pos]
  · intro x _ y _ hxy
    exact Nat.eq_of_mul_eq_mul_right hqp.pos hxy

/-! ### Soundness of the checker -/

theorem check_sound (hv : Valid d) {T : Finset ℕ} (hT : Sol d T) :
    ∀ (c : Cert) (s : St), Good d T s → check d c s = true → False
  | .lo, s, hg, hc => by
    simp only [check, Nat.blt_eq] at hc
    have hsub : T ⊆ (edgeSet d).filter (fun n => s.out.testBit n = false) := by
      intro n hn
      rw [Finset.mem_filter]
      refine ⟨mem_edgeSet_of_sp hv (hT.sp n hn) (hT.le n hn), ?_⟩
      cases h : s.out.testBit n
      · rfl
      · exact absurd hn (hg.hout n h)
    have := Finset.sum_le_sum_of_subset (f := fun n => d.D / n) hsub
    have := hg.hsAll
    have := hT.sum
    omega
  | .hi, s, hg, hc => by
    simp only [check, Nat.blt_eq] at hc
    have h1 := Finset.sum_le_sum_of_subset (f := fun n => d.D / n)
      (Finset.filter_subset (fun n => s.inn.testBit n = true) T)
    have := hg.hsIn
    have := hT.sum
    omega
  | .md q, s, hg, hc => by
    simp only [check, modLeaf, Bool.and_eq_true] at hc
    obtain ⟨hq, hc⟩ := hc
    have hqp : q.Prime := hv.pm q hq
    obtain ⟨hrho, x, hxq, hxR, hxe⟩ := modAcc_spec hqp.pos hg.hin hg.hout (nbrs d.Bd q d.PL) 0 1 0
      (hqp.pos) ⟨0, hqp.pos, Nat.testBit_one_zero, rfl⟩
    have hres : resid T q = 0 := hT.loc q hqp
    rw [resid_eq_sig hv hT.sp hT.le hq, ZMod.natCast_eq_zero_iff] at hres
    generalize hm : modAcc q s (nbrs d.Bd q d.PL) 0 1 = r at hc hrho hxR hxe
    obtain ⟨rho, R⟩ := r
    simp only [Bool.not_eq_true'] at hc hrho hxR hxe
    rw [zero_add, Nat.mod_eq_zero_of_dvd hres] at hxe
    -- `rho + x ≡ 0 (mod q)` with `rho, x < q` forces `x = (q - rho) % q`
    have hx : x = (q - rho) % q := by
      obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hxe
      have hk2 : k < 2 := by
        by_contra h
        have : q * 2 ≤ q * k := Nat.mul_le_mul_left q (by omega)
        omega
      interval_cases k
      · have : rho = 0 := by omega
        have : x = 0 := by omega
        subst_vars; simp
      · rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [hx] at hxR
    rw [hxR] at hc
    exact absurd hc (by decide)
  | .br n c1 c2, s, hg, hc => by
    simp only [check, Bool.and_eq_true, Nat.ble_eq, Bool.not_eq_true'] at hc
    obtain ⟨⟨⟨⟨⟨hnB, hnE⟩, hni⟩, hno⟩, hc1⟩, hc2⟩ := hc
    by_cases hnT : n ∈ T
    · refine check_sound hv hT c1 _ ⟨?_, ?_, ?_, ?_⟩ hc1
      · intro m hm
        rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq] at hm
        rcases hm with hm | rfl
        · exact hg.hin m hm
        · exact hnT
      · exact hg.hout
      · have hins : T.filter (fun m => (s.inn ||| 2 ^ n).testBit m = true) =
            insert n (T.filter (fun m => s.inn.testBit m = true)) := by
          ext m
          simp only [Finset.mem_filter, Finset.mem_insert, Nat.testBit_or, Nat.testBit_two_pow,
            Bool.or_eq_true, decide_eq_true_eq]
          constructor
          · rintro ⟨hm, h | rfl⟩
            · exact Or.inr ⟨hm, h⟩
            · exact Or.inl rfl
          · rintro (rfl | ⟨hm, h⟩)
            · exact ⟨hnT, Or.inr rfl⟩
            · exact ⟨hm, Or.inl h⟩
        have hnotin : n ∉ T.filter (fun m => s.inn.testBit m = true) := by
          simp [hni]
        simp only
        rw [hins, Finset.sum_insert hnotin]
        have := hg.hsIn
        omega
      · exact hg.hsAll
    · refine check_sound hv hT c2 _ ⟨?_, ?_, ?_, ?_⟩ hc2
      · exact hg.hin
      · intro m hm
        rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq] at hm
        rcases hm with hm | rfl
        · exact hg.hout m hm
        · exact hnT
      · exact hg.hsIn
      · have hnE' : n ∈ edgeSet d := by
          simp only [edgeSet, Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, hnE⟩
        have hins : (edgeSet d).filter (fun m => s.out.testBit m = false) =
            insert n ((edgeSet d).filter (fun m => (s.out ||| 2 ^ n).testBit m = false)) := by
          ext m
          simp only [Finset.mem_filter, Finset.mem_insert, Nat.testBit_or, Nat.testBit_two_pow,
            Bool.or_eq_false_iff, decide_eq_false_iff_not]
          constructor
          · rintro ⟨hm, h⟩
            by_cases hmn : m = n
            · exact Or.inl hmn
            · exact Or.inr ⟨hm, h, fun h' => hmn h'.symm⟩
          · rintro (rfl | ⟨hm, h, -⟩)
            · exact ⟨hnE', hno⟩
            · exact ⟨hm, h⟩
        have hnotin : n ∉ (edgeSet d).filter (fun m => (s.out ||| 2 ^ n).testBit m = false) := by
          simp [Nat.testBit_or, Nat.testBit_two_pow]
        have h1 := hg.hsAll
        rw [hins, Finset.sum_insert hnotin] at h1
        simp only
        omega

/-- Scaling: for a common multiple `D > 0` of the elements, `recipSum T = 1` iff
`∑ D / n = D`. -/
theorem sum_scaled_eq {T : Finset ℕ} {D : ℕ} (hpos : ∀ n ∈ T, 0 < n) (hdvd : ∀ n ∈ T, n ∣ D) :
    ((∑ n ∈ T, D / n : ℕ) : ℚ) = D * recipSum T := by
  rw [recipSum, Finset.mul_sum, Nat.cast_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (hpos n hn).ne'
  rw [Nat.cast_div (hdvd n hn) hn0]
  field_simp

/-- **Soundness of the method.**  If the data are valid and the checker accepts a certificate
from the initial state, then no set of squarefree semiprimes `≤ Bd` has reciprocal sum `1`. -/
theorem no_solution (hv : Valid d) {c : Cert} (hc : check d c (st0 d) = true)
    (T : Finset ℕ) (hsp : ∀ n ∈ T, IsSP n) (hle : ∀ n ∈ T, n ≤ d.Bd) (h1 : recipSum T = 1) :
    False := by
  have hloc : LocalCond T := (integral_iff_localCond T hsp).1 ⟨1, by rw [h1]; norm_num⟩
  have hdvd : ∀ n ∈ T, n ∣ d.D := fun n hn => hv.dvd n (mem_edgeSet_of_sp hv (hsp n hn) (hle n hn))
  have hsum : ∑ n ∈ T, d.D / n = d.D := by
    have := sum_scaled_eq (fun n hn => (hsp n hn).pos) hdvd
    rw [h1, mul_one] at this
    exact_mod_cast this
  refine check_sound hv ⟨hsp, hle, hloc, hsum⟩ c (st0 d) ⟨?_, ?_, ?_, ?_⟩ hc
  · intro n hn; simp [st0] at hn
  · intro n hn; simp [st0] at hn
  · simp [st0]
  · have hall : (edgeSet d).filter (fun n => (st0 d).out.testBit n = false) = edgeSet d :=
      Finset.filter_true_of_mem (fun n _ => Nat.zero_testBit n)
    rw [hall]
    exact hv.s0

end SemiprimeEgypt.MaxDen
