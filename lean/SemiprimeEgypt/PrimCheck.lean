/-
# Primitive sets with reciprocal sum 1: a certificate checker and its soundness

A set `T ⊆ {2, 3, …}` is *primitive* if no element divides another.  This file proves:

* `no_primePow`: a prime power `p ^ k` (`k ≥ 1`) never lies in a primitive set with
  `∑ 1/n = 1`.
* `no_solution`: if valid data for a bound `Bd` (`Valid`, tested by `validB`) and a certificate
  accepted by `check` are given, then no primitive `T ⊆ [2, Bd]` has `∑_{n ∈ T} 1/n = 1`.

The checker works on natural numbers only (`D` is a common multiple of the candidates, so
`∑ 1/n = 1 ⟺ ∑ D/n = D`).  A certificate is a tree of splits `n ∈ T / n ∉ T`; in the branch
`n ∈ T` all multiples and divisors of `n` are excluded automatically.  Its leaves are closed by

* `hi`   : the elements in `T` already sum to more than `1`;
* `lo`   : the *chain bound* is below `1`: a family of divisibility chains with weights `y_c`
           covering every candidate `n` (`∑_{c ∋ n} y_c ≥ D/n`); a primitive set meets each
           chain at most once, so its sum is at most the total weight of the chains that still
           contain a non-excluded element;
* `md p` : for the prime `p` and `M = gcd(D, p ^ Bd)`, the congruence
           `∑_{n ∈ T, p ∣ n} (D/n mod M) ≡ 0 (mod M)` cannot be met (residue bit masks).
-/
import SemiprimeEgypt.Basic
import SemiprimeEgypt.MaxDenCheck
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.IntervalCases

open Finset

namespace SemiprimeEgypt.Prim

/-! ### Prime powers are impossible -/

/-- Primitive: no element divides another. -/
def Primitive (T : Finset ℕ) : Prop := ∀ a ∈ T, ∀ b ∈ T, a ∣ b → a = b

theorem no_primePow {T : Finset ℕ} (hpos : ∀ n ∈ T, 0 < n) (hprim : Primitive T)
    (h1 : recipSum T = 1) {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (hmem : p ^ k ∈ T) : False := by
  have : Fact p.Prime := ⟨hp⟩
  set T' := T.erase (p ^ k) with hT'
  have hsum : recipSum T = 1 / ((p : ℚ) ^ k) + ∑ n ∈ T', (1 : ℚ) / n := by
    rw [recipSum, ← Finset.add_sum_erase T _ hmem]
    push_cast
    rfl
  -- every other element has valuation < k
  have hval : ∀ n ∈ T', padicValNat p n < k := by
    intro n hn
    have hnT := Finset.mem_of_mem_erase hn
    have hne := Finset.ne_of_mem_erase hn
    by_contra hge
    rw [not_lt] at hge
    have hdvd : p ^ k ∣ n := (padicValNat_dvd_iff_le (hpos n hnT).ne').2 hge
    exact hne (hprim _ hmem _ hnT hdvd).symm
  by_cases hT'e : T' = ∅
  · rw [hT'e, Finset.sum_empty, add_zero] at hsum
    rw [h1, one_div] at hsum
    have h' : ((p : ℚ) ^ k) = 1 := inv_eq_one.1 hsum.symm
    have h'' : p ^ k = 1 := by exact_mod_cast h'
    have : (1 : ℕ) < p ^ k := Nat.one_lt_pow hk.ne' hp.one_lt
    omega
  · have hne : T'.Nonempty := Finset.nonempty_iff_ne_empty.2 hT'e
    let F : ℕ → ℚ := fun i => if i = 0 then 1 else 1 / (i : ℚ)
    have hFpos : ∀ i, 0 < F i := by
      intro i; simp only [F]; split_ifs with h
      · norm_num
      · have : (0 : ℚ) < i := by exact_mod_cast Nat.pos_of_ne_zero h
        exact div_pos one_pos this
    have hFj : F (p ^ k) = 1 / ((p : ℚ) ^ k) := by
      simp only [F, ite_eq_right (pow_ne_zero k hp.ne_zero)]; push_cast; rfl
    have hvj : padicValRat p (F (p ^ k)) = -(k : ℤ) := by
      rw [hFj, one_div, padicValRat.self_pow_inv]
    have hvi : ∀ i ∈ T', padicValRat p (F (p ^ k)) < padicValRat p (F i) := by
      intro i hi
      have hi0 : i ≠ 0 := (hpos i (Finset.mem_of_mem_erase hi)).ne'
      simp only [F, ite_eq_right hi0]
      rw [hvj, one_div, padicValRat.inv, padicValRat.of_nat]
      have := hval i hi
      omega
    have hlt := padicValRat.lt_sum_of_lt hne hvi hFpos
    have hsumF : ∑ i ∈ T', F i = ∑ n ∈ T', (1 : ℚ) / n := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi0 : i ≠ 0 := (hpos i (Finset.mem_of_mem_erase hi)).ne'
      simp [F, hi0]
    rw [hsumF, hFj] at hlt
    rw [hFj] at hvj
    have hS : 0 < ∑ n ∈ T', (1 : ℚ) / n :=
      Finset.sum_pos (fun i hi => by
        have := hpos i (Finset.mem_of_mem_erase hi)
        have : (0 : ℚ) < i := by exact_mod_cast this
        exact div_pos one_pos this) hne
    have hq : (1 : ℚ) / (p : ℚ) ^ k ≠ 0 := by
      have : (0 : ℚ) < (p : ℚ) ^ k := pow_pos (by exact_mod_cast hp.pos) k
      exact (div_pos one_pos this).ne'
    have hadd := padicValRat.add_eq_of_lt (p := p)
      (by rw [← hsum, h1]; norm_num) hq hS.ne' hlt
    rw [← hsum, h1, hvj] at hadd
    simp at hadd
    omega

/-! ### Data structures and the checker -/

/-- A binary trie, least significant bit first. -/
inductive Tr (α : Type) where
  | l : α → Tr α
  | n : Tr α → Tr α → Tr α

/-- Lookup in a trie. -/
def Tr.get {α : Type} : Tr α → ℕ → α
  | .l a, _ => a
  | .n t0 t1, k => if k % 2 == 0 then t0.get (k / 2) else t1.get (k / 2)

/-- A certificate: a tree of splits with refutation leaves. -/
inductive Cert where
  | lo : Cert
  | hi : Cert
  | md : ℕ → Cert
  | br : ℕ → Cert → Cert → Cert

/-- The data for a bound `Bd`. -/
structure Data where
  /-- the bound -/
  Bd : ℕ
  /-- a common multiple of the candidates -/
  D : ℕ
  /-- bit mask of the candidates (the non-prime-powers in `[2, Bd]`) -/
  EM : ℕ
  /-- bit mask of the primes used by `md` leaves -/
  PM : ℕ
  /-- a list of primes (used to recognize prime powers in `validB`) -/
  PL : List ℕ
  /-- number of chains -/
  NC : ℕ
  /-- chain `c`: (elements, bit mask of the elements, weight) -/
  chains : Tr (List ℕ × ℕ × ℕ)
  /-- the chains through `n`: (index, bit mask, weight) -/
  chainsOf : Tr (List (ℕ × ℕ × ℕ))
  /-- initial chain bound -/
  cb0 : ℕ

/-- A state: in-mask, out-mask, scaled sum of the elements in, chain bound. -/
structure St where
  inn : ℕ
  out : ℕ
  sIn : ℕ
  cb : ℕ

variable (d : Data)

def cmask (c : ℕ) : ℕ := (d.chains.get c).2.1
def cwt (c : ℕ) : ℕ := (d.chains.get c).2.2
def celems (c : ℕ) : List ℕ := (d.chains.get c).1

/-- The candidates that are not excluded. -/
def liveMask (out : ℕ) : ℕ := d.EM ^^^ (d.EM &&& out)

/-- Subtract the weights of the chains in `L` that have no live element left. -/
def subDead (lm : ℕ) : List (ℕ × ℕ × ℕ) → ℕ → ℕ
  | [], acc => acc
  | c :: L, acc => subDead lm L (if c.2.1 &&& lm == 0 then acc - c.2.2 else acc)

/-- Exclude `n`. -/
def excl (s : St) (n : ℕ) : St :=
  ⟨s.inn, s.out ||| 2 ^ n, s.sIn,
    subDead (liveMask d (s.out ||| 2 ^ n)) (d.chainsOf.get n) s.cb⟩

/-- Exclude `m` if it is a candidate that is still undecided. -/
def exclIf (s : St) (m : ℕ) : St :=
  if d.EM.testBit m && !s.inn.testBit m && !s.out.testBit m then excl d s m else s

/-- Exclude the multiples `n * k`, `2 ≤ k ≤ K`. -/
def exclMult (n : ℕ) : ℕ → St → St
  | 0, s => s
  | k + 1, s => exclMult n k (if 2 ≤ k + 1 then exclIf d s (n * (k + 1)) else s)

/-- Exclude the divisors `k` and `n / k` of `n` for `k = j, j+1, …` while `k * k ≤ n`. -/
def exclDiv (n : ℕ) : ℕ → ℕ → St → St
  | 0, _, s => s
  | f + 1, k, s =>
    if n < k * k then s
    else exclDiv n f (k + 1)
      (if n % k == 0 then exclIf d (exclIf d s k) (n / k) else s)

/-- The branch `n ∈ T`. -/
def inStep (n : ℕ) (s : St) : St :=
  exclDiv d n n 2
    (exclMult d n (d.Bd / n) ⟨s.inn ||| 2 ^ n, s.out, s.sIn + d.D / n, s.cb⟩)

/-- Rotation of an `M`-bit residue mask by `a`. -/
def rot (M a R : ℕ) : ℕ := ((R <<< a) ||| (R >>> (M - a))) &&& (2 ^ M - 1)

/-- Walk the multiples `p * k`, `k = K, …, 1`: `rho` sums the residues of the elements in,
`R` is the set of subset sums of the residues of the undecided elements. -/
def mdAcc (s : St) (p M : ℕ) : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, rho, R => (rho, R)
  | k + 1, rho, R =>
    if d.EM.testBit (p * (k + 1)) then
      if s.inn.testBit (p * (k + 1)) then mdAcc s p M k ((rho + d.D / (p * (k + 1)) % M) % M) R
      else if s.out.testBit (p * (k + 1)) then mdAcc s p M k rho R
      else mdAcc s p M k rho (R ||| rot M (d.D / (p * (k + 1)) % M) R)
    else mdAcc s p M k rho R

def mdTest (p : ℕ) (s : St) (M : ℕ) : Bool :=
  match mdAcc d s p M (d.Bd / p) 0 1 with
    | (rho, R) => !(R.testBit ((M - rho) % M))

def mdLeaf (p : ℕ) (s : St) : Bool :=
  d.PM.testBit p && mdTest d p s (Nat.gcd d.D (p ^ d.Bd))

/-- The certificate checker. -/
def check : Cert → St → Bool
  | .lo, s => Nat.blt s.cb d.D
  | .hi, s => Nat.blt d.D s.sIn
  | .md p, s => mdLeaf d p s
  | .br n c1 c2, s => Nat.ble 2 n && Nat.ble n d.Bd && d.EM.testBit n && !(s.inn.testBit n) &&
      !(s.out.testBit n) && check c1 (inStep d n s) && check c2 (excl d s n)

def st0 : St := ⟨0, 0, 0, d.cb0⟩

/-! ### Validity of the data -/

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

/-- `n` is a positive power of `p` (fuel `f`). -/
def isPowOf (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, n => n % p == 0 && (n / p == 1 || isPowOf p f (n / p))

theorem isPowOf_spec {p : ℕ} : ∀ f n, isPowOf p f n = true → ∃ k, 0 < k ∧ p ^ k = n
  | 0, n, h => by simp [isPowOf] at h
  | f + 1, n, h => by
    simp only [isPowOf, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h
    obtain ⟨hmod, h | h⟩ := h
    · refine ⟨1, one_pos, ?_⟩
      have := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)
      rw [h, one_mul] at this; rw [pow_one, this]
    · obtain ⟨k, hk, hpk⟩ := isPowOf_spec f (n / p) h
      refine ⟨k + 1, Nat.succ_pos k, ?_⟩
      rw [pow_succ, hpk, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)]

/-- `n` is a prime power (sound test; `PL` must consist of primes). -/
def ppB (n : ℕ) : Bool := isPrimeB n || d.PL.any (fun p => isPowOf p n n)

/-- `∑_{i < n} f i` by plain recursion. -/
def sumTo (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => sumTo f k + f k

theorem sumTo_eq (f : ℕ → ℕ) (n : ℕ) : sumTo f n = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp [sumTo]
  | succ k ih => rw [sumTo, ih, Finset.sum_range_succ]

/-- The bit mask of a list. -/
def maskOf : List ℕ → ℕ
  | [] => 0
  | e :: L => 2 ^ e ||| maskOf L

theorem testBit_maskOf (L : List ℕ) (i : ℕ) : (maskOf L).testBit i = true ↔ i ∈ L := by
  induction L with
  | nil => simp [maskOf]
  | cons e L ih =>
    rw [maskOf, Nat.testBit_or, Bool.or_eq_true, ih, Nat.testBit_two_pow, decide_eq_true_eq,
      List.mem_cons]
    constructor
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h

/-- What the soundness proof uses. -/
structure Valid : Prop where
  Dpos : 0 < d.D
  dvd : ∀ n, n ≤ d.Bd → d.EM.testBit n = true → n ∣ d.D
  pm : ∀ p, d.PM.testBit p = true → p.Prime
  em : ∀ n, 2 ≤ n → n ≤ d.Bd → (∀ p k, p.Prime → 0 < k → p ^ k ≠ n) → d.EM.testBit n = true
  chain : ∀ c, c < d.NC → cmask d c = maskOf (celems d c) ∧
    ∀ a ∈ celems d c, ∀ b ∈ celems d c, a ∣ b ∨ b ∣ a
  cof : ∀ n, n ≤ d.Bd → ((d.chainsOf.get n).map Prod.fst).Nodup ∧
    ∀ c ∈ d.chainsOf.get n, c.1 < d.NC ∧ c.2.1 = cmask d c.1 ∧ c.2.2 = cwt d c.1 ∧
      (cmask d c.1).testBit n = true
  cover : ∀ n, n ≤ d.Bd → d.EM.testBit n = true →
    d.D / n ≤ ((d.chainsOf.get n).map (fun c => c.2.2)).sum
  cb0 : sumTo (cwt d) d.NC ≤ d.cb0

/-- The Boolean validity test. -/
def validB : Bool :=
  decide (0 < d.D) &&
  (List.range (d.Bd + 1)).all (fun n => !d.EM.testBit n || d.D % n == 0) &&
  decide (d.PM < 2 ^ (d.Bd + 1)) &&
  (List.range (d.Bd + 1)).all (fun p => !d.PM.testBit p || isPrimeB p) &&
  d.PL.all isPrimeB &&
  (List.range (d.Bd + 1)).all (fun n => decide (n < 2) || d.EM.testBit n || ppB d n) &&
  (List.range d.NC).all (fun c => cmask d c == maskOf (celems d c) &&
    (celems d c).all (fun a => (celems d c).all (fun b => b % a == 0 || a % b == 0))) &&
  (List.range (d.Bd + 1)).all (fun n => decide ((d.chainsOf.get n).map Prod.fst).Nodup &&
    (d.chainsOf.get n).all (fun c => decide (c.1 < d.NC) && c.2.1 == cmask d c.1 &&
      c.2.2 == cwt d c.1 && (cmask d c.1).testBit n)) &&
  (List.range (d.Bd + 1)).all (fun n => !d.EM.testBit n ||
    decide (d.D / n ≤ ((d.chainsOf.get n).map (fun c => c.2.2)).sum)) &&
  decide (sumTo (cwt d) d.NC ≤ d.cb0)

theorem valid_of_validB (h : validB d = true) : Valid d := by
  simp only [validB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hD, hdv⟩, hpmlt⟩, hpm⟩, hpl⟩, hem⟩, hch⟩, hcof⟩, hcov⟩, hcb⟩ := h
  refine ⟨hD, ?_, ?_, ?_, ?_, ?_, ?_, hcb⟩
  · intro n hn hb
    rcases hdv n (by omega) with h' | h'
    · rw [hb] at h'; exact absurd h' (by decide)
    · exact Nat.dvd_of_mod_eq_zero h'
  · intro p hp
    have hlt : p < d.Bd + 1 := by
      by_contra hge
      have : d.PM < 2 ^ p := lt_of_lt_of_le hpmlt (Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [Nat.testBit_lt_two_pow this] at hp
      exact Bool.false_ne_true hp
    rcases hpm p hlt with h' | h'
    · rw [hp] at h'; exact absurd h' (by decide)
    · exact (isPrimeB_iff p).1 h'
  · intro n h2 hn hnpp
    rcases hem n (by omega) with (h' | h') | h'
    · omega
    · exact h'
    · exfalso
      simp only [ppB, Bool.or_eq_true, List.any_eq_true] at h'
      rcases h' with h' | ⟨p, hpL, hpow⟩
      · exact hnpp n 1 ((isPrimeB_iff n).1 h') one_pos (pow_one n)
      · obtain ⟨k, hk, hpk⟩ := isPowOf_spec n n hpow
        exact hnpp p k ((isPrimeB_iff p).1 (hpl p hpL)) hk hpk
  · intro c hc
    obtain ⟨h1, h2⟩ := hch c hc
    refine ⟨h1, fun a ha b hb => ?_⟩
    rcases h2 a ha b hb with h | h
    · exact Or.inl (Nat.dvd_of_mod_eq_zero h)
    · exact Or.inr (Nat.dvd_of_mod_eq_zero h)
  · intro n hn
    obtain ⟨h1, h2⟩ := hcof n (by omega)
    refine ⟨h1, fun c hc => ?_⟩
    obtain ⟨⟨⟨a, b⟩, e⟩, f⟩ := h2 c hc
    exact ⟨a, b, e, f⟩
  · intro n hn hb
    rcases hcov n (by omega) with h' | h'
    · rw [hb] at h'; exact absurd h' (by decide)
    · exact h'

/-! ### Semantics -/

/-- The chain `c` still contains a candidate that is not excluded. -/
def cLive (out c : ℕ) : Prop := cmask d c &&& liveMask d out ≠ 0

/-- The chain bound of a state: the total weight of the live chains. -/
def cbound (out : ℕ) : ℕ :=
  ∑ c ∈ (range d.NC).filter (fun c => cmask d c &&& liveMask d out ≠ 0), cwt d c

/-- The solution to be refuted. -/
structure Sol (T : Finset ℕ) : Prop where
  two : ∀ n ∈ T, 2 ≤ n
  le : ∀ n ∈ T, n ≤ d.Bd
  prim : Primitive T
  sum : ∑ n ∈ T, d.D / n = d.D
  em : ∀ n ∈ T, d.EM.testBit n = true

/-- `T` is consistent with the state `s`. -/
structure Good (T : Finset ℕ) (s : St) : Prop where
  hin : ∀ n, s.inn.testBit n = true → n ∈ T
  hout : ∀ n, s.out.testBit n = true → n ∉ T
  hsIn : s.sIn ≤ ∑ n ∈ T.filter (fun n => s.inn.testBit n = true), d.D / n
  hcb : cbound d s.out ≤ s.cb

variable {d}

theorem testBit_liveMask (out i : ℕ) :
    (liveMask d out).testBit i = (d.EM.testBit i && !out.testBit i) := by
  unfold liveMask
  rw [Nat.testBit_xor, Nat.testBit_and]
  cases d.EM.testBit i <;> cases out.testBit i <;> rfl

theorem land_ne_zero_iff (a b : ℕ) : a &&& b ≠ 0 ↔ ∃ i, a.testBit i = true ∧ b.testBit i = true := by
  constructor
  · intro h
    by_contra hno
    simp only [not_exists, not_and, Bool.not_eq_true] at hno
    apply h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.zero_testBit]
    cases ha : a.testBit i
    · rfl
    · simp [hno i ha]
  · rintro ⟨i, ha, hb⟩ h0
    have := congrArg (fun x => x.testBit i) h0
    simp only [Nat.testBit_and, ha, hb, Nat.zero_testBit] at this
    exact absurd this (by decide)

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

/-! #### The chain bound under exclusion -/

theorem subDead_eq (lm : ℕ) : ∀ (L : List (ℕ × ℕ × ℕ)) (acc : ℕ),
    subDead lm L acc = acc - ((L.filter (fun c => c.2.1 &&& lm == 0)).map (fun c => c.2.2)).sum
  | [], acc => by simp [subDead]
  | c :: L, acc => by
    rw [subDead, subDead_eq lm L]
    by_cases h : (c.2.1 &&& lm == 0) = true
    · rw [ite_eq_left h]
      simp [h, Nat.sub_sub]
    · rw [ite_eq_right h]
      simp [h]

theorem testBit_liveMask_or (out n i : ℕ) :
    (liveMask d (out ||| 2 ^ n)).testBit i = ((liveMask d out).testBit i && !decide (n = i)) := by
  rw [testBit_liveMask, testBit_liveMask, Nat.testBit_or, Nat.testBit_two_pow]
  cases d.EM.testBit i <;> cases out.testBit i <;> cases decide (n = i) <;> rfl

/-- Excluding `n` only kills chains through `n`. -/
theorem cLive_of_or {out n c : ℕ} (hc : (cmask d c).testBit n = false)
    (h : cmask d c &&& liveMask d out ≠ 0) : cmask d c &&& liveMask d (out ||| 2 ^ n) ≠ 0 := by
  rw [land_ne_zero_iff] at h ⊢
  obtain ⟨i, hi1, hi2⟩ := h
  refine ⟨i, hi1, ?_⟩
  rw [testBit_liveMask_or, hi2]
  have : n ≠ i := by rintro rfl; rw [hc] at hi1; exact absurd hi1 (by decide)
  simp [this]

theorem cLive_mono {out n c : ℕ} (h : cmask d c &&& liveMask d (out ||| 2 ^ n) ≠ 0) :
    cmask d c &&& liveMask d out ≠ 0 := by
  rw [land_ne_zero_iff] at h ⊢
  obtain ⟨i, hi1, hi2⟩ := h
  refine ⟨i, hi1, ?_⟩
  rw [testBit_liveMask_or, Bool.and_eq_true] at hi2
  exact hi2.1

theorem cbound_excl (hv : Valid d) {out cb n : ℕ} (hn : n ≤ d.Bd) (hEM : d.EM.testBit n = true)
    (hout : out.testBit n = false) (hcb : cbound d out ≤ cb) :
    cbound d (out ||| 2 ^ n) ≤
      subDead (liveMask d (out ||| 2 ^ n)) (d.chainsOf.get n) cb := by
  rw [subDead_eq]
  set lm' := liveMask d (out ||| 2 ^ n)
  set L := d.chainsOf.get n
  obtain ⟨hnd, hL⟩ := hv.cof n hn
  -- the chains of `L` that die
  set Ld := L.filter (fun c => c.2.1 &&& lm' == 0)
  have hS : (Ld.map (fun c => c.2.2)).sum =
      ∑ i ∈ (Ld.map Prod.fst).toFinset, cwt d i := by
    have hnd' : (Ld.map Prod.fst).Nodup := (List.Sublist.map _ List.filter_sublist).nodup hnd
    rw [List.sum_toFinset _ hnd', List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    have := (hL c (List.mem_of_mem_filter hc)).2.2.1
    simp [Function.comp, this]
  -- live before = live after ∪ dying, and the dying chains of `L` are among the dying ones
  set A := (range d.NC).filter (fun c => cmask d c &&& liveMask d out ≠ 0)
  set A' := (range d.NC).filter (fun c => cmask d c &&& lm' ≠ 0)
  have hsub : A' ⊆ A := by
    intro c hc
    simp only [A', A, Finset.mem_filter] at hc ⊢
    exact ⟨hc.1, cLive_mono hc.2⟩
  have hdis : (Ld.map Prod.fst).toFinset ⊆ A \ A' := by
    intro c hc
    rw [List.mem_toFinset, List.mem_map] at hc
    obtain ⟨e, he, rfl⟩ := hc
    have heL := List.mem_of_mem_filter he
    obtain ⟨hlt, hm, -, hbit⟩ := hL e heL
    have hdead : e.2.1 &&& lm' = 0 := by
      have := List.of_mem_filter he; simpa using this
    simp only [Finset.mem_sdiff, A, A', Finset.mem_filter, Finset.mem_range]
    refine ⟨⟨hlt, ?_⟩, fun h => ?_⟩
    · rw [land_ne_zero_iff]
      refine ⟨n, hbit, ?_⟩
      rw [testBit_liveMask, hEM, hout]; rfl
    · exact h.2 (by rw [← hm]; exact hdead)
  have hsplit : cbound d out = cbound d (out ||| 2 ^ n) + ∑ i ∈ A \ A', cwt d i := by
    unfold cbound
    rw [← Finset.sum_sdiff hsub, add_comm]
  have hle : ∑ i ∈ (Ld.map Prod.fst).toFinset, cwt d i ≤ ∑ i ∈ A \ A', cwt d i :=
    Finset.sum_le_sum_of_subset hdis
  rw [hS]
  omega

/-! #### Consistency of the states -/

theorem good_excl (hv : Valid d) {T : Finset ℕ} {s : St} (hg : Good d T s) {n : ℕ}
    (hnT : n ∉ T) (hn : n ≤ d.Bd) (hEM : d.EM.testBit n = true) (hout : s.out.testBit n = false) :
    Good d T (excl d s n) := by
  refine ⟨hg.hin, ?_, hg.hsIn, ?_⟩
  · intro m hm
    simp only [excl, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq] at hm
    rcases hm with hm | rfl
    · exact hg.hout m hm
    · exact hnT
  · exact cbound_excl hv hn hEM hout hg.hcb

/-- Excluding an element that cannot be in `T`. -/
theorem good_exclIf (hv : Valid d) {T : Finset ℕ} {s : St} (hg : Good d T s) {m : ℕ}
    (hmT : m ∉ T) (hm : m ≤ d.Bd) : Good d T (exclIf d s m) := by
  unfold exclIf
  split_ifs with h
  · simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    exact good_excl hv hg hmT hm h.1.1 h.2
  · exact hg

theorem good_exclMult (hv : Valid d) {T : Finset ℕ} (hprim : Primitive T) {n : ℕ} (hnT : n ∈ T)
    (hn0 : 0 < n) : ∀ (K : ℕ) (s : St), K ≤ d.Bd / n → Good d T s → Good d T (exclMult d n K s)
  | 0, s, _, hg => hg
  | k + 1, s, hK, hg => by
    rw [exclMult]
    apply good_exclMult hv hprim hnT hn0 k _ (by omega)
    split_ifs with h2
    · refine good_exclIf hv hg ?_ ?_
      · intro hm
        have := hprim n hnT _ hm (dvd_mul_right n (k + 1))
        have h3 : n * 1 < n * (k + 1) := Nat.mul_lt_mul_of_pos_left (by omega) hn0
        omega
      · calc n * (k + 1) ≤ n * (d.Bd / n) := Nat.mul_le_mul_left n hK
          _ ≤ d.Bd := Nat.mul_div_le d.Bd n
    · exact hg

theorem good_exclDiv (hv : Valid d) {T : Finset ℕ} (hprim : Primitive T) {n : ℕ} (hnT : n ∈ T)
    (hnB : n ≤ d.Bd) : ∀ (f k : ℕ) (s : St), 2 ≤ k → Good d T s → Good d T (exclDiv d n f k s)
  | 0, _, s, _, hg => hg
  | f + 1, k, s, hk, hg => by
    rw [exclDiv]
    split_ifs with h1 h2
    · exact hg
    · apply good_exclDiv hv hprim hnT hnB f (k + 1) _ (by omega)
      have hdvd : k ∣ n := Nat.dvd_of_mod_eq_zero (by simpa using h2)
      have hkn : k < n := by nlinarith
      have hq : n / k < n := Nat.div_lt_self (by omega) (by omega)
      have hqd : n / k ∣ n := Nat.div_dvd_of_dvd hdvd
      refine good_exclIf hv (good_exclIf hv hg ?_ (by omega)) ?_ ?_
      · intro hm
        have := hprim k hm n hnT hdvd
        omega
      · intro hm
        have := hprim _ hm n hnT hqd
        omega
      · have := Nat.div_le_self n k; omega
    · exact good_exclDiv hv hprim hnT hnB f (k + 1) _ (by omega) hg

theorem good_inStep (hv : Valid d) {T : Finset ℕ} (hprim : Primitive T) {s : St}
    (hg : Good d T s) {n : ℕ} (hnT : n ∈ T) (h2 : 2 ≤ n) (hnB : n ≤ d.Bd)
    (hni : s.inn.testBit n = false) : Good d T (inStep d n s) := by
  unfold inStep
  apply good_exclDiv hv hprim hnT hnB n 2 _ le_rfl
  apply good_exclMult hv hprim hnT (by omega) _ _ le_rfl
  refine ⟨?_, hg.hout, ?_, hg.hcb⟩
  · intro m hm
    simp only [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq] at hm
    rcases hm with hm | rfl
    · exact hg.hin m hm
    · exact hnT
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
    have hnotin : n ∉ T.filter (fun m => s.inn.testBit m = true) := by simp [hni]
    show s.sIn + d.D / n ≤ _
    rw [hins, Finset.sum_insert hnotin]
    have := hg.hsIn
    omega

/-! #### The congruence leaves -/

/-- The sum of the residues of the multiples `p * j`, `1 ≤ j ≤ k`, that lie in `T`. -/
def msig (T : Finset ℕ) (p M : ℕ) (k : ℕ) : ℕ :=
  ∑ j ∈ range k, if p * (j + 1) ∈ T then d.D / (p * (j + 1)) % M else 0

theorem mdAcc_spec {T : Finset ℕ} {s : St} {p M : ℕ} (hM : 0 < M)
    (hin : ∀ n, s.inn.testBit n = true → n ∈ T) (hout : ∀ n, s.out.testBit n = true → n ∉ T)
    (hem : ∀ n ∈ T, d.EM.testBit n = true) :
    ∀ (k rho R σ : ℕ), rho < M → (∃ x < M, R.testBit x = true ∧ (rho + x) % M = σ % M) →
      (mdAcc d s p M k rho R).1 < M ∧ ∃ x < M, (mdAcc d s p M k rho R).2.testBit x = true ∧
        ((mdAcc d s p M k rho R).1 + x) % M = (σ + msig (d := d) T p M k) % M
  | 0, rho, R, σ, hrho, hx => by simpa [mdAcc, msig] using ⟨hrho, hx⟩
  | k + 1, rho, R, σ, hrho, ⟨x, hxM, hxR, hxe⟩ => by
    set n := p * (k + 1)
    set a := d.D / n % M
    have ha : a < M := Nat.mod_lt _ hM
    have hsig : msig (d := d) T p M (k + 1) = msig (d := d) T p M k + (if n ∈ T then a else 0) := by
      simp only [msig]; rw [Finset.sum_range_succ]
    rw [hsig]
    unfold mdAcc
    by_cases hE : d.EM.testBit n = true
    · rw [ite_eq_left hE]
      by_cases h1 : s.inn.testBit n = true
      · rw [ite_eq_left h1, ite_eq_left (hin _ h1)]
        have := mdAcc_spec (p := p) hM hin hout hem k ((rho + a) % M) R (σ + a) (Nat.mod_lt _ hM)
          ⟨x, hxM, hxR, by rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_right_comm,
            Nat.add_mod, hxe, ← Nat.add_mod]⟩
        have e : σ + (msig (d := d) T p M k + a) = σ + a + msig (d := d) T p M k := by omega
        rw [e]; exact this
      · rw [ite_eq_right h1]
        by_cases h2 : s.out.testBit n = true
        · rw [ite_eq_left h2, ite_eq_right (hout _ h2)]
          simpa using mdAcc_spec (p := p) hM hin hout hem k rho R σ hrho ⟨x, hxM, hxR, hxe⟩
        · rw [ite_eq_right h2]
          by_cases hT : n ∈ T
          · rw [ite_eq_left hT]
            have := mdAcc_spec (p := p) hM hin hout hem k rho (R ||| rot M a R) (σ + a) hrho
              ⟨(x + a) % M, Nat.mod_lt _ hM, by
                rw [Nat.testBit_or, rot_testBit ha hxM hxR, Bool.or_true], by
                rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, ← Nat.add_assoc, Nat.add_mod,
                  hxe, ← Nat.add_mod]⟩
            have e : σ + (msig (d := d) T p M k + a) = σ + a + msig (d := d) T p M k := by omega
            rw [e]; exact this
          · rw [ite_eq_right hT]
            simpa using mdAcc_spec (p := p) hM hin hout hem k rho (R ||| rot M a R) σ hrho
              ⟨x, hxM, by rw [Nat.testBit_or, hxR, Bool.true_or], hxe⟩
    · rw [ite_eq_right hE]
      have hT : n ∉ T := fun h => hE (hem n h)
      rw [ite_eq_right hT]
      simpa using mdAcc_spec (p := p) hM hin hout hem k rho R σ hrho ⟨x, hxM, hxR, hxe⟩

/-- The multiples of `p` in `T` are the `p * (j + 1)`, `j < Bd / p`. -/
theorem msig_eq {T : Finset ℕ} (hT : Sol d T) {p M : ℕ} (hp : 0 < p) :
    msig (d := d) T p M (d.Bd / p) = ∑ n ∈ T.filter (fun n => p ∣ n), d.D / n % M := by
  unfold msig
  rw [← Finset.sum_filter]
  have himg : T.filter (fun n => p ∣ n) =
      ((range (d.Bd / p)).filter (fun j => p * (j + 1) ∈ T)).image (fun j => p * (j + 1)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨hnT, m, rfl⟩
      have h2 := hT.two _ hnT
      have hle := hT.le _ hnT
      have hm : 1 ≤ m := by
        rcases m with _ | m
        · simp at h2
        · omega
      refine ⟨m - 1, ⟨?_, ?_⟩, ?_⟩
      · have : m ≤ d.Bd / p := (Nat.le_div_iff_mul_le hp).2 (by rw [mul_comm]; exact hle)
        omega
      · rw [Nat.sub_add_cancel hm]; exact hnT
      · rw [Nat.sub_add_cancel hm]
    · rintro ⟨j, ⟨-, hj⟩, rfl⟩
      exact ⟨hj, dvd_mul_right p _⟩
  rw [himg, Finset.sum_image]
  intro x _ y _ hxy
  have := Nat.eq_of_mul_eq_mul_left hp hxy
  omega

/-- The congruence at `p`: `∑_{n ∈ T, p ∣ n} (D/n mod M) ≡ 0 (mod M)` for `M = gcd(D, p^Bd)`. -/
theorem md_congr (hv : Valid d) {T : Finset ℕ} (hT : Sol d T) {p : ℕ} (hp : p.Prime) :
    (∑ n ∈ T.filter (fun n => p ∣ n), d.D / n % Nat.gcd d.D (p ^ d.Bd)) %
      Nat.gcd d.D (p ^ d.Bd) = 0 := by
  set M := Nat.gcd d.D (p ^ d.Bd)
  have hMD : M ∣ d.D := Nat.gcd_dvd_left _ _
  obtain ⟨j, -, hMj⟩ := (Nat.dvd_prime_pow hp).1 (Nat.gcd_dvd_right d.D (p ^ d.Bd))
  have hdvdD : ∀ n ∈ T, n ∣ d.D := fun n hn => hv.dvd n (hT.le n hn) (hT.em n hn)
  -- elements not divisible by p contribute multiples of M
  have hnot : ∀ n ∈ T.filter (fun n => ¬ p ∣ n), M ∣ d.D / n := by
    intro n hn
    rw [Finset.mem_filter] at hn
    have hcop : Nat.Coprime M n := by
      have hMj' : M = p ^ j := hMj
      rw [hMj']; exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hn.2)
    have h1 : M ∣ n * (d.D / n) := by rw [Nat.mul_div_cancel' (hdvdD n hn.1)]; exact hMD
    exact hcop.dvd_of_dvd_mul_left h1
  have hsplit := Finset.sum_filter_add_sum_filter_not T (fun n => p ∣ n) (fun n => d.D / n)
  rw [hT.sum] at hsplit
  have h2 : M ∣ ∑ n ∈ T.filter (fun n => ¬ p ∣ n), d.D / n := Finset.dvd_sum hnot
  have h3 : M ∣ ∑ n ∈ T.filter (fun n => p ∣ n), d.D / n := by
    have : M ∣ ∑ n ∈ T.filter (fun n => p ∣ n), d.D / n +
        ∑ n ∈ T.filter (fun n => ¬ p ∣ n), d.D / n := by rw [hsplit]; exact hMD
    exact (Nat.dvd_add_right h2).1 (by rwa [add_comm] at this)
  rw [← Finset.sum_nat_mod, Nat.mod_eq_zero_of_dvd h3]

/-! #### The chain bound -/

theorem sum_le_cbound (hv : Valid d) {T : Finset ℕ} (hT : Sol d T) {out : ℕ}
    (hout : ∀ n, out.testBit n = true → n ∉ T) :
    ∑ n ∈ T, d.D / n ≤ cbound d out := by
  -- every element is covered by the chains through it
  have hcov : ∀ n ∈ T, d.D / n ≤ ∑ c ∈ (range d.NC).filter (fun c => (cmask d c).testBit n = true),
      cwt d c := by
    intro n hn
    have hnB := hT.le n hn
    obtain ⟨hnd, hL⟩ := hv.cof n hnB
    calc d.D / n ≤ ((d.chainsOf.get n).map (fun c => c.2.2)).sum := hv.cover n hnB (hT.em n hn)
      _ = ∑ c ∈ ((d.chainsOf.get n).map Prod.fst).toFinset, cwt d c := by
          rw [List.sum_toFinset _ hnd, List.map_map]
          congr 1
          apply List.map_congr_left
          intro c hc
          simp [Function.comp, (hL c hc).2.2.1]
      _ ≤ _ := by
          apply Finset.sum_le_sum_of_subset
          intro c hc
          rw [List.mem_toFinset, List.mem_map] at hc
          obtain ⟨e, he, rfl⟩ := hc
          obtain ⟨hlt, -, -, hbit⟩ := hL e he
          simp [hlt, hbit]
  -- each chain meets `T` at most once
  have hone : ∀ c < d.NC, (T.filter (fun n => (cmask d c).testBit n = true)).card ≤ 1 := by
    intro c hc
    obtain ⟨hm, hch⟩ := hv.chain c hc
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, hm, testBit_maskOf] at ha hb
    rcases hch a ha.2 b hb.2 with h | h
    · exact hT.prim a ha.1 b hb.1 h
    · exact (hT.prim b hb.1 a ha.1 h).symm
  calc ∑ n ∈ T, d.D / n
      ≤ ∑ n ∈ T, ∑ c ∈ (range d.NC).filter (fun c => (cmask d c).testBit n = true), cwt d c :=
        Finset.sum_le_sum hcov
    _ = ∑ c ∈ range d.NC, ∑ n ∈ T.filter (fun n => (cmask d c).testBit n = true), cwt d c := by
        simp_rw [Finset.sum_filter]
        exact Finset.sum_comm
    _ = ∑ c ∈ range d.NC, (T.filter (fun n => (cmask d c).testBit n = true)).card * cwt d c := by
        simp [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ c ∈ range d.NC, if cmask d c &&& liveMask d out ≠ 0 then cwt d c else 0 := by
        apply Finset.sum_le_sum
        intro c hc
        have h1 := hone c (Finset.mem_range.1 hc)
        split_ifs with hl
        · calc _ ≤ 1 * cwt d c := Nat.mul_le_mul_right _ h1
            _ = cwt d c := one_mul _
        · have h0 : (T.filter (fun n => (cmask d c).testBit n = true)).card = 0 := by
            rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro n hn hbit
            apply hl
            rw [land_ne_zero_iff]
            refine ⟨n, hbit, ?_⟩
            rw [testBit_liveMask, hT.em n hn]
            cases h : out.testBit n
            · rfl
            · exact absurd hn (hout n h)
          rw [h0, zero_mul]
    _ = cbound d out := by rw [cbound, Finset.sum_filter]

/-! #### Soundness -/

theorem check_sound (hv : Valid d) {T : Finset ℕ} (hT : Sol d T) :
    ∀ (c : Cert) (s : St), Good d T s → check d c s = true → False
  | .lo, s, hg, hc => by
    simp only [check, Nat.blt_eq] at hc
    have h1 := sum_le_cbound hv hT hg.hout
    have h2 := hg.hcb
    have h3 := hT.sum
    omega
  | .hi, s, hg, hc => by
    simp only [check, Nat.blt_eq] at hc
    have h1 := Finset.sum_le_sum_of_subset (f := fun n => d.D / n)
      (Finset.filter_subset (fun n => s.inn.testBit n = true) T)
    have := hg.hsIn
    have := hT.sum
    omega
  | .md p, s, hg, hc => by
    simp only [check, mdLeaf, Bool.and_eq_true] at hc
    obtain ⟨hp, hc⟩ := hc
    have hpp : p.Prime := hv.pm p hp
    set M := Nat.gcd d.D (p ^ d.Bd) with hM
    have hMpos : 0 < M := Nat.gcd_pos_of_pos_left _ hv.Dpos
    obtain ⟨hrho, x, hxM, hxR, hxe⟩ := mdAcc_spec (d := d) hMpos hg.hin hg.hout hT.em
      (d.Bd / p) 0 1 0 hMpos ⟨0, hMpos, Nat.testBit_one_zero, rfl⟩
    have hcong := md_congr hv hT hpp
    rw [← hM, ← msig_eq hT hpp.pos] at hcong
    unfold mdTest at hc
    generalize hm : mdAcc d s p M (d.Bd / p) 0 1 = r at hc hrho hxR hxe
    obtain ⟨rho, R⟩ := r
    simp only [Bool.not_eq_true'] at hc hrho hxR hxe
    rw [zero_add, hcong] at hxe
    have hx : x = (M - rho) % M := by
      obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hxe
      have hk2 : k < 2 := by
        by_contra h
        have : M * 2 ≤ M * k := Nat.mul_le_mul_left M (by omega)
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
    obtain ⟨⟨⟨⟨⟨⟨h2, hnB⟩, hnE⟩, hni⟩, hno⟩, hc1⟩, hc2⟩ := hc
    by_cases hnT : n ∈ T
    · exact check_sound hv hT c1 _ (good_inStep hv hT.prim hg hnT h2 hnB hni) hc1
    · exact check_sound hv hT c2 _ (good_excl hv hg hnT hnB hnE hno) hc2

/-- **Soundness of the method.**  Valid data and an accepted certificate: no primitive set of
integers in `[2, Bd]` has reciprocal sum `1`. -/
theorem no_solution (hv : Valid d) {c : Cert} (hc : check d c (st0 d) = true)
    (T : Finset ℕ) (h2 : ∀ n ∈ T, 2 ≤ n) (hle : ∀ n ∈ T, n ≤ d.Bd) (hprim : Primitive T)
    (h1 : recipSum T = 1) : False := by
  have hem : ∀ n ∈ T, d.EM.testBit n = true := by
    intro n hn
    refine hv.em n (h2 n hn) (hle n hn) (fun p k hp hk hpk => ?_)
    exact no_primePow (fun m hm => by have := h2 m hm; omega) hprim h1 hp hk (hpk ▸ hn)
  have hdvd : ∀ n ∈ T, n ∣ d.D := fun n hn => hv.dvd n (hle n hn) (hem n hn)
  have hsum : ∑ n ∈ T, d.D / n = d.D := by
    have := SemiprimeEgypt.MaxDen.sum_scaled_eq (fun n hn => by have := h2 n hn; omega) hdvd
    rw [h1, mul_one] at this
    exact_mod_cast this
  refine check_sound hv ⟨h2, hle, hprim, hsum, hem⟩ c (st0 d) ⟨?_, ?_, ?_, ?_⟩ hc
  · intro n hn; simp [st0] at hn
  · intro n hn; simp [st0] at hn
  · simp [st0]
  · simp only [st0]
    refine le_trans ?_ hv.cb0
    rw [sumTo_eq, cbound]
    exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- Assembling a checked split from its two checked children (used to split the kernel check
of a large certificate into independent theorems). -/
theorem check_br_of {n : ℕ} {c1 c2 : Cert} {s : St}
    (h : (Nat.ble 2 n && Nat.ble n d.Bd && d.EM.testBit n && !(s.inn.testBit n) &&
      !(s.out.testBit n)) = true)
    (h1 : check d c1 (inStep d n s) = true) (h2 : check d c2 (excl d s n) = true) :
    check d (.br n c1 c2) s = true := by
  simp only [check, h, h1, h2, Bool.and_self]

end SemiprimeEgypt.Prim
