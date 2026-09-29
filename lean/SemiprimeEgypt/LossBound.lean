/-
**The loss bound (P4)**, the new pruning test of `semiprime48.cpp`.

At a node of the search, the edges of the final core `E` split into the decided edges `Dst` and
the future edges `F`, all of whose endpoints lie in the set `Q` of undecided primes; the
unsatisfied primes outside `Q` are already decided (`Ust`).  Put `w(e) = up(e) - θ`.
Every future edge `{a, b}` hands its weight to its endpoints in two rounded-up shares
(`share a b + share b a ≥ w`), and every undecided prime `k` receives at most `L k`, where `L k`
bounds the best *local configuration* of `k`: a set `Y` of future neighbours with
`res(k) + Σ_Y (P y)⁻¹ ≡ 0 (mod P k)` (if `k` ends up satisfied), or any `Y` plus the allowance
`GV k - θ` of the unsatisfied option.  Then (`loss_bound`)

  su E + gz(U E) + VB(K - |E| - |U E|)  ≤  su Dst + gz Ust + (K - |Dst| - |Ust|) θ + VTH + Σ_{k∈Q} L k.

The left side is the quantity of the final Step-1 test, so a node whose right side is `< ONE`
has no descendant core passing that test.
-/
import SemiprimeEgypt.Search
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open Finset

namespace SemiprimeEgypt
namespace Srch
namespace Inst

variable {I : Inst}

lemma wt_symm (a b : ℕ) : I.wt a b = I.wt b a := by
  unfold wt EU; rw [Nat.mul_comm]

/-- The two shares of an edge add up to at least its weight. -/
lemma share_add_ge (hI : InstOK I) {a b : ℕ} (hab : a < b) :
    I.wt a b ≤ I.share a b + I.share b a := by
  unfold share
  rw [if_neg (by omega : ¬ b < a), if_pos hab, wt_symm b a]
  have := cdiv_add_cdiv_ge (I.wt a b) (I.sh a) hI.AD_pos (hI.sh_le a)
  linarith

/-- The future neighbours of `k` in an edge set `F`. -/
def nbrF (F : Finset (ℕ × ℕ)) (k : ℕ) : Finset ℕ :=
  (F.filter (fun e => e.1 = k)).image Prod.snd ∪ (F.filter (fun e => e.2 = k)).image Prod.fst

/-- Summing an endpoint-indexed quantity over the edges at `k` = summing over the neighbours. -/
lemma sum_edges_at {β : Type*} [AddCommMonoid β] (F : Finset (ℕ × ℕ))
    (hF : ∀ e ∈ F, e.1 < e.2) (k : ℕ) (f : ℕ → β) :
    ∑ e ∈ F, ((if e.1 = k then f e.2 else 0) + (if e.2 = k then f e.1 else 0)) =
      ∑ y ∈ nbrF F k, f y := by
  rw [Finset.sum_add_distrib, nbrF]
  have hdisj : Disjoint ((F.filter (fun e => e.1 = k)).image Prod.snd)
      ((F.filter (fun e => e.2 = k)).image Prod.fst) := by
    rw [Finset.disjoint_left]
    intro y hy hy'
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨e', he', hee'⟩ := Finset.mem_image.1 hy'
    have h1 := Finset.mem_filter.1 he
    have h2 := Finset.mem_filter.1 he'
    have := hF e h1.1
    have := hF e' h2.1
    omega
  rw [Finset.sum_union hdisj]
  congr 1
  · rw [← Finset.sum_filter, Finset.sum_image]
    intro e he e' he' h
    have h1 := (Finset.mem_filter.1 he).2
    have h2 := (Finset.mem_filter.1 he').2
    exact Prod.ext (by rw [h1, h2]) h
  · rw [← Finset.sum_filter, Finset.sum_image]
    intro e he e' he' h
    have h1 := (Finset.mem_filter.1 he).2
    have h2 := (Finset.mem_filter.1 he').2
    exact Prod.ext h (by rw [h1, h2])

lemma sum_ctr_eq (F : Finset (ℕ × ℕ)) (hF : ∀ e ∈ F, e.1 < e.2) (k : ℕ) :
    ∑ e ∈ F, I.ctr k e = ∑ y ∈ nbrF F k, I.inv k y := by
  rw [← sum_edges_at F hF k (I.inv k)]; rfl

lemma nbrF_subset (F : Finset (ℕ × ℕ)) (k : ℕ) (Cand : Finset ℕ)
    (h : ∀ e ∈ F, (e.1 = k → e.2 ∈ Cand) ∧ (e.2 = k → e.1 ∈ Cand)) : nbrF F k ⊆ Cand := by
  intro y hy
  rw [nbrF, Finset.mem_union] at hy
  rcases hy with hy | hy
  · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hy
    have := Finset.mem_filter.1 he
    exact (h e this.1).1 this.2
  · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hy
    have := Finset.mem_filter.1 he
    exact (h e this.1).2 this.2

/-- The residue of the whole core at `k`, in terms of the decided part and the future
neighbours. -/
lemma res_split {E Dst F : Finset (ℕ × ℕ)} (hE : E = Dst ∪ F) (hdisj : Disjoint Dst F)
    (hF : ∀ e ∈ F, e.1 < e.2) (k : ℕ) :
    I.res E k = (I.res Dst k + ∑ y ∈ nbrF F k, I.inv k y) % I.P k := by
  rw [res, res, hE, Finset.sum_union hdisj, sum_ctr_eq F hF k]
  exact (Nat.mod_add_mod _ _ _).symm

/-- **The loss bound.** -/
theorem loss_bound (hI : InstOK I) {T : Tables}
    (hvth : ∀ x ≤ I.K, (T.VB x : ℤ) - x * I.TH ≤ T.VTH)
    {E Dst F : Finset (ℕ × ℕ)} {Q Ust : Finset ℕ} {Cand : ℕ → Finset ℕ} {L : ℕ → ℤ}
    (hE : E = Dst ∪ F) (hdisj : Disjoint Dst F)
    (hF : ∀ e ∈ F, e.1 < e.2 ∧ e.1 ∈ Q ∧ e.2 ∈ Q ∧ e.2 ∈ Cand e.1 ∧ e.1 ∈ Cand e.2)
    (hUst : Ust = (I.UE E).filter (· ∉ Q)) (hQ : ∀ k ∈ Q, k < I.m)
    (hL1 : ∀ k ∈ Q, ∀ Y ⊆ Cand k, (I.res Dst k + ∑ y ∈ Y, I.inv k y) % I.P k = 0 →
      ∑ y ∈ Y, I.share k y ≤ L k)
    (hL2 : ∀ k ∈ Q, ∀ Y ⊆ Cand k, (I.GV k : ℤ) - I.TH + ∑ y ∈ Y, I.share k y ≤ L k)
    (hK : E.card + (I.UE E).card ≤ I.K) :
    ((I.su E + I.gz (I.UE E) + T.VB (I.K - E.card - (I.UE E).card) : ℕ) : ℤ) ≤
      ((I.su Dst + I.gz Ust + (I.K - (Dst.card + Ust.card)) * I.TH : ℕ) : ℤ) + T.VTH +
        ∑ k ∈ Q, L k := by
  classical
  have hF1 : ∀ e ∈ F, e.1 < e.2 := fun e he => (hF e he).1
  set UQ := (I.UE E).filter (· ∈ Q) with hUQ
  -- decompositions
  have hsu : I.su E = I.su Dst + I.su F := by rw [su, su, su, hE, Finset.sum_union hdisj]
  have hUE : I.UE E = Ust ∪ UQ := by
    rw [hUst, hUQ]; ext k; simp only [Finset.mem_union, Finset.mem_filter]; tauto
  have hUdisj : Disjoint Ust UQ := by
    rw [hUst, hUQ, Finset.disjoint_filter]; intro k _ h1 h2; exact h1 h2
  have hgz : I.gz (I.UE E) = I.gz Ust + I.gz UQ := by
    rw [gz, gz, gz, hUE, Finset.sum_union hUdisj]
  have hEc : E.card = Dst.card + F.card := by rw [hE, Finset.card_union_of_disjoint hdisj]
  have hUc : (I.UE E).card = Ust.card + UQ.card := by
    rw [hUE, Finset.card_union_of_disjoint hUdisj]
  set x := I.K - E.card - (I.UE E).card with hx
  have hxK : x ≤ I.K := by omega
  have hslack : I.K - (Dst.card + Ust.card) = F.card + UQ.card + x := by omega
  -- the three parts
  have h1 := hvth x hxK
  -- future edges: weight ≤ shares, regrouped by endpoints
  have hw : ((I.su F : ℕ) : ℤ) - F.card * I.TH ≤ ∑ e ∈ F, (I.share e.1 e.2 + I.share e.2 e.1) := by
    have : ((I.su F : ℕ) : ℤ) - F.card * I.TH = ∑ e ∈ F, I.wt e.1 e.2 := by
      simp only [su, wt]; rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, Nat.cast_sum]
    rw [this]
    exact Finset.sum_le_sum fun e he => share_add_ge hI (hF1 e he)
  have hregroup : ∑ e ∈ F, (I.share e.1 e.2 + I.share e.2 e.1) =
      ∑ k ∈ Q, ∑ e ∈ F, ((if e.1 = k then I.share k e.2 else 0) +
        (if e.2 = k then I.share k e.1 else 0)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [Finset.sum_add_distrib]
    have h1' : ∑ k ∈ Q, (if e.1 = k then I.share k e.2 else 0) = I.share e.1 e.2 := by
      rw [Finset.sum_ite_eq]; exact if_pos (hF e he).2.1
    have h2' : ∑ k ∈ Q, (if e.2 = k then I.share k e.1 else 0) = I.share e.2 e.1 := by
      rw [Finset.sum_ite_eq]; exact if_pos (hF e he).2.2.1
    rw [h1', h2']
  -- unsatisfied undecided primes
  have hg : ((I.gz UQ : ℕ) : ℤ) - UQ.card * I.TH =
      ∑ k ∈ Q, if k ∈ I.UE E then ((I.GV k : ℤ) - I.TH) else 0 := by
    rw [← Finset.sum_filter]
    have hset : Q.filter (· ∈ I.UE E) = UQ := by
      rw [hUQ]; ext k; simp only [Finset.mem_filter]; tauto
    rw [hset, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, gz, Nat.cast_sum]
  -- per prime
  have hloc : ∀ k ∈ Q, (∑ e ∈ F, ((if e.1 = k then I.share k e.2 else 0) +
        (if e.2 = k then I.share k e.1 else 0))) +
      (if k ∈ I.UE E then ((I.GV k : ℤ) - I.TH) else 0) ≤ L k := by
    intro k hk
    rw [sum_edges_at F hF1 k (I.share k)]
    have hY : nbrF F k ⊆ Cand k := nbrF_subset F k (Cand k) fun e he =>
      ⟨fun h => h ▸ (hF e he).2.2.2.1, fun h => h ▸ (hF e he).2.2.2.2⟩
    by_cases hkU : k ∈ I.UE E
    · rw [if_pos hkU]
      have := hL2 k hk _ hY
      linarith
    · rw [if_neg hkU, add_zero]
      apply hL1 k hk _ hY
      have hkm := hQ k hk
      have h0 : I.res E k = 0 := by
        by_contra hne
        exact hkU (Finset.mem_filter.2 ⟨Finset.mem_range.2 hkm, hne⟩)
      rw [← res_split hE hdisj hF1 k]; exact h0
  have hsum := Finset.sum_le_sum hloc
  rw [Finset.sum_add_distrib] at hsum
  -- assemble
  have e1 : ((I.su E + I.gz (I.UE E) + T.VB x : ℕ) : ℤ) =
      (I.su Dst : ℤ) + (I.gz Ust : ℤ) + ((I.su F : ℤ) - F.card * I.TH) +
        (((I.gz UQ : ℕ) : ℤ) - UQ.card * I.TH) + ((T.VB x : ℤ) - x * I.TH) +
        ((F.card + UQ.card + x : ℕ) : ℤ) * I.TH := by
    rw [hsu, hgz]; push_cast; ring
  have e2 : ((I.su Dst + I.gz Ust + (I.K - (Dst.card + Ust.card)) * I.TH : ℕ) : ℤ) =
      (I.su Dst : ℤ) + (I.gz Ust : ℤ) + ((F.card + UQ.card + x : ℕ) : ℤ) * I.TH := by
    rw [hslack]; push_cast; ring
  rw [e1, e2]
  rw [hregroup] at hw
  rw [← hg] at hsum
  linarith

end Inst
end Srch
end SemiprimeEgypt
