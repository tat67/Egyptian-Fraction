/-
The concrete tables `mkTables` have the soundness properties `TablesOK`
(`mkTables_ok`).  The two ingredients are the top-`k` bound `le_topSum` (for `MX`, `BT`) and the
correctness of the residue knapsack `dpRun` (`dpRun_ge`, for `LOC`, `TOPT`).
-/
import SemiprimeEgypt.SearchTables
import SemiprimeEgypt.SearchCorrect
import Mathlib.Algebra.Order.BigOperators.Group.Multiset

open Finset

namespace SemiprimeEgypt
namespace Srch

lemma getD_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) {i : ℕ} (d : α) (h : i < n) :
    (Array.ofFn f).getD i d = f ⟨i, h⟩ := by
  simp [Array.getD, h]

/-! ### The residue knapsack -/

lemma mod_back {q r c : ℕ} (hq : 0 < q) (hr : r < q) :
    ((r + c) % q + q - c % q) % q = r := by
  have hc : c % q < q := Nat.mod_lt _ hq
  rw [Nat.add_mod r c q, Nat.mod_eq_of_lt hr]
  rcases Nat.lt_or_ge (r + c % q) q with h | h
  · rw [Nat.mod_eq_of_lt h, show r + c % q + q - c % q = r + q by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hr]
  · have h2 : r + c % q - q < q := by omega
    rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt h2,
      show r + c % q - q + q - c % q = r by omega, Nat.mod_eq_of_lt hr]

lemma dpStep_size (q iv : ℕ) (s : ℤ) (b : Array ℤ) : (dpStep q iv s b).size = q := by
  simp [dpStep]

lemma dpStep_ge_left {q iv : ℕ} {s : ℤ} {b : Array ℤ} {r : ℕ} (hr : r < q) :
    b.getD r NEG ≤ (dpStep q iv s b).getD r NEG := by
  rw [dpStep, getD_ofFn _ _ hr]; exact le_max_left _ _

lemma dpStep_ge_right {q iv : ℕ} {s : ℤ} {b : Array ℤ} {r : ℕ} (hq : 0 < q) (hr : r < q) :
    b.getD r NEG + s ≤ (dpStep q iv s b).getD ((r + iv) % q) NEG := by
  rw [dpStep, getD_ofFn _ _ (Nat.mod_lt _ hq)]
  simp only
  rw [mod_back hq hr]
  exact le_max_right _ _

/-- Knapsack invariant: from any start array, every sub-list of items is dominated. -/
lemma foldl_dp_ge {q : ℕ} (hq : 0 < q) :
    ∀ (xs ys : List (ℕ × ℤ)), ys.Sublist xs → ∀ (b : Array ℤ) (r : ℕ), r < q →
      b.getD r NEG + (ys.map Prod.snd).sum ≤
        (xs.foldl (fun b c => dpStep q c.1 c.2 b) b).getD ((r + (ys.map Prod.fst).sum) % q) NEG
  | [], ys, hys, b, r, hr => by
    rw [List.sublist_nil.1 hys]
    simp [Nat.mod_eq_of_lt hr]
  | c :: xs, ys, hys, b, r, hr => by
    rw [List.foldl_cons]
    cases hys with
    | cons _ h =>
      have := foldl_dp_ge hq xs ys h (dpStep q c.1 c.2 b) r hr
      have h2 := dpStep_ge_left (iv := c.1) (s := c.2) (b := b) hr
      linarith
    | cons_cons _ h =>
      rename_i ys'
      have hr' : (r + c.1) % q < q := Nat.mod_lt _ hq
      have := foldl_dp_ge hq xs ys' h (dpStep q c.1 c.2 b) ((r + c.1) % q) hr'
      have h2 := dpStep_ge_right (iv := c.1) (s := c.2) (b := b) hq hr
      simp only [List.map_cons, List.sum_cons]
      have e : ((r + c.1) % q + (ys'.map Prod.fst).sum) % q = (r + (c.1 + (ys'.map Prod.fst).sum)) % q := by
        rw [Nat.mod_add_mod, Nat.add_assoc]
      rw [e] at this
      linarith

/-- **Knapsack correctness.** -/
theorem dpRun_ge {q : ℕ} (hq : 0 < q) (xs ys : List (ℕ × ℤ)) (hys : ys.Sublist xs) :
    (ys.map Prod.snd).sum ≤ (dpRun q xs).getD ((ys.map Prod.fst).sum % q) NEG := by
  have := foldl_dp_ge hq xs ys hys (Array.ofFn (n := q) fun r => if r.1 = 0 then 0 else NEG) 0 hq
  rw [getD_ofFn _ _ hq, if_pos rfl, zero_add, zero_add] at this
  exact this

/-! ### Local bounds -/

namespace Inst

variable {I : Inst}

lemma sum_filter_list {β : Type*} [AddCommMonoid β] (cs : List ℕ) (hcs : cs.Nodup) (Y : Finset ℕ)
    (hY : Y ⊆ cs.toFinset) (f : ℕ → β) :
    ((cs.filter (fun y => decide (y ∈ Y))).map f).sum = ∑ y ∈ Y, f y := by
  have hnd : (cs.filter (fun y => decide (y ∈ Y))).Nodup := hcs.filter _
  have hset : (cs.filter (fun y => decide (y ∈ Y))).toFinset = Y := by
    ext y; simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h; exact ⟨List.mem_toFinset.1 (hY h), h⟩
  conv_rhs => rw [← hset]
  rw [List.sum_toFinset _ hnd]

theorem locB_res (hI : InstOK I) {k : ℕ} {cs : List ℕ} (hcs : cs.Nodup) {r : ℕ} (hr : r < I.P k)
    {Y : Finset ℕ} (hY : Y ⊆ cs.toFinset) (h0 : (r + ∑ y ∈ Y, I.inv k y) % I.P k = 0) :
    ∑ y ∈ Y, I.share k y ≤ I.locB k cs r := by
  have hq := hI.P_pos k
  set ys := (cs.filter (fun y => decide (y ∈ Y))).map fun x => (I.inv k x, I.share k x)
  have hsub : ys.Sublist (cs.map fun x => (I.inv k x, I.share k x)) :=
    (List.filter_sublist).map _
  have hdp := dpRun_ge hq _ _ hsub
  have e1 : (ys.map Prod.snd).sum = ∑ y ∈ Y, I.share k y := by
    simp only [ys, List.map_map]
    exact sum_filter_list cs hcs Y hY (fun x => I.share k x)
  have e2 : (ys.map Prod.fst).sum = ∑ y ∈ Y, I.inv k y := by
    simp only [ys, List.map_map]
    exact sum_filter_list cs hcs Y hY (fun x => I.inv k x)
  rw [e1, e2] at hdp
  have e3 : (∑ y ∈ Y, I.inv k y) % I.P k = (I.P k - r % I.P k) % I.P k := by
    rw [Nat.mod_eq_of_lt hr]
    set s := ∑ y ∈ Y, I.inv k y
    have hs : s % I.P k < I.P k := Nat.mod_lt _ hq
    have h1 : (r + s % I.P k) % I.P k = 0 := by rw [Nat.add_mod_mod]; exact h0
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · simp only [zero_add, Nat.mod_mod] at h1; rw [h1, Nat.sub_zero, Nat.mod_self]
    · have h2 : r + s % I.P k = I.P k := by
        have := Nat.dvd_of_mod_eq_zero h1
        obtain ⟨c, hc⟩ := this
        have : c = 1 := by
          rcases c with _ | _ | c
          · omega
          · rfl
          · nlinarith
        rw [hc, this, mul_one]
      rw [show I.P k - r = s % I.P k by omega, Nat.mod_mod]
  rw [e3] at hdp
  unfold locB
  exact le_trans hdp (le_max_left _ _)

theorem locB_U {k : ℕ} {cs : List ℕ} (hcs : cs.Nodup) (r : ℕ) {Y : Finset ℕ}
    (hY : Y ⊆ cs.toFinset) :
    (I.GV k : ℤ) - I.TH + ∑ y ∈ Y, I.share k y ≤ I.locB k cs r := by
  unfold locB
  refine le_trans ?_ (le_max_right _ _)
  have : ∑ y ∈ Y, I.share k y ≤ (cs.map fun x => max (I.share k x) 0).sum := by
    rw [← List.sum_toFinset _ hcs]
    calc ∑ y ∈ Y, I.share k y ≤ ∑ y ∈ Y, max (I.share k y) 0 :=
          Finset.sum_le_sum fun y _ => le_max_left _ _
      _ ≤ ∑ y ∈ cs.toFinset, max (I.share k y) 0 :=
          Finset.sum_le_sum_of_subset_of_nonneg hY fun _ _ _ => le_max_right _ _
  linarith

end Inst

/-! ### Sums of subsets and `topSum` -/

/-- The sum of `g` over a subset `S` of a duplicate-free list `L` is at most the sum of the
`|S|` largest values of `g` on `L` (for `g ≥ 0`). -/
theorem sum_le_topSum {α : Type*} [DecidableEq α] (L : List α) (hL : L.Nodup) (S : Finset α)
    (hS : S ⊆ L.toFinset) (g : α → ℤ) (hg : ∀ a, 0 ≤ g a) :
    ∑ a ∈ S, g a ≤ topSum S.card (L.map g) := by
  have h1 : S.val ≤ (L : Multiset α) := by
    rw [Multiset.le_iff_subset S.nodup]
    intro a ha
    have := hS (Finset.mem_def.2 ha)
    exact Multiset.mem_coe.2 (List.mem_toFinset.1 this)
  have h2 : S.val.map g ≤ ((L.map g : List ℤ) : Multiset ℤ) := by
    rw [← Multiset.map_coe]; exact Multiset.map_le_map h1
  obtain ⟨A, hA⟩ := Quotient.exists_rep (S.val.map g)
  have hA' : (A : Multiset ℤ) = S.val.map g := hA
  rw [← hA'] at h2
  have hsub : A.Subperm (L.map g) := Multiset.coe_le.1 h2
  have hsum : A.sum = ∑ a ∈ S, g a := by
    rw [Finset.sum_eq_multiset_sum, ← hA', Multiset.sum_coe]
  have hlen : A.length = S.card := by
    rw [← Multiset.coe_card, hA', Multiset.card_map, Finset.card_val]
  rw [← hsum]
  exact le_topSum S.card A (L.map g) (fun x hx => by
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx; exact hg a) hsub hlen.le

lemma mem_pairList {j : ℕ} {e : ℕ × ℕ} : e ∈ pairList j ↔ e.1 < e.2 ∧ e.2 < j := by
  unfold pairList
  simp only [List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨b, hb, a, ha, rfl⟩; exact ⟨ha, hb⟩
  · rintro ⟨h1, h2⟩; exact ⟨e.2, h2, e.1, h1, rfl⟩

lemma pairList_nodup (j : ℕ) : (pairList j).Nodup := by
  unfold pairList
  rw [List.nodup_flatMap]
  refine ⟨fun b _ => (List.nodup_range).map fun a a' h => by simpa using h, ?_⟩
  refine List.Pairwise.imp_of_mem ?_ (List.nodup_range)
  intro b b' _ _ hne
  rw [Function.onFun, List.disjoint_left]
  intro e h1 h2
  obtain ⟨a, -, rfl⟩ := List.mem_map.1 h1
  obtain ⟨a', -, h⟩ := List.mem_map.1 h2
  simp only [Prod.mk.injEq] at h
  exact hne h.2.symm

lemma pairList_toFinset (j : ℕ) : (pairList j).toFinset = pairsBelow j := by
  ext e
  rw [List.mem_toFinset, mem_pairList]
  unfold pairsBelow
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨by omega, h2⟩, h1⟩
  · rintro ⟨⟨-, h2⟩, h1⟩; exact ⟨h1, h2⟩

namespace Inst

variable {I : Inst}

lemma su_le_topSum {j : ℕ} {F : Finset (ℕ × ℕ)} (hF : F ⊆ pairsBelow j) :
    ((I.su F : ℕ) : ℤ) ≤ topSum F.card (I.pairVals j) := by
  have := sum_le_topSum (pairList j) (pairList_nodup j) F (by rw [pairList_toFinset]; exact hF)
    (fun e => ((I.EU e.1 e.2 : ℕ) : ℤ)) (fun _ => Int.natCast_nonneg _)
  unfold su; push_cast; exact this

lemma row_le_topSum {j i : ℕ} {A : Finset ℕ} (hA : A ⊆ range i) :
    ((∑ a ∈ A, I.EU a j : ℕ) : ℤ) ≤ topSum A.card (I.rowVals j i) := by
  have := sum_le_topSum (List.range i) List.nodup_range A (by rw [List.toFinset_range]; exact hA)
    (fun a => ((I.EU a j : ℕ) : ℤ)) (fun _ => Int.natCast_nonneg _)
  push_cast; exact this

/-! ### The concrete tables -/

lemma mk_VB {x : ℕ} (hx : x < I.K + 2) : (I.mkTables).VB x = I.VBspec x := by
  simp only [mkTables]; rw [getD_ofFn _ _ hx]

lemma mk_MX {j R : ℕ} (hj : j ≤ I.m) (hR : R ≤ I.K) :
    (I.mkTables).MX j R = (range (R + 1)).sup
      (fun x => (topSum x (I.pairVals j)).toNat + (I.mkTables).VB (R - x)) := by
  simp only [mkTables]
  rw [getD_ofFn _ _ (by omega), getD_ofFn _ _ (by omega)]
  refine Finset.sup_congr rfl fun x hx => ?_
  have : x < I.K + 1 := by have := Finset.mem_range.1 hx; omega
  rw [getD_ofFn _ _ (by omega), getD_ofFn _ _ this]

lemma mk_BT {j i R : ℕ} (hj : j < I.m) (hi : i ≤ j) (hR : R ≤ I.K) :
    (I.mkTables).BT j i R = (range (min i R + 1)).sup
      (fun t => (topSum t (I.rowVals j i)).toNat + (I.mkTables).MX j (R - t)) := by
  simp only [mkTables]
  rw [getD_ofFn _ _ hj, getD_ofFn _ _ (by simp only [Fin.val_mk]; omega),
    getD_ofFn _ _ (by omega)]

lemma mk_LOC {J k r : ℕ} (hJ : J < I.m) (hk : k ≤ J) (hr : r < I.P k) :
    (I.mkTables).LOC J k r = I.LOCspec J k r := by
  simp only [mkTables]
  rw [getD_ofFn _ _ hJ, getD_ofFn _ _ (by simp only [Fin.val_mk]; omega),
    getD_ofFn _ _ (by simp only [Fin.val_mk]; exact hr)]

lemma mk_TOPT {j i t : ℕ} (hj : j < I.m) (hi : i ≤ j) (ht : t < I.P j) :
    (I.mkTables).TOPT j i t = I.TOPTspec j i t := by
  simp only [mkTables]
  rw [getD_ofFn _ _ hj, getD_ofFn _ _ (by simp only [Fin.val_mk]; omega),
    getD_ofFn _ _ (by simp only [Fin.val_mk]; exact ht)]

lemma filter_ne_nodup (J k : ℕ) : ((List.range (J + 1)).filter (· ≠ k)).Nodup :=
  List.nodup_range.filter _

lemma filter_ne_toFinset (J k : ℕ) :
    ((List.range (J + 1)).filter (· ≠ k)).toFinset = (range (J + 1)).erase k := by
  ext y; simp [and_comm]

/-- **The concrete tables are sound.** -/
theorem mkTables_ok (hI : InstOK I) : TablesOK I I.mkTables where
  vth := by
    intro x hx
    have e : (I.mkTables).VTH = (range (I.K + 1)).sup' ⟨0, by simp⟩
        (fun x => ((I.mkTables.VB x : ℕ) : ℤ) - x * I.TH) := rfl
    rw [e]
    exact Finset.le_sup' (f := fun x => ((I.mkTables.VB x : ℕ) : ℤ) - x * I.TH)
      (Finset.mem_range.2 (by omega))
  mx := by
    intro j hj R hR F hF hFR
    rw [mk_MX hj hR]
    have h1 := su_le_topSum (I := I) hF
    have h2 : I.su F ≤ (topSum F.card (I.pairVals j)).toNat := by omega
    calc I.su F + (I.mkTables).VB (R - F.card)
        ≤ (topSum F.card (I.pairVals j)).toNat + (I.mkTables).VB (R - F.card) := by omega
      _ ≤ _ := Finset.le_sup (f := fun x => (topSum x (I.pairVals j)).toNat +
            (I.mkTables).VB (R - x)) (Finset.mem_range.2 (by omega))
  bt := by
    intro j hj i hi R hR A hA hAR
    rw [mk_BT hj hi hR]
    have hAi : A.card ≤ i := by
      have := Finset.card_le_card hA; rwa [Finset.card_range] at this
    have h1 := row_le_topSum (I := I) (j := j) hA
    have h2 : (∑ a ∈ A, I.EU a j) ≤ (topSum A.card (I.rowVals j i)).toNat := by omega
    calc (∑ a ∈ A, I.EU a j) + (I.mkTables).MX j (R - A.card)
        ≤ (topSum A.card (I.rowVals j i)).toNat + (I.mkTables).MX j (R - A.card) := by omega
      _ ≤ _ := Finset.le_sup (f := fun t => (topSum t (I.rowVals j i)).toNat +
            (I.mkTables).MX j (R - t)) (Finset.mem_range.2 (by omega))
  topt_res := by
    intro j hj i hi t ht Y hY h0
    rw [mk_TOPT hj hi ht]
    exact locB_res hI List.nodup_range ht (by rw [List.toFinset_range]; exact hY) h0
  topt_U := by
    intro j hj i hi t ht Y hY
    rw [mk_TOPT hj hi ht]
    exact locB_U List.nodup_range t (by rw [List.toFinset_range]; exact hY)
  loc_res := by
    intro J hJ k hk r hr Y hY h0
    rw [mk_LOC hJ hk hr]
    exact locB_res hI (filter_ne_nodup J k) hr (by rw [filter_ne_toFinset]; exact hY) h0
  loc_U := by
    intro J hJ k hk r hr Y hY
    rw [mk_LOC hJ hk hr]
    exact locB_U (filter_ne_nodup J k) r (by rw [filter_ne_toFinset]; exact hY)

end Inst

end Srch
end SemiprimeEgypt
