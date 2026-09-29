/-
**The search is exhaustive.**  For any tables with the soundness properties `TablesOK`, every
core `E` satisfying the integer acceptance condition `IntAdm` (Lemma 3 for every upper segment
of `U`, rounded, together with the budget and `Σ_C ≤ 1`) is in the output of `search`
(`mem_search`).

The proof follows the path of `E` through the depth-first search: at the node `(j, i)` the
decided edges are those with larger index `> j` together with the edges `{a, j}`, `a ≥ i`; every
pruning test holds along this path (P1 budget, P2 core sum, P3 via `TablesOK.mx/bt`, P4 via
`loss_bound`), and at every branching the branch of `E` is taken.
-/
import SemiprimeEgypt.LossBound

open Finset

namespace SemiprimeEgypt
namespace Srch

variable {I : Inst} {T : Tables}

/-! ### Edge-set bookkeeping -/

lemma mem_star {j : ℕ} {A : Finset ℕ} {e : ℕ × ℕ} : e ∈ star j A ↔ e.1 ∈ A ∧ e.2 = j := by
  unfold star
  constructor
  · rintro h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 h
    exact ⟨ha, rfl⟩
  · rintro ⟨h1, h2⟩
    exact Finset.mem_image.2 ⟨e.1, h1, by rw [← h2]⟩

lemma star_card (j : ℕ) (A : Finset ℕ) : (star j A).card = A.card :=
  Finset.card_image_of_injective _ fun a b h => by simpa using h

namespace Inst

lemma su_union {A B : Finset (ℕ × ℕ)} (h : Disjoint A B) : I.su (A ∪ B) = I.su A + I.su B := by
  unfold su; rw [Finset.sum_union h]

lemma sl_union {A B : Finset (ℕ × ℕ)} (h : Disjoint A B) : I.sl (A ∪ B) = I.sl A + I.sl B := by
  unfold sl; rw [Finset.sum_union h]

lemma su_star (j : ℕ) (A : Finset ℕ) : I.su (star j A) = ∑ a ∈ A, I.EU a j := by
  unfold su star
  rw [Finset.sum_image fun a _ b _ h => by simpa using h]

lemma sl_mono {A B : Finset (ℕ × ℕ)} (h : A ⊆ B) : I.sl A ≤ I.sl B :=
  Finset.sum_le_sum_of_subset h

lemma gz_insert {U : Finset ℕ} {k : ℕ} (hk : k ∉ U) : I.gz (insert k U) = I.GV k + I.gz U := by
  unfold gz; rw [Finset.sum_insert hk]

/-- An edge not touching `k` does not contribute to the residue at `k`. -/
lemma ctr_eq_zero {k : ℕ} {e : ℕ × ℕ} (h1 : e.1 ≠ k) (h2 : e.2 ≠ k) : I.ctr k e = 0 := by
  unfold ctr; rw [if_neg h1, if_neg h2]

lemma res_eq_of_touch {A B : Finset (ℕ × ℕ)} (hAB : A ⊆ B) (k : ℕ)
    (h : ∀ e ∈ B, e ∉ A → e.1 ≠ k ∧ e.2 ≠ k) : I.res B k = I.res A k := by
  unfold res
  congr 1
  rw [← Finset.sum_sdiff hAB]
  have : ∑ e ∈ B \ A, I.ctr k e = 0 := by
    refine Finset.sum_eq_zero fun e he => ?_
    obtain ⟨heB, heA⟩ := Finset.mem_sdiff.1 he
    exact ctr_eq_zero (h e heB heA).1 (h e heB heA).2
  rw [this, zero_add]

end Inst

/-! ### The path of a core through the search -/

/-- Edges of `E` with larger index `> j`. -/
def Dof (E : Finset (ℕ × ℕ)) (j : ℕ) : Finset (ℕ × ℕ) := E.filter (fun e => j < e.2)
/-- Unsatisfied primes of `E` with index `> j`. -/
def Uof (I : Inst) (E : Finset (ℕ × ℕ)) (j : ℕ) : Finset ℕ := (I.UE E).filter (fun k => j < k)
/-- Neighbours `a` of `j` in `E` with `i ≤ a < j`. -/
def Cof (E : Finset (ℕ × ℕ)) (j i : ℕ) : Finset ℕ := (range j).filter (fun a => i ≤ a ∧ (a, j) ∈ E)
/-- Neighbours `a` of `j` in `E` with `a < i`. -/
def Acut (E : Finset (ℕ × ℕ)) (j i : ℕ) : Finset ℕ := (range i).filter (fun a => (a, j) ∈ E)
/-- Edges of `E` with both indices `< j`. -/
def Flow (E : Finset (ℕ × ℕ)) (j : ℕ) : Finset (ℕ × ℕ) := E.filter (fun e => e.2 < j)

section Path

variable {E : Finset (ℕ × ℕ)}

lemma lt_of_mem_pairs {n : ℕ} {e : ℕ × ℕ} (h : e ∈ pairsBelow n) : e.1 < e.2 ∧ e.2 < n := by
  unfold pairsBelow at h
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at h
  exact ⟨h.2, h.1.2⟩

lemma Dof_disj_star (j : ℕ) (C : Finset ℕ) : Disjoint (Dof E j) (star j C) := by
  rw [Finset.disjoint_left]
  intro e he he'
  have h1 := (Finset.mem_filter.1 he).2
  have h2 := (mem_star.1 he').2
  omega

/-- The decomposition of `E` at the node `(j, i)`. -/
lemma node_split (hE : ∀ e ∈ E, e.1 < e.2) {j i : ℕ} (hij : i ≤ j) :
    E = (Dof E j ∪ star j (Cof E j i)) ∪ (star j (Acut E j i) ∪ Flow E j) := by
  ext e
  simp only [Finset.mem_union, Dof, Cof, Acut, Flow, Finset.mem_filter, mem_star,
    Finset.mem_range]
  constructor
  · intro he
    have := hE e he
    rcases lt_trichotomy j e.2 with h | h | h
    · exact Or.inl (Or.inl ⟨he, h⟩)
    · by_cases hi : i ≤ e.1
      · exact Or.inl (Or.inr ⟨⟨by omega, hi, by rw [h]; exact he⟩, h.symm⟩)
      · exact Or.inr (Or.inl ⟨⟨by omega, by rw [h]; exact he⟩, h.symm⟩)
    · exact Or.inr (Or.inr ⟨he, h⟩)
  · rintro ((⟨he, -⟩ | ⟨⟨-, -, he⟩, h⟩) | (⟨⟨-, he⟩, h⟩ | ⟨he, -⟩))
    · exact he
    · rw [← h] at he; exact he
    · rw [← h] at he; exact he
    · exact he

lemma node_disj (j i : ℕ) :
    Disjoint (Dof E j ∪ star j (Cof E j i)) (star j (Acut E j i) ∪ Flow E j) := by
  rw [Finset.disjoint_left]
  intro e he he'
  simp only [Finset.mem_union, Dof, Cof, Acut, Flow, Finset.mem_filter, mem_star,
    Finset.mem_range] at he he'
  omega

lemma star_disj_Flow (j i : ℕ) : Disjoint (star j (Acut E j i)) (Flow E j) := by
  rw [Finset.disjoint_left]
  intro e he he'
  simp only [Acut, Flow, Finset.mem_filter, mem_star, Finset.mem_range] at he he'
  omega

lemma Acut_subset (j i : ℕ) : Acut E j i ⊆ range i := Finset.filter_subset _ _

lemma Flow_subset {n : ℕ} (hE : E ⊆ pairsBelow n) (j : ℕ) : Flow E j ⊆ pairsBelow j := by
  intro e he
  have h := Finset.mem_filter.1 he
  have := lt_of_mem_pairs (hE h.1)
  unfold pairsBelow
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  exact ⟨⟨by omega, h.2⟩, this.1⟩

lemma card_node (j i : ℕ) :
    (Dof E j ∪ star j (Cof E j i)).card = (Dof E j).card + (Cof E j i).card := by
  rw [Finset.card_union_of_disjoint (Dof_disj_star j _), star_card]

lemma Uof_eq_filter (j : ℕ) : Uof I E j = (I.UE E).filter (fun k => j + 1 ≤ k) := rfl

lemma Uof_eq_not_mem (j : ℕ) : Uof I E j = (I.UE E).filter (· ∉ range (j + 1)) := by
  unfold Uof; ext k; simp only [Finset.mem_filter, Finset.mem_range]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩

lemma Uof_card_le (j : ℕ) : (Uof I E j).card ≤ (I.UE E).card := Finset.card_filter_le _ _

/-- At the leaf of level `j` the decided edges are those of `Dof E (j-1)`. -/
lemma leaf_D (hE : ∀ e ∈ E, e.1 < e.2) {j : ℕ} (hj : 1 ≤ j) (i : ℕ) :
    (Dof E j ∪ star j (Cof E j i)) ∪ star j (Acut E j i) = Dof E (j - 1) := by
  ext e
  simp only [Finset.mem_union, Dof, Cof, Acut, Finset.mem_filter, mem_star, Finset.mem_range]
  constructor
  · rintro ((⟨he, h⟩ | ⟨⟨h1, -, he⟩, h⟩) | ⟨⟨h1, he⟩, h⟩)
    · exact ⟨he, by omega⟩
    · rw [← h] at he; exact ⟨he, by omega⟩
    · rw [← h] at he; exact ⟨he, by omega⟩
  · rintro ⟨he, h⟩
    have := hE e he
    rcases Nat.lt_or_ge j e.2 with h' | h'
    · exact Or.inl (Or.inl ⟨he, h'⟩)
    · have hej : e.2 = j := by omega
      by_cases hi : i ≤ e.1
      · exact Or.inl (Or.inr ⟨⟨by omega, hi, by rw [← hej]; exact he⟩, hej⟩)
      · exact Or.inr ⟨⟨by omega, by rw [← hej]; exact he⟩, hej⟩

end Path

/-! ### The tests hold along the path -/

section Tests

variable {E : Finset (ℕ × ℕ)}

/-- Consequences of `IntAdm` used below. -/
structure AdmFacts (I : Inst) (T : Tables) (E : Finset (ℕ × ℕ)) : Prop where
  pairs : E ⊆ pairsBelow I.m
  lt : ∀ e ∈ E, e.1 < e.2
  budget : E.card + (I.UE E).card ≤ I.K
  slE : I.sl E ≤ ONE
  seg : ∀ s ≤ I.m, ONE ≤ I.su E + I.gz ((I.UE E).filter (s ≤ ·)) +
      T.VB (I.K - E.card - ((I.UE E).filter (s ≤ ·)).card)

lemma AdmFacts.of (h : IntAdm I T E) : AdmFacts I T E :=
  ⟨h.1, fun e he => (lt_of_mem_pairs (h.1 he)).1, h.2.1, h.2.2.1, h.2.2.2⟩

lemma UE_filter_zero : (I.UE E).filter (0 ≤ ·) = I.UE E :=
  Finset.filter_true_of_mem fun _ _ => Nat.zero_le _

lemma mem_UE {k : ℕ} (hk : k < I.m) : k ∈ I.UE E ↔ I.res E k ≠ 0 := by
  unfold Inst.UE; rw [Finset.mem_filter, Finset.mem_range]; exact ⟨fun h => h.2, fun h => ⟨hk, h⟩⟩

lemma UE_lt {k : ℕ} (hk : k ∈ I.UE E) : k < I.m := by
  unfold Inst.UE at hk; exact Finset.mem_range.1 (Finset.mem_filter.1 hk).1

/-- The value of the final Step-1 test is at least `ONE`. -/
lemma val_ge (hA : AdmFacts I T E) :
    ONE ≤ I.su E + I.gz (I.UE E) + T.VB (I.K - E.card - (I.UE E).card) := by
  have := hA.seg 0 (Nat.zero_le _)
  rwa [UE_filter_zero] at this

/-- The residue bound `res < P`. -/
lemma res_lt (hI : InstOK I) (D : Finset (ℕ × ℕ)) (k : ℕ) : I.res D k < I.P k :=
  Nat.mod_lt _ (hI.P_pos k)

/-- The tests (P1)–(P4) hold at every node on the path of `E`. -/
theorem nodeOK_path (hI : InstOK I) (hT : TablesOK I T) (hA : AdmFacts I T E)
    {j i : ℕ} (hjm : j < I.m) (hij : i ≤ j) :
    I.nodeOK T j i (Dof E j) (Uof I E j) (Cof E j i) = true := by
  classical
  set D' := Dof E j ∪ star j (Cof E j i) with hD'
  set A := Acut E j i with hAdef
  set Fl := Flow E j with hFl
  set U := Uof I E j with hU
  have hsplit := node_split hA.lt hij (E := E)
  have hdisj := node_disj (E := E) j i
  have hdisj2 := star_disj_Flow (E := E) j i
  have hcE : E.card = D'.card + A.card + Fl.card := by
    conv_lhs => rw [hsplit]
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_union_of_disjoint hdisj2, star_card]
    ring
  have hsuE : I.su E = I.su D' + ((∑ a ∈ A, I.EU a j) + I.su Fl) := by
    conv_lhs => rw [hsplit]
    rw [Inst.su_union hdisj, Inst.su_union hdisj2, Inst.su_star]
  have hUle : U.card ≤ (I.UE E).card := Uof_card_le j
  have hbud := hA.budget
  have hD'E : D' ⊆ E := by
    intro e he; rw [hsplit]; exact Finset.mem_union_left _ he
  unfold Inst.nodeOK
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  simp only [← hD', ← hU]
  refine ⟨⟨⟨by omega, le_trans (Inst.sl_mono hD'E) hA.slE⟩, ?_⟩, ?_⟩
  · -- (P3)
    have hseg := hA.seg (j + 1) (by omega)
    rw [← Uof_eq_filter, ← hU, hsuE] at hseg
    have hmx := hT.mx j hjm.le (I.K - (D'.card + U.card) - A.card) (by omega) Fl
      (Flow_subset hA.pairs j) (by omega)
    have hbt := hT.bt j hjm i hij (I.K - (D'.card + U.card)) (by omega) A (Acut_subset j i)
      (by omega)
    have hidx : I.K - E.card - U.card = I.K - (D'.card + U.card) - A.card - Fl.card := by omega
    rw [hidx] at hseg
    omega
  · -- (P4) the loss bound
    have hval := val_ge hA
    set Cand : ℕ → Finset ℕ := fun k =>
      if k = j then range i else if k < i then (range (j + 1)).erase k else (range j).erase k
      with hCand
    set L : ℕ → ℤ := fun k =>
      if k = j then T.TOPT j i (I.res D' j)
      else if k < i then T.LOC j k (I.res D' k) else T.LOC (j - 1) k (I.res D' k) with hLdef
    have hF : ∀ e ∈ star j A ∪ Fl, e.1 < e.2 ∧ e.1 ∈ range (j + 1) ∧ e.2 ∈ range (j + 1) ∧
        e.2 ∈ Cand e.1 ∧ e.1 ∈ Cand e.2 := by
      intro e he
      simp only [Finset.mem_union, mem_star, hAdef, Acut, hFl, Flow, Finset.mem_filter,
        Finset.mem_range] at he
      simp only [hCand, Finset.mem_range]
      rcases he with ⟨⟨h1, h2⟩, h3⟩ | ⟨h1, h2⟩
      · have := hA.lt e (by rw [show e = (e.1, j) from Prod.ext rfl h3]; exact h2)
        refine ⟨by omega, by omega, by omega, ?_, ?_⟩
        · rw [if_neg (by omega), if_pos h1, Finset.mem_erase, Finset.mem_range]; omega
        · rw [if_pos h3, Finset.mem_range]; exact h1
      · have := hA.lt e h1
        refine ⟨this, by omega, by omega, ?_, ?_⟩
        · rw [if_neg (by omega)]
          split_ifs <;> rw [Finset.mem_erase, Finset.mem_range] <;> omega
        · rw [if_neg (by omega)]
          split_ifs <;> rw [Finset.mem_erase, Finset.mem_range] <;> omega
    have hQ : ∀ k ∈ range (j + 1), k < I.m := fun k hk => by
      have := Finset.mem_range.1 hk; omega
    have hL1 : ∀ k ∈ range (j + 1), ∀ Y ⊆ Cand k,
        (I.res D' k + ∑ y ∈ Y, I.inv k y) % I.P k = 0 → ∑ y ∈ Y, I.share k y ≤ L k := by
      intro k hk Y hY h0
      have hkj := Finset.mem_range.1 hk
      simp only [hCand, hLdef] at hY ⊢
      by_cases h1 : k = j
      · subst h1; rw [if_pos rfl] at hY ⊢
        exact hT.topt_res k hjm i hij _ (res_lt hI D' k) Y hY h0
      · rw [if_neg h1] at hY ⊢
        by_cases h2 : k < i
        · rw [if_pos h2] at hY ⊢
          exact hT.loc_res j hjm k (by omega) _ (res_lt hI D' k) Y hY h0
        · rw [if_neg h2] at hY ⊢
          have hj' : j - 1 + 1 = j := by omega
          exact hT.loc_res (j - 1) (by omega) k (by omega) _ (res_lt hI D' k) Y
            (by rw [hj']; exact hY) h0
    have hL2 : ∀ k ∈ range (j + 1), ∀ Y ⊆ Cand k,
        (I.GV k : ℤ) - I.TH + ∑ y ∈ Y, I.share k y ≤ L k := by
      intro k hk Y hY
      have hkj := Finset.mem_range.1 hk
      simp only [hCand, hLdef] at hY ⊢
      by_cases h1 : k = j
      · subst h1; rw [if_pos rfl] at hY ⊢
        exact hT.topt_U k hjm i hij _ (res_lt hI D' k) Y hY
      · rw [if_neg h1] at hY ⊢
        by_cases h2 : k < i
        · rw [if_pos h2] at hY ⊢
          exact hT.loc_U j hjm k (by omega) _ (res_lt hI D' k) Y hY
        · rw [if_neg h2] at hY ⊢
          have hj' : j - 1 + 1 = j := by omega
          exact hT.loc_U (j - 1) (by omega) k (by omega) _ (res_lt hI D' k) Y
            (by rw [hj']; exact hY)
    have hlb := Inst.loss_bound hI hT.vth (E := E) (Dst := D') (F := star j A ∪ Fl)
      (Q := range (j + 1)) (Ust := U) (Cand := Cand) (L := L) hsplit hdisj hF
      (by rw [hU]; exact Uof_eq_not_mem j) hQ hL1 hL2 hbud
    have hsumL : ∑ k ∈ range (j + 1), L k = T.TOPT j i (I.res D' j) + I.SL T j i D' := by
      rw [Finset.sum_range_succ, add_comm]
      congr 1
      · simp only [hLdef, if_pos rfl]
      · unfold Inst.SL
        refine Finset.sum_congr rfl fun k hk => ?_
        have : k ≠ j := by have := Finset.mem_range.1 hk; omega
        simp only [hLdef, if_neg this]
    rw [hsumL] at hlb
    have hval' : (ONE : ℤ) ≤ ((I.su E + I.gz (I.UE E) +
        T.VB (I.K - E.card - (I.UE E).card) : ℕ) : ℤ) := by exact_mod_cast hval
    linarith

lemma Flow_disj_leaf (j : ℕ) : Disjoint (Dof E (j - 1)) (Flow E j) := by
  rw [Finset.disjoint_left]
  intro e he he'
  have h1 := (Finset.mem_filter.1 he).2
  have h2 := (Finset.mem_filter.1 he').2
  omega

lemma leaf_split (hE : ∀ e ∈ E, e.1 < e.2) {j : ℕ} (hj1 : 1 ≤ j) :
    E = Dof E (j - 1) ∪ Flow E j := by
  ext e
  simp only [Finset.mem_union, Dof, Flow, Finset.mem_filter]
  constructor
  · intro he; rcases Nat.lt_or_ge (j - 1) e.2 with h | h
    · exact Or.inl ⟨he, h⟩
    · exact Or.inr ⟨he, by omega⟩
  · rintro (⟨he, -⟩ | ⟨he, -⟩) <;> exact he

lemma Uof_pred {j : ℕ} (hjm : j < I.m) (hj1 : 1 ≤ j) :
    Uof I E (j - 1) = if j ∈ I.UE E then insert j (Uof I E j) else Uof I E j := by
  unfold Uof
  split_ifs with h
  · ext k; simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hk, hk'⟩
      rcases Nat.lt_or_ge j k with h' | h'
      · exact Or.inr ⟨hk, h'⟩
      · exact Or.inl (by omega)
    · rintro (rfl | ⟨hk, hk'⟩)
      · exact ⟨h, by omega⟩
      · exact ⟨hk, by omega⟩
  · ext k; simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hk, hk'⟩
      refine ⟨hk, ?_⟩
      rcases Nat.lt_or_ge j k with h' | h'
      · exact h'
      · have : k = j := by omega
        subst this; exact absurd hk h
    · rintro ⟨hk, hk'⟩; exact ⟨hk, by omega⟩

/-- The leaf step on the path of `E` passes and moves to the next level. -/
theorem leafStep_path (hI : InstOK I) (hT : TablesOK I T) (hA : AdmFacts I T E)
    {j : ℕ} (hj1 : 1 ≤ j) (hjm : j < I.m) :
    I.leafStep T j (Dof E j) (Uof I E j) (Cof E j (I.lowN j)) (Acut E j (I.lowN j)) =
      some (Dof E (j - 1), Uof I E (j - 1)) := by
  classical
  have hij : I.lowN j ≤ j := min_le_left _ _
  set i := I.lowN j with hi
  set D' := Dof E j ∪ star j (Cof E j i) with hD'
  set A := Acut E j i with hAdef
  set Fl := Flow E j with hFl
  set U := Uof I E j with hU
  have hD'' : D' ∪ star j A = Dof E (j - 1) := leaf_D hA.lt hj1 i
  have hsplit := leaf_split hA.lt hj1 (E := E)
  have hdisjL := Flow_disj_leaf (E := E) j
  have hdisjA : Disjoint D' (star j A) := by
    have := node_disj (E := E) j i
    exact Finset.disjoint_of_subset_right Finset.subset_union_left this
  have hcD'' : (Dof E (j - 1)).card = D'.card + A.card := by
    rw [← hD'', Finset.card_union_of_disjoint hdisjA, star_card]
  have hcE : E.card = (Dof E (j - 1)).card + Fl.card := by
    conv_lhs => rw [hsplit]
    rw [Finset.card_union_of_disjoint hdisjL]
  have hsuE : I.su E = I.su (Dof E (j - 1)) + I.su Fl := by
    conv_lhs => rw [hsplit]
    rw [Inst.su_union hdisjL]
  have hsuD'' : I.su (Dof E (j - 1)) = I.su D' + ∑ a ∈ A, I.EU a j := by
    rw [← hD'', Inst.su_union hdisjA, Inst.su_star]
  have hresj : I.res (Dof E (j - 1)) j = I.res E j := by
    refine (Inst.res_eq_of_touch (A := Dof E (j - 1)) (B := E) (Finset.filter_subset _ _) j ?_).symm
    intro e he heD
    have heF : e ∈ Fl := by
      rw [hsplit, Finset.mem_union] at he
      exact he.resolve_left heD
    have h1 := (Finset.mem_filter.1 heF).2
    have h2 := hA.lt e (Finset.mem_filter.1 heF).1
    exact ⟨by omega, by omega⟩
  have hUle : U.card ≤ (I.UE E).card := Uof_card_le j
  have hbud := hA.budget
  have hsegj := hA.seg j hjm.le
  have hUj : (I.UE E).filter (j ≤ ·) = Uof I E (j - 1) := by
    unfold Uof; ext k; simp only [Finset.mem_filter]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
  rw [hUj] at hsegj
  have hUp := Uof_pred (E := E) hjm hj1
  have hUc' : (Uof I E (j - 1)).card ≤ (I.UE E).card := Uof_card_le (j - 1)
  have hD'E : Dof E (j - 1) ⊆ E := Finset.filter_subset _ _
  -- the loss bound at the leaf
  have hloss : (ONE : ℤ) ≤ ((I.su (Dof E (j - 1)) + I.gz (Uof I E (j - 1)) +
      (I.K - ((Dof E (j - 1)).card + (Uof I E (j - 1)).card)) * I.TH : ℕ) : ℤ) + T.VTH +
      ∑ k ∈ range j, T.LOC (j - 1) k (I.res (Dof E (j - 1)) k) := by
    have hF : ∀ e ∈ Fl, e.1 < e.2 ∧ e.1 ∈ range j ∧ e.2 ∈ range j ∧
        e.2 ∈ (range j).erase e.1 ∧ e.1 ∈ (range j).erase e.2 := by
      intro e he
      have h1 := (Finset.mem_filter.1 he).2
      have h2 := hA.lt e (Finset.mem_filter.1 he).1
      simp only [Finset.mem_erase, Finset.mem_range]
      omega
    have hj' : j - 1 + 1 = j := by omega
    have hlb := Inst.loss_bound hI hT.vth (E := E) (Dst := Dof E (j - 1)) (F := Fl)
      (Q := range j) (Ust := Uof I E (j - 1)) (Cand := fun k => (range j).erase k)
      (L := fun k => T.LOC (j - 1) k (I.res (Dof E (j - 1)) k)) hsplit hdisjL hF
      (by unfold Uof; ext k; simp only [Finset.mem_filter, Finset.mem_range]
          constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩)
      (fun k hk => by have := Finset.mem_range.1 hk; omega)
      (fun k hk Y hY h0 => hT.loc_res (j - 1) (by omega) k
        (by have := Finset.mem_range.1 hk; omega) _ (res_lt hI _ k) Y (by rw [hj']; exact hY) h0)
      (fun k hk Y hY => hT.loc_U (j - 1) (by omega) k
        (by have := Finset.mem_range.1 hk; omega) _ (res_lt hI _ k) Y (by rw [hj']; exact hY))
      hbud
    have hval := val_ge hA
    have hval' : (ONE : ℤ) ≤ ((I.su E + I.gz (I.UE E) +
        T.VB (I.K - E.card - (I.UE E).card) : ℕ) : ℤ) := by exact_mod_cast hval
    linarith
  -- the value test at the leaf (P3)
  have hmxTest : ONE ≤ I.su (Dof E (j - 1)) + I.gz (Uof I E (j - 1)) +
      T.MX j (I.K - ((Dof E (j - 1)).card + (Uof I E (j - 1)).card)) := by
    have hUc : (Uof I E (j - 1)).card ≤ (I.UE E).card := Uof_card_le _
    have hmx := hT.mx j hjm.le (I.K - ((Dof E (j - 1)).card + (Uof I E (j - 1)).card)) (by omega)
      Fl (Flow_subset hA.pairs j) (by omega)
    have hidx : I.K - E.card - (Uof I E (j - 1)).card =
        I.K - ((Dof E (j - 1)).card + (Uof I E (j - 1)).card) - Fl.card := by omega
    rw [hidx, hsuE] at hsegj
    omega
  have hslD : I.sl (Dof E (j - 1)) ≤ ONE := le_trans (Inst.sl_mono hD'E) hA.slE
  unfold Inst.leafStep
  simp only [← hD', ← hU]
  rw [hD'', hresj]
  by_cases hjU : j ∈ I.UE E
  · have hres0 : I.res E j ≠ 0 := (mem_UE hjm).1 hjU
    rw [if_pos hjU] at hUp
    have hjnU : j ∉ U := by
      rw [hU]; unfold Uof; rw [Finset.mem_filter]; omega
    have hUc1 : U.card + 1 ≤ (I.UE E).card := by
      have : insert j U ⊆ I.UE E := by
        intro k hk; rw [Finset.mem_insert] at hk
        rcases hk with rfl | hk
        · exact hjU
        · exact (Finset.mem_filter.1 hk).1
      have := Finset.card_le_card this
      rw [Finset.card_insert_of_notMem hjnU] at this
      exact this
    -- the unsatisfied-option test (BT with one budget unit less)
    have hbtTest : ONE ≤ I.su D' + I.gz U + T.BT j i (I.K - (D'.card + U.card) - 1) + I.GV j := by
      have hsegj' := hA.seg j hjm.le
      rw [hUj, hUp, Inst.gz_insert hjnU, hsuE, hsuD'', Finset.card_insert_of_notMem hjnU]
        at hsegj'
      have hmx := hT.mx j hjm.le (I.K - (D'.card + U.card) - 1 - A.card) (by omega) Fl
        (Flow_subset hA.pairs j) (by omega)
      have hbt := hT.bt j hjm i hij (I.K - (D'.card + U.card) - 1) (by omega) A
        (Acut_subset j i) (by omega)
      have hidx : I.K - E.card - (U.card + 1) =
          I.K - (D'.card + U.card) - 1 - A.card - Fl.card := by omega
      rw [hidx] at hsegj'
      omega
    have hcond : (decide (I.res E j ≠ 0)) = true := decide_eq_true hres0
    simp only [hcond, Bool.not_true, Bool.false_or, Bool.and_eq_true,
      decide_eq_true_eq, ↓reduceIte]
    have hUU : insert j U = Uof I E (j - 1) := by rw [hUp]
    have hcU : (Uof I E (j - 1)).card = U.card + 1 := by
      rw [← hUU, Finset.card_insert_of_notMem hjnU]
    rw [hUU]
    rw [if_pos ⟨⟨⟨⟨⟨by omega, hbtTest⟩, by omega⟩, hslD⟩, hmxTest⟩, hloss⟩]
  · have hres0 : I.res E j = 0 := by
      by_contra h; exact hjU ((mem_UE hjm).2 h)
    rw [if_neg hjU] at hUp
    have hcond : (decide (I.res E j ≠ 0)) = false := by simp [hres0]
    simp only [hcond, Bool.not_false, Bool.true_or, Bool.true_and, Bool.and_eq_true,
      decide_eq_true_eq, Bool.false_eq_true, ↓reduceIte]
    have hUU : U = Uof I E (j - 1) := by rw [hUp]
    rw [hUU]
    rw [if_pos ⟨⟨⟨by omega, hslD⟩, hmxTest⟩, hloss⟩]

/-- The last prime (index 0). -/
theorem last_path (hA : AdmFacts I T E) (hm : 1 ≤ I.m) : E ∈ I.last T (Dof E 0) (Uof I E 0) := by
  classical
  have hD0 : Dof E 0 = E := Finset.filter_true_of_mem fun e he => by
    have := hA.lt e he; omega
  have hval := val_ge hA
  have hbud := hA.budget
  rw [hD0]
  unfold Inst.last Inst.fin
  by_cases h0 : I.res E 0 = 0
  · have hU0 : Uof I E 0 = I.UE E := by
      unfold Uof
      refine Finset.filter_true_of_mem fun k hk => ?_
      rcases Nat.eq_zero_or_pos k with rfl | hk'
      · exact absurd h0 ((mem_UE hm).1 hk)
      · exact hk'
    rw [if_pos h0, hU0, if_pos hval]
    exact List.mem_singleton_self _
  · have h0U : 0 ∈ I.UE E := (mem_UE hm).2 h0
    have hU0 : insert 0 (Uof I E 0) = I.UE E := by
      unfold Uof; ext k; simp only [Finset.mem_insert, Finset.mem_filter]
      constructor
      · rintro (rfl | ⟨hk, -⟩)
        · exact h0U
        · exact hk
      · intro hk
        rcases Nat.eq_zero_or_pos k with rfl | hk'
        · exact Or.inl rfl
        · exact Or.inr ⟨hk, hk'⟩
    have h0n : 0 ∉ Uof I E 0 := by unfold Uof; rw [Finset.mem_filter]; omega
    have hcard : (Uof I E 0).card + 1 = (I.UE E).card := by
      rw [← hU0, Finset.card_insert_of_notMem h0n]
    rw [if_neg h0, if_pos (by omega), hU0, if_pos hval]
    exact List.mem_singleton_self _

end Tests

/-! ### Exhaustiveness -/

section Main

variable {E : Finset (ℕ × ℕ)}

lemma Cof_self (j : ℕ) : Cof E j j = ∅ := by
  unfold Cof; ext a; simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty,
    iff_false]; omega

lemma Cof_step {j i : ℕ} (hij : i < j) :
    Cof E j i = if (i, j) ∈ E then insert i (Cof E j (i + 1)) else Cof E j (i + 1) := by
  unfold Cof
  split_ifs with h
  · ext a; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    constructor
    · rintro ⟨ha, hia, haE⟩
      rcases Nat.eq_or_lt_of_le hia with rfl | h'
      · exact Or.inl rfl
      · exact Or.inr ⟨ha, h', haE⟩
    · rintro (rfl | ⟨ha, hia, haE⟩)
      · exact ⟨hij, le_refl _, h⟩
      · exact ⟨ha, by omega, haE⟩
  · ext a; simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨ha, hia, haE⟩
      rcases Nat.eq_or_lt_of_le hia with rfl | h'
      · exact absurd haE h
      · exact ⟨ha, h', haE⟩
    · rintro ⟨ha, hia, haE⟩; exact ⟨ha, by omega, haE⟩

lemma Acut_toFinset (j i : ℕ) :
    ((List.range i).filter fun a => decide ((a, j) ∈ E)).toFinset = Acut E j i := by
  unfold Acut; ext a; simp [List.mem_filter, List.mem_range]

/-- The path of `E` from the node `(j, i)` reaches `E`. -/
theorem mem_go (hI : InstOK I) (hT : TablesOK I T) (hA : AdmFacts I T E) :
    ∀ j, 1 ≤ j → j < I.m → ∀ i, I.lowN j ≤ i → i ≤ j →
      E ∈ I.go T j i (Dof E j) (Uof I E j) (Cof E j i) := by
  classical
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hj1 hjm i hi
  induction i, hi using Nat.le_induction with
  | base =>
    intro _
    rw [Inst.go, if_pos (nodeOK_path hI hT hA (i := I.lowN j) hjm (min_le_left _ _)),
      dif_pos (le_refl _)]
    rw [List.mem_flatMap]
    refine ⟨(List.range (I.lowN j)).filter fun a => decide ((a, j) ∈ E),
      List.mem_sublists.2 List.filter_sublist, ?_⟩
    rw [Acut_toFinset, leafStep_path hI hT hA hj1 hjm]
    dsimp only
    split_ifs with hj
    · have : j = 1 := by omega
      subst this
      exact last_path hA (by omega)
    · have := ih (j - 1) (by omega) (by omega) (by omega) (j - 1) (min_le_left _ _) (le_refl _)
      rwa [Cof_self] at this
  | succ i hi' ihi =>
    intro hij
    rw [Inst.go, if_pos (nodeOK_path hI hT hA hjm hij),
      dif_neg (by have : I.lowN j ≤ i := hi'; omega)]
    simp only [Nat.add_sub_cancel, List.mem_append]
    have hstep := Cof_step (E := E) (j := j) (i := i) (by omega)
    by_cases hE : (i, j) ∈ E
    · rw [if_pos hE] at hstep
      left; rw [← hstep]; exact ihi (by omega)
    · rw [if_neg hE] at hstep
      right; rw [← hstep]; exact ihi (by omega)

/-- **The search is exhaustive**: every core satisfying the acceptance condition `IntAdm` is
kept, for any tables with the soundness properties `TablesOK`. -/
theorem mem_search (hI : InstOK I) (hT : TablesOK I T) (hE : IntAdm I T E) :
    E ∈ I.search T := by
  classical
  have hA := AdmFacts.of hE
  have hm := hI.two_le_m
  unfold Inst.search
  rw [if_neg (by omega)]
  have hD : Dof E (I.m - 1) = ∅ := by
    unfold Dof; ext e; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
    intro he; have := (lt_of_mem_pairs (hA.pairs he)).2; omega
  have hU : Uof I E (I.m - 1) = ∅ := by
    unfold Uof; ext k; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
    intro hk; have := UE_lt hk; omega
  have := mem_go hI hT hA (I.m - 1) (by omega) (by omega) (I.m - 1) (min_le_left _ _) (le_refl _)
  rwa [hD, hU, Cof_self] at this

end Main

end Srch
end SemiprimeEgypt
