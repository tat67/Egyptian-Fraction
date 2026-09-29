/-
Generic lemmas used by the search tables.

* `topSum k L`: the sum of the `k` largest entries of a list of integers (greedy definition,
  computable).  `le_topSum`: for nonnegative entries, the sum of any `≤ k` entries (a sub-multiset
  of `L`) is at most `topSum k L`.
* `cdiv x d = ⌈x / d⌉` and `cdiv_add_cdiv_ge`: two rounded-up shares of a weight add up to at
  least the weight.
-/
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace SemiprimeEgypt

/-- The sum of the `k` largest entries of `L` (greedy: take the maximum, remove it, repeat). -/
def topSum : ℕ → List ℤ → ℤ
  | 0, _ => 0
  | k + 1, L => match L.max? with
    | none => 0
    | some a => a + topSum k (L.erase a)

lemma topSum_nonneg : ∀ (k : ℕ) (L : List ℤ), (∀ x ∈ L, 0 ≤ x) → 0 ≤ topSum k L
  | 0, _, _ => le_refl _
  | k + 1, L, hL => by
    unfold topSum
    split
    · exact le_refl _
    · rename_i a ha
      have ha' := List.max?_mem ha
      have h1 := topSum_nonneg k (L.erase a) fun x hx => hL x (List.mem_of_mem_erase hx)
      have := hL a ha'
      linarith

/-- **Top-`k` bound.**  If all entries of `L` are nonnegative, `A` is a sub-multiset of `L` and
`|A| ≤ k`, then `Σ A ≤ topSum k L`. -/
theorem le_topSum : ∀ (k : ℕ) (A L : List ℤ), (∀ x ∈ L, 0 ≤ x) → A.Subperm L → A.length ≤ k →
    A.sum ≤ topSum k L
  | 0, A, L, _, _, hk => by
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hk)]; simp [topSum]
  | k + 1, A, L, hL, hAL, hk => by
    unfold topSum
    split
    · rename_i hnone
      have hL0 : L = [] := List.max?_eq_none_iff.1 hnone
      subst hL0
      have : A = [] := List.subperm_nil.mp hAL
      subst this; simp
    · rename_i a ha
      obtain ⟨haL, hmax⟩ := List.max?_eq_some_iff.1 ha
      have hLe : ∀ x ∈ L.erase a, 0 ≤ x := fun x hx => hL x (List.mem_of_mem_erase hx)
      by_cases haA : a ∈ A
      · -- A = a :: (A.erase a), and A.erase a is a sub-multiset of L.erase a
        have hsum : A.sum = a + (A.erase a).sum := by
          rw [← List.sum_cons]; exact (List.perm_cons_erase haA).sum_eq
        have hsub : (A.erase a).Subperm (L.erase a) := List.Subperm.erase a hAL
        have hlen : (A.erase a).length ≤ k := by
          rw [List.length_erase_of_mem haA]; omega
        have := le_topSum k (A.erase a) (L.erase a) hLe hsub hlen
        linarith
      · rcases A with _ | ⟨b, A'⟩
        · have := topSum_nonneg k (L.erase a) hLe
          have := hL a haL
          simp only [List.sum_nil]; linarith
        · -- replace `b` by the maximum `a`
          have hbL : b ∈ L := hAL.subset List.mem_cons_self
          have hba : b ≤ a := hmax b hbL
          have hA'sub : A'.Subperm (L.erase a) := by
            have h1 : (b :: A').Subperm (L.erase a) := by
              rw [List.subperm_ext_iff]
              intro x hx
              have hc := (List.subperm_ext_iff.1 hAL) x hx
              by_cases hxa : x = a
              · subst hxa; exact absurd hx haA
              · rw [List.count_erase_of_ne hxa]; exact hc
            exact (List.sublist_cons_self b A').subperm.trans h1
          have hlen : A'.length ≤ k := by simp at hk; omega
          have := le_topSum k A' (L.erase a) hLe hA'sub hlen
          simp only [List.sum_cons]
          linarith

/-- `cdiv x d = ⌈x / d⌉` for `d > 0`. -/
def cdiv (x : ℤ) (d : ℕ) : ℤ := -((-x) / (d : ℤ))

lemma mul_cdiv_ge (x : ℤ) {d : ℕ} (hd : 0 < d) : x ≤ (d : ℤ) * cdiv x d := by
  unfold cdiv
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  have := Int.mul_ediv_self_le (x := -x) (k := (d : ℤ)) hd'.ne'
  linarith

/-- Two rounded-up shares `⌈s w / d⌉ + ⌈(d - s) w / d⌉ ≥ w`. -/
lemma cdiv_add_cdiv_ge (w : ℤ) (s : ℕ) {d : ℕ} (hd : 0 < d) (hs : s ≤ d) :
    w ≤ cdiv (w * s) d + cdiv (w * ((d - s : ℕ) : ℤ)) d := by
  have h1 := mul_cdiv_ge (w * s) hd
  have h2 := mul_cdiv_ge (w * ((d - s : ℕ) : ℤ)) hd
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  have e : ((d - s : ℕ) : ℤ) = d - s := by push_cast [hs]; ring
  rw [e] at h2
  have : (d : ℤ) * w ≤ (d : ℤ) * (cdiv (w * s) d + cdiv (w * ((d - s : ℕ) : ℤ)) d) := by
    rw [e]; nlinarith
  exact le_of_mul_le_mul_left this hd'

end SemiprimeEgypt
