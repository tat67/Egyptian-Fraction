/-
Splitting the search into independent subtrees (used to run it in parallel).

`frontier d` unfolds the first `d` levels of the include/exclude recursion of `Inst.go`; the
search is the concatenation, in order, of the searches below the nodes of the frontier
(`search_eq_frontier`).  A parallel runner that evaluates `Inst.go` at the frontier nodes and
concatenates the results in order therefore computes exactly `Inst.search`.
-/
import SemiprimeEgypt.Search

namespace SemiprimeEgypt
namespace Srch
namespace Inst

variable (I : Inst) (T : Tables)

/-- A node of the search: level `(j, i)`, decided edges `D`, decided unsatisfied set `U`,
chosen neighbours `C`. -/
abbrev Node := ℕ × ℕ × Finset (ℕ × ℕ) × Finset ℕ × Finset ℕ

/-- The search below a node. -/
def goNode (x : Node) : List (Finset (ℕ × ℕ)) := I.go T x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2

/-- The frontier after at most `d` unfolding steps of `go` (an include/exclude step, or the
leaf step, which produces the nodes of the next level).  Pruned nodes are dropped, since
`go` returns `[]` there. -/
def frontier : ℕ → Node → List Node
  | 0, x => [x]
  | d + 1, (j, i, D, U, C) =>
    if I.nodeOK T j i D U C then
      if i ≤ I.lowN j then
        if j ≤ 1 then [(j, i, D, U, C)]
        else ((List.range (I.lowN j)).sublists).flatMap fun ms =>
          match I.leafStep T j D U C ms.toFinset with
          | none => []
          | some (D'', U') => frontier d (j - 1, j - 1, D'', U', ∅)
      else frontier d (j, i - 1, D, U, insert (i - 1) C) ++ frontier d (j, i - 1, D, U, C)
    else []

theorem go_prune {j i : ℕ} {D : Finset (ℕ × ℕ)} {U C : Finset ℕ}
    (h : ¬ I.nodeOK T j i D U C = true) : I.go T j i D U C = [] := by
  rw [Inst.go]
  simp only [h, Bool.false_eq_true, ↓reduceIte]

/-- One include/exclude step of `go`. -/
theorem go_step {j i : ℕ} {D : Finset (ℕ × ℕ)} {U C : Finset ℕ}
    (h : I.nodeOK T j i D U C = true) (hi : ¬ i ≤ I.lowN j) :
    I.go T j i D U C = I.go T j (i - 1) D U (insert (i - 1) C) ++ I.go T j (i - 1) D U C := by
  rw [Inst.go]
  simp only [h, hi, ↓reduceIte, ↓reduceDIte]

/-- The leaf step of `go` (above the last level). -/
theorem go_leaf {j i : ℕ} {D : Finset (ℕ × ℕ)} {U C : Finset ℕ}
    (h : I.nodeOK T j i D U C = true) (hi : i ≤ I.lowN j) (hj : ¬ j ≤ 1) :
    I.go T j i D U C = ((List.range (I.lowN j)).sublists).flatMap fun ms =>
      match I.leafStep T j D U C ms.toFinset with
      | none => []
      | some (D'', U') => I.go T (j - 1) (j - 1) D'' U' ∅ := by
  rw [Inst.go]
  simp only [h, hi, hj, ↓reduceIte, ↓reduceDIte]
  rfl

theorem flatMap_frontier : ∀ (d : ℕ) (x : Node),
    (I.frontier T d x).flatMap (I.goNode T) = I.goNode T x
  | 0, x => by simp [frontier]
  | d + 1, (j, i, D, U, C) => by
    unfold frontier
    by_cases h : I.nodeOK T j i D U C = true
    · by_cases hi : i ≤ I.lowN j
      · by_cases hj : j ≤ 1
        · simp only [h, hi, hj, ↓reduceIte, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        · simp only [h, hi, hj, ↓reduceIte]
          rw [List.flatMap_assoc]
          simp only [goNode]
          rw [go_leaf I T h hi hj]
          congr 1
          funext ms
          rcases I.leafStep T j D U C ms.toFinset with _ | ⟨D'', U'⟩
          · rfl
          · exact flatMap_frontier d (j - 1, j - 1, D'', U', ∅)
      · simp only [h, hi, ↓reduceIte]
        rw [List.flatMap_append, flatMap_frontier d, flatMap_frontier d]
        simp only [goNode]
        rw [go_step I T h hi]
    · simp only [h, Bool.false_eq_true, ↓reduceIte, List.flatMap_nil, goNode]
      rw [go_prune I T h]

/-- A work item: a node (the search below it), or a node at its leaf step together with one
choice `ms` of the smallest neighbours (the leaf step for `ms` and the search below it). -/
abbrev Item := Node ⊕ (Node × List ℕ)

/-- The search results of a work item. -/
def evalItem : Item → List (Finset (ℕ × ℕ))
  | .inl x => I.goNode T x
  | .inr ((j, _, D, U, C), ms) =>
    match I.leafStep T j D U C ms.toFinset with
    | none => []
    | some (D'', U') => if _hj : j ≤ 1 then I.last T D'' U' else I.go T (j - 1) (j - 1) D'' U' ∅

/-- The work items after at most `d` include/exclude steps; a node at its leaf step is split
into one item per choice of the smallest neighbours. -/
def items : ℕ → Node → List Item
  | 0, x => [.inl x]
  | d + 1, (j, i, D, U, C) =>
    if I.nodeOK T j i D U C then
      if i ≤ I.lowN j then
        ((List.range (I.lowN j)).sublists).map fun ms => .inr ((j, i, D, U, C), ms)
      else items d (j, i - 1, D, U, insert (i - 1) C) ++ items d (j, i - 1, D, U, C)
    else []

theorem flatMap_items : ∀ (d : ℕ) (x : Node),
    (I.items T d x).flatMap (I.evalItem T) = I.goNode T x
  | 0, x => by simp [items, evalItem]
  | d + 1, (j, i, D, U, C) => by
    unfold items
    by_cases h : I.nodeOK T j i D U C = true
    · by_cases hi : i ≤ I.lowN j
      · simp only [h, hi, ↓reduceIte, List.flatMap_map]
        simp only [goNode]
        rw [Inst.go]
        simp only [h, hi, ↓reduceIte, ↓reduceDIte]
        rfl
      · simp only [h, hi, ↓reduceIte]
        rw [List.flatMap_append, flatMap_items d, flatMap_items d]
        simp only [goNode]
        rw [go_step I T h hi]
    · simp only [h, Bool.false_eq_true, ↓reduceIte, List.flatMap_nil, goNode]
      rw [go_prune I T h]

/-- Refine a work item: one include/exclude or leaf-splitting step for a node; the leaf step
itself for a leaf item (whose result is then a node of the next level). -/
def expandItem : Item → List Item
  | .inl x => I.items T 1 x
  | .inr ((j, i, D, U, C), ms) =>
    match I.leafStep T j D U C ms.toFinset with
    | none => []
    | some (D'', U') =>
      if j ≤ 1 then [.inr ((j, i, D, U, C), ms)] else [.inl (j - 1, j - 1, D'', U', ∅)]

theorem flatMap_expandItem (it : Item) :
    (I.expandItem T it).flatMap (I.evalItem T) = I.evalItem T it := by
  rcases it with x | ⟨⟨j, i, D, U, C⟩, ms⟩
  · simp only [expandItem, flatMap_items, evalItem]
  · simp only [expandItem, evalItem]
    cases hls : I.leafStep T j D U C ms.toFinset with
    | none => rfl
    | some p =>
      obtain ⟨D'', U'⟩ := p
      by_cases hj : j ≤ 1
      · simp [hj, evalItem, hls]
      · simp [hj, evalItem, goNode]

/-- Refining a list of work items does not change the concatenated results. -/
theorem flatMap_expand (L : List Item) :
    (L.flatMap (I.expandItem T)).flatMap (I.evalItem T) = L.flatMap (I.evalItem T) := by
  rw [List.flatMap_assoc]
  exact congrArg (fun f => L.flatMap f) (funext fun it => flatMap_expandItem I T it)

/-- Refine a work item `d` times recursively, then evaluate the pieces. -/
def evalDeep : ℕ → Item → List (Finset (ℕ × ℕ))
  | 0, it => I.evalItem T it
  | d + 1, it => (I.expandItem T it).flatMap (evalDeep d)

theorem evalDeep_eq : ∀ (d : ℕ) (it : Item), I.evalDeep T d it = I.evalItem T it
  | 0, _ => rfl
  | d + 1, it => by
    have h : evalDeep I T d = I.evalItem T := funext (evalDeep_eq d)
    simp only [evalDeep, h, flatMap_expandItem]

/-- **The search, evaluated through recursive refinement to depth `d`.** -/
theorem search_eq_evalDeep (hm : ¬ I.m ≤ 1) (d : ℕ) :
    I.search T = I.evalDeep T d (.inl (I.m - 1, I.m - 1, ∅, ∅, ∅)) := by
  rw [evalDeep_eq, search, ite_eq_right_of_eq_false _ _ (eq_false hm)]
  rfl

/-- `r` rounds of refinement of a list of work items. -/
def expandRounds : ℕ → List Item → List Item
  | 0, L => L
  | r + 1, L => expandRounds r (L.flatMap (I.expandItem T))

theorem flatMap_expandRounds : ∀ (r : ℕ) (L : List Item),
    (I.expandRounds T r L).flatMap (I.evalItem T) = L.flatMap (I.evalItem T)
  | 0, _ => rfl
  | r + 1, L => by rw [expandRounds, flatMap_expandRounds r, flatMap_expand]

/-- **The search is the concatenation of the results of the refined work items.** -/
theorem search_eq_rounds (hm : ¬ I.m ≤ 1) (r : ℕ) :
    I.search T = (I.expandRounds T r [.inl (I.m - 1, I.m - 1, ∅, ∅, ∅)]).flatMap (I.evalItem T) := by
  rw [flatMap_expandRounds, List.flatMap_singleton, search,
    ite_eq_right_of_eq_false _ _ (eq_false hm)]
  rfl

/-- **The search is the concatenation of the results of the work items.** -/
theorem search_eq_items (hm : ¬ I.m ≤ 1) (d : ℕ) :
    I.search T = (I.items T d (I.m - 1, I.m - 1, ∅, ∅, ∅)).flatMap (I.evalItem T) := by
  rw [flatMap_items, search, ite_eq_right_of_eq_false _ _ (eq_false hm)]
  rfl

/-- **The search is the concatenation of the searches below the frontier.** -/
theorem search_eq_frontier (hm : ¬ I.m ≤ 1) (d : ℕ) :
    I.search T = (I.frontier T d (I.m - 1, I.m - 1, ∅, ∅, ∅)).flatMap (I.goNode T) := by
  rw [flatMap_frontier, search, ite_eq_right_of_eq_false _ _ (eq_false hm)]
  rfl

end Inst
end Srch
end SemiprimeEgypt
