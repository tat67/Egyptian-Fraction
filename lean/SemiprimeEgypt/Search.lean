/-
The core search (Step 1) of `semiprime48.cpp`, written as a Lean function.

An *instance* fixes the primes of `S` (in increasing order, index `k ↦ P k`), the budget `K`,
the least prime `big` above `S`, the list `bs` of the smallest semiprimes with a prime factor
`≥ big`, the Lagrange multiplier `θ = ⌊2^96 / theta⌋ / 2^96`, the shares `sh a / AD`, and the
number `lown` of primes handled by the table-driven leaf step.  All quantities are integers:
reciprocals are 96-bit fixed point numbers, rounded up (`up`) or down (`lo`).

A core is a finite set `E` of index pairs `(a, b)`, `a < b < m`, standing for the elements
`P a * P b`.  The search processes the primes in decreasing order: at the prime with index `j`
it chooses the neighbours of `j` among the smaller indices (`i` counts down; the smallest
`lowN j` indices are chosen at once in the *leaf* step), then decides whether `j` is
unsatisfied, and continues with `j - 1`.  Every node is tested with

* (P1) the budget, (P2) the lower-rounded core sum `≤ 1`, (P3) the value bound through the
  tables `MX`, `BT`, and (P4) the loss bound through the tables `VTH`, `TOPT`, `LOC`;

a leaf is tested with the corresponding final forms, and a complete core with the value
condition `ONE ≤ su + gz + VB`.

The expensive tables are an argument `T : Tables`; `SearchCorrect.lean` proves that the search
is exhaustive for *any* tables with the soundness properties `TablesOK`, and
`SearchTables.lean` builds concrete tables and proves `TablesOK` for them.
-/
import SemiprimeEgypt.TopSum
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.List.Sublists

open Finset

namespace SemiprimeEgypt
namespace Srch

/-- The fixed-point unit `2^96`. -/
def ONE : ℕ := 2 ^ 96
/-- `⌈2^96 / n⌉`. -/
def up (n : ℕ) : ℕ := (ONE + n - 1) / n
/-- `⌊2^96 / n⌋`. -/
def lo (n : ℕ) : ℕ := ONE / n

/-- An instance of the search. -/
structure Inst where
  /-- the primes of `S`, increasing -/
  pr : List ℕ
  /-- the budget -/
  K : ℕ
  /-- the least prime above `S` -/
  big : ℕ
  /-- the smallest semiprimes with a prime factor `≥ big`, increasing -/
  bs : List ℕ
  /-- `θ = ⌊ONE / theta⌋` -/
  theta : ℕ
  /-- denominator of the shares -/
  AD : ℕ
  /-- share numerators, indexed by the smaller endpoint (default `8`) -/
  shn : List ℕ
  /-- number of primes handled by the leaf step -/
  lown : ℕ

/-- The edges joining the indices of `A` to `j`. -/
def star (j : ℕ) (A : Finset ℕ) : Finset (ℕ × ℕ) := A.image (fun a => (a, j))
/-- All edges with both indices `< j`. -/
def pairsBelow (j : ℕ) : Finset (ℕ × ℕ) := (range j ×ˢ range j).filter (fun e => e.1 < e.2)

namespace Inst

variable (I : Inst)

/-- The number of primes of `S`. -/
def m : ℕ := I.pr.length
/-- The prime with index `k`. -/
def P (k : ℕ) : ℕ := I.pr.getD k 1
/-- `(P b)⁻¹ mod P a`. -/
def inv (a b : ℕ) : ℕ := ((I.P b : ZMod (I.P a))⁻¹).val
/-- Rounded-up value of the edge `{a, b}`. -/
def EU (a b : ℕ) : ℕ := up (I.P a * I.P b)
/-- Rounded-down value of the edge `{a, b}`. -/
def EL (a b : ℕ) : ℕ := lo (I.P a * I.P b)
/-- Rounded-up value `1/(big · P k)` of the big edge of an unsatisfied prime. -/
def GV (k : ℕ) : ℕ := up (I.big * I.P k)
/-- The Lagrange multiplier `θ` in fixed point. -/
def TH : ℕ := ONE / I.theta
/-- Share numerator for an edge whose smaller endpoint is `a`. -/
def sh (a : ℕ) : ℕ := I.shn.getD a 8
/-- The weight `up(1/(P a P b)) - θ` of an edge. -/
def wt (a b : ℕ) : ℤ := (I.EU a b : ℤ) - I.TH
/-- The share of the weight of the edge `{k, x}` received by `k`: `⌈σ w⌉` for the larger
endpoint and `⌈(1 - σ) w⌉` for the smaller one, `σ = sh(smaller) / AD`. -/
def share (k x : ℕ) : ℤ :=
  if x < k then cdiv (I.wt k x * I.sh x) I.AD
  else cdiv (I.wt k x * ((I.AD - I.sh k : ℕ) : ℤ)) I.AD

/-- Contribution of the edge `e` to the residue of the index `k`. -/
def ctr (k : ℕ) (e : ℕ × ℕ) : ℕ :=
  (if e.1 = k then I.inv k e.2 else 0) + (if e.2 = k then I.inv k e.1 else 0)
/-- The residue at `k` of an edge set. -/
def res (D : Finset (ℕ × ℕ)) (k : ℕ) : ℕ := (∑ e ∈ D, I.ctr k e) % I.P k
/-- Rounded-up sum of an edge set. -/
def su (D : Finset (ℕ × ℕ)) : ℕ := ∑ e ∈ D, I.EU e.1 e.2
/-- Rounded-down sum of an edge set. -/
def sl (D : Finset (ℕ × ℕ)) : ℕ := ∑ e ∈ D, I.EL e.1 e.2
/-- Sum of the big-edge allowances of a set of unsatisfied primes. -/
def gz (U : Finset ℕ) : ℕ := ∑ k ∈ U, I.GV k
/-- The unsatisfied set of a core. -/
def UE (E : Finset (ℕ × ℕ)) : Finset ℕ := (range I.m).filter (fun k => I.res E k ≠ 0)
/-- The number of smallest indices chosen at once at level `j`. -/
def lowN (j : ℕ) : ℕ := min j I.lown

end Inst

/-- The expensive tables of the search. -/
structure Tables where
  VB : ℕ → ℕ
  VTH : ℤ
  MX : ℕ → ℕ → ℕ
  BT : ℕ → ℕ → ℕ → ℕ
  LOC : ℕ → ℕ → ℕ → ℤ
  TOPT : ℕ → ℕ → ℕ → ℤ

namespace Inst

variable (I : Inst) (T : Tables)

/-- The loss-bound contribution of the undecided primes `k < j` at the node `(j, i)`. -/
def SL (j i : ℕ) (D : Finset (ℕ × ℕ)) : ℤ :=
  ∑ k ∈ range j, if k < i then T.LOC j k (I.res D k) else T.LOC (j - 1) k (I.res D k)

/-- The tests (P1)–(P4) at the node `(j, i)`: decided edges `D` (larger index `> j`),
decided unsatisfied set `U`, chosen neighbours `C` of `j` among the indices `i, …, j - 1`. -/
def nodeOK (j i : ℕ) (D : Finset (ℕ × ℕ)) (U C : Finset ℕ) : Bool :=
  let D' := D ∪ star j C
  let used := D'.card + U.card
  decide (used ≤ I.K) && decide (I.sl D' ≤ ONE) &&
    decide (ONE ≤ I.su D' + I.gz U + T.BT j i (I.K - used)) &&
    decide ((ONE : ℤ) ≤ ((I.su D' + I.gz U + (I.K - used) * I.TH : ℕ) : ℤ) + T.VTH +
      T.TOPT j i (I.res D' j) + I.SL T j i D')

/-- The leaf step at level `j`: add the edges from `j` to the chosen set `M` of the smallest
indices, decide whether `j` is unsatisfied, and test. -/
def leafStep (j : ℕ) (D : Finset (ℕ × ℕ)) (U C M : Finset ℕ) :
    Option (Finset (ℕ × ℕ) × Finset ℕ) :=
  let D' := D ∪ star j C
  let D'' := D' ∪ star j M
  let exc := decide (I.res D'' j ≠ 0)
  let U' := if exc then insert j U else U
  let used0 := D'.card + U.card
  let used := D''.card + U'.card
  let okExc := !exc || (decide (used0 + 1 ≤ I.K) &&
    decide (ONE ≤ I.su D' + I.gz U + T.BT j (I.lowN j) (I.K - used0 - 1) + I.GV j))
  let ok := okExc && decide (used ≤ I.K) && decide (I.sl D'' ≤ ONE) &&
    decide (ONE ≤ I.su D'' + I.gz U' + T.MX j (I.K - used)) &&
    decide ((ONE : ℤ) ≤ ((I.su D'' + I.gz U' + (I.K - used) * I.TH : ℕ) : ℤ) + T.VTH +
      ∑ k ∈ range j, T.LOC (j - 1) k (I.res D'' k))
  if ok then some (D'', U') else none

/-- A complete core passes if its value condition holds. -/
def fin (D : Finset (ℕ × ℕ)) (U : Finset ℕ) : List (Finset (ℕ × ℕ)) :=
  if ONE ≤ I.su D + I.gz U + T.VB (I.K - D.card - U.card) then [D] else []

/-- The last prime (index 0): satisfied, or unsatisfied if the budget allows. -/
def last (D : Finset (ℕ × ℕ)) (U : Finset ℕ) : List (Finset (ℕ × ℕ)) :=
  if I.res D 0 = 0 then I.fin T D U
  else if D.card + U.card + 1 ≤ I.K then I.fin T D (insert 0 U) else []

/-- The depth-first search from the node `(j, i)`. -/
def go (j i : ℕ) (D : Finset (ℕ × ℕ)) (U C : Finset ℕ) : List (Finset (ℕ × ℕ)) :=
  if I.nodeOK T j i D U C then
    if _hi : i ≤ I.lowN j then
      ((List.range (I.lowN j)).sublists).flatMap fun ms =>
        match I.leafStep T j D U C ms.toFinset with
        | none => []
        | some (D'', U') =>
          if hj : j ≤ 1 then I.last T D'' U' else go (j - 1) (j - 1) D'' U' ∅
    else go j (i - 1) D U (insert (i - 1) C) ++ go j (i - 1) D U C
  else []
termination_by (j, i)
decreasing_by
  · exact Prod.Lex.left _ _ (by omega)
  · exact Prod.Lex.right _ (by omega)
  · exact Prod.Lex.right _ (by omega)

/-- **The search.**  The list of all cores kept by Step 1. -/
def search : List (Finset (ℕ × ℕ)) :=
  if I.m ≤ 1 then I.last T ∅ ∅ else I.go T (I.m - 1) (I.m - 1) ∅ ∅ ∅

end Inst

/-- The soundness properties of the tables used by the pruning tests. -/
structure TablesOK (I : Inst) (T : Tables) : Prop where
  vth : ∀ x ≤ I.K, (T.VB x : ℤ) - x * I.TH ≤ T.VTH
  mx : ∀ j ≤ I.m, ∀ R ≤ I.K, ∀ F ⊆ pairsBelow j, F.card ≤ R →
    I.su F + T.VB (R - F.card) ≤ T.MX j R
  bt : ∀ j < I.m, ∀ i ≤ j, ∀ R ≤ I.K, ∀ A ⊆ range i, A.card ≤ R →
    (∑ a ∈ A, I.EU a j) + T.MX j (R - A.card) ≤ T.BT j i R
  topt_res : ∀ j < I.m, ∀ i ≤ j, ∀ t < I.P j, ∀ Y ⊆ range i,
    (t + ∑ y ∈ Y, I.inv j y) % I.P j = 0 → ∑ y ∈ Y, I.share j y ≤ T.TOPT j i t
  topt_U : ∀ j < I.m, ∀ i ≤ j, ∀ t < I.P j, ∀ Y ⊆ range i,
    (I.GV j : ℤ) - I.TH + ∑ y ∈ Y, I.share j y ≤ T.TOPT j i t
  loc_res : ∀ J < I.m, ∀ k ≤ J, ∀ r < I.P k, ∀ Y ⊆ (range (J + 1)).erase k,
    (r + ∑ y ∈ Y, I.inv k y) % I.P k = 0 → ∑ y ∈ Y, I.share k y ≤ T.LOC J k r
  loc_U : ∀ J < I.m, ∀ k ≤ J, ∀ r < I.P k, ∀ Y ⊆ (range (J + 1)).erase k,
    (I.GV k : ℤ) - I.TH + ∑ y ∈ Y, I.share k y ≤ T.LOC J k r

/-- Basic requirements on an instance. -/
structure InstOK (I : Inst) : Prop where
  two_le_m : 2 ≤ I.m
  P_pos : ∀ k, 0 < I.P k
  AD_pos : 0 < I.AD
  sh_le : ∀ a, I.sh a ≤ I.AD

/-- The integer form of the Step-1 acceptance condition (Lemma 3 for every upper segment of
`U`, rounded): the search must keep every core satisfying it. -/
def IntAdm (I : Inst) (T : Tables) (E : Finset (ℕ × ℕ)) : Prop :=
  E ⊆ pairsBelow I.m ∧ E.card + (I.UE E).card ≤ I.K ∧ I.sl E ≤ ONE ∧
    ∀ s ≤ I.m, ONE ≤ I.su E + I.gz ((I.UE E).filter (s ≤ ·)) +
      T.VB (I.K - E.card - ((I.UE E).filter (s ≤ ·)).card)

end Srch
end SemiprimeEgypt
