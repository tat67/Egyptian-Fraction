/-
Concrete tables for the search (the same formulas as `semiprime48.cpp`), built once as arrays.

* `VB x = Σ_{i<x} up(bs i)`, `VTH = max_{x ≤ K} (VB x - x θ)`;
* `MX j R = max_{x ≤ R} (topSum x (edge values below j) + VB (R - x))`;
* `BT j i R = max_{t ≤ min i R} (topSum t (values of the edges {a, j}, a < i) + MX j (R - t))`;
* `LOC J k r`, `TOPT j i t`: the best local configuration of a prime (knapsack over residues,
  `dpRun`), or the unsatisfied option.
-/
import SemiprimeEgypt.Search

open Finset

namespace SemiprimeEgypt
namespace Srch

/-- `-2^120`, "minus infinity" of the knapsack. -/
def NEG : ℤ := -(2 ^ 120)

/-- One step of the residue knapsack: add an item of residue `iv` and value `s`. -/
def dpStep (q iv : ℕ) (s : ℤ) (b : Array ℤ) : Array ℤ :=
  Array.ofFn (n := q) fun r => max (b.getD r NEG) (b.getD ((r.1 + q - iv % q) % q) NEG + s)

/-- The residue knapsack: entry `r` is the largest value of a subset of the items whose
residues add up to `r` (mod `q`). -/
def dpRun (q : ℕ) (xs : List (ℕ × ℤ)) : Array ℤ :=
  xs.foldl (fun b c => dpStep q c.1 c.2 b) (Array.ofFn (n := q) fun r => if r.1 = 0 then 0 else NEG)

/-- The edges with both indices `< j`, as a list. -/
def pairList (j : ℕ) : List (ℕ × ℕ) := (List.range j).flatMap fun b => (List.range b).map fun a => (a, b)

namespace Inst

variable (I : Inst)

/-- Local bound of the prime `k` with candidate neighbours `cs` and residue `r` of its decided
edges: best subset with total residue `≡ 0`, or the unsatisfied option. -/
def locB (k : ℕ) (cs : List ℕ) (r : ℕ) : ℤ :=
  let q := I.P k
  let arr := dpRun q (cs.map fun x => (I.inv k x, I.share k x))
  max (arr.getD ((q - r % q) % q) NEG) ((I.GV k : ℤ) - I.TH + (cs.map fun x => max (I.share k x) 0).sum)

/-- `LOC J k r`: candidates `0, …, J` except `k`. -/
def LOCspec (J k r : ℕ) : ℤ := I.locB k ((List.range (J + 1)).filter (· ≠ k)) r
/-- `TOPT j i t`: candidates `0, …, i - 1`. -/
def TOPTspec (j i t : ℕ) : ℤ := I.locB j (List.range i) t

/-- `VB x`. -/
def VBspec (x : ℕ) : ℕ := ∑ i ∈ range x, up (I.bs.getD i 0)
/-- The values of the edges with both indices `< j`. -/
def pairVals (j : ℕ) : List ℤ := (pairList j).map fun e => ((I.EU e.1 e.2 : ℕ) : ℤ)
/-- The values of the edges `{a, j}`, `a < i`. -/
def rowVals (j i : ℕ) : List ℤ := (List.range i).map fun a => ((I.EU a j : ℕ) : ℤ)

/-- The tables, computed once. -/
def mkTables : Tables :=
  let K := I.K
  let m := I.m
  let vbA : Array ℕ := Array.ofFn (n := K + 2) fun x => I.VBspec x
  let VB : ℕ → ℕ := fun x => vbA.getD x 0
  let vth : ℤ := (range (K + 1)).sup' ⟨0, by simp⟩ fun x => (VB x : ℤ) - x * I.TH
  -- topSum x (pairVals j), x ≤ K
  let tsA : Array (Array ℕ) := Array.ofFn (n := m + 1) fun j =>
    Array.ofFn (n := K + 1) fun x => (topSum x (I.pairVals j)).toNat
  let mxA : Array (Array ℕ) := Array.ofFn (n := m + 1) fun j =>
    Array.ofFn (n := K + 1) fun R =>
      (range (R.1 + 1)).sup (fun x => (tsA.getD j #[]).getD x 0 + VB (R.1 - x))
  let MX : ℕ → ℕ → ℕ := fun j R => (mxA.getD j #[]).getD R 0
  let btA : Array (Array (Array ℕ)) := Array.ofFn (n := m) fun j =>
    Array.ofFn (n := j.1 + 1) fun i =>
      Array.ofFn (n := K + 1) fun R =>
        (range (min i.1 R.1 + 1)).sup (fun t => (topSum t (I.rowVals j i)).toNat + MX j (R.1 - t))
  let locA : Array (Array (Array ℤ)) := Array.ofFn (n := m) fun J =>
    Array.ofFn (n := J.1 + 1) fun k => Array.ofFn (n := I.P k) fun r => I.LOCspec J k r
  let toptA : Array (Array (Array ℤ)) := Array.ofFn (n := m) fun j =>
    Array.ofFn (n := j.1 + 1) fun i => Array.ofFn (n := I.P j) fun t => I.TOPTspec j i t
  { VB := VB
    VTH := vth
    MX := MX
    BT := fun j i R => ((btA.getD j #[]).getD i #[]).getD R 0
    LOC := fun J k r => ((locA.getD J #[]).getD k #[]).getD r 0
    TOPT := fun j i t => ((toptA.getD j #[]).getD i #[]).getD t 0 }

end Inst

/-! ### Instances -/

/-- Naive primality (for building test instances). -/
def isPrimeB (n : ℕ) : Bool := 2 ≤ n && (List.range n).all fun d => d < 2 || n % d != 0

/-- The primes `≤ B`. -/
def primesUpTo (B : ℕ) : List ℕ := (List.range (B + 1)).filter isPrimeB

/-- The least prime `> B`. -/
def nextPrime (B : ℕ) : ℕ := ((List.range (4 * B + 100)).filter fun n => B < n && isPrimeB n).headD 0

/-- The `c` smallest squarefree semiprimes `p q` with `p < q` and `q ≥ big` (search up to `60 big`,
as in the C++ program). -/
def bigSemiprimes (big c : ℕ) : List ℕ :=
  ((List.range (60 * big + 1)).filter fun n =>
    (List.range n).any fun p => 2 ≤ p && n % p == 0 && p < n / p && big ≤ n / p &&
      isPrimeB p && isPrimeB (n / p)).take c

/-- The instance with `S` = primes `≤ SB` and budget `K`, with the parameters of
`semiprime48.cpp` (`θ = 1/145`, shares `12, 11, 11, 10, 10, 9, 8, 8, …` / 12, 8 leaf primes). -/
def mkInst (SB K : ℕ) : Inst where
  pr := primesUpTo SB
  K := K
  big := nextPrime SB
  bs := bigSemiprimes (nextPrime SB) (K + 1)
  theta := 145
  AD := 12
  shn := [12, 11, 11, 10, 10, 9]
  lown := 8

end Srch
end SemiprimeEgypt
