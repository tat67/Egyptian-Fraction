import SemiprimeEgypt.SearchReal
import SemiprimeEgypt.SearchSplit
open SemiprimeEgypt Srch

/-- A core, as the sorted list of its elements `P a * P b`. -/
def coreLine (I : Inst) (E : Finset (ℕ × ℕ)) : String :=
  " ".intercalate (((E.image fun e => I.P e.1 * I.P e.2).sort (· ≤ ·)).map toString)

/-- Share `p` of `nproc` of the search `I.search I.mkTables`.  By `Inst.search_eq_rounds` the
search is the concatenation, in order, of `evalItem` over the work items
`expandRounds r [root]`; this process evaluates the items whose index is `≡ p (mod nproc)` and
prints each core preceded by the index of its item.  Sorting the union of the outputs of all
shares stably by the index gives the output of the search, in order.
`runS K r nproc p` (S = primes ≤ 73) or `runS SB K r nproc p` (`mkInst SB K`). -/
def main (args : List String) : IO Unit := do
  let (name, I, r, nproc, p) := match args with
    | [sb, k, r, n, p] => (s!"mkInst {sb} {k}", mkInst sb.toNat! k.toNat!, r.toNat!, n.toNat!, p.toNat!)
    | [k, r, n, p] => (s!"inst73 {k}", inst73 k.toNat!, r.toNat!, n.toNat!, p.toNat!)
    | _ => ("inst73 46", inst73 46, 26, 1, 0)
  let t0 ← IO.monoMsNow
  let T := I.mkTables
  let its := I.expandRounds T r [.inl (I.m - 1, I.m - 1, ∅, ∅, ∅)]
  let t1 ← IO.monoMsNow
  IO.eprintln s!"{name}: {r} rounds, {its.length} work items, share {p}/{nproc}, ms {t1 - t0}"
  let mut idx := 0
  let mut n := 0
  for it in its do
    if idx % nproc == p then
      for E in I.evalItem T it do
        IO.println s!"{idx} {coreLine I E}"
        n := n + 1
    idx := idx + 1
  let t2 ← IO.monoMsNow
  IO.eprintln s!"{name}: share {p}/{nproc}: cores {n} ms {t2 - t0}"
