import SemiprimeEgypt.SearchReal
import SemiprimeEgypt.SearchSplit
open SemiprimeEgypt Srch

/-- A core, as the sorted list of its elements `P a * P b`. -/
def coreLine (I : Inst) (E : Finset (ℕ × ℕ)) : String :=
  " ".intercalate (((E.image fun e => I.P e.1 * I.P e.2).sort (· ≤ ·)).map toString)

/-- Like `RunS`, with a different partition of the work items `expandRounds r [root]`
(`Inst.search_eq_rounds`): `runT K r m c n p` evaluates the items whose index `i` satisfies
`i % m = c` and `(i / 256 + (i % 256) / m) % n = p`, and prints each core preceded by `i`.
(Consecutive blocks of 256 items come from the 256 choices of the final step at one node; the
key spreads the items of a block, and the blocks, over the `n` processes.) -/
def main (args : List String) : IO Unit := do
  let (K, r, m, c, n, p) := match args.map String.toNat! with
    | [K, r, m, c, n, p] => (K, r, m, c, n, p)
    | _ => (46, 26, 1, 0, 1, 0)
  let I := inst73 K
  let t0 ← IO.monoMsNow
  let T := I.mkTables
  let its := I.expandRounds T r [.inl (I.m - 1, I.m - 1, ∅, ∅, ∅)]
  let t1 ← IO.monoMsNow
  IO.eprintln s!"inst73 {K}: {r} rounds, {its.length} work items, class {c} mod {m}, share {p}/{n}, ms {t1 - t0}"
  let mut idx := 0
  let mut cnt := 0
  for it in its do
    if idx % m == c && (idx / 256 + (idx % 256) / m) % n == p then
      for E in I.evalItem T it do
        IO.println s!"{idx} {coreLine I E}"
        cnt := cnt + 1
    idx := idx + 1
  let t2 ← IO.monoMsNow
  IO.eprintln s!"inst73 {K}: class {c} mod {m}, share {p}/{n}: cores {cnt} ms {t2 - t0}"
