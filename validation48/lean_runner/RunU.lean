import SemiprimeEgypt.SearchReal
import SemiprimeEgypt.SearchSplit
open SemiprimeEgypt Srch

/-- A core, as the sorted list of its elements `P a * P b`. -/
def coreLine (I : Inst) (E : Finset (ℕ × ℕ)) : String :=
  " ".intercalate (((E.image fun e => I.P e.1 * I.P e.2).sort (· ≤ ·)).map toString)

/-- The "spine" of the search: no core edge decided and none chosen. -/
def isSpine : Inst.Item → Bool
  | .inl (_, _, D, _, C) => D.card == 0 && C.card == 0
  | .inr ((_, _, D, _, C), ms) => D.card == 0 && C.card == 0 && ms.isEmpty

/-- Decompose the work item `it` along the spine: repeatedly replace the current item by its
refinement `expandItem` (which has the same results, `Inst.flatMap_expandItem`), keep the
refined pieces that are not on the spine as `(step, position, item)`, and continue with the
piece on the spine.  The results of `it` are the concatenation of the results of the kept
pieces, ordered by `(step, position)` with the spine piece of each step replaced by the later
steps. -/
def spineDecomp (I : Inst) (T : Tables) (it : Inst.Item) : Array (ℕ × ℕ × Inst.Item) := Id.run do
  let mut cur := it
  let mut out : Array (ℕ × ℕ × Inst.Item) := #[]
  for step in [0:1000] do
    let subs := I.expandItem T cur
    let k0 := subs.findIdx isSpine
    -- stop at a fixed point (last level), or when no piece is on the spine
    if subs.length == 1 && k0 == 0 && step > 0 && (match subs, cur with
        | [.inr ((j, _, _, _, _), _)], _ => j ≤ 1 | _, _ => false) then
      out := out.push (step, 0, cur)
      return out
    if k0 ≥ subs.length then
      for (s, k) in subs.zipIdx do out := out.push (step, k, s)
      return out
    for (s, k) in subs.zipIdx do
      if k != k0 then out := out.push (step, k, s)
    cur := subs[k0]!
  out := out.push (1000, 0, cur)
  return out

/-- `runU skip K r m c n p X`: as `runT K r m c n p`, but without the item `X`.
`runU spine K r X n p`: the pieces `spineDecomp` of the item `X` whose position in the
decomposition is `≡ p (mod n)`; prints `X step position core`. -/
def main (args : List String) : IO Unit := do
  match args with
  | ["find", k, r] =>
    let I := inst73 k.toNat!; let T := I.mkTables
    let its := I.expandRounds T r.toNat! [.inl (I.m - 1, I.m - 1, ∅, ∅, ∅)]
    let mut idx := 0
    for it in its do
      if isSpine it then IO.println s!"spine item {idx}"
      idx := idx + 1
  | ["skip", k, r, m, c, n, p, x] =>
    let (K, m, c, n, p, X) := (k.toNat!, m.toNat!, c.toNat!, n.toNat!, p.toNat!, x.toNat!)
    let I := inst73 K; let T := I.mkTables
    let its := I.expandRounds T r.toNat! [.inl (I.m - 1, I.m - 1, ∅, ∅, ∅)]
    let t0 ← IO.monoMsNow
    let mut idx := 0
    let mut cnt := 0
    for it in its do
      if idx != X && idx % m == c && (idx / 256 + (idx % 256) / m) % n == p then
        for E in I.evalItem T it do
          IO.println s!"{idx} 0 0 {coreLine I E}"
          cnt := cnt + 1
      idx := idx + 1
    let t1 ← IO.monoMsNow
    IO.eprintln s!"skip {X}: class {c} mod {m}, share {p}/{n}: cores {cnt} ms {t1 - t0}"
  | ["spine", k, r, x, n, p] =>
    let (K, X, n, p) := (k.toNat!, x.toNat!, n.toNat!, p.toNat!)
    let I := inst73 K; let T := I.mkTables
    let its := I.expandRounds T r.toNat! [.inl (I.m - 1, I.m - 1, ∅, ∅, ∅)]
    let t0 ← IO.monoMsNow
    let pieces := spineDecomp I T its[X]!
    IO.eprintln s!"spine {X}: {pieces.size} pieces, {(pieces.foldl (fun a q => max a q.1) 0)} steps"
    let mut cnt := 0
    let mut pos := 0
    for (step, k, it) in pieces do
      if pos % n == p then
        for E in I.evalItem T it do
          IO.println s!"{X} {step} {k} {coreLine I E}"
          cnt := cnt + 1
      pos := pos + 1
    let t1 ← IO.monoMsNow
    IO.eprintln s!"spine {X}: share {p}/{n}: cores {cnt} ms {t1 - t0}"
  | _ => IO.eprintln "usage: runU find K r | skip K r m c n p X | spine K r X n p"
