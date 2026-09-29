import SemiprimeEgypt.SearchReal
open SemiprimeEgypt Srch

/-- A core, as the sorted list of its elements `P a * P b`. -/
def coreLine (I : Inst) (E : Finset (ℕ × ℕ)) : String :=
  " ".intercalate (((E.image fun e => I.P e.1 * I.P e.2).sort (· ≤ ·)).map toString)

/-- `runG K`: the verified search `(inst73 K).search (inst73 K).mkTables` (S = primes ≤ 73);
`runG SB K`: the same search on the reduced instance `mkInst SB K` (S = primes ≤ SB). -/
def main (args : List String) : IO Unit := do
  let (name, I) := match args with
    | [sb, k] => (s!"mkInst {sb} {k}", mkInst sb.toNat! k.toNat!)
    | [k] => (s!"inst73 {k}", inst73 k.toNat!)
    | _ => ("inst73 46", inst73 46)
  let t0 ← IO.monoMsNow
  let out := I.search I.mkTables
  let n := out.length
  let t1 ← IO.monoMsNow
  IO.eprintln s!"{name}: cores {n} ms {t1 - t0}"
  for E in out do IO.println (coreLine I E)
