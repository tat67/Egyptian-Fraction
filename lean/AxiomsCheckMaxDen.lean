/- Run with `lake env lean AxiomsCheckMaxDen.lean` (after `lake build SemiprimeEgypt.MaxDenMain`):
lists the axioms used by the results on the smallest possible largest element (589).
Expected output: only `propext`, `Classical.choice`, `Quot.sound` (no `sorryAx`, no
`Lean.ofReduceBool`, i.e. no `native_decide`). -/
import SemiprimeEgypt.MaxDenMain
open SemiprimeEgypt SemiprimeEgypt.MaxDen
#print axioms integral_iff_localCond
#print axioms check_sound
#print axioms no_solution
#print axioms valid_of_validB
#print axioms data588_valid
#print axioms cert588_ok
#print axioms no_solution_le_588
#print axioms exists_ge_589
#print axioms T589_sp
#print axioms T589_sum
#print axioms T589_max
#print axioms isLeast_589
