/- Run with `lake env lean AxiomsCheckPrim.lean` (after `lake build SemiprimeEgypt.PrimCardMain`):
lists the axioms used by the results on primitive Egyptian fractions of 1.
Expected output: only `propext`, `Classical.choice`, `Quot.sound` (no `sorryAx`, no
`Lean.ofReduceBool`, i.e. no `native_decide`). -/
import SemiprimeEgypt.PrimCardMain
open SemiprimeEgypt SemiprimeEgypt.Prim
#print axioms no_primePow
#print axioms check_sound
#print axioms no_solution
#print axioms valid_of_validB
#print axioms data412_valid
#print axioms C412.cert_ok
#print axioms no_solution_le_412
#print axioms exists_ge_413
#print axioms T413_primitive
#print axioms T413_sum
#print axioms T413_max
#print axioms isLeast_413
#print axioms q1_with_one
#print axioms lagrange_bound
#print axioms lag129_valid
#print axioms card_ge_39
#print axioms T47_sum
#print axioms card_bounds
