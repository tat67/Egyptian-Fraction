/- Run with `lake env lean AxiomsCheck.lean`: lists the axioms used by the main results.
Expected output: only `propext`, `Classical.choice`, `Quot.sound` (no `sorryAx`, no
`Lean.ofReduceBool`). -/
import SemiprimeEgypt
open SemiprimeEgypt
#print axioms integral_iff_localCond
#print axioms recipSum_eq_one_of_integral
#print axioms card_ge_38
#print axioms card_Uset_le
#print axioms value_lower_subset
#print axioms shape_value_bound
#print axioms parity_two
#print axioms star_size
#print axioms starCand_of_real
#print axioms comp_value
#print axioms comp_local_iff
#print axioms comp_divisor_eq
#print axioms comp_enum
#print axioms comp_of_divisor
#print axioms admissible_of_real
#print axioms shapeOK_of_real
#print axioms Sol23_valid
#print axioms Sol23_card
#print axioms no_integral_sum_le_46
#print axioms card_ge_47_of_integral
#print axioms solutions47_complete
#print axioms solutions47_iff
#print axioms solutions47_integral_iff
#print axioms solutions47_ncard
-- the verified search (semiprime48.cpp, Step 1)
#print axioms le_topSum
#print axioms Srch.Inst.loss_bound
#print axioms Srch.mem_search
#print axioms Srch.Inst.mkTables_ok
#print axioms Srch.intAdm_of_admissible
#print axioms Srch.core_mem_search
#print axioms Srch.core_of_solution_mem_search
#print axioms mem_searchCores
#print axioms recipSum_eq_one_of_integral_48
#print axioms core_mem_searchCores
#print axioms search46_of
#print axioms search47_of
#print axioms no_integral_sum_le_46'
#print axioms card_ge_47_of_integral'
#print axioms solutions47_iff'
#print axioms solutions47_integral_iff'
#print axioms solutions47_ncard'
#print axioms Srch.Inst.search_eq_rounds
#print axioms Srch.Inst.search_eq_evalDeep
-- the smallest possible largest element (589): MaxDenCheck / MaxDenMain
#print axioms SemiprimeEgypt.MaxDen.no_solution
#print axioms SemiprimeEgypt.MaxDen.isLeast_589
-- primitive sets: min max T = 413, 39 <= min |T| <= 47 (PrimMain / PrimCardMain)
#print axioms SemiprimeEgypt.Prim.isLeast_413
#print axioms SemiprimeEgypt.Prim.card_bounds
