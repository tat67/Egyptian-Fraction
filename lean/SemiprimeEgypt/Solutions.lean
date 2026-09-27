/-
The 23 sets of 47 squarefree semiprimes with reciprocal sum 1 (README47), verified
unconditionally: each consists of 47 distinct squarefree semiprimes and has reciprocal sum
exactly 1 (exact rational arithmetic by `norm_num`).
-/
import SemiprimeEgypt.SumBounds

open Finset

namespace SemiprimeEgypt

/-- Solution 1. -/
def sol1 : Finset ℕ :=
  {6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62, 65, 69, 74, 77, 82, 85, 87, 91, 93, 95, 111, 115, 119, 123, 133, 143, 145, 155, 203, 219, 221, 287, 299, 391, 481, 1299, 2117, 16021, 31609}

/-- Solution 2. -/
def sol2 : Finset ℕ :=
  {6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62, 65, 69, 74, 77, 82, 85, 87, 91, 93, 95, 111, 115, 119, 123, 133, 143, 155, 185, 203, 221, 287, 299, 319, 391, 407, 481, 933, 1555, 11507}

/-- Solution 3. -/
def sol3 : Finset ℕ :=
  {6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62, 65, 69, 74, 77, 82, 85, 87, 91, 93, 95, 111, 115, 119, 123, 133, 145, 155, 161, 187, 221, 253, 259, 287, 407, 629, 667, 1509, 6539, 14587}

/-- Solution 4. -/
def sol4 : Finset ℕ :=
  {6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62, 65, 69, 74, 77, 82, 85, 87, 91, 93, 95, 115, 119, 123, 129, 133, 143, 145, 155, 187, 213, 221, 287, 301, 559, 629, 781, 1247, 1591, 1633}

/-- Solution 5. -/
def sol5 : Finset ℕ :=
  {6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62, 65, 69, 74, 77, 82, 86, 87, 91, 93, 95, 106, 111, 115, 123, 133, 155, 159, 161, 185, 203, 215, 253, 265, 583, 667, 731, 109591, 139823, 154939}

/-- Solution 6. -/
def sol6 : Finset ℕ :=
  {6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62, 65, 69, 74, 77, 82, 86, 91, 93, 95, 111, 119, 122, 123, 133, 143, 145, 155, 161, 183, 187, 259, 287, 299, 319, 473, 481, 559, 671, 1591}

/-- Solution 7. -/
def sol7 : Finset ℕ :=
  {6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62, 65, 69, 74, 77, 85, 86, 87, 91, 93, 94, 95, 111, 115, 119, 133, 141, 142, 145, 155, 187, 213, 517, 629, 799, 1247, 1591, 1633, 2021, 2627}

/-- Solution 8. -/
def sol8 : Finset ℕ :=
  {6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62, 65, 69, 74, 77, 86, 87, 91, 93, 94, 95, 111, 115, 118, 119, 129, 133, 145, 155, 161, 185, 187, 329, 517, 667, 851, 1073, 1357, 1363, 2537}

/-- Solution 9. -/
def sol9 : Finset ℕ :=
  {6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62, 65, 69, 74, 82, 85, 86, 87, 91, 93, 95, 106, 111, 123, 133, 145, 155, 159, 185, 203, 215, 253, 265, 287, 319, 493, 583, 731, 851, 1073}

/-- Solution 10. -/
def sol10 : Finset ℕ :=
  {6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62, 65, 69, 77, 82, 85, 86, 87, 91, 93, 94, 95, 111, 115, 119, 133, 141, 142, 155, 187, 205, 213, 235, 493, 517, 1363, 1633, 1763, 1927, 2627}

/-- Solution 11. -/
def sol11 : Finset ℕ :=
  {6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62, 65, 69, 77, 82, 85, 86, 87, 91, 93, 94, 95, 115, 118, 119, 123, 129, 133, 141, 155, 203, 287, 319, 391, 799, 1345, 1357, 2537, 2959, 12643}

/-- Solution 12. -/
def sol12 : Finset ℕ :=
  {6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62, 65, 69, 77, 82, 85, 86, 87, 91, 93, 94, 95, 115, 118, 119, 123, 133, 143, 145, 155, 203, 221, 287, 391, 559, 1357, 2537, 12209, 18103, 19787}

/-- Solution 13. -/
def sol13 : Finset ℕ :=
  {6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62, 65, 69, 77, 82, 85, 86, 87, 91, 93, 94, 95, 115, 119, 123, 129, 133, 141, 142, 145, 155, 187, 517, 799, 1207, 1247, 1633, 1763, 2021, 2911}

/-- Solution 14. -/
def sol14 : Finset ℕ :=
  {6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62, 65, 69, 77, 82, 85, 86, 87, 91, 93, 94, 95, 118, 119, 123, 129, 133, 155, 161, 187, 213, 287, 329, 355, 493, 497, 517, 1357, 1363, 2537}

/-- Solution 15. -/
def sol15 : Finset ℕ :=
  {6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62, 65, 69, 77, 82, 85, 86, 87, 91, 93, 94, 95, 118, 119, 123, 133, 145, 155, 161, 187, 203, 215, 287, 329, 493, 517, 1247, 1357, 1363, 2537}

/-- Solution 16. -/
def sol16 : Finset ℕ :=
  {6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62, 65, 69, 77, 82, 85, 86, 87, 93, 94, 95, 115, 118, 119, 123, 129, 133, 141, 143, 145, 155, 287, 377, 391, 551, 799, 893, 1357, 1363, 2537}

/-- Solution 17. -/
def sol17 : Finset ℕ :=
  {6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62, 65, 69, 77, 82, 85, 86, 87, 93, 94, 95, 115, 118, 119, 123, 129, 133, 143, 145, 155, 177, 287, 299, 391, 551, 611, 799, 893, 1711, 2537}

/-- Solution 18. -/
def sol18 : Finset ℕ :=
  {6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62, 65, 69, 77, 82, 85, 86, 91, 93, 94, 95, 115, 119, 123, 133, 141, 142, 143, 155, 203, 221, 235, 287, 299, 355, 377, 391, 559, 2021, 2059}

/-- Solution 19. -/
def sol19 : Finset ℕ :=
  {6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62, 65, 69, 77, 82, 85, 87, 91, 93, 94, 95, 111, 115, 118, 119, 123, 133, 142, 155, 187, 213, 287, 295, 329, 413, 493, 517, 1363, 1633, 2627}

/-- Solution 20. -/
def sol20 : Finset ℕ :=
  {6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62, 65, 69, 77, 82, 86, 87, 91, 93, 94, 95, 118, 119, 123, 129, 133, 145, 155, 161, 177, 187, 203, 287, 299, 329, 377, 517, 1363, 1711, 2537}

/-- Solution 21. -/
def sol21 : Finset ℕ :=
  {6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62, 65, 69, 77, 82, 86, 91, 93, 94, 95, 111, 115, 119, 123, 133, 141, 142, 143, 145, 155, 203, 213, 221, 235, 287, 493, 559, 1633, 2021, 2627}

/-- Solution 22. -/
def sol22 : Finset ℕ :=
  {6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62, 65, 69, 77, 82, 87, 91, 93, 95, 106, 111, 115, 119, 122, 123, 133, 142, 155, 159, 183, 187, 203, 213, 265, 287, 319, 583, 671, 1633, 2627}

/-- Solution 23. -/
def sol23 : Finset ℕ :=
  {6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62, 65, 74, 77, 82, 85, 87, 91, 93, 95, 111, 115, 119, 123, 129, 133, 143, 145, 155, 161, 221, 253, 259, 287, 299, 391, 473, 481, 1247, 1591}

/-- The 23 solutions. -/
def Sol23 : Finset (Finset ℕ) :=
  {sol1, sol2, sol3, sol4, sol5, sol6, sol7, sol8, sol9, sol10, sol11, sol12, sol13, sol14, sol15, sol16, sol17, sol18, sol19, sol20, sol21, sol22, sol23}

/-- All elements occurring in the 23 solutions (122 numbers). -/
def solElems : Finset ℕ :=
  {6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62, 65, 69, 74, 77, 82, 85, 86, 87, 91, 93, 94, 95, 106, 111, 115, 118, 119, 122, 123, 129, 133, 141, 142, 143, 145, 155, 159, 161, 177, 183, 185, 187, 203, 205, 213, 215, 219, 221, 235, 253, 259, 265, 287, 295, 299, 301, 319, 329, 355, 377, 391, 407, 413, 473, 481, 493, 497, 517, 551, 559, 583, 611, 629, 667, 671, 731, 781, 799, 851, 893, 933, 1073, 1207, 1247, 1299, 1345, 1357, 1363, 1509, 1555, 1591, 1633, 1711, 1763, 1927, 2021, 2059, 2117, 2537, 2627, 2911, 2959, 6539, 11507, 12209, 12643, 14587, 16021, 18103, 19787, 31609, 109591, 139823, 154939}

/-- Every element occurring in a solution is a squarefree semiprime (explicit factorisations,
primality by `norm_num`). -/
lemma solElems_sp : ∀ n ∈ solElems, IsSP n := by
  intro n hn
  simp only [solElems, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2, 3, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, 5, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, 7, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 5, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 7, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, 11, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, 13, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 11, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, 17, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 7, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, 19, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 13, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, 23, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 17, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 11, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 19, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, 29, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, 31, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 13, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 23, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, 37, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7, 11, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, 41, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 17, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, 43, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 29, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7, 13, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 31, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, 47, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 19, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, 53, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 37, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 23, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, 59, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7, 17, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, 61, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 41, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 43, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7, 19, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 47, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, 71, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨11, 13, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 29, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 31, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 53, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7, 23, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 59, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 61, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 37, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨11, 17, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7, 29, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 41, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 71, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 43, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 73, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨13, 17, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 47, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨11, 23, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7, 37, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 53, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7, 41, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 59, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨13, 23, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7, 43, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨11, 29, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7, 47, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 71, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨13, 29, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨17, 23, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨11, 37, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7, 59, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨11, 43, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨13, 37, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨17, 29, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7, 71, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨11, 47, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨19, 29, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨13, 43, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨11, 53, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨13, 47, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨17, 37, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨23, 29, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨11, 61, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨17, 43, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨11, 71, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨17, 47, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨23, 37, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨19, 47, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 311, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨29, 37, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨17, 71, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨29, 43, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 433, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 269, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨23, 59, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨29, 47, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 503, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 311, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨37, 43, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨23, 71, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨29, 59, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨41, 43, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨41, 47, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨43, 47, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨29, 71, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨29, 73, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨43, 59, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨37, 71, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨41, 71, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨11, 269, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨13, 503, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨37, 311, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨29, 421, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨47, 269, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨29, 503, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨37, 433, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨43, 421, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨47, 421, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨73, 433, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨29, 3779, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨37, 3779, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨41, 3779, by norm_num, by norm_num, by norm_num, by norm_num⟩

set_option maxRecDepth 100000 in
lemma Sol23_card : Sol23.card = 23 := by decide

set_option maxRecDepth 100000 in
lemma sol1_valid : sol1 ⊆ solElems ∧ (sol1).card = 47 ∧ recipSum sol1 = 1 :=
  ⟨by decide, by decide, by unfold recipSum sol1; norm_num [Finset.sum_insert]⟩

set_option maxRecDepth 100000 in
lemma sol2_valid : sol2 ⊆ solElems ∧ (sol2).card = 47 ∧ recipSum sol2 = 1 :=
  ⟨by decide, by decide, by unfold recipSum sol2; norm_num [Finset.sum_insert]⟩

set_option maxRecDepth 100000 in
lemma sol3_valid : sol3 ⊆ solElems ∧ (sol3).card = 47 ∧ recipSum sol3 = 1 :=
  ⟨by decide, by decide, by unfold recipSum sol3; norm_num [Finset.sum_insert]⟩

set_option maxRecDepth 100000 in
lemma sol4_valid : sol4 ⊆ solElems ∧ (sol4).card = 47 ∧ recipSum sol4 = 1 :=
  ⟨by decide, by decide, by unfold recipSum sol4; norm_num [Finset.sum_insert]⟩

set_option maxRecDepth 100000 in
lemma sol5_valid : sol5 ⊆ solElems ∧ (sol5).card = 47 ∧ recipSum sol5 = 1 :=
  ⟨by decide, by decide, by unfold recipSum sol5; norm_num [Finset.sum_insert]⟩

set_option maxRecDepth 100000 in
lemma sol6_valid : sol6 ⊆ solElems ∧ (sol6).card = 47 ∧ recipSum sol6 = 1 :=
  ⟨by decide, by decide, by unfold recipSum sol6; norm_num [Finset.sum_insert]⟩

set_option maxRecDepth 100000 in
lemma sol7_valid : sol7 ⊆ solElems ∧ (sol7).card = 47 ∧ recipSum sol7 = 1 :=
  ⟨by decide, by decide, by unfold recipSum sol7; norm_num [Finset.sum_insert]⟩

set_option maxRecDepth 100000 in
lemma sol8_valid : sol8 ⊆ solElems ∧ (sol8).card = 47 ∧ recipSum sol8 = 1 :=
  ⟨by decide, by decide, by unfold recipSum sol8; norm_num [Finset.sum_insert]⟩

set_option maxRecDepth 100000 in
lemma sol9_valid : sol9 ⊆ solElems ∧ (sol9).card = 47 ∧ recipSum sol9 = 1 :=
  ⟨by decide, by decide, by unfold recipSum sol9; norm_num [Finset.sum_insert]⟩

set_option maxRecDepth 100000 in
lemma sol10_valid : sol10 ⊆ solElems ∧ (sol10).card = 47 ∧ recipSum sol10 = 1 :=
  ⟨by decide, by decide, by unfold recipSum sol10; norm_num [Finset.sum_insert]⟩

set_option maxRecDepth 100000 in
lemma sol11_valid : sol11 ⊆ solElems ∧ (sol11).card = 47 ∧ recipSum sol11 = 1 :=
  ⟨by decide, by decide, by unfold recipSum sol11; norm_num [Finset.sum_insert]⟩

set_option maxRecDepth 100000 in
lemma sol12_valid : sol12 ⊆ solElems ∧ (sol12).card = 47 ∧ recipSum sol12 = 1 :=
  ⟨by decide, by decide, by unfold recipSum sol12; norm_num [Finset.sum_insert]⟩

set_option maxRecDepth 100000 in
lemma sol13_valid : sol13 ⊆ solElems ∧ (sol13).card = 47 ∧ recipSum sol13 = 1 :=
  ⟨by decide, by decide, by unfold recipSum sol13; norm_num [Finset.sum_insert]⟩

set_option maxRecDepth 100000 in
lemma sol14_valid : sol14 ⊆ solElems ∧ (sol14).card = 47 ∧ recipSum sol14 = 1 :=
  ⟨by decide, by decide, by unfold recipSum sol14; norm_num [Finset.sum_insert]⟩

set_option maxRecDepth 100000 in
lemma sol15_valid : sol15 ⊆ solElems ∧ (sol15).card = 47 ∧ recipSum sol15 = 1 :=
  ⟨by decide, by decide, by unfold recipSum sol15; norm_num [Finset.sum_insert]⟩

set_option maxRecDepth 100000 in
lemma sol16_valid : sol16 ⊆ solElems ∧ (sol16).card = 47 ∧ recipSum sol16 = 1 :=
  ⟨by decide, by decide, by unfold recipSum sol16; norm_num [Finset.sum_insert]⟩

set_option maxRecDepth 100000 in
lemma sol17_valid : sol17 ⊆ solElems ∧ (sol17).card = 47 ∧ recipSum sol17 = 1 :=
  ⟨by decide, by decide, by unfold recipSum sol17; norm_num [Finset.sum_insert]⟩

set_option maxRecDepth 100000 in
lemma sol18_valid : sol18 ⊆ solElems ∧ (sol18).card = 47 ∧ recipSum sol18 = 1 :=
  ⟨by decide, by decide, by unfold recipSum sol18; norm_num [Finset.sum_insert]⟩

set_option maxRecDepth 100000 in
lemma sol19_valid : sol19 ⊆ solElems ∧ (sol19).card = 47 ∧ recipSum sol19 = 1 :=
  ⟨by decide, by decide, by unfold recipSum sol19; norm_num [Finset.sum_insert]⟩

set_option maxRecDepth 100000 in
lemma sol20_valid : sol20 ⊆ solElems ∧ (sol20).card = 47 ∧ recipSum sol20 = 1 :=
  ⟨by decide, by decide, by unfold recipSum sol20; norm_num [Finset.sum_insert]⟩

set_option maxRecDepth 100000 in
lemma sol21_valid : sol21 ⊆ solElems ∧ (sol21).card = 47 ∧ recipSum sol21 = 1 :=
  ⟨by decide, by decide, by unfold recipSum sol21; norm_num [Finset.sum_insert]⟩

set_option maxRecDepth 100000 in
lemma sol22_valid : sol22 ⊆ solElems ∧ (sol22).card = 47 ∧ recipSum sol22 = 1 :=
  ⟨by decide, by decide, by unfold recipSum sol22; norm_num [Finset.sum_insert]⟩

set_option maxRecDepth 100000 in
lemma sol23_valid : sol23 ⊆ solElems ∧ (sol23).card = 47 ∧ recipSum sol23 = 1 :=
  ⟨by decide, by decide, by unfold recipSum sol23; norm_num [Finset.sum_insert]⟩

set_option maxRecDepth 100000 in
/-- **The 23 listed sets are solutions** (unconditional): each is a set of 47 squarefree
semiprimes with reciprocal sum exactly `1`. -/
theorem Sol23_valid : ∀ T ∈ Sol23, (∀ n ∈ T, IsSP n) ∧ T.card = 47 ∧ recipSum T = 1 := by
  have key : ∀ T ∈ Sol23, T ⊆ solElems ∧ T.card = 47 ∧ recipSum T = 1 := by
    intro T hT
    simp only [Sol23, Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact sol1_valid
    · exact sol2_valid
    · exact sol3_valid
    · exact sol4_valid
    · exact sol5_valid
    · exact sol6_valid
    · exact sol7_valid
    · exact sol8_valid
    · exact sol9_valid
    · exact sol10_valid
    · exact sol11_valid
    · exact sol12_valid
    · exact sol13_valid
    · exact sol14_valid
    · exact sol15_valid
    · exact sol16_valid
    · exact sol17_valid
    · exact sol18_valid
    · exact sol19_valid
    · exact sol20_valid
    · exact sol21_valid
    · exact sol22_valid
    · exact sol23_valid
  intro T hT
  obtain ⟨h1, h2, h3⟩ := key T hT
  exact ⟨fun n hn => solElems_sp n (Finset.mem_of_subset h1 hn), h2, h3⟩

end SemiprimeEgypt
