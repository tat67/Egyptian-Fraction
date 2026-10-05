# primitive_explore: exploratory scripts for primitive Egyptian fractions

These scripts support [`../README_PRIMITIVE.md`](../README_PRIMITIVE.md). They are **exploratory**:

* the exact checks (`verify_sets.py`) are rigorous;
* the CP-SAT and compression results are evidence only.

The rigorous results are elsewhere:
* Q1 (`max T = 413`) and the bounds `39 ≤ min |T| ≤ 44`: Lean, `lean/SemiprimeEgypt/Prim*.lean`.
* `|T| = 39, 40, 41` impossible, hence `42 ≤ min |T|`: the exact search in [`../primitive_q2/`](../primitive_q2/README.md).

| file | what it does | status |
|---|---|---|
| `verify_sets.py` | Checks the explicit sets `T413`, the 49-element `T413b`, `T46`, `T44` and the semiprime `T47` with Python `Fraction`s: distinct, all `≥ 2`, primitive, and sum exactly 1. Output: `verify_sets_output.txt`. | exact |
| `cpsat_q2.py` | CP-SAT (OR-Tools) search for a primitive `T` with `Σ 1/n = 1` and at most `K` elements, inside a finite universe of non-prime-powers. Solutions it reports are re-verified exactly. `T46` and `T44` were found this way. | evidence only: infeasibility relies on the solver and covers bounded elements only |
| `enum_q2.py` | Enumerates **all** primitive solutions with exactly `K` terms and every element `≤ X`: an exact residue pre-filter, the CP-SAT model of `cpsat_q2.py` with `\|T\| = K`, optional valid Lagrangian cuts (Lemmas 2–3 of `../primitive_q2/README.md`), and a no-good loop. Every solution is re-verified exactly. Outputs: `enum_q2_<X>_<K>.txt`. | solutions exact; completeness relies on the solver's final INFEASIBLE (uncertified) |
| `compress.py` | Tries to replace two elements `a, b` of the 47- and 48-term semiprime solutions (`../solutions47.txt`, `../solutions48.txt`) by one element `ab/(a+b)` while keeping the set primitive. | exact for the sets tried; exploratory |
| `compress3.py` | Tries to replace three elements by two (Egyptian-fraction search over the smaller new element). | exact for the sets tried; exploratory |

The CP-SAT results, including universes up to `10^5` with no primitive solution of at most 43 terms, are tabulated in [`../primitive_q2_notes.md`](../primitive_q2_notes.md). The same `10^5` baseline is recorded in `../primitive_q2/runs/baseline_cpsat_100000_43.txt`.

**44-term solutions with bounded elements** (`enum_q2.py`):

| `X` | candidates after the filter | 44-term solutions with all elements `≤ X` | time |
|---:|---:|---|---|
| 20 000 | 14 636 | exactly 1: `T44` | 9 min (4 workers) |
| 30 000 | 22 211 | exactly 1: `T44` | 29 min (2 workers, with the cuts) |

Run from the repository root:

```
python3 primitive_explore/verify_sets.py
python3 primitive_explore/cpsat_q2.py X Pmax K seconds workers BIGMAX     # see the docstring
python3 primitive_explore/enum_q2.py 20000 44 4 0 out.txt                  # all 44-term solutions <= 20000
```
