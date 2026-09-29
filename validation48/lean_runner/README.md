# Running the verified Lean search

`../../lean/SemiprimeEgypt/Search.lean` defines Step 1 of `semiprime48.cpp` as a Lean function. Lean proves it exhaustive: `core_mem_search` in `SearchReal.lean` states that every admissible core is in its output. The function is executable. The two runners in this directory compile it to native code, so that its output can be compared with the core lists of the C++ program.

| file | content |
|---|---|
| `RunG.lean` | `runG K` prints the cores of `(inst73 K).search (inst73 K).mkTables` (S = primes ≤ 73). `runG SB K` does the same for the reduced instance `mkInst SB K` (S = primes ≤ SB). |
| `RunS.lean` | `runS K r n p` computes share `p` of `n` of the same search, for running it in several processes. By `Inst.search_eq_rounds` (`SearchSplit.lean`), the search is the concatenation, in order, of `evalItem` over the work items `expandRounds r [root]`. Share `p` evaluates the items whose index is `≡ p (mod n)` and prefixes every core with the index of its item. A stable sort of all shares by that index gives the output of the search, in order. |
| `build.sh`, `closure.py` | the build steps that were used: C code of the import closure, `leanc -O3`, link |

The Lean function is written for clarity, not speed. In particular it recomputes residues at every node and evaluates all 256 choices at every leaf step. Compiled, it is roughly 1000 to 3000 times slower than `semiprime48.cpp`.

The comparison script is `../lean_vs_cpp.sh`, and its output is `../lean_vs_cpp_output.txt`.
