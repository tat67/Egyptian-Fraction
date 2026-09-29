# Running the verified Lean search

`../../lean/SemiprimeEgypt/Search.lean` defines Step 1 of `semiprime48.cpp` as a Lean function. Lean proves it exhaustive: `core_mem_search` in `SearchReal.lean` states that every admissible core is in its output. The function is executable. The two runners in this directory compile it to native code, so that its output can be compared with the core lists of the C++ program.

| file | content |
|---|---|
| `RunG.lean` | `runG K` prints the cores of `(inst73 K).search (inst73 K).mkTables` (S = primes ≤ 73). `runG SB K` does the same for the reduced instance `mkInst SB K` (S = primes ≤ SB). |
| `RunS.lean` | `runS K r n p` computes share `p` of `n` of the same search, for running it in several processes. By `Inst.search_eq_rounds` (`SearchSplit.lean`), the search is the concatenation, in order, of `evalItem` over the work items `expandRounds r [root]`. Share `p` evaluates the items whose index is `≡ p (mod n)` and prefixes every core with the index of its item. A stable sort of all shares by that index gives the output of the search, in order. |
| `RunT.lean` | `runT K r m c n p`: the same, with a finer partition. It evaluates the items with index `i ≡ c (mod m)` and `(i / 256 + (i % 256) / m) ≡ p (mod n)`. Consecutive blocks of 256 items are the 256 choices of the final step at one node; this key spreads a block, and the blocks, over the processes. |
| `build.sh`, `closure.py` | the build steps that were used: C code of the import closure, `leanc -O3`, link |

The Lean function is written for clarity, not speed. In particular it recomputes residues at every node and evaluates all 256 choices at every leaf step. Compiled, it is several hundred to several thousand times slower than `semiprime48.cpp`. For budget 46 it took about 8.5 CPU hours; the C++ search takes 4.6 s with one thread.

The comparison script is `../lean_vs_cpp.sh`, and its output is `../lean_vs_cpp_output.txt`.

**Budget 46 on the real instance** was run in several processes, because the sequential run would take many hours. After 26 refinement rounds there are 890,624 work items. Every item was evaluated by exactly one process, as follows.

1. `runS 46 26 4 p`, `p = 1, 2, 3`: the items with index `≢ 0 (mod 4)`. Result: 0 cores (1690, 716 and 949 s).
2. `runT 46 26 4 0 8 p`, `p = 0, …, 7`: the items with index `≡ 0 (mod 4)`. These were first assigned to `runS 46 26 4 0`, which was stopped because it got all the heaviest items. For `p ≠ 4` the result was 0 cores (190–1026 s each).
3. Sub-share `p = 4` contains the item 740352 (`runU find 46 26`). This is the *spine* item, in which no core edge has been chosen at the primes 73 and 71; it dominates the work. The sub-share was replaced by two runs:
   * `runU skip 46 26 4 0 8 4 740352`: the other items of sub-share 4. Result: 0 cores (250 s).
   * `runU spine 46 26 740352 3 p`, `p = 0, 1, 2`: item 740352, refined along the spine with `expandItem` (same results, `Inst.flatMap_expandItem`) into 2349 pieces, of which each process takes every third. Result: 51 + 73 + 54 = 178 cores (8487, 8761 and 5863 s).

The union of all outputs is 178 distinct cores (`../lean46_cores.txt`). It equals the list of the C++ Step 1 (`../lean_vs_cpp_output.txt`). The processes that were stopped were redundant and produced no output that was used.

| file | content |
|---|---|
| `RunU.lean` | `runU find K r` (the spine item), `runU skip K r m c n p X` (as `runT`, without item `X`), `runU spine K r X n p` (the spine decomposition of item `X`, piece `≡ p (mod n)`) |
