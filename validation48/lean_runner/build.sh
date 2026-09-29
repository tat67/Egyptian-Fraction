#!/bin/bash
# Build the native runners of the Lean search (runG, runS) used by ../lean_vs_cpp.sh.
#
# This is the procedure that was used; it links against a Mathlib checkout that has been built
# with `lake build` (so that .lake/build/ir contains the C code of every Mathlib module) and in
# which the modules of ../../lean/SemiprimeEgypt have been compiled (to .olean) under
# $M/SemiprimeEgypt.  (A lake `lean_exe` target in ../../lean would do the same.)
#
# Usage: M=/path/to/mathlib4 OUT=/path/to/outdir bash build.sh
set -e
: "${M:?set M to the Mathlib checkout}"
: "${OUT:?set OUT to an output directory}"
HERE=$(cd "$(dirname "$0")" && pwd)
LEANC=$(dirname "$(elan which lean)")/leanc
mkdir -p "$OUT/c" "$OUT/o"
cp "$HERE/RunG.lean" "$HERE/RunS.lean" "$M/SemiprimeEgypt/"
cd "$M"
# 1. the import closure of the runners (module, source root)
python3 "$HERE/closure.py" SemiprimeEgypt.RunG SemiprimeEgypt.RunS > "$OUT/closure.txt"
# 2. C code of the project modules and of the runners (Mathlib's C code already exists)
for m in $(grep '^SemiprimeEgypt' "$OUT/closure.txt" | awk '{print $1}'); do
  lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -c "$OUT/c/$m.c" "$(echo $m | tr . /).lean"
done
# 3. compile every module of the closure
while read m d; do
  case $m in
    SemiprimeEgypt.*) c="$OUT/c/$m.c" ;;
    *) c="$d/.lake/build/ir/$(echo $m | tr . /).c" ;;
  esac
  echo "$c $m"
done < "$OUT/closure.txt" | xargs -P 4 -n 2 sh -c "[ -f $OUT/o/\$1.o ] || $LEANC -c -O3 -DNDEBUG -o $OUT/o/\$1.o \$0"
# 4. link (each runner with every module except the other runner)
ls "$OUT"/o/*.o | grep -v 'SemiprimeEgypt.Run[GS].o' > "$OUT/objs.txt"
$LEANC -o "$OUT/runG" $(cat "$OUT/objs.txt") "$OUT/o/SemiprimeEgypt.RunG.o"
$LEANC -o "$OUT/runS" $(cat "$OUT/objs.txt") "$OUT/o/SemiprimeEgypt.RunS.o"
echo "built $OUT/runG $OUT/runS"
