#!/bin/sh
# End-to-end check for the `clightgen -lean` backend.
#
# Regenerates demo.lean from demo.c using the locally built clightgen, then
# typechecks it against the Lean support library (export/Clightdefs.lean).
#
# Requirements:
#   - ../../clightgen  (build with: ./configure -clightgen <target>; make clightgen)
#   - lean 4 on PATH   (see lean-toolchain at the repository root for the pinned version)

set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
export="$root/export"

echo "[1/3] Generating demo.lean with clightgen -lean ..."
"$root/clightgen" -lean -normalize "$here/demo.c"

echo "[2/3] Building the Lean support libraries (CCLib + Clightdefs) ..."
( cd "$export" && lake build CCLib Clightdefs )

echo "[3/3] Typechecking the generated file ..."
cp "$here/demo.lean" "$export/Demo_generated.lean"
( cd "$export" && LEAN_PATH=.lake/build/lib/lean lean Demo_generated.lean )
rm -f "$export/Demo_generated.lean"

echo "OK: demo.lean typechecks."
