#!/bin/sh
# Differential test: CC.Integers (Lean, BitVec-based) vs CompCert's lib/Integers.v (Rocq).
#
# CompCert represents a machine integer as a Z with a range proof; the Lean port
# uses `BitVec w` instead.  This script checks that substitution empirically:
# ~25k operations are evaluated on both sides and the results compared.
#
# Requirements:
#   - CompCert's Rocq development built (make proof), with coqc on PATH:
#       eval $(opam env --switch=compcert-4.14)
#   - lean on PATH (see lean-toolchain at the repository root)
#
# Exit status 0 iff every case agrees.

set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
exp="$root/export"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

INC="-R $root/lib compcert.lib -R $root/common compcert.common \
-R $root/aarch64 compcert.aarch64 -R $root/backend compcert.backend \
-R $root/cfrontend compcert.cfrontend -R $root/driver compcert.driver \
-R $root/cparser compcert.cparser -R $root/export compcert.export \
-R $root/flocq Flocq -R $root/MenhirLib MenhirLib"

echo "[1/4] Generating matched test batteries ..."
python3 "$here/gen_int_diff.py"

echo "[2/4] Running the Rocq oracle (CompCert lib/Integers.v) ..."
# shellcheck disable=SC2086
coqc $INC "$here/int_diff.v" > "$tmp/coq.raw" 2>"$tmp/coq.err" || {
  echo "coqc failed:"; head -20 "$tmp/coq.err"; exit 1; }
grep -E '^ *= ' "$tmp/coq.raw" | sed -E 's/^ *= //; s/[[:space:]]*$//' > "$tmp/coq.vals"

echo "[3/4] Running the Lean subject (CCLib/lib/Integers.lean) ..."
cp "$here/IntDiff.lean" "$exp/IntDiff.lean"
( cd "$exp" && LEAN_PATH=. lean -o CCLib/aarch64/Archi.olean CCLib/aarch64/Archi.lean \
  && LEAN_PATH=. lean -o CCLib/lib/Integers.olean CCLib/lib/Integers.lean \
  && LEAN_PATH=. lean IntDiff.lean ) > "$tmp/lean.vals"
rm -f "$exp/IntDiff.lean"

echo "[4/4] Comparing ..."
nc=$(wc -l < "$tmp/coq.vals"); nl=$(wc -l < "$tmp/lean.vals")
if [ "$nc" -ne "$nl" ]; then
  echo "FAIL: case-count mismatch (rocq $nc, lean $nl)"; exit 1
fi
paste -d'|' "$tmp/coq.vals" "$tmp/lean.vals" > "$tmp/pairs"
bad=$(awk -F'|' '$1!=$2{n++} END{print n+0}' "$tmp/pairs")
if [ "$bad" -ne 0 ]; then
  echo "FAIL: $bad of $nc cases disagree.  First 10:"
  awk -F'|' '$1!=$2{print NR": rocq="$1"  lean="$2}' "$tmp/pairs" | head -10
  echo "(test i corresponds to line i+6 of test/lean/int_diff.v)"
  exit 1
fi
echo "OK: all $nc cases agree."
