#!/bin/sh
# Differential validation of CCLib (the Lean port of CompCert's semantic stack)
# against CompCert itself.  Four levels:
#
#   1. Integers  — ~25k operations, oracle = CompCert's lib/Integers.v via coqc
#   2. Values +  — ~38k operations, oracle = common/Values.v + common/Memdata.v
#      Memdata     via coqc
#   3. Ctypes +  — ~6.6k operations: layout (sizeof/alignof/field offsets incl.
#      Cop         bitfields) and the operator semantics (sem_cast, bool_val,
#                  sem_unary/binary_operation), oracle = cfrontend/Ctypes.v +
#                  cfrontend/Cop.v via coqc
#   4. Memory    — scenario suite, oracle = the OCaml EXTRACTION of
#                  common/Memory.v.  Coq's `Compute` cannot evaluate
#                  Mem.store/load/free (range_perm_dec is defined by
#                  well-founded recursion over an opaque accessibility proof),
#                  but the extraction is exactly what CompCert's own reference
#                  interpreter runs.
#
# Requirements:
#   - CompCert built in the supported toolchain:
#       eval $(opam env --switch=compcert-4.14)
#       ./configure -clightgen aarch64-macos && make proof && make extraction
#       make clightgen          # also produces the .cmx files level 3 links against
#   - lean on PATH (see lean-toolchain at the repository root)
#
# Exit status 0 iff every level agrees.

set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
exp="$root/export"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"; rm -f "$exp/IntDiff.lean" "$exp/SemDiff.lean" "$exp/TyDiff.lean" "$exp/MemDiff.lean" \
      "$exp/MemOracle.ml" "$exp/MemOracle.cmi" "$exp/MemOracle.cmx" "$exp/MemOracle.o" \
      "$root/mem_oracle_bin"' EXIT

INC="-R $root/lib compcert.lib -R $root/common compcert.common \
-R $root/aarch64 compcert.aarch64 -R $root/backend compcert.backend \
-R $root/cfrontend compcert.cfrontend -R $root/driver compcert.driver \
-R $root/cparser compcert.cparser -R $root/export compcert.export \
-R $root/flocq Flocq -R $root/MenhirLib MenhirLib"
INCS="-I extraction -I lib -I common -I aarch64 -I backend -I cfrontend \
-I cparser -I driver -I export -I debug"

echo "Building the Lean libraries ..."
( cd "$exp" && lake build CCLib >/dev/null )

compare () {          # compare <name> <oracle-file> <subject-file>
  no=$(wc -l < "$2"); ns=$(wc -l < "$3")
  if [ "$no" -ne "$ns" ]; then
    echo "FAIL ($1): observation-count mismatch (oracle $no, lean $ns)"; exit 1
  fi
  paste -d'|' "$2" "$3" > "$tmp/pairs"
  bad=$(awk -F'|' '$1!=$2{n++} END{print n+0}' "$tmp/pairs")
  if [ "$bad" -ne 0 ]; then
    echo "FAIL ($1): $bad of $no observations disagree.  First 10:"
    awk -F'|' '$1!=$2{print NR": rocq="$1"  lean="$2}' "$tmp/pairs" | head -10
    exit 1
  fi
  echo "  OK ($1): all $no agree."
}

# ---------------------------------------------------------------- 1. Integers
echo "[1/4] Integers ..."
python3 "$here/gen_int_diff.py" >/dev/null
coqc $INC "$here/int_diff.v" > "$tmp/c1.raw" 2>"$tmp/c1.err" || true
grep -q "^Error" "$tmp/c1.err" && { echo "coqc error:"; grep -A3 "^Error" "$tmp/c1.err" | head; exit 1; }
grep -E '^ *= ' "$tmp/c1.raw" | sed -E 's/^ *= //; s/[[:space:]]*$//' > "$tmp/c1.vals"
cp "$here/IntDiff.lean" "$exp/IntDiff.lean"
( cd "$exp" && LEAN_PATH=.lake/build/lib/lean lean IntDiff.lean ) > "$tmp/l1.vals"
compare Integers "$tmp/c1.vals" "$tmp/l1.vals"

# ------------------------------------------------------- 2. Values + Memdata
echo "[2/4] Values + Memdata ..."
python3 "$here/gen_sem_diff.py" >/dev/null
coqc $INC "$here/sem_diff.v" > "$tmp/c2.raw" 2>"$tmp/c2.err" || true
grep -q "^Error" "$tmp/c2.err" && { echo "coqc error:"; grep -A3 "^Error" "$tmp/c2.err" | head; exit 1; }
grep -E '^ *= ' "$tmp/c2.raw" | sed -E 's/^ *= //; s/[[:space:]]*$//' > "$tmp/c2.vals"
cp "$here/SemDiff.lean" "$exp/SemDiff.lean"
( cd "$exp" && LEAN_PATH=.lake/build/lib/lean lean SemDiff.lean ) > "$tmp/l2.vals"
compare "Values+Memdata" "$tmp/c2.vals" "$tmp/l2.vals"

# ------------------------------------------------------------- 3. Ctypes + Cop
echo "[3/4] Ctypes + Cop ..."
python3 "$here/gen_ty_diff.py" >/dev/null
coqc $INC "$here/ty_diff.v" > "$tmp/c4.raw" 2>"$tmp/c4.err" || true
grep -q "^Error" "$tmp/c4.err" && { echo "coqc error:"; grep -A3 "^Error" "$tmp/c4.err" | head; exit 1; }
grep -E '^ *= ' "$tmp/c4.raw" | sed -E 's/^ *= //; s/[[:space:]]*$//' > "$tmp/c4.vals"
cp "$here/TyDiff.lean" "$exp/TyDiff.lean"
( cd "$exp" && LEAN_PATH=.lake/build/lib/lean lean TyDiff.lean ) > "$tmp/l4.vals"
compare "Ctypes+Cop" "$tmp/c4.vals" "$tmp/l4.vals"

# ---------------------------------------------------------------- 4. Memory
echo "[4/4] Memory (oracle = OCaml extraction) ..."
cp "$here/mem_oracle.ml" "$exp/MemOracle.ml"
cd "$root"
ocamldep -slash $INCS export/MemOracle.ml > "$tmp/oracle.dep" 2>/dev/null
cat "$root/.depend.extr" "$tmp/oracle.dep" > "$tmp/dep.all"
ocamlopt -c $INCS -I +str -I +unix export/MemOracle.ml
OBJS=$(tools/modorder "$tmp/dep.all" export/MemOracle.cmx)
# shellcheck disable=SC2086
ocamlopt $INCS -I +str -I +unix str.cmxa unix.cmxa $OBJS -o "$root/mem_oracle_bin" 2>/dev/null
"$root/mem_oracle_bin" > "$tmp/c3.vals"     # must run from $root: reads compcert.ini
cp "$here/MemDiff.lean" "$exp/MemDiff.lean"
( cd "$exp" && LEAN_PATH=.lake/build/lib/lean lean --run MemDiff.lean ) > "$tmp/l3.vals"
compare Memory "$tmp/c3.vals" "$tmp/l3.vals"

echo "All four levels agree."
