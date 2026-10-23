#!/bin/sh
# Level 5 of the differential suite: run whole C programs two ways and compare
# what they return.
#
#   oracle  : ccomp -interp  (CompCert's own reference interpreter), falling back
#             to the host C compiler for programs it cannot execute.  Each result
#             says which oracle was used.  The fallback is only sound because the
#             corpus is written to be free of undefined and
#             implementation-defined behaviour — a native compiler will happily
#             run programs whose behaviour CompCert leaves undefined.
#   subject : clightgen -lean, then the Lean interpreter (CCLib.cfrontend.ClightExec)
#
# IMPORTANT about what this does and does not check.  `ccomp -interp` executes
# **CompCert C** (`Csem`), not Clight — CompCert has no executable Clight
# semantics.  So this compares the *observable result* of a whole program, not
# step-by-step Clight behaviour, and it is only meaningful for programs with no
# undefined behaviour.  The step counts are deliberately not compared: the two
# semantics work at different granularities.
#
# Requirements: ccomp and clightgen built (see diff_all.sh), lean on PATH.
# Exit status 0 iff every program agrees.

set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
exp="$root/export"
corpus=${1:-"$here/corpus"}
tmp=$(mktemp -d)
work="$exp/.diff-$$"
trap 'rm -rf "$tmp" "$work"' EXIT
mkdir -p "$work"
cp "$exp/DiffRun.lean" "$work/DiffRun.lean"

echo "Building the Lean libraries ..."
( cd "$exp" && lake build CCLib >/dev/null )

# passing structs/unions by value is behind a flag in CompCert; the corpus uses
# it, and clightgen accepts the same flag.
CCFLAGS="-fstruct-passing"

pass=0; fail=0
for c in "$corpus"/*.c; do
  name=$(basename "$c" .c)

  # --- oracle: CompCert's reference interpreter ---
  # NB: `ccomp -interp` exits WITH THE PROGRAM'S status, so its exit code says
  # nothing about success; parse stdout instead.
  "$root/ccomp" -interp $CCFLAGS "$c" > "$tmp/cc.out" 2>"$tmp/cc.err" || true
  expected=$(sed -n 's/.*exit code = \(-\{0,1\}[0-9]*\).*/\1/p' "$tmp/cc.out" | tail -1)
  oracle=interp
  if [ -z "$expected" ]; then
    # CompCert's interpreter could not run it; fall back to the host compiler.
    # Only valid because the corpus is written to be free of undefined and
    # implementation-defined behaviour.
    if ${CC:-cc} -O0 -w -o "$tmp/ref" "$c" 2>/dev/null; then
      # guarded with `if` because a nonzero exit is the *result* here, and
      # `set -e` would otherwise abort the run
      if "$tmp/ref"; then expected=0; else expected=$?; fi
      oracle=nativecc
    else
      echo "  SKIP $name (neither oracle could run it: $(head -1 "$tmp/cc.out" "$tmp/cc.err" | tail -1))"
      continue
    fi
  fi

  # --- subject: clightgen -lean, then the Lean interpreter ---
  "$root/clightgen" -lean -normalize $CCFLAGS -o "$tmp/DiffProg.lean" "$c"
  cp "$tmp/DiffProg.lean" "$work/DiffProg.lean"
  # Generated modules live in a per-source namespace (so that several of them can
  # be imported together — see CCLib/common/Linking.lean).  Read it out of the file
  # rather than recomputing the exporter's naming rule here.
  ns=$(sed -n 's/^namespace \(.*\)$/\1/p' "$work/DiffProg.lean" | head -1)
  sed "s/^open CC$/open CC\nopen $ns/" "$exp/DiffRun.lean" > "$work/DiffRun.lean"
  # `import` needs a compiled module, so build DiffProg.olean first.  Both files
  # sit at the root of $work, so `import DiffProg` resolves there.
  if ! ( cd "$work" \
         && LEAN_PATH="$exp/.lake/build/lib/lean" lean -o DiffProg.olean DiffProg.lean \
         && LEAN_PATH="$exp/.lake/build/lib/lean:." lean --run DiffRun.lean ) \
         > "$tmp/lean.out" 2>"$tmp/lean.err"; then
    printf '  FAIL %-14s lean run failed: %s\n' "$name" "$(head -1 "$tmp/lean.err")"
    fail=$((fail+1)); continue
  fi
  got=$(tail -1 "$tmp/lean.out")
  # `ccomp -interp` prints the full returned int, but a process exit status is
  # only the low 8 bits, so mask the subject too when using the native oracle.
  case "$oracle" in
    nativecc) case "$got" in
                ''|*[!0-9-]*) : ;;
                *) got=$(( ((got % 256) + 256) % 256 )) ;;
              esac ;;
  esac

  if [ "$expected" = "$got" ]; then
    printf '  OK   %-14s -> %-12s (%s)\n' "$name" "$got" "$oracle"
    pass=$((pass+1))
  else
    printf '  FAIL %-14s oracle(%s)=%s  lean=%s\n' "$name" "$oracle" "$expected" "$got"
    fail=$((fail+1))
  fi
done

echo "$pass passed, $fail failed."
[ "$fail" -eq 0 ]
