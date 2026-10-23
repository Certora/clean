# The clightgen tool

## Overview

`clightgen` is an experimental tool that transforms C source files
into Clight abstract syntax or Csyntax abstract syntax, pretty-printed
in Coq format inside `.v` files.

These generated `.v` files can be loaded in a Coq session for
interactive verification, for example using the
[VST](https://vst.cs.princeton.edu/) toolchain.

## How to build

Configure CompCert with `./configure -clightgen`.

Build CompCert as usual.

The `clightgen` tool will be installed in the same directory as the
`ccomp` compiler.

## Usage
```
   clightgen [options] <C source files>
```
For each source file `src.c`, its Clight abstract syntax is generated
in `src.v`.

Run `clightgen -help` for a list of options.

Several options are shared with the `ccomp` compiler; 
see [user's manual](http://compcert.inria.fr/man/manual003.html)
for full documentation).

## Lean 4 output (experimental)

The `-lean` flag makes `clightgen` emit the Clight abstract syntax as a
**Lean 4** file (`src.lean`) instead of a Rocq/Coq `.v` file:

```
   clightgen -lean [options] <C source files>
```

`-lean` is only supported together with `-clight` (the default mode); it is
rejected with `-csyntax`.  All other options (`-normalize`,
`-canonical-idents`, `-short-idents`, ...) act on the AST before printing and
compose normally.

### Scope and caveats

The generated `.lean` file is a faithful Lean value of the program's *syntax*.

- There is still **no** link to CompCert's correctness theorem — that guarantee
  lives entirely in Rocq and does not transfer to a hand-written Lean mirror.  A
  Lean proof about the exported value says nothing (formally) about the compiled
  machine code.
- The Lean `Program` carries `prog_comp_env` (computed by `buildCompositeEnv`)
  but not CompCert's `prog_comp_env_eq` *proof*; see the `CCLib` section below.
- An operational semantics for exported programs now exists in `CCLib` — see
  [`LEAN.md`](LEAN.md).  Proofs no longer have to invent their own meaning for the
  exported AST (the toy `ClightSem.lean` that once did is superseded).

### Support library

Generated files start with `import Clightdefs; open CC` and rely on
`Clightdefs.lean` (in this directory), a hand-written Lean mirror of the Rocq
support files `Clightdefs.v` and `Ctypesdefs.v`.  It defines a Lean type for
every Rocq type a `Clight.program` transitively mentions.  Keep it next to the
generated files (it is not compiled by the CompCert Rocq build).

### Typechecking generated files

The Lake project is the one at the repository root (`lakefile.toml`,
`lean-toolchain`), which uses `export/` as its source directory.
`Demo.lean` is a representative generated file exercising every construct.

```
   lake build            # from the repository root; typechecks Clightdefs.lean and Demo.lean
```

To typecheck one generated file `foo.lean` without Lake, place it next to
`Clightdefs.lean` and run:

```
   lean -o Clightdefs.olean Clightdefs.lean
   LEAN_PATH=. lean foo.lean
```

### End-to-end check

`test/lean/demo.c` + `test/lean/check.sh` exercise the whole pipeline: they run
the locally built `clightgen -lean` on the C file and typecheck the result.
This has been verified end-to-end (clightgen built with Coq 9.1.0 / OCaml
4.14.2; generated `demo.lean` typechecks under Lean 4.32.1).

### Implementation

The backend mirrors the Rocq printers function-for-function, changing only the
emitted surface syntax: `ExportLeanBase.ml`, `ExportLeanCtypes.ml`,
`ExportLeanClight.ml` (parallel to `ExportBase.ml`, `ExportCtypes.ml`,
`ExportClight.ml`).  The `-lean` flag is dispatched in `ExportDriver.ml`.

## A real Clight semantics, an interpreter, and a program logic

The `-lean` export is only the front door.  Everything that gives an exported
program *meaning* — a Lean port of Clight's operational semantics, an executable
interpreter proved sound against it, a Hoare logic, the differential-testing
suites that validate all of it against CompCert itself, and a machine-checked
theorem about a real C function — is documented separately:

**→ [`LEAN.md`](LEAN.md)**

In short: `CCLib/` holds ~15k lines of Lean (no `sorry`) mirroring the Rocq
semantic stack, validated by 71,222 operation-level differential observations
against CompCert's own Rocq code and by 516 whole-program comparisons against
`ccomp -interp`; `CCLib/logic/Hoare.lean` adds a Hoare logic whose soundness is
definitional; and `IsSortedReal.lean` uses it to prove that `is_sorted` from
`main.c` returns `true` on sorted input, under `CC.Step`.
