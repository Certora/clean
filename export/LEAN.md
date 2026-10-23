# C → Lean 4: Clight semantics and a separation logic, in Lean

This document describes the Lean 4 backend added to CompCert 3.18. It covers
what exists, what it guarantees, and how to use it. The work has four parts:

1. a `-lean` flag for `clightgen`, which exports a C program's Clight abstract
   syntax as a Lean 4 module;
2. a Lean 4 port of Clight's operational semantics and of the CompCert memory
   model it depends on;
3. an executable interpreter for that semantics, proved sound against it, and a
   determinism theorem for the step relation;
4. a separation logic for Clight, with function specifications, a frame rule,
   and rules for calls, function pointers, `goto`, structs, arrays and unions,
   used to prove real C functions correct and memory-safe.

The development (the `CCLib` root) has no external dependencies (no Mathlib)
and contains no `sorry` and no `native_decide`. (It is built by the repository-root
`lakefile.toml`, with `export/` as source directory, on the toolchain
`leanprover/lean4:v4.32.1` pinned in the root `lean-toolchain`. The root project additionally requires
Mathlib for the second root `CCLibMathlib`, which contains the proofs that
the port's duplicates of Mathlib/Batteries/core definitions agree with them
(see `../MATHLIB_DUPLICATION.md`); `CCLib` itself does not import Mathlib.
The floating-point semantics is computed by the exact IEEE-754 model
`CCLib/lib/FloatModel.lean` (a backport of Lean core's `Float.Model`), so the
port contains no Flocq; see `../MODULE_AUDIT.md` for which modules the port
should and should not contain.)

---

## 1. Components

| Component | Where | Purpose |
|---|---|---|
| Exporter | `ExportLean{Base,Ctypes,Clight}.ml`, `ExportDriver.ml` | `clightgen -lean` |
| AST | `Clightdefs.lean`, `CCLib/{AST,Ctypes,Clight}.lean` | the Clight syntax generated files refer to |
| Semantics | `CCLib/` (Integers, Floats, Values, Memdata, Memory, Cop, Globalenvs, Events, Clight) | port of the Rocq semantic stack |
| Interpreter | `CCLib/cfrontend/ClightExec.lean`, `CCLib/cfrontend/ClightExecSound.lean` | executable `doStep`, proved sound |
| Determinism | `CCLib/common/Determinism.lean` | the step relation is deterministic |
| Memory lemmas | `CCLib/{Maps,Memdata,Memory}Lemmas.lean` | store/load algebra for the logic |
| Memory relations | `CCLib/{MemoryUnchanged,MemdataInject,MemoryInject,MemoryExtends,MemoryInjections}.lean` | `unchanged_on`, `mem_inj`, `Mem.extends`, `Mem.inject` and their theorems (port of `Memory.v`) |
| Separation logic | `CCLib/{Heap,SepLogic,SepHoare,Funspec,FunPtr,Aggregate,Locals,Temps,Tactics}.lean` | assertions, rules, specs, automation |
| Linking | `CCLib/common/Linking.lean` | merge several generated modules into one program |
| Hoare logic (original) | `CCLib/logic/Hoare.lean`, `HoareArray.lean`, `HoareLong.lean` | the pre-separation logic, still supported |
| Examples | `examples/` | generated test programs, the proofs about them, and the non-vacuity checks |
| Validation | `test/lean/` | differential tests against CompCert |

The Lean side is about 15,000 lines under `CCLib/`; the exporter is about 650
lines of OCaml.

## 2. The exporter

`clightgen -lean` prints a translation unit's Clight AST as Lean 4 instead of
Rocq:

```
clightgen -lean -normalize -include stdbool.h -o Main.lean main.c
```

The generated module is wrapped in a namespace derived from the source file's
basename (`deflate.c` becomes `namespace Deflate`), so several generated
modules can be imported into one Lean file. A consumer opens the namespace it
needs and gets `prog` (the whole `Program`), `composites`, and one definition
per function (`f_is_sorted`, `f_main`, …), plus a named identifier for every C
symbol (`_numbers`, `_len`, …).

The Lean printers mirror the Rocq printers function for function; only the
emitted syntax differs. The generated files depend on a small, fixed
vocabulary of names (`Integers.Int.repr`, `Floats.Float.ofBits`,
`identOfString`, `mkprogram`, …), so generated output is stable across changes
to the libraries underneath it. Everything `clightgen` accepts for the Rocq
backend is accepted for the Lean backend, including `-normalize`.

## 3. The semantics

The port covers the Rocq modules a Clight semantics transitively needs:
`Maps`, `Integers`, `Floats`, `Values`, `Memdata`, `Memory`, `Ctypes`, `Cop`,
`Globalenvs`, `Events`, `Smallstep` and `Clight` itself. The step relation
`Step` is parameterized over the function-entry relation, as in Rocq, so both
`function_entry1` and `function_entry2` are available; generated code uses the
second.

Three representation choices distinguish the port from a verbatim
transcription.

**Machine integers are `BitVec`.** CompCert's `int`, `int64`, `ptrofs` are
`Z` modulo a power of two with a range invariant; Lean's `BitVec w` is exactly
that. Signed division, remainder, comparisons and the wrap-around corner
cases coincide with CompCert's definitions, and this is checked by the
differential tests in §8.

**Floats are IEEE bit patterns.** A `Float` or `Float32` is its bit pattern,
so equality is structural and NaN payloads are preserved. Every operation is
computed exactly in pure Lean: the numeric part comes from `CCLib.lib.FloatModel`,
a backport of Lean core's IEEE-754 reference model `Float.Model` (core ships it
from v4.33.0; the pinned v4.32.1 does not have it), and NaN results follow
CompCert's `binop_nan`/`unop_nan`/`fma_nan` rules with the target's `Archi`
settings. The float↔integer conversions use the same model (`unpack` for
Flocq's `ZofB_range`, `normalize` + `pack` for `BofZ`). Everything is written
once, generically in the format, in `Floats.Gen`; `Float`/`Float32` only
instantiate it. Lean's built-in `Float`/`Float32` are not used by any
operation: their arithmetic is opaque to the kernel and its NaN payloads are
the host's. Everything reduces in the kernel; see
`examples/FloatConvCheck.lean` for `decide`-checked cases.

**Proof-carrying structures stay proof-carrying.** `Mem.mem` keeps CompCert's
three memory invariants. Lean's definitional proof irrelevance means
extensionality of memories needs no axiom.

External functions are uninterpreted, as they are in Rocq's `Events.v`: two
axioms, `externalFunctionsSem` and `inlineAssemblySem`, give them a meaning
without constraining it. The built-in external calls with a fixed semantics in
CompCert (`malloc`, `free`, `memcpy`, volatile loads and stores, annotations,
debug) are defined as in Rocq; named compiler builtins are treated as unknown
externals.

Deviations from the Rocq definitions are confined to three places and are
documented at their definitions: `PTree` is a plain three-constructor trie
rather than the canonical one; `composite` and `Genv.t` drop their `Prop`
invariants (the one invariant later needed, symbol injectivity, is recovered
as a theorem about `globalenv`); and `Program` stores a computed
`prog_comp_env` rather than a proof that it was computed.

## 4. The interpreter

CompCert has no executable Clight semantics (its reference interpreter runs
CompCert C, one level up). `CCLib/cfrontend/ClightExec.lean` provides one:

```lean
doStep : CGenv → State → Option (Trace × State)
```

together with a fuel-bounded runner that executes a whole program from
`main`. `DiffRun.lean` is the fixed driver the whole-program differential
tests (§8) use to run a generated program and print what `main` returned.

The interpreter is proved sound against the relation:

```lean
theorem doStep_sound : doStep ge s = some (t, s') → Step ge fe s t s'
```

across every step rule, via soundness lemmas for l-value and r-value
evaluation, `derefLoc`, `assignLoc`, `allocVariables`, `bindParameters` and
`functionEntry2`. Any run of the interpreter is therefore a witness for the
relation. Completeness (that the interpreter finds every step the relation
permits) is not proved; it is false as stated for external calls, which the
interpreter does not execute.

## 5. Determinism

`CCLib/common/Determinism.lean` is the analogue of CompCert's
`Clight.semantics_determinate`:

```lean
theorem step_determ (hfe : EntryDeterm fe) (hinj : SymbolsInjective …)
    (h1 : Step ge fe s t1 s1) (h2 : Step ge fe s t2 s2) :
    MatchTraces … t1 t2 ∧ (t1 = t2 → s1 = s2)
```

Two consequences are exported for use by the logic: `sstep_determ` (the
silent step relation is a partial function) and `starE0_endpoint_unique` (two
silent runs from the same state that both reach a stuck state reach the same
one). The second is what turns an existence proof of a run into a statement
about every run.

Determinism of the external-call rules rests on two further axioms,
`externalFunctionsSemDeterm` and `inlineAssemblySemDeterm`, mirroring the
`ec_determ` fields of CompCert's `extcall_properties`. They are used only where
an external call can occur, and the axiom set of every theorem in the
development has been checked to contain nothing else.

## 6. The program logic

### 6.1 The triple

The logic is a separation logic whose triple is *defined* as a statement about
`Step`. Informally,

> `Triple ge fe f P s R` holds when, for every heap fragment described by `P`,
> every frame disjoint from it, every memory realizing their union, and every
> continuation, executing `s` reaches an outcome whose fragment satisfies `R`
> and whose frame is unchanged.

Soundness is therefore by construction: nothing connects the logic to the
semantics except the definition, and `Steps.toStar` converts any triple back
into a `Star (Step ge fe)` execution. The triple is *total correctness*: it
asserts that a terminating execution exists, so a proof also proves
termination and the absence of undefined behaviour along the way.

Postconditions are a record of four assertions, one per way a Clight statement
can finish: fall through, `break`, `continue`, `return`, plus a fifth for
`goto` outcomes carrying the target label.

### 6.2 Assertions

`CCLib/logic/Heap.lean` and `CCLib/logic/SepLogic.lean` define heap fragments and the
assertion language:

- `emp`, pure facts `⌜φ⌝`, separating conjunction `∗`, existentials, with the
  usual BI laws (associativity, commutativity, unit);
- `mapsto chunk p b ofs v`: one cell of the given chunk, at permission `p`,
  holding `v`;
- `bytesPtsTo`, `anyBytes`, `undefBytes`: raw byte windows with known,
  unknown, or undefined contents, with append/split lemmas;
- `arrayOf elt stride ofs n`: an array of any element predicate at any stride,
  so arrays of structs and multi-dimensional arrays are nested instances;
  `arrayU8`, `arrayU16`, `arrayU32` are the scalar instances. `arrayOf_split`
  is an equality (it also joins), and `arrayOf_update` is the write pattern;
- `structAt` / `fieldsAt`, with `fieldsAt_split` to pull one field out as the
  frame for an access, and `field_offset` computed from the generated
  composite environment by `decide`;
- `unionAt`: a union owning its whole footprint;
- `funcPtrAt`: a cell holding a pointer to a named function.

Ownership is unique: one permission per byte, no fractions. A caller lends a
buffer to a callee and gets it back in the postcondition.

### 6.3 Rules

`CCLib/logic/SepHoare.lean` proves one rule per statement form plus the structural
rules:

| Group | Rules |
|---|---|
| Structural | `conseq`, `exists`, `frame`, `vacuous`, `fallthrough` |
| Statements | `skip`, `set`, `assign`, `assign_copy` (struct copy), `seq`, `if` / `if_true` / `if_false`, `switch` / `switch_const`, `loop`, `break`, `continue`, `return` / `return_none`, `label`, `goto` |

`assign` (and the `deref`/`field`/`union` read lemmas) take an extra argument
`hw : Mem.ChunkNoWrap chunk ofs`: CompCert's `Mem.loadv`/`storev` reject an
access that would wrap past the end of the address space, and the argument
says this cannot happen. It defaults to `by exact Or.inl rfl`, which closes it
automatically for every chunk except `Mfloat64`/`Many64` (8 bytes, only
4-byte aligned); for those, prove `ofs + 8 ≤ Ptrofs.modulus`.

The loop rule carries a `Nat` measure that must strictly decrease on every
iteration, so it proves termination together with the invariant. Loop
invariants and measures are supplied by hand, as in VST.

### 6.4 Function specifications and calls

`CCLib/logic/Funspec.lean` defines `FunSpec` (argument types, heap-only pre- and
postcondition, and a well-founded measure on the arguments) and the call rule
`triple_call`. A callee's specification is heap-only, so it cannot refer to the
caller's local state; the frame rule carries everything the caller does not
lend.

Recursion is handled by the measure rather than by step-indexing: the call
rule may invoke a callee only at arguments whose measure is strictly smaller,
and the whole-program theorem `closure` proves that a table of specifications
all of whose bodies are verified under that discipline is met by every
function in the table. Because the measure is global, mutual recursion is
covered.

Function entry and exit are covered end to end (`CCLib/logic/Locals.lean`): entering
a function with address-taken locals yields ownership of their fresh,
all-undefined footprint; individual fields are carved out of it as writable
`mapsto`s; and returning frees the block, with ownership being what makes the
free succeed. `satisfies_internal_noVars` (no address-taken locals) and
`satisfies_internal` (with them) turn a body triple into a `FunSpec` being
satisfied.

`CCLib/logic/FunPtr.lean` covers calls through function pointers in the three
shapes `clightgen -normalize` emits: a global name, a pointer held in a
temporary, and `(*p)(…)` through a dereference. Function code is not a
resource, so an indirect call composes with the frame rule with no extra
machinery, and higher-order specifications (a caller correct for *any* callee
meeting a spec) are expressible.

`goto` is supported in both directions. A forward `goto` to a label whose
continuation falls through or returns is handled by `satisfies_internal_goto`
and its `_lands` / `_seq` variants, covering labels at the end of a function
body and labels at the head of a sequence. A backward `goto` (a loop with no
`Sloop`) is handled by `satisfies_internal_goto_measure`, whose goto-assertion
carries a `Nat` measure that must decrease before the label is re-entered.

### 6.5 Local state and automation

`CCLib/logic/Temps.lean` represents the temporaries a proof tracks as a list, so
stepping over an assignment re-establishes the whole list with one lemma
whose side condition (distinctness of identifiers) is discharged by `decide`.
The cost of a statement is constant in the number of tracked temporaries.
Identifiers are kernel-reducible, which
is what makes `decide` sufficient here and for every composite-environment
fact.

`CCLib/logic/Tactics.lean` provides `sep_cancel` (entailment between `∗`-chains, by
normalising both sides to a canonical order) and forward-shaped rules
(`triple_set_fwd`, `setLocal`) that compute a statement's postcondition from
its precondition, so a straight-line block is proved by chaining `refine`s
with the intermediate assertions fixed by unification. There is no frame
inference and no automatic invariant discovery.

### 6.6 Linking

`clightgen` emits one module per translation unit. `CCLib/common/Linking.lean` merges
several generated `Program`s into one, following CompCert's `link_fundef` /
`link_def`: an `extern` declaration resolves against a definition in another
unit, matching externals merge, duplicate definitions are a conflict, and the
composite environment is rebuilt from the merged composites. Cross-module
calls then resolve through `Genv.findFunct` to internal bodies, so `closure`
applies to a multi-file program.

### 6.7 The original Hoare logic

`CCLib/logic/Hoare.lean`, with `HoareArray.lean` and `HoareLong.lean`, is the
non-separating logic that preceded the above. It has the same triple shape
without a frame, fifteen rules, and 32-bit and 64-bit arithmetic bridges.

## 7. Examples

`examples/` holds small C programs exported with `clightgen -lean` (the `Gen*`
modules, with their sources under `test/lean/`) and proofs about them. They are
built by default, so they double as regression tests for the library, and they
are the templates to copy when verifying a new function. Each proof begins with
a `rfl` check that the AST it reasons about is the one `clightgen` produced.

| Proof | C shape | What it establishes |
|---|---|---|
| `IsSortedReal` | `is_sorted` over an array | full call-to-return execution against `Step`, for every sorted array (Hoare logic) |
| `IsSortedSep` | same function | meets a `FunSpec`; callable via `triple_call` with the frame rule |
| `SwapSep` | `swap(int *a, int *b)` | writes through two separately owned cells; each write leaves the other alone |
| `StructSep` | `p->x` on a two-field struct | field read via `structAt` / `fieldsAt_split`, offsets by `decide` |
| `StructCopySep` | `*dst = local_struct` | the `By_copy` assignment rule on a three-field packed struct |
| `LocalVarSep` | stack-allocated struct passed by address to a callee | entry/exit ownership transfer, writes into a fresh local, abstract callee |
| `FuncPtrSep` | `apply(g, x)`, `(*o->fp)(x)` | higher-order spec correct for any callee; call through a struct field; instantiated at a concrete callee |
| `GotoSep` | loop exiting to a top-level cleanup label | forward `goto` through `if` inside `loop` inside `seq` |
| `GotoBackSep` | loop built from a backward `goto` | measure-indexed backward jump, no `Sloop` |
| `U16LoopSep` | `for (len = 0; len <= 15; len++) count[len] = 0` | array initialisation with an "initialised prefix ∗ undefined suffix" invariant |
| `OOBSep` | `return a[9]` on a nine-element array | **negative control**: the out-of-bounds read is *not* provable safe, and the obligation that blocks it is refuted |

The negative control matters because the triple is total correctness: an
out-of-bounds access has no step in the semantics, so no triple for it can be
proved. `OOBSep.lean` shows the framework notices, that the failing obligation
is false rather than merely unproven, and that the caller's ownership provably
does not cover the byte read. CompCert's own interpreter rejects the same
program as undefined behaviour.

The `*Check` modules apply the library's theorems to concrete data, see §8.

## 8. Validation

Nothing in this port is covered by CompCert's compiler-correctness theorem,
so it is validated independently at four levels.

**Operation-level differential testing.** `test/lean/diff_all.sh` compares
the Lean definitions against CompCert's own Rocq code, evaluated with
`Compute`, or against its OCaml extraction where Rocq cannot compute:

| Level | Oracle | Agreeing observations |
|---|---|---|
| Integers | Rocq `Compute` on `lib/Integers.v` | 24,880 |
| Values + Memdata | Rocq `Compute` | 37,729 |
| Ctypes + Cop | Rocq `Compute` | 8,503 |
| Memory | OCaml extraction | 110 |

**Whole-program differential testing.** `test/lean/diff_exec.sh` runs C
programs under `ccomp -interp` and under `clightgen -lean` plus the Lean
interpreter, and compares the value `main` returns. The corpus is 16
hand-written programs, each targeting one language area (signed and unsigned
arithmetic, division corners, shifts, conversions, loops with `break` /
`continue`, `switch` fall-through and `goto`, pointers, structs by value,
unions, arrays of structs, 2-D arrays, linked lists, recursion, globals, 64-bit
arithmetic, floating point, bitfield read and read-modify-write), plus 500
programs from `gen_random_c.py`, a generator that produces programs free of
undefined behaviour by construction. All 516 agree. The floating-point program
agrees exactly, including a 20-term harmonic sum with repeated rounding; it is
the end-to-end evidence for the IEEE substitution in §3.

**The soundness theorem** (§4) ties the interpreter to the relation, so a
discrepancy between the two Lean artifacts is impossible.

**Non-vacuity checks.** The `*Check` modules in `examples/` apply the
library's theorems to concrete data, so none of them holds only because its
premises are unsatisfiable:

- `MemCheck`: each memory lemma computed at a concrete memory, by `decide`,
  including that a store at one offset leaves another untouched;
- `SepCheck`: the closure theorem used to close self- and mutual recursion;
- `DetermCheck`: determinism applied to derivable steps, and the axiom guard
  for the whole development;
- `TempsCheck`: the constant-cost claim for tracked temporaries, at twenty.

These checks rely on the Lean memory model being executable. CompCert's own
`Mem.store` / `Mem.load` cannot be evaluated by Rocq's `Compute`, so the same
checks cannot be run against the Rocq definitions.

**Axiom footprint.** `#print axioms` on any theorem in the development reports
Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`) plus, where
an external call can occur, the two uninterpreted-external axioms CompCert
itself declares and, for determinism results, their two `ec_determ`
counterparts. The memory lemma library is axiom-free beyond the standard
three. `bv_decide` is not used anywhere, because it discharges through a
native-evaluation axiom.

## 9. Trusted base and scope

- **No link to CompCert's compiler-correctness theorem.** That theorem lives in
  Rocq and does not transfer to a hand port. A Lean proof here is a statement
  about the Clight semantics of the source, not about generated machine code.
  The Rocq + VST path remains the one that ends at assembly.
- **Trusted:** the `clightgen` frontend (shared with the Rocq path), the
  transcription fidelity of the port (mitigated by §8), the IEEE floating-point
  substitution, and Lean itself.
- **External calls** have no specifications. `malloc`, `free`, `memcpy` and
  other library functions must be given axiomatised specs before a program
  that calls them can be verified.
- **Not covered:** fractional permissions, the magic wand, frame inference,
  automatic invariant discovery, volatile accesses (all verified executions
  are silent), diverging programs (the logic is total correctness),
  interpreter completeness, and `-csyntax` output in Lean.
- **Memory model restriction:** heap fragments carry one permission per byte,
  which assumes CompCert's `Cur` and `Max` permissions coincide. Every
  operation in the memory model preserves this except `dropPerm`, which only
  global initialisation uses.

## 10. Building and running

**Build `clightgen`.** Use the dedicated opam switch (OCaml 4.14.2, Rocq
9.1.0):

```
eval $(opam env --switch=compcert-4.14)
./configure -clightgen aarch64-macos
make -j proof && make extraction && make clightgen
make ccomp                                  # oracle for diff_exec.sh
```

**Build the Lean side** (Lean 4.32.1, pinned in the repository-root
`lean-toolchain`). The only Lake project is the one at the repository root
(`lakefile.toml`, with `export/` as source directory); run `lake` from there:

```
lake build
```

**Run the validation suites** (with the opam switch active):

```
bash test/lean/check.sh          # clightgen -lean on every test program, then typecheck
bash test/lean/diff_all.sh       # the four operation levels
bash test/lean/diff_exec.sh      # whole programs against ccomp -interp
```

**Verify a C function.** Export it with `clightgen -lean -normalize`, import
the generated module and `CCLib`, `open` the generated namespace, state a
`FunSpec`, and prove the body with the rules of §6. The proofs in `examples/`
are the templates: `SwapSep` for pointer writes, `StructSep` for field access,
`LocalVarSep` for stack locals and calls, `U16LoopSep` for loops over arrays,
`FuncPtrSep` for calls through function pointers.
