/-
  Build note (see `MODULE_AUDIT.md` and `MISSING_MODULES.md` at the repository
  root).  Lines of the form
    `-- missing (to port): import M` name a module that should exist (it has a
      Rocq/OCaml counterpart) but whose source file is not in this checkout;
    `-- blocked: import M` name a present module that depends on such a module.
  Restore the `import` once the module is ported.  Modules that should not
  exist in the Lean port (Flocq, extraction, per-target copies of the back end,
  duplicates of Lean core / Mathlib) are not listed.

  `CCLib` — Phase 0 foundations for a CompCert-grade Clight semantics in Lean.

  * `CCLib.aarch64.Archi`    — target parameters (port of `<arch>/Archi.v`)
  * `CCLib.lib.Integers` — machine integers on `BitVec` (substitutes `lib/Integers.v`
                       + `lib/Zbits.v`).  Validated against CompCert's Rocq
                       implementation by `test/lean/int_diff.sh` (24,880 cases).
  * `CCLib.lib.IntegersLemmas`, `CCLib.lib.IntegersBits`, `CCLib.lib.IntegersShifts` —
                       the theorems of `lib/Integers.v`, generic in the word
                       size; `CCLib.lib.IntegersInt`/`IntegersInt64`/`IntegersPtrofs`
                       restate them for each module under CompCert's names;
                       `CCLib.lib.IntegersPow2` adds powers of two, rotations
                       (`rolm`) and signed division by `2^n` (`shrx`).
  * `CCLib.lib.FloatModel` — exact IEEE-754 reference model (backport of Lean
                       core's `Float.Model`); `CCLib.lib.FloatModelLemmas` adds the
                       pack/unpack lemmas (from core and Batteries).
  * `CCLib.lib.Floats`   — `lib/Floats.v`: binary32/64 by bit pattern, every
                       operation computed exactly (model + CompCert's aarch64
                       NaN rules); replaces Flocq.  `CCLib.lib.FloatsLemmas` has the
                       `Floats.v` theorems proved so far.

  Phase 1 — values and the memory model:

  * `CCLib.lib.Positive` — Coq's `positive`; `ident`, `block`, and the string↔ident
                       encoding from `export/Ctypesdefs.v`.
  * `CCLib.lib.Maps`     — `PTree` / `PMap` / `ZMap` (port of `lib/Maps.v` core);
                       `CCLib.lib.MapsTheory` adds `remove`/`map`/`filter1`/
                       `combine`/`elements`/`fold` and their theorems.
  * `CCLib.common.AST`      — `common/AST.v`: value types, chunks, signatures,
                       external functions, global definitions;
                       `CCLib.common.ASTTheory` adds the rest of the file: generic
                       programs, `prog_defmap`, `transform_program`,
                       `transform_partial_program(2)`, `rpair`, builtin
                       arguments and the type/chunk lemmas.
  * `CCLib.common.Values`   — `common/Values.v`: the `Val` type and its operations;
                       `CCLib.common.ValuesLemmas` adds their algebraic and comparison
                       laws, `lessdef` and value injections;
                       `CCLib.common.ValuesOps` the remaining (backend) operations,
                       `CCLib.common.ValuesTheory`/`CCLib.common.ValuesInject` the remaining
                       theorems of the file.
  * `CCLib.common.Memdata`  — `common/Memdata.v`: `MemVal`, `encodeVal`/`decodeVal`;
                       `CCLib.common.MemdataTheory`/`CCLib.common.MemdataEncode` the remaining
                       chunk, byte-encoding, `decode_encode_val` and shape lemmas.
  * `CCLib.common.Memory`   — `common/Memory.v` operational core: the proof-carrying
                       `Mem` record with load/store/alloc/free/perm;
                       `CCLib.common.MemoryTheory` adds block-validity, `nextblock`
                       and success-condition theorems for every operation;
                       `CCLib.common.MemoryUnchanged` (`unchanged_on`),
                       `CCLib.common.MemdataInject` (`memval_inject`),
                       `CCLib.common.MemoryInject` (`mem_inj`),
                       `CCLib.common.MemoryExtends` (`Mem.extends`) and
                       `CCLib.common.MemoryInjections` (`Mem.inject`,
                       `Mem.inject_neutral`) and `CCLib.common.MemoryDrop`
                       (`drop_perm`, `disjoint_or_equal_inject`, ...) port
                       the memory relations.

  Phase 2 — types and operators:

  * `CCLib.cfrontend.Ctypes`   — `cfrontend/Ctypes.v`: the C type syntax plus its layout
                       semantics (`sizeof`, `alignof`, `fieldOffset`,
                       `accessMode`, `buildCompositeEnv`);
                       `CCLib.cfrontend.CtypesTheory` adds the size, alignment and
                       field-layout theorems and `buildCompositeEnv_wf`.
  * `CCLib.cfrontend.Cop`      — `cfrontend/Cop.v`: `semCast`, `boolVal`,
                       `semUnaryOperation`, `semBinaryOperation`;
                       `CCLib.cfrontend.CopInject` proves they commute with memory
                       injections (`GENERIC_INJECTION`), and
                       `CCLib.cfrontend.CopTheory` adds `val_casted` and the cast lemmas;
                       `CCLib.cfrontend.CopArith` the ISO C arithmetic conversions
                       and `cast_bool_bool_val`.

  Phase 3 — the semantics:

  * `CCLib.common.Globalenvs` — `common/Globalenvs.v`: `Genv`, symbol/function lookup,
                       and `init_mem`'s allocation of globals;
                       `CCLib.common.GlobalenvsTheory` adds the lookup theorems and
                       proof principles, `CCLib.common.GlobalenvsInitMem` the
                       `init_mem` theorems; `CCLib.cfrontend.ClightGlobalenv`
                       instantiates them for Clight programs;
                       `CCLib.common.GlobalenvsTransf` ports `match_program` and the
                       `MATCH_PROGRAMS`/`TRANSFORM_*` sections (lookups, symbol
                       environments and `init_mem` of transformed programs).
  * `CCLib.common.LinkingTheory`, `CCLib.common.LinkingMatch` — `common/Linking.v`: the
                       `Linker` class and its instances, `link_prog`,
                       `match_program_gen` with linking contexts,
                       `link_match_program`, `TransfLink`, `link_list` and pass
                       composition; `CCLib.cfrontend.CtypesLinking` — the linking part
                       of `Ctypes.v` (composite definitions,
                       `link_build_composite_env`, the Clight program linker).
  * `CCLib.common.Builtins` — `Builtins0/1.v`, `Builtins.v`: the standard built-in
                       table with typing and injection proofs.
  * `CCLib.common.Events`   — `common/Events.v` (minimal slice): traces, volatile
                       accesses, and the `malloc`/`free`/`memcpy` builtins;
                       `CCLib.common.EventsMem` proves the memory fields of
                       `extcall_properties` for every defined builtin, and
                       `CCLib.common.EventsExtends` proves `ec_mem_extends`,
                       `CCLib.common.EventsInject` proves `ec_mem_inject`, and
                       `CCLib.common.EventsProps` proves `ec_well_typed` and
                       `ec_symbols_preserved`, `CCLib.common.EventsReceptive`
                       proves `ec_receptive`.
  * `CCLib.cfrontend.Clight`   — `cfrontend/Clight.v`: the Clight AST *and* its small-step
                       operational semantics (`DerefLoc`/`AssignLoc`,
                       `EvalExpr`/`EvalLvalue`, continuations, `Step`,
                       `InitialState`/`FinalState`), plus `star`/`plus`.

  Phase 4 — the executable semantics:

  * `CCLib.cfrontend.ClightExec` — an interpreter (`doStep`, `run`, `runProgram`) plus its
                       soundness against the relation.  CompCert has no
                       executable Clight semantics, so this has no Rocq original.
  * `CCLib.cfrontend.ClightExecSound` — soundness of the interpreter against the relation.

  * `CCLib.common.Determinism` — `Clight.semantics_determinate`: the step relation is a
                       partial function up to `MatchTraces`, so ∀-run facts
                       follow from ∃-run ones.  Adds two axioms (see the file).

  Phase 5 — whole-program behaviours:

  * `CCLib.common.Smallstep` — generic transition systems (`common/Smallstep.v` core):
                       `star`/`plus`/`starN`, `nostep`, infinite traces,
                       `forever_silent`/`forever_reactive`, `semantics`, `safe`.
  * `CCLib.common.Behaviors` — `common/Behaviors.v` (first half): program behaviours
                       and `program_behaves_exists`.
  * `CCLib.common.BehaviorsAtomic` — `common/Behaviors.v`, section `ATOMIC`: `atomic_behaviors`.
  * `CCLib.cfrontend.ClightBehaviors` — `Clight.semantics1/2` as `Smallstep.Semantics`,
                       their determinacy, and the existence of behaviours;
                       `CCLib.cfrontend.ClightReceptive` proves `semantics_receptive`.
  * `CCLib.common.Simulation` — forward simulations (`Smallstep.v`): the record, the
                       step/plus/star/opt constructors, composition, and their
                       preservation of behaviours (`Behaviors.v`).
  * `CCLib.common.BackwardSimulation`, `CCLib.common.ForwardToBackward` — backward
                       simulations and `forward_to_backward_simulation`.
  * `CCLib.common.Bigstep`  — `forever` (infinite runs), `bigstep_semantics`,
                       `bigstep_sound`, `forever_silent_or_reactive` and the
                       `behavior_bigstep_*` theorems (`Smallstep.v`/`Behaviors.v`).
  * `CCLib.cfrontend.ClightBigstep` — `cfrontend/ClightBigstep.v`: the big-step
                       semantics of Clight (terminating and, coinductively,
                       diverging) and `bigstep_semantics_sound`.

  Phase 6 — CompCert C:

  * `CCLib.cfrontend.Csyntax`  — `cfrontend/Csyntax.v`: expressions with side effects,
                       statements, functions and programs (namespace
                       `CC.Csyntax`), plus `Cop.incr_or_decr`/`incrdecr_type`.
  * `CCLib.cfrontend.Csem`     — `cfrontend/Csem.v`: the nondeterministic reduction
                       semantics (head reductions, reduction contexts,
                       `imm_safe`, `estep`/`sstep`, `semantics`) and
                       `semantics_single_events` (namespace `CC.Csem`).
  * `CCLib.cfrontend.Cstrategy` — `cfrontend/Cstrategy.v` (whole file): simple
                       expressions and their big-step evaluation, left
                       contexts, the compiler's deterministic evaluation
                       strategy (`estep`, `semantics`), `context_compose`,
                       safe states, `expr_kind`, `eval_simple_*_steps`;
                       `CCLib.cfrontend.CstrategyInversion` the inversion lemmas
                       (`invert_expr_prop`, `imm_safe_inv`, `safe_inv`);
                       `CCLib.cfrontend.CstrategyDecompose` the decomposition of safe
                       expressions; `CCLib.cfrontend.CstrategySimulation`
                       `estep_simulation`, `can_estep`;
                       `CCLib.cfrontend.CstrategyBackward` `progress` and
                       `strategy_simulation` (backward simulation between
                       `Csem.semantics` and `Cstrategy.semantics`);
                       `CCLib.cfrontend.CstrategyReceptive`
                       `semantics_strongly_receptive`;
                       `CCLib.cfrontend.CstrategyBigstep` the big-step semantics
                       (`eval_expr`, `exec_stmt`, `eval_funcall`,
                       `evalinf_*`, `execinf_stmt`, `bigstep_semantics`);
                       `CCLib.cfrontend.CstrategyBigstepSound` `bigstep_to_steps`,
                       `evalinf_funcall_steps`, `bigstep_semantics_sound`.
  * `CCLib.common.SmallstepAtomic` — `Smallstep.v`: `well_behaved_traces`,
                       `strongly_receptive`, `atomic`, `atomic_receptive`
                       (and `Events.output_event`/`output_trace`).
  * `CCLib.cfrontend.Initializers` — `cfrontend/Initializers.v`: compile-time
                       evaluation of initializers (`constval`,
                       `transl_init`, `transl_init_single`, …);
                       `CCLib.cfrontend.InitializersproofSimple` the first part of
                       `Initializersproof.v`: big-step evaluation of simple
                       expressions, `eval_simple_steps`, and soundness of
                       `constval` (`constval_rvalue`, `constval_steps`);
                       `CCLib.cfrontend.InitializersproofState` and
                       `CCLib.cfrontend.InitializersproofMatch` the correctness of the
                       operations over initialization states (`match_state`,
                       `store_data_correct`, `load_int_correct`,
                       `init_data_list_of_state_correct`), and
                       `CCLib.cfrontend.Initializersproof` the rest of the file, ending
                       in `transl_init_sound`.  They use
                       `CCLib.common.GlobalenvsBytes` (`Globalenvs.v`:
                       `bytes_of_init_data`, `readbytes_as_zero`,
                       `store_init_data_list_loadbytes`) and
                       `CCLib.common.MemoryBytes` (`Memory.v`: `loadbytes_concat`,
                       `loadbytes_split`, `loadbytes_load`,
                       `loadbytes_store_same`, …).
  * `CCLib.cfrontend.Ctyping`  — first part of `cfrontend/Ctyping.v`: operations
                       over types, the typing rules (`wt_rvalue`,
                       `wt_lvalue`, `wt_stmt`, `wt_program`, …) and the
                       type-checker (`retype_expr`, `retype_stmt`,
                       `typecheck_program`); `CCLib.cfrontend.CtypingSound` its
                       soundness (`retype_expr_sound`, `retype_stmt_sound`,
                       `typecheck_program_sound`).
  * `CCLib.cfrontend.CtypingPreservation`, `CCLib.cfrontend.CtypingSubjectReduction` — the
                       subject-reduction half of `Ctyping.v`: operators,
                       memory reads and head reductions preserve typing
                       (`pres_sem_binop`, `wt_deref_loc`, `wt_rred`, …),
                       typing of contexts, continuations and states,
                       `preservation` and `wt_initial_state`.
  * `CCLib.common.Worlds`   — the "worlds" part of `common/Determinism.v`: an
                       external world as a state machine answering I/O and
                       volatile accesses, `possible_event`/`possible_trace`.
  * `CCLib.common.SimulationDeterm` — `common/Smallstep.v`, sections
                       `FORWARD_SIMU_EVENTUALLY(_PLUS)`, `DETERMINACY`,
                       `FORWARD_SIMU_DETERM(_DIAGRAMS)`: `forward_simulation_eventually`,
                       `star_determinacy`, `forward_simulation_determ{,_star,_plus,_one}`.
  * `CCLib.common.DeterminismSem` — the rest of `common/Determinism.v`:
                       `possible_traceinf`, `match_possible_traces`,
                       `sem_deterministic`, `program_behaves_deterministic`,
                       `world_sem` and `world_sem_deterministic`.
  * `CCLib.common.SmallstepForever` — `common/Smallstep.v`: `forever_N`,
                       `forever_plus`, `forever_silent_N` and their equivalence
                       with `forever`/`forever_silent`.
  * `CCLib.common.EventsTraceinf` — the `traceinf` part of `common/Events.v`:
                       `traceinf_sim`, `traceinf_sim'`, `traceinf'`, prefixes.
  * `CCLib.driver.ComplementsSeparate` — `driver/Complements.v`, section
                       `SEPARATE_COMPILATION`.
  * `CCLib.cfrontend.Cexec`    — `cfrontend/Cexec.v`: the reference interpreter for
                       CompCert C (`step_expr`, `do_step`, `do_initial_state`,
                       `at_final_state`); external calls go through an
                       explicit oracle (`ExtOracle`).  `CCLib.cfrontend.CexecEvents`
                       proves the memory/event helpers sound and complete,
                       `CCLib.cfrontend.CexecExpr`/`CCLib.cfrontend.CexecExprSound` the soundness
                       of `step_expr`, `CCLib.cfrontend.CexecComplete` its completeness
                       (`step_expr_context`, `not_imm_safe_t`), and
                       `CCLib.cfrontend.CexecStep` `do_step_sound`/`do_step_complete`.
  * `CCLib.cfrontend.SimplExpr` — `cfrontend/SimplExpr.v`: the first compiler pass,
                       CompCert C → Clight (pulling side effects out of
                       expressions, introducing fresh temporaries) with its
                       state-and-error monad; `CCLib.cfrontend.SimplExprspec` the
                       relational specification of `SimplExprspec.v`
                       (`tr_expr`, `tr_stmt`, `tr_function`, …), and
                       `CCLib.cfrontend.SimplExprspecCorrect`/`CCLib.cfrontend.SimplExprspecMain`
                       the proof that the translation meets it
                       (`transl_meets_spec`, `transl_stmt_meets_spec`,
                       `transl_function_spec`, `transl_fundef_spec`).
  * `CCLib.cfrontend.SimplExprproofEnv`/`Context`/`Smart`/`Match`/`Estep`/`Step` —
                       `cfrontend/SimplExprproof.v`: semantic preservation
                       of `SimplExpr` (`transl_program_correct`, a forward
                       simulation from `Cstrategy.semantics` to
                       `Clight.semantics1`).
  * `CCLib.cfrontend.SimplLocals` — `cfrontend/SimplLocals.v`: the second compiler
                       pass (Clight → Clight), turning scalar local variables
                       whose address is never taken into temporaries.
  * `CCLib.cfrontend.SimplLocalsproofEnv`/`Alloc`/`Expr`/`Match`/`Step` —
                       `cfrontend/SimplLocalsproof.v`: semantic preservation
                       of SimplLocals, ending in `transf_program_correct`
                       (forward simulation `semantics1 prog` →
                       `semantics2 tprog`).
  * `CCLib.backend.Cminor`   — syntax, states and operators of `backend/Cminor.v`
                       (`eval_constant`, `eval_unop`, `eval_binop`).
  * `CCLib.cfrontend.Csharpminor` — syntax of `cfrontend/Csharpminor.v`.
  * `CCLib.cfrontend.Cshmgen`  — `cfrontend/Cshmgen.v`: the third compiler pass,
                       Clight → Csharpminor.
  * `CCLib.cfrontend.Cminorgen` — `cfrontend/Cminorgen.v`: the fourth compiler pass,
                       Csharpminor → Cminor (stack layout of address-taken
                       locals, compilation of `switch`).
  * `CCLib.cfrontend.CminorgenproofEnv`/`Alloc`/`Expr`/`Match`/`Step` —
                       `cfrontend/Cminorgenproof.v`: semantic preservation
                       of Cminorgen, ending in `transl_program_correct`.
  * `CCLib.driver.FrontendCorrect` — the front end of `driver/Compiler.v`
                       (`transfCFrontend`, CompCert C → Cminor) and its
                       correctness `transfCFrontend_correct`, composing the
                       four simulations above; `transfCProgram_eq` splits the
                       whole compiler into front end and back end.
  * `CCLib.aarch64.Conventions1` — `return_value_needs_normalization` and
                       `parameter_needs_normalization` of
                       `aarch64/Conventions1.v`.
  * `CCLib.common.Switch`   — `switch_target`, `switch_argument` of `common/Switch.v`.
  * `CCLib.common.DetermTac` — the `determ_using` tactic used by the determinism
                       proofs of the intermediate languages.
  * `CCLib.backend.CminorSem` — small-step semantics of Cminor (`backend/Cminor.v`):
                       `eval_expr`, `step`, `semantics`, receptiveness and
                       determinacy.
  * `CCLib.backend.CminorBigstep` — big-step semantics of Cminor
                       (`backend/Cminor.v`): `exec_stmt`/`eval_funcall`,
                       `execinf_stmt`/`evalinf_funcall` and
                       `bigstep_semantics_sound`.
  * `CCLib.cfrontend.CsharpminorSem` — small-step semantics of Csharpminor
                       (`cfrontend/Csharpminor.v`), receptiveness and
                       determinacy.
  * `CCLib.aarch64.Op`       — `aarch64/Op.v`: machine operators, conditions and
                       addressing modes, their evaluation and typing.
  * `CCLib.backend.CminorSel` — `backend/CminorSel.v`: Cminor after instruction
                       selection (syntax, semantics, `lift`, `bind_exprs`).
  * `CCLib.common.EventsBuiltinArgs` — `eval_builtin_arg(s)` of `common/Events.v`.
  * `CCLib.backend.RTL`      — `backend/Registers.v` and `backend/RTL.v`: the RTL
                       language, its semantics, receptiveness and determinacy.
  * `CCLib.backend.RTLgen`   — `backend/RTLgen.v`: the CminorSel → RTL pass.
  * `CCLib.aarch64.Machregs` — `aarch64/Machregs.v`: machine registers `Mreg`.
  * `CCLib.backend.Locations` — `backend/Locations.v`: locations, slots, `Locmap`.
  * `CCLib.backend.Conventions` — `aarch64/Conventions1.v` + `backend/Conventions.v`.
  * `CCLib.lib.Postorder` — `backend/Postorder.v`: postorder numbering of CFGs.
  * `CCLib.backend.Tailcall` — `backend/Tailcall.v`: tail-call recognition (RTL → RTL).
  * `CCLib.backend.Renumber` — `backend/Renumber.v`: CFG renumbering (RTL → RTL).
  * `CCLib.backend.LTL` — `backend/LTL.v`: LTL syntax and semantics.
  * `CCLib.backend.Linear` — `backend/Linear.v`: Linear syntax and semantics.
  * `CCLib.backend.Mach` — `backend/Mach.v`: Mach syntax, semantics, `wf_step`.
  * `CCLib.lib.UnionFind` — `lib/UnionFind.v`: persistent union-find over positives.
  * `CCLib.backend.Tunneling` — `backend/Tunneling.v`: branch tunneling (LTL → LTL).
  * `CCLib.lib.Lattice` — `lib/Lattice.v`: `SEMILATTICE` class and `LBoolean`.
  * `CCLib.lib.Ordered` — `lib/Ordered.v`: the `OrderedType` class with instances for
                       positives, integers, machine integers, indexed types and pairs.
  * `CCLib.common.Subtyping` — `common/Subtyping.v`: solver for subtyping constraints
                       (`TypeAlgebra`, `SubSolver`) with `solve_sound` and `solve_complete`.
  * `CCLib.common.Memtype` — `common/Memtype.v`: abstract memory-model interface
                       (`MemOps` operations and the `MEM` specification class,
                       split as `MEMCore` + `alloc_left_mapped_inject`);
                       `CCLib.common.MemoryMemtype` shows that the concrete memory is
                       an instance of `MEMCore` but not of `MEM`;
                       `CCLib.common.MemoryAxioms` has the `Memory.v` theorems it needs.
  * `CCLib.lib.FSetAVL` — finite sets as AVL trees (the Rocq standard library's
                       `FSetAVL`/`MSetAVL`, included by `lib/FSetAVLplus.v`).
  * `CCLib.lib.FSetAVLplus` — `lib/FSetAVLplus.v`: `mem_between`, `elements_between`,
                       `for_all_between`, `partition_between` with their specifications.
  * `CCLib.backend.SplitLong` — `backend/SplitLong.vp`: selection of 64-bit operations
                       as pairs of 32-bit ones (32-bit targets), on the aarch64 operators;
                       `CCLib.backend.SplitLongproof` and `CCLib.backend.SplitLongproof2`
                       prove its constructors correct (all but `longofsingle` /
                       `longuofsingle`).
  * `CCLib.lib.Parmov` — `lib/Parmov.v`: compilation of parallel moves into sequential
                       moves, with `parmove_correctness`, `parmove2_correctness` and
                       `parmove2_correctness_with_overlap`.
  * `CCLib.backend.Kildall` — `backend/Kildall.v` + `PrimIter`: forward/backward dataflow solvers and their correctness theorems.
  * `CCLib.backend.Linearize` — `backend/Linearize.v` (+ `Linearizeaux.ml` heuristic): LTL → Linear.
  * `CCLib.backend.CleanupLabels` — `backend/CleanupLabels.v`: unused-label removal (Linear → Linear).
  * `CCLib.powerpc.Builtins1` — `powerpc/Builtins1.v` (with both `builtin_sem`
                       obligations proved).  `arm/Builtins1.v` declares no built-in, like
                       aarch64's: it is the `PlatformBuiltin` of `CCLib.common.Builtins`.
  * `CCLib.arm.PrintOp`, `CCLib.powerpc.PrintOp` — `arm/PrintOp.ml`, `powerpc/PrintOp.ml`
                       (checked in `examples/PrintOpCheck.lean`).
  * `CCLib.arm.*`, `CCLib.powerpc.*` — the ARM and PowerPC back ends up to instruction
                       selection: `Op` (+ `OpTheory` for the lemmas of `Op.v`), `Machregs`,
                       `Locations`, `Conventions1` (all lemmas), `Conventions`, `Bounds`
                       (frame part), `Stacklayout` (all lemmas), `CombineOp`, `NeedOp` and
                       `ValueAOp` (with their soundness theorems), `ConstpropOp`,
                       `CminorSel`, `SelectOp`, `SplitLong`, `SelectLong`.  The value layer
                       is 64-bit, so pointer arithmetic on these 32-bit targets yields
                       `Vundef` (see `PORT_GAP_ANALYSIS.md`).  Proofs: `CombineOpproof`,
                       `ConstpropOpproof`, `SelectOpproof`, `SplitLongproof` and
                       `SelectLongproof` (PowerPC: `SelectLongproof` + `SelectLongproof2`, both
                       configurations of `Archi.ppc64`).  `Mach` (syntax and semantics,
                       instantiated with the target operators and conventions) and `Asm`
                       (instruction set and semantics, target parameters as arguments).
-/
import CCLib.aarch64.Archi
import CCLib.lib.Positive
import CCLib.lib.Integers
import CCLib.lib.IntegersLemmas
import CCLib.lib.IntegersBits
import CCLib.lib.IntegersShifts
import CCLib.lib.IntegersShiftsExtra
import CCLib.lib.IntegersInt
import CCLib.lib.IntegersInt64
import CCLib.lib.IntegersPtrofs
import CCLib.lib.FloatModel
import CCLib.lib.FloatModelLemmas
import CCLib.lib.Floats
import CCLib.lib.FloatsLemmas
import CCLib.lib.FloatsConv
import CCLib.lib.IEEE754_extra
import CCLib.lib.FloatsDecomp
import CCLib.lib.FloatsSingle
import CCLib.lib.FloatsLong
import CCLib.lib.Maps
import CCLib.common.AST
import CCLib.common.Values
import CCLib.common.ValuesLemmas
import CCLib.common.Memdata
import CCLib.common.MemdataInject
import CCLib.common.Memory
import CCLib.cfrontend.Ctypes
import CCLib.cfrontend.CtypesTheory
import CCLib.cfrontend.Cop
import CCLib.cfrontend.CopInject
import CCLib.cfrontend.CopTheory
import CCLib.common.Globalenvs
import CCLib.common.GlobalenvsTheory
import CCLib.common.Builtins
import CCLib.common.Events
import CCLib.common.EventsMem
import CCLib.common.EventsExtends
import CCLib.common.EventsInject
import CCLib.common.EventsProps
import CCLib.common.EventsReceptive
import CCLib.cfrontend.Clight
import CCLib.common.GlobalenvsInitMem
import CCLib.cfrontend.ClightGlobalenv
import CCLib.cfrontend.ClightExec
import CCLib.cfrontend.ClightExecSound
import CCLib.lib.MapsLemmas
import CCLib.lib.MapsTheory
import CCLib.lib.MapsProperties
import CCLib.logic.Heap
import CCLib.logic.SepLogic
import CCLib.logic.SepHoare
import CCLib.logic.Funspec
import CCLib.logic.FunspecVoid
import CCLib.logic.Diverge
import CCLib.logic.ExactTemps
import CCLib.logic.ExactTempsHeap
import CCLib.logic.PtrCompare
import CCLib.logic.Globals
import CCLib.logic.ForLoop
import CCLib.logic.Tactics
import CCLib.common.MemdataLemmas
import CCLib.common.MemoryLemmas
import CCLib.common.MemoryTheory
import CCLib.common.MemoryUnchanged
import CCLib.common.MemoryInject
import CCLib.common.MemoryExtends
import CCLib.common.MemoryInjections
import CCLib.common.MemoryDrop
import CCLib.logic.Hoare
import CCLib.logic.HoareArray
import CCLib.logic.HoareArrayInt
import CCLib.logic.ArrayStore
import CCLib.logic.ArrayInit
import CCLib.logic.HoareLong
import CCLib.logic.HoareArrayLong
import CCLib.logic.HoareArray8
import CCLib.logic.HoareArrayDouble
import CCLib.logic.HoareArrayL64
import CCLib.logic.Temps
import CCLib.logic.FunPtr
import CCLib.logic.Aggregate
import CCLib.common.Linking
import CCLib.logic.Locals
import CCLib.logic.OneLocal
import CCLib.logic.ListRep
import CCLib.logic.ListNode
import CCLib.logic.StructField
import CCLib.logic.CString
import CCLib.common.Determinism
import CCLib.common.Smallstep
import CCLib.common.Behaviors
import CCLib.common.BehaviorsAtomic
import CCLib.cfrontend.ClightBehaviors
import CCLib.cfrontend.ClightReceptive
import CCLib.common.Simulation
import CCLib.common.SimulationEventually
import CCLib.common.SimulationDeterm
import CCLib.common.BackwardSimulation
import CCLib.common.ForwardToBackward
import CCLib.common.Bigstep
import CCLib.cfrontend.ClightBigstep
import CCLib.common.ASTTheory
import CCLib.common.GlobalenvsTransf
import CCLib.common.LinkingTheory
import CCLib.common.LinkingMatch
import CCLib.common.LinkingFundef
import CCLib.cfrontend.CtypesLinking
import CCLib.cfrontend.CsyntaxLinking
import CCLib.lib.IntegersPow2
import CCLib.common.ValuesOps
import CCLib.common.ValuesTheory
import CCLib.common.ValuesInject
import CCLib.common.MemdataTheory
import CCLib.common.MemdataEncode
import CCLib.cfrontend.CopArith
import CCLib.cfrontend.Csyntax
import CCLib.cfrontend.Csem
import CCLib.cfrontend.Cstrategy
import CCLib.cfrontend.CstrategyInversion
import CCLib.cfrontend.CstrategyDecompose
import CCLib.cfrontend.CstrategySimulation
import CCLib.cfrontend.CstrategyBackward
import CCLib.common.SmallstepAtomic
import CCLib.common.SmallstepFactor
import CCLib.cfrontend.CstrategyReceptive
import CCLib.cfrontend.CstrategyBigstep
import CCLib.cfrontend.CstrategyBigstepSound
import CCLib.cfrontend.Initializers
import CCLib.cfrontend.Ctyping
import CCLib.cfrontend.CtypingSound
import CCLib.cfrontend.CtypingPreservation
import CCLib.cfrontend.CtypingSubjectReduction
import CCLib.cfrontend.InitializersproofSimple
import CCLib.common.MemoryBytes
import CCLib.common.GlobalenvsBytes
import CCLib.cfrontend.InitializersproofState
import CCLib.cfrontend.InitializersproofMatch
import CCLib.cfrontend.Initializersproof
import CCLib.common.Worlds
import CCLib.common.DeterminismSem
import CCLib.common.SmallstepForever
import CCLib.common.EventsTraceinf
import CCLib.cfrontend.Cexec
import CCLib.cfrontend.CexecEvents
import CCLib.cfrontend.CexecExpr
import CCLib.cfrontend.CexecExprSound
import CCLib.cfrontend.CexecComplete
import CCLib.cfrontend.CexecStep
import CCLib.cfrontend.SimplExpr
import CCLib.cfrontend.SimplExprspec
import CCLib.cfrontend.SimplExprspecCorrect
import CCLib.cfrontend.SimplExprspecMain
import CCLib.cfrontend.SimplExprproofEnv
import CCLib.cfrontend.SimplExprproofContext
import CCLib.cfrontend.SimplExprproofSmart
import CCLib.cfrontend.SimplExprproofMatch
import CCLib.cfrontend.SimplExprproofEstep
import CCLib.cfrontend.SimplExprproofStep
import CCLib.cfrontend.SimplExprproofLink
import CCLib.cfrontend.SimplLocals
import CCLib.cfrontend.SimplLocalsproofEnv
import CCLib.cfrontend.SimplLocalsproofAlloc
import CCLib.cfrontend.SimplLocalsproofExpr
import CCLib.cfrontend.SimplLocalsproofMatch
import CCLib.cfrontend.SimplLocalsproofStep
import CCLib.cfrontend.SimplLocalsproofLink
import CCLib.aarch64.Conventions1
import CCLib.backend.Cminor
import CCLib.cfrontend.Csharpminor
import CCLib.cfrontend.Cshmgen
import CCLib.cfrontend.CshmgenproofOps
import CCLib.cfrontend.CshmgenproofOps2
import CCLib.cfrontend.CshmgenproofEnv
import CCLib.cfrontend.CshmgenproofExpr
import CCLib.cfrontend.CshmgenproofMatch
import CCLib.cfrontend.CshmgenproofStep
import CCLib.cfrontend.CshmgenproofLink
import CCLib.cfrontend.Cminorgen
import CCLib.cfrontend.CminorgenproofEnv
import CCLib.cfrontend.CminorgenproofAlloc
import CCLib.cfrontend.CminorgenproofExpr
import CCLib.cfrontend.CminorgenproofMatch
import CCLib.cfrontend.CminorgenproofStep
import CCLib.driver.FrontendCorrect
import CCLib.driver.BackendCorrect
import CCLib.driver.CompilerCorrect
import CCLib.driver.Complements
-- missing (to port): import CCLib.driver.ComplementsSeparate
import CCLib.driver.CompilerMatch
import CCLib.common.Switch
import CCLib.common.DetermTac
import CCLib.backend.CminorSem
import CCLib.cfrontend.CsharpminorSem
import CCLib.aarch64.Op
import CCLib.backend.CminorSel
import CCLib.common.EventsBuiltinArgs
import CCLib.backend.RTL
import CCLib.backend.RTLgen
import CCLib.backend.RTLgenspecBasic
import CCLib.backend.RTLgenspecDefs
import CCLib.backend.RTLgenspecExpr
import CCLib.backend.RTLgenspecStmt
import CCLib.backend.RTLgenproofEnv
import CCLib.backend.RTLgenproofExpr
import CCLib.backend.RTLgenproofBuiltin
import CCLib.backend.RTLgenproofMatch
import CCLib.backend.RTLgenproofMain
import CCLib.aarch64.Machregs
import CCLib.backend.Locations
import CCLib.backend.Conventions
import CCLib.lib.Postorder
import CCLib.backend.Tailcall
import CCLib.backend.Renumber
import CCLib.backend.LTL
import CCLib.backend.Linear
import CCLib.backend.Mach
import CCLib.backend.MachSyntax
import CCLib.lib.UnionFind
import CCLib.backend.Tunneling
import CCLib.lib.Lattice
import CCLib.lib.Ordered
import CCLib.lib.Heaps
import CCLib.lib.Iteration
import CCLib.lib.FSetAVL
import CCLib.lib.FSetAVLplus
import CCLib.backend.SplitLong
import CCLib.backend.SplitLongproof
import CCLib.backend.SplitLongproof2
import CCLib.lib.Parmov
import CCLib.backend.Kildall
import CCLib.backend.Linearize
import CCLib.backend.CleanupLabels
import CCLib.backend.Liveness
import CCLib.backend.Bounds
import CCLib.backend.Lineartyping
import CCLib.common.Separation
import CCLib.aarch64.Stacklayout
import CCLib.backend.Stacking
import CCLib.backend.Debugvar
import CCLib.backend.Unusedglob
import CCLib.aarch64.SelectOp
import CCLib.aarch64.SelectOpproof
import CCLib.aarch64.SelectOpproof2
import CCLib.aarch64.SelectOpproof3
import CCLib.aarch64.SelectLong
import CCLib.lib.IntegersShifts64
import CCLib.aarch64.SelectLongproof
import CCLib.aarch64.SelectLongproof2
import CCLib.backend.SelectDiv
import CCLib.backend.SelectDivproof
import CCLib.backend.SelectDivproof2
import CCLib.backend.SelectionproofExpr
import CCLib.common.SwitchProof
import CCLib.backend.SelectionproofSwitch
import CCLib.backend.SelectionproofLessdef
import CCLib.backend.SelectionproofExprs
import CCLib.backend.SelectionproofIfconv
import CCLib.backend.SelectionproofMatch
import CCLib.backend.SelectionproofMain
import CCLib.backend.SelectionproofHelpers
import CCLib.common.Unityping
import CCLib.common.UnitypingSound
import CCLib.common.Subtyping
import CCLib.common.Memtype
import CCLib.backend.Cminortyping
import CCLib.backend.CminortypingSpec
import CCLib.backend.CminortypingSubject
import CCLib.backend.Selection
import CCLib.backend.RTLtyping
import CCLib.backend.RTLtypingSound
import CCLib.backend.RTLtypingSubject
import CCLib.backend.Allocation
import CCLib.backend.AllocproofShape
import CCLib.backend.AllocproofEqs
import CCLib.backend.AllocproofCall
import CCLib.backend.AllocproofStep
import CCLib.backend.AllocproofSimBasic
import CCLib.backend.AllocproofSimOp
import CCLib.backend.AllocproofSimCall
import CCLib.backend.AllocproofSimFun
import CCLib.backend.Allocproof
import CCLib.backend.Inlining
import CCLib.backend.InliningspecBasic
import CCLib.backend.InliningspecCfg
import CCLib.backend.InliningspecExpand
import CCLib.backend.Inliningspec
import CCLib.aarch64.OpInject
import CCLib.aarch64.OpTyping
import CCLib.backend.InliningproofBasic
import CCLib.backend.InliningproofStacks
import CCLib.backend.InliningproofMatch
import CCLib.backend.InliningproofStep
import CCLib.backend.InliningproofMain
import CCLib.common.GlobalenvsInitChar
import CCLib.backend.UnusedglobproofSpec
import CCLib.backend.UnusedglobproofGlobals
import CCLib.backend.UnusedglobproofStep
import CCLib.backend.UnusedglobproofMain
import CCLib.backend.UnusedglobproofLink
import CCLib.aarch64.Asm
import CCLib.aarch64.AsmDeterm
import CCLib.aarch64.Asmgen
import CCLib.backend.ValueDomain
import CCLib.lib.LatticeFree
import CCLib.backend.ValueDomainMem
import CCLib.backend.ValueDomainProof
import CCLib.backend.ValueDomainProofArith
import CCLib.backend.ValueDomainProofMul
import CCLib.backend.ValueDomainProofDiv
import CCLib.backend.ValueDomainProofDiv2
import CCLib.backend.ValueDomainProofLong
import CCLib.backend.ValueDomainProofConv
import CCLib.backend.ValueDomainProofCmp
import CCLib.backend.ValueDomainProofNorm
import CCLib.backend.ValueDomainProofNormMono
import CCLib.backend.ValueDomainMemProof
import CCLib.backend.ValueDomainMmatch
import CCLib.backend.ValueDomainInj
import CCLib.backend.ValueDomainEnv
import CCLib.aarch64.ValueAOp
import CCLib.aarch64.ValueAOpproof
import CCLib.backend.ValueAnalysis
import CCLib.backend.ValueAnalysisSoundBasic
import CCLib.backend.ValueAnalysisSoundBC
import CCLib.backend.ValueAnalysisSoundExtcall
import CCLib.backend.ValueAnalysisSoundStack
import CCLib.backend.ValueAnalysisSoundStep
import CCLib.backend.ValueAnalysisSoundBuiltin
import CCLib.backend.ValueAnalysisSoundInit
import CCLib.aarch64.ConstpropOp
import CCLib.backend.Constprop
import CCLib.aarch64.ConstpropOpproof
import CCLib.aarch64.ConstpropOpproof2
import CCLib.backend.Constpropproof
import CCLib.backend.ConstpropproofStep
import CCLib.backend.KildallBBlock
import CCLib.backend.CSEdomain
import CCLib.aarch64.CombineOp
import CCLib.aarch64.CombineOpproof
import CCLib.backend.CSE
import CCLib.backend.CSEproof
import CCLib.backend.CSEproofMem
import CCLib.backend.CSEproofReduce
import CCLib.backend.CSEproofStep
import CCLib.lib.IntvSets
import CCLib.backend.NeedDomain
import CCLib.backend.NeedDomainBits
import CCLib.backend.NeedDomainProof
import CCLib.backend.NeedDomainProof2
import CCLib.backend.NeedDomainProof3
import CCLib.backend.DeadcodeproofMem
import CCLib.backend.Deadcodeproof
import CCLib.backend.DeadcodeproofStep
import CCLib.backend.DeadcodeproofBuiltin
import CCLib.backend.DeadcodeproofMain
import CCLib.aarch64.NeedOp
import CCLib.aarch64.NeedOpProof
import CCLib.backend.Deadcode
import CCLib.driver.Compiler
import CCLib.backend.CleanupLabelsproof
import CCLib.lib.PostorderCorrect
import CCLib.backend.Renumberproof
import CCLib.backend.Debugvarproof
import CCLib.aarch64.OpLessdef
import CCLib.backend.TunnelingBranch
import CCLib.backend.Tunnelingproof
import CCLib.backend.Tailcallproof
import CCLib.backend.Linearizeproof
import CCLib.backend.StackingproofFrame
import CCLib.backend.StackingproofAgree
import CCLib.backend.StackingproofCallee
import CCLib.backend.StackingproofMatch
import CCLib.backend.StackingproofStep
import CCLib.backend.Asmgenproof0
import CCLib.aarch64.Asmgenproof1Imm
import CCLib.aarch64.Asmgenproof1Shift
import CCLib.aarch64.Asmgenproof1Cond
import CCLib.aarch64.Asmgenproof1CondTransl
import CCLib.aarch64.Asmgenproof1Op
import CCLib.aarch64.Asmgenproof1Mem
import CCLib.aarch64.AsmgenproofLabel
import CCLib.aarch64.AsmgenproofBasic
import CCLib.aarch64.AsmgenproofStep1
import CCLib.aarch64.AsmgenproofStep2
import CCLib.aarch64.Asmgenproof
import CCLib.lib.IntegersExtMin
import CCLib.lib.IntegersDivmod2
import CCLib.lib.IntegersOverflow
import CCLib.targets.Archi
import CCLib.x86.Op
import CCLib.x86.OpTheory
import CCLib.x86.OpInject
import CCLib.x86.Machregs
import CCLib.x86.Conventions
import CCLib.x86.Asm
import CCLib.x86.Asmgen
import CCLib.x86.OpTyping
import CCLib.x86.ValueAOp
import CCLib.x86.NeedOp
import CCLib.x86.CombineOp
import CCLib.x86.CombineOpproof
import CCLib.x86.Stacklayout
import CCLib.x86.ConstpropOp
import CCLib.x86.ConstpropOpproof
import CCLib.x86.ConstpropOpproof2
import CCLib.x86.SelectOp
import CCLib.x86.SelectLong
import CCLib.x86.SelectOpproof
import CCLib.x86.SelectOpproof2
import CCLib.x86.SelectOpproof3
import CCLib.x86.SelectLongproof
import CCLib.x86.SelectLongproof2
import CCLib.x86.Asmgenproof0
import CCLib.x86.Asmgenproof1
import CCLib.x86.Asmgenproof1Cond
import CCLib.x86.Asmgenproof1Op
import CCLib.x86.AsmgenproofLabel
import CCLib.x86.AsmgenproofBasic
import CCLib.x86.AsmgenproofStep1
import CCLib.x86.AsmgenproofStep2
import CCLib.x86.Asmgenproof
import CCLib.x86.AsmDeterm
import CCLib.riscV.Op
import CCLib.riscV.OpTheory
import CCLib.riscV.OpInject
import CCLib.riscV.Machregs
import CCLib.riscV.Conventions
import CCLib.riscV.Asm
import CCLib.riscV.Asmgen
import CCLib.riscV.ValueAOp
import CCLib.riscV.NeedOp
import CCLib.riscV.CombineOp
import CCLib.riscV.CombineOpproof
import CCLib.riscV.Stacklayout
import CCLib.riscV.ConstpropOp
import CCLib.riscV.ConstpropOpproof
import CCLib.riscV.SelectOp
import CCLib.riscV.SelectLong
import CCLib.riscV.SelectOpproof
import CCLib.riscV.SelectOpproof2
import CCLib.riscV.SelectOpproof3
import CCLib.riscV.SelectOpproof4
import CCLib.riscV.SelectLongproof
import CCLib.riscV.SelectLongproof2
import CCLib.riscV.Asmgenproof0
import CCLib.riscV.Asmgenproof1
import CCLib.riscV.Asmgenproof1Cond
import CCLib.riscV.Asmgenproof1Op
import CCLib.riscV.Asmgenproof1Mem
import CCLib.riscV.AsmgenproofLabel
import CCLib.riscV.AsmgenproofBasic
import CCLib.riscV.AsmgenproofStep1
import CCLib.riscV.AsmgenproofStep2
import CCLib.riscV.Asmgenproof
import CCLib.riscV.AsmDeterm
import CCLib.cparser.Cabs
import CCLib.cparser.Parser
import CCLib.cparser.C
import CCLib.cparser.Machine
import CCLib.cparser.Diagnostics
import CCLib.cparser.Env
import CCLib.cparser.Cprint
import CCLib.cparser.Cutil
import CCLib.cparser.Ceval
import CCLib.cparser.Transform
import CCLib.cparser.Rename
import CCLib.cparser.Unblock
import CCLib.cparser.SwitchNorm
import CCLib.cparser.Cleanup
import CCLib.cparser.GCC
import CCLib.cparser.Cabshelper
import CCLib.cparser.Cflow
import CCLib.cparser.Checks
import CCLib.cparser.ExtendedAsm
import CCLib.cparser.StructPassing
import CCLib.cparser.PackedStructs
import CCLib.cparser.Lexer
import CCLib.cparser.PreParser
import CCLib.cparser.ElabBase
import CCLib.cparser.ElabTypes
import CCLib.cparser.ElabInit
import CCLib.cparser.ElabExpr
import CCLib.cparser.Elab
import CCLib.cparser.Parse
import CCLib.MenhirLib.InterpreterFast
import CCLib.x86.CBuiltins
import CCLib.aarch64.CBuiltins
import CCLib.riscV.CBuiltins
import CCLib.arm.CBuiltins
import CCLib.powerpc.CBuiltins
import CCLib.lib.Tokenize
import CCLib.cfrontend.CPragmas
import CCLib.cfrontend.C2CBase
import CCLib.cfrontend.C2C
import CCLib.driver.Clflags
import CCLib.driver.Frontend
import CCLib.MenhirLib.Alphabet
import CCLib.MenhirLib.Grammar
import CCLib.MenhirLib.Automaton
import CCLib.MenhirLib.Validator_classes
import CCLib.MenhirLib.Validator_safe
import CCLib.MenhirLib.Validator_complete
import CCLib.MenhirLib.Interpreter
import CCLib.MenhirLib.Interpreter_correct
import CCLib.MenhirLib.Interpreter_complete
import CCLib.MenhirLib.Main
import CCLib.common.Errors
import CCLib.driver.Compopts
import CCLib.cfrontend.Cminorgenproof
import CCLib.cfrontend.Cshmgenproof
import CCLib.cfrontend.SimplExprproof
import CCLib.cfrontend.SimplLocalsproof
import CCLib.backend.Inliningproof
import CCLib.backend.RTLgenproof
import CCLib.backend.RTLgenspec
import CCLib.backend.Selectionproof
import CCLib.backend.Stackingproof
import CCLib.backend.Unusedglobproof
import CCLib.aarch64.Asmgenproof1
import CCLib.powerpc.Builtins1
import CCLib.arm.Op
-- missing (to port): import CCLib.arm.OpTheory
import CCLib.arm.Machregs
-- missing (to port): import CCLib.arm.Conventions1
-- missing (to port): import CCLib.arm.Stacklayout
-- missing (to port): import CCLib.arm.CombineOp
-- missing (to port): import CCLib.arm.CombineOpproof
-- missing (to port): import CCLib.arm.NeedOp
-- missing (to port): import CCLib.arm.ValueAOp
-- missing (to port): import CCLib.arm.ConstpropOp
-- missing (to port): import CCLib.arm.ConstpropOpproof
-- missing (to port): import CCLib.arm.ConstpropOpproof2
-- missing (to port): import CCLib.arm.SelectOp
-- missing (to port): import CCLib.arm.SelectLong
-- missing (to port): import CCLib.arm.SelectOpproof
-- missing (to port): import CCLib.arm.SelectOpproof2
-- missing (to port): import CCLib.arm.SelectOpproof3
-- missing (to port): import CCLib.arm.SelectLongproof
import CCLib.arm.Asm
import CCLib.arm.Asmgen
import CCLib.powerpc.Op
-- missing (to port): import CCLib.powerpc.OpTheory
import CCLib.powerpc.Machregs
-- missing (to port): import CCLib.powerpc.Conventions1
-- missing (to port): import CCLib.powerpc.Stacklayout
-- missing (to port): import CCLib.powerpc.CombineOp
-- missing (to port): import CCLib.powerpc.CombineOpproof
-- missing (to port): import CCLib.powerpc.NeedOp
-- missing (to port): import CCLib.powerpc.ValueAOp
-- missing (to port): import CCLib.powerpc.ConstpropOp
-- missing (to port): import CCLib.powerpc.ConstpropOpproof
-- missing (to port): import CCLib.powerpc.ConstpropOpproof2
-- missing (to port): import CCLib.powerpc.SelectOp
-- missing (to port): import CCLib.powerpc.SelectLong
-- missing (to port): import CCLib.powerpc.SelectOpproof
-- missing (to port): import CCLib.powerpc.SelectOpproof2
-- missing (to port): import CCLib.powerpc.SelectOpproof3
-- missing (to port): import CCLib.powerpc.SelectLongproof
-- missing (to port): import CCLib.powerpc.SelectLongproof2
import CCLib.powerpc.Asm
import CCLib.powerpc.Asmgen
-- missing (to port): import CCLib.arm.Asmgenproof0
-- missing (to port): import CCLib.arm.Asmgenproof1
-- missing (to port): import CCLib.arm.Asmgenproof1Cond
-- missing (to port): import CCLib.arm.Asmgenproof1Op
-- missing (to port): import CCLib.arm.Asmgenproof
-- missing (to port): import CCLib.powerpc.Asmgenproof0
-- missing (to port): import CCLib.powerpc.Asmgenproof1
-- missing (to port): import CCLib.powerpc.Asmgenproof1Cond
-- missing (to port): import CCLib.powerpc.Asmgenproof1Op
-- missing (to port): import CCLib.powerpc.Asmgenproof
-- missing (to port): import CCLib.arm.OpInject
-- missing (to port): import CCLib.powerpc.OpInject
-- missing (to port): import CCLib.lib.IntegersMore
-- missing (to port): import CCLib.lib.IntegersWords
-- missing (to port): import CCLib.common.MemoryMore
-- missing (to port): import CCLib.common.MemoryAxioms
-- missing (to port): import CCLib.common.MemoryMemtype
-- missing (to port): import CCLib.lib.MapsMore
import CCLib.common.SmallstepMore
-- missing (to port): import CCLib.backend.NeedDomainAgree
-- missing (to port): import CCLib.common.MemdataMore
-- missing (to port): import CCLib.lib.IntegersExtra
-- missing (to port): import CCLib.lib.IntegersPrimed
-- missing (to port): import CCLib.common.BehaviorsMore
import CCLib.backend.LocationsMore
-- missing (to port): import CCLib.common.EventsMore
-- missing (to port): import CCLib.lib.UnionFindMore
-- missing (to port): import CCLib.lib.LatticeMore
-- missing (to port): import CCLib.backend.RTLMore
import CCLib.backend.CminorBigstep
-- missing (to port): import CCLib.backend.RTLtypingComplete
-- missing (to port): import CCLib.common.GlobalenvsLoadStore
-- missing (to port): import CCLib.cfrontend.CtypesMore
-- missing (to port): import CCLib.common.EventsSpec
-- missing (to port): import CCLib.arm.AsmDeterm
-- missing (to port): import CCLib.powerpc.AsmDeterm
import CCLib.cfrontend.CtypesAttr
-- missing (to port): import CCLib.common.EventsVolatile
-- missing (to port): import CCLib.common.Builtins0Num
-- missing (to port): import CCLib.common.GlobalenvsMatch
import CCLib.lib.FloatsParsed
import CCLib.lib.MapsRemove
import CCLib.common.Switchaux
import CCLib.backend.Regalloc
import CCLib.lib.Camlcoq
import CCLib.backend.RTLgenaux
import CCLib.backend.Selectionaux
import CCLib.backend.Inliningaux
import CCLib.common.Sections
import CCLib.backend.Asmexpandaux
import CCLib.backend.PrintAsmaux
import CCLib.backend.PrintAsm
import CCLib.x86.Asmexpand
import CCLib.x86.TargetPrinter
import CCLib.aarch64.Asmexpand
import CCLib.aarch64.TargetPrinter
import CCLib.arm.Constantexpand
import CCLib.arm.Asmexpand
import CCLib.arm.TargetPrinter
import CCLib.arm.AsmToJSON
import CCLib.powerpc.Asmexpand
import CCLib.powerpc.TargetPrinter
import CCLib.powerpc.AsmToJSON
import CCLib.backend.Machregsnames
import CCLib.backend.Linearizeaux
import CCLib.backend.AisAnnot
import CCLib.extraction.extraction
import CCLib.driver.Driver
import CCLib.riscV.Asmexpand
import CCLib.riscV.TargetPrinter
import CCLib.common.PrintAST
import CCLib.lib.Format
import CCLib.aarch64.PrintOp
import CCLib.x86.PrintOp
import CCLib.riscV.PrintOp
import CCLib.aarch64.Machregsaux
import CCLib.arm.Machregsaux
import CCLib.powerpc.Machregsaux
import CCLib.riscV.Machregsaux
import CCLib.x86.Machregsaux
import CCLib.backend.PrintRTL
import CCLib.backend.PrintLTL
import CCLib.backend.PrintMach
import CCLib.backend.PrintCminor
import CCLib.cfrontend.PrintCsyntax
import CCLib.cfrontend.PrintClight
import CCLib.aarch64.AsmToJSON
import CCLib.x86.AsmToJSON
import CCLib.riscV.AsmToJSON
import CCLib.backend.XTL
import CCLib.backend.IRC
import CCLib.backend.Splitting
import CCLib.backend.PrintXTL
import CCLib.lib.Commandline
import CCLib.lib.Responsefile
import CCLib.lib.Readconfig
import CCLib.lib.Printlines
import CCLib.driver.Configuration
import CCLib.driver.Driveraux
import CCLib.driver.Timing
import CCLib.driver.Assembler
import CCLib.driver.Linker
import CCLib.driver.CommonOptions
import CCLib.debug.DebugInit
import CCLib.debug.DwarfTypes
import CCLib.debug.DwarfUtil
import CCLib.debug.DebugTypes
import CCLib.debug.Debug
import CCLib.debug.DwarfPrinter
import CCLib.debug.DebugInformation
import CCLib.debug.Dwarfgen
import CCLib.lib.OCamlHashtbl
-- missing (to port): import CCLib.driver.InterpPrintf
import CCLib.driver.Interp
import CCLib.backend.Json
import CCLib.backend.Fileinfo
import CCLib.cparser.deLexer
import CCLib.backend.JsonAST
import CCLib.arm.PrintOp
import CCLib.powerpc.PrintOp
-- clightgen with the Lean backend (export/Export*.ml, export/Clightnorm.ml)
import CCLib.exportclight.ExportLeanBase
import CCLib.exportclight.ExportLeanCtypes
import CCLib.exportclight.ExportLeanClight
import CCLib.exportclight.Clightnorm
import CCLib.exportclight.ExportDriver
