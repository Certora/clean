# Lean port of CompCert (`export/CCLib`): gap analysis

Scope: the Lean 4 port in `export/` (`CCLib/`, `Clightdefs.lean`, `examples/`)
compared with the Rocq sources in this tree (`lib/`, `common/`, `cfrontend/`,
`aarch64/`). Measured against CompCert 3.17 (`VERSION`).

## Status update 84 (VST `queue2`; queue proofs shared between programs)

- The queue proofs of update 83 are now stated for any composite
  environment with the queue's layout (`QueueCenv`: `struct fifo` with
  `head`/`tail` at 0/8, `struct elem` with an `int` field at 0 and `next`
  at 8), and the second word of an element (`QElem.b`) is any value.
  `QueueFuns` is parametrized by the body of `make_elem`, and `call_put`
  by the calling function.
- VST test port of `progs/queue2.c` (VST's `verif_queue2.v`), without
  `sorry`, on the generated `export/VST/progs/queue2.lean`:
  `verif_queue2` (`surely_malloc`, `fifo_new`, `fifo_put`, `fifo_empty`,
  `fifo_get` are `rfl`-equal to `queue.c`'s and their proofs are reused
  through `queue2Cenv`; `make_elem(data)` returns an element with
  undefined padding) and `verif_queue2_main` (`main` returns `1`).

## Status update 83 (struct fields; VST `queue`)

- `logic/StructField.lean` (new): reading and writing any field
  `x->fld` of a struct through a pointer temporary, given the field's
  offset (`Sep.eval_field_mapsto`, `Sep.triple_store_field`, and
  `Sep.triple_store_field_any` for the raw bytes of a fresh `malloc`);
  `Sep.mallocToken_weakValidPointer` (a `malloc`ed pointer is weakly valid
  even for a zero-sized block, so `if (!p)` is decided),
  `Sep.eval_notbool_validptr`, `Sep.anyBytes_of_mapsto`,
  `Sep.mallocPayload_undefBytes`.
- VST test port of `progs/queue.c` (VST's `verif_queue.v`), without
  `sorry`, in five files on the generated `export/VST/progs/queue.lean`:
  `verif_queue_rep` (the representation `fifo`/`fifo_body` as list
  segments of nodes, and `surely_malloc`, which meets `malloc`'s own
  specification), `verif_queue` (`fifo_empty`, `fifo_get`),
  `verif_queue_put` (`fifo_put`), `verif_queue_new` (`fifo_new`,
  `make_elem`) and `verif_queue_main` (`main` returns `1 + 10`, calling
  all of the above through their specifications).  Without fractional
  shares in the heap model, the queue owns its elements entirely while
  they are queued (VST splits them with `Qsh`/`Qsh'`), so an element of
  `contents` records its pointer and the values of `a` and `b`.

## Status update 82 (malloc/free specifications; generic `for` loops; filling arrays; VST `rotate`)

- `logic/Funspec.lean`: the `malloc` specification now returns `void *`
  (`tptr tvoid`, as CompCert's `EF_malloc` signature does) and takes
  `unsigned long`; `free` accepts a block with any contents
  (`anyBytes .Freeable`), which is what VST's `free_spec` asks for.
- `logic/ForLoop.lean`: `triple_for_guard` (any `int`-typed guard
  expression), `triple_for_guard_from` (loops starting at any `j0`),
  `triple_pure_pre`; `triple_for_lt` is now a corollary.
- `logic/ArrayInit.lean` (new): filling a freshly `malloc`'d block as an
  `int` array (`arrayU32_snoc`, `arrayU32_anyBytes`,
  `mallocPayload_anyBytes`, `Sep.triple_store_index_init`,
  `Sep.triple_store_index_int_frame`).
- VST test ports, without `sorry`: `verif_rotate` (`rotate` of `rotate.c`
  against `rotate_spec`: `malloc` a buffer, three loops, `free`) and
  `verif_rotate_sorted` (`sorted_rotate` calls `rotate` and adds `N` to
  the wrapped elements; it meets `sorted_rotate_spec`, and VST's
  `sorted_rotate` of a sorted list with elements in `[0, N]` is sorted).
- The duplicate `readable_of_writable` in `verif_revarray` was removed in
  favour of the one in `logic/ExactTempsHeap.lean`.

## Status update 81 (printers of `Op`; PowerPC builtins; sorting and merging lists in VST)

- `arm/PrintOp.lean` and `powerpc/PrintOp.lean` (new, from the targets'
  `PrintOp.ml`): conditions, addressing modes and operators as text;
  the comparison names are shared through `PrintAST.comparisonName`
  instead of being repeated per target. `examples/PrintOpCheck.lean`
  checks sample outputs.
- `powerpc/Builtins1.lean` (new, from `powerpc/Builtins1.v`): the
  platform builtins with their semantics and the `BuiltinSem` proofs.
- Program logic: `ListNode.listrep_cons_front` (a non-empty list next to
  a frame), `ListNode.eval_null_cast` (`(void *) 0`),
  `ListRep.semCast_ofBool_bool`, `ListNode.triple_store_tail_expr` (store
  of any link expression into `x->tail`), `Tactics.triple_or`.
- VST test ports, all without `sorry`: `verif_insertionsort` (`insert`
  against `insert_spec`; `insertionsort` builds the left fold of
  `insert`), `verif_insertionsort_sorted` (that fold is VST's
  `insertion_sort`, via Mathlib's `List.insertionSort`, so
  `insertionsort` meets `insertionsort_spec`), and `verif_merge` (`merge`
  of `merge.c` against `merge_spec`: two lists merged in place through a
  pointer `x` to the cell to write next, which is the addressable local
  `ret` at first and then the `tail` field of the last merged node).
- `MISSING_MODULES.md` regenerated (335 missing, 71 to port).

## Status update 80 (de-lexer; C strings in the program logic; VST progs)

- `cparser/deLexer.lean` (new, from `cparser/deLexer.ml`): `delex` on the
  terminals of the verified parser (total, including the three terminals
  `deLexer.ml` does not list), `delexSymbol`, `delexSentence`.
  `examples/ParseCheck.lean` checks that the lexer reads every `delex t`
  back as `t`.
- Program logic: `logic/CString.lean` (new): VST's `cstring` (`CC.cstring`
  over `arrayU8`), `str[i]` with a `size_t` index
  (`eval_index_bytes_ulong`, `byteOfsL_unsigned`), character comparisons
  (`eval_eq_uchar`, `eval_lt_uchar`, `eval_gt_uchar`), `cstring_zero_iff`.
- VST test ports, all without `sorry`: `verif_floyd_tests`
  (`test_sizeof`), `verif_reverse_client` (`last_foo`, assuming
  `reverse_spec` as VST's `Gprog` does, and also linked with `f_reverse`
  of `reverse.c`, which discharges the assumption), `verif_message`
  (`intpair_serialize`, `intpair_deserialize`), `verif_strlib` (`strlen`,
  `strchr`), `verif_strlib_strcmp` (`strcmp`) and `verif_object`
  (the methods `foo_reset`, `foo_twiddle` against `foo_invariant`).
- `MISSING_MODULES.md` regenerated (338 missing, 75 to port).

## Status update 79 (driver options; lists, 8-byte arrays and globals in the program logic; VST progs)

- `driver/Compopts.lean` (new, from `driver/Compopts.v`): the structure
  `CC.Compopts` of compiler flags; the `Config` structures of
  `driver/`, `x86/` and `riscV/Compiler.lean` now extend it instead of
  repeating the fields.
- `lib/Printlines.lean` (from `lib/Printlines.ml`) and
  `backend/Fileinfo.lean` (from `backend/Fileinfo.ml`).
- Program logic: `logic/HoareArray8.lean` (new): arrays of any 8-byte
  scalar (`array8`, `eval_index8`, `triple_store_index8`);
  `HoareArrayDouble` is now an instance of it, and
  `logic/HoareArrayL64.lean` (new) adds `long` arrays.
  `logic/ListRep.lean` (new): list segments `lseg`/`listrep` over any node
  predicate (`lseg_append`, `lseg_snoc`, NULL tests);
  `logic/ListNode.lean` (new): the node layout `struct { int head;
  struct list *tail; }` with field reads and `x->tail = y`.
  `logic/Globals.lean`: global variables and fields of global structs as
  l-values (`lvalue_global`, `lvalue_global_field`);
  `ExactTempsHeap.triple_assign_atE_front`: a store into the first cell of
  a fragment next to a frame.
- VST test ports, all without `sorry`: `verif_prod` (`product`, plus a
  proof that VST's `2^27` bound does not rule out overflow),
  `verif_reverse` (`sumlist`, `reverse`), `verif_append` (`append`),
  `verif_union` (`g`), `verif_libglob` (`LG_init`, `LG_bump`, `LG_get`,
  `client`, `main` and `LG.initial`).
- `MISSING_MODULES.md` regenerated (339 missing).

## Status update 78 (addressable locals; `double` arrays; location order; VST progs)

- Program logic: `logic/OneLocal.lean` (new): function entry and
  `return` for a function with one addressable local
  (`Sep.satisfies_oneLocal`, `Sep.triple_return_oneLocal`, address and
  lvalue evaluation of the local); `ExactTemps.AtE` generalizes `AtH` to
  any local environment.
- `logic/HoareArrayDouble.lean` (new): `double` arrays (`arrayV64`,
  `arrayF64`), indexed read (`eval_index_f64`), indexed store next to a
  frame (`triple_store_index_f64`), IEEE-754 `+`/`*` on `double`.
- `backend/LocationsMore.lean` (new, from `backend/Locations.v`): the
  total order `OrderedLoc` and `outside_interval_diff`/
  `diff_outside_interval`; `backend/Allocation.lean` now uses it instead
  of its own copy.  `common/SmallstepMore.lean` (new): `star_three`…,
  `plus_two`…, `plus_ind2`, `plus_E0_ind`.
- VST test ports, all without `sorry`: `verif_stackframe_demo` (`iden`),
  `verif_structcopy` (`f`), `verif_funcptr` (`myfunc`, `main`),
  `verif_float` (`main`), `verif_dotprod` (`dotprod`) and
  `verif_dotprod_add` (`add`).
- `MISSING_MODULES.md` regenerated (342 missing, 79 to port).

## Status update 77 (PTree removal/cardinal; exact temps with heap; VST progs)

- `lib/MapsRemove.lean` (new): `elements_extensional`, `elements_remove`,
  `cardinal_set_none`, `cardinal_set` (remaining `PTree_Properties`
  lemmas about `remove`/`cardinal` from `lib/Maps.v`).
- Program logic: `logic/ExactTempsHeap.lean` (new) with `Sep.AtH`
  (exact temporaries plus heap), set/assign/return rules for it,
  unsigned pointer-offset arithmetic, `eval_lvalue_mapsto`;
  `HoareArray.semBinop_mul_int`.
- VST test ports, all without `sorry`: `verif_peel` (disjunctive loop
  invariant instead of loop peeling), `verif_field_loadstore` (`sub1`,
  `sub2`, `sub3`), `verif_store_demo` (`set22`, `fiddle`),
  `verif_load_demo` (`get22`, `get_little_endian`) and
  `verif_load_demo_fiddle` (the loop of `fiddle`).
- `MISSING_MODULES.md` regenerated.
- Next: `verif_structcopy` needs a generic function-entry rule for
  functions with addressable locals (allocation of the local frame and
  its release on return).

## Status update 76 (determinism; traceinf; PTree properties; VST progs)

- `common/DeterminismSem.lean` (new): the rest of `common/Determinism.v`
  (`match_possible_traces`, possible behaviors, deterministic semantics,
  `program_behaves_deterministic`, world-restricted semantics and
  `world_sem_deterministic`).
- `common/EventsTraceinf.lean` (new): infinite-trace part of
  `common/Events.v` (`Econsinf`, trace prefixes, `traceinfOfSeq`);
  `Behaviors.lean` reuses it and `List.getD`.
- `lib/MapsProperties.lean` (new): `PTree_Properties` gathered in one place
  (previously scattered duplicates of `cardinal`, `of_list`, `for_all`,
  element ordering removed); `option_rel` replaced by core `Option.Rel`;
  `exists_`, `beq`, `for_all_false`, `exists_false` ported.
- Program logic: `logic/HoareArrayLong.lean` (arrays indexed by `long`),
  generic indexed load/store lemmas in `HoareArrayInt`/`ArrayStore`.
- VST test ports, all without `sorry`: `verif_nest3`, `verif_min64`,
  `verif_bin_search`.
- `MISSING_MODULES.md` regenerated.

## Status update 75 (determinacy simulations; Cminor big-step; VST progs)

- `common/SimulationDeterm.lean` (new): forward simulations with an
  "eventually" index (`forward_simulation_eventually{,_plus}`), the
  determinacy lemmas `sd_determ_1/2/3`, `star_determinacy`, and
  `forward_simulation_determ{,_star,_plus,_one}` (remaining part of
  `common/Smallstep.v`).
- `BehaviorsInfSeq` confirmed as already covered by `common/Bigstep.lean`
  (recorded as merged).
- `backend/CminorBigstep.lean` (new): Cminor big-step semantics
  (terminating and diverging), and its soundness with respect to the
  small-step semantics (`bigstep_semantics_sound`).
- Program logic: `logic/PtrCompare.lean` (pointer equality between owned
  cells), `logic/Globals.lean` (reading global variables).
- VST test ports, all without `sorry`: `verif_ptr_compare`, `verif_even`,
  `verif_odd`, `verif_cast_test`, `verif_global`, `verif_nest2`.
- `MISSING_MODULES.md` regenerated.

## Status update 74 (forever lemmas; exact-temps logic; recursion; VST progs)

- `common/SmallstepForever.lean` (restored module): the `Forever` coinductive
  (moved out of `Bigstep.lean`), `ForeverN`, `ForeverPlus`, `ForeverSilentN`
  and their equivalences with `Forever`/`ForeverSilent`.
- Program logic: `logic/Diverge.lean` (non-termination from repeated steps),
  `logic/ExactTemps.lean` (exact local states `Sep.At`; `set`/`if`/`return`
  rules; `satisfies_at`), `logic/ForLoop.lean` (`for (i = a; i < b; i++)`
  loops); `FunspecCall.triple_call_at` and `satisfies_rec` (recursive and
  mutually recursive functions with `WITH`-parameterised specs, by a measure);
  unsigned operand lemmas in `HoareArray`.
- VST test ports, all without `sorry`: `VST/progs/verif_dead_if.lean`,
  `verif_sumarray2.lean`, `verif_logical_compare.lean`, `verif_fib.lean`
  (loop, loop with saved variable, recursive), `verif_evenodd.lean` (mutual
  recursion) and `verif_switch.lean` (`twice`, `f`).
- `Builtins0`/`Builtins1` recorded as merged modules; `MISSING_MODULES.md`
  regenerated.

## Status update 73 (Mach syntax; `arm`/`powerpc` `Asmgen`; VST progs)

- `backend/MachSyntax.lean`: target-generic Mach syntax (instructions,
  functions, programs, `isLeafFunction`), parameterised by the target's
  operation/addressing/condition/register types.
- `arm/Asmgen.lean` and `powerpc/Asmgen.lean`: ports of `arm/Asmgen.v` and
  `powerpc/Asmgen.v`, including the `transl_code'`/`transl_code` equivalence.
  They unblock `arm/Asmexpand` and `powerpc/Asmexpand`, which build again.
- Program logic: `logic/HoareArrayInt.lean` (signed `int` array indexing,
  casts, negation), `logic/ArrayStore.lean` (Hoare rule for a store into an
  `int` array), `logic/FunspecVoid.lean` (void functions that fall off their end).
- VST test ports, all without `sorry`: `VST/progs/verif_min.lean`,
  `VST/progs/verif_loop_minus1.lean` and `VST/progs/verif_revarray.lean`.
- `MISSING_MODULES.md` regenerated.

## Status update 72 (module audit: modules that should not exist, restored modules, splits)

See `MODULE_AUDIT.md` (analysis and plan) and the regenerated
`MISSING_MODULES.md`. In short: the Flocq port (`flocq/`, root `CCLibReal`) was
removed, because the float semantics uses the `Float.Model` backport
`lib/FloatModel.lean`. Some modules were deleted because they duplicate Lean
core (`lib/{BoolEqual, Decidableplus, Wfsimpl}`); others were deleted because
they were per-target copies of shared files (`{arm, powerpc}/{Stacking,
Compiler}`). `cparser/Cabs`, `common/Errors`, `lib/FloatsParsed` (float literals, on the `Float.Model` backport) and `driver/Clflags` were restored, so `cparser/{Cabshelper, ElabBase}` and `cfrontend/{C2CBase, C2C}` build again.
`lib/MathlibEquiv` builds again, as the root `CCLibMathlib`. Seven files over
1000 lines were split. The status updates below that mention `CCLibReal`, the
real-number Flocq files or `flocq/Core/MathlibEquiv.lean` describe files that
no longer exist.

## Status update 69 (Mathlib; Flocq over the real numbers: `round`, `mag`, `Bsqrt_correct`, square-root error bounds)

**Toolchain.** The repository-root `lakefile.toml` now requires Mathlib
(`leanprover-community/mathlib4`, pinned to revision
`520045ab14e26149ee970e2e617ca04b09bde5d6`, which is built for
`leanprover/lean4:v4.32.1`); `lake-manifest.json` lists it and its
dependencies. The `CCLib` root still imports Lean core only, so `import CCLib`
does not load Mathlib. (`export/lakefile.toml` and `export/lean-toolchain`
have since been removed; the root files are the only Lake configuration.) The Mathlib-based modules form a second root, `CCLibReal`
(`export/CCLibReal.lean`). The library of generated test programs is now called
`CCTest`, with source directory `test/`, so its modules are `lean.<file>`
(e.g. `lean.demo`, imported by `examples/AsmTestPrograms.lean`) instead of
`test.lean.<file>`: ProofWidgets (a Mathlib dependency) declares a library
`test` that owns every `test.*` module, which made `lake build` look for
`test/lean/demo.lean` inside ProofWidgets. A full `lake build` from the
repository root succeeds (9912 jobs).

**What was missing.** The Flocq port works over `Rat`. That is enough for every
IEEE operation except the square root, whose specification was given by the
relation `is_round_sqrt` (a rational description of `round (sqrt x)`); the
real-number statements of `Raux.v` and `Div_sqrt_error.v` were stated over the
classes `RatSqrtField`/`RatExpField`, with no instance.

| Rocq source | Lean file (new) | Content |
| --- | --- | --- |
| `flocq/Core/Raux.v` | `flocq/Core/RauxReal.lean` | `ℝ` is an instance of `RatSqrtField` (`Real.sqrt`) and `RatExpField` (`Real.exp`, `Real.log`); `bpowR` (`bpow` on `R`) with `bpow_cast`, `bpowR_plus`, `bpowR_lt_iff`, `bpowR_le_iff`; `exp_le_real`, `bpow_exp_real` (`bpow r e = exp (e * ln r)`); `magR` (`mag` on `R`) with `magR_spec` (`mag_prop`), `magR_unique`, `magR_unique_pos`, and `magR_cast` (agrees with the rational `mag`) |
| `flocq/Core/Generic_fmt.v` | `flocq/Core/Generic_fmtReal.lean` | `F2RR`, `cexpR`, `scaled_mantissaR`, `generic_formatR`, `roundR` (Rocq's `round` on `R`); `ZfloorR`, `ZceilR`, `ZtruncR`, `ZawayR`, `ZnearestR`; `round_cast`, `generic_formatR_cast` (agreement with the rational versions); the predicate `Rnd_ext` (a real rounding function extending a rational one) and its five instances; `roundR_near_irrational` |
| `flocq/IEEE754/BinarySingleNaN.v` | `flocq/IEEE754/BinarySingleNaNSqrtReal.lean` | `is_round_sqrt_real`, `is_round_sqrt_roundR`, `is_round_sqrt_iff_real` (`is_round_sqrt x r ↔ r = round (sqrt x)` on `ℝ`), `round_modeR`, `Rnd_ext_round_mode`, `BSN.Bsqrt_correct_real` (Rocq's `Bsqrt_correct`) |
| `flocq/IEEE754/Binary.v`, `Bits.v` | `flocq/IEEE754/BinarySqrtReal.lean` | `Bsqrt_correct_real`, `b32_sqrt_correct_real`, `b64_sqrt_correct_real` |
| `flocq/Prop/Div_sqrt_error.v` | `flocq/Prop/Div_sqrt_errorR.lean` | `sqrt_error_N_FLX_real`, `sqrt_error_N_FLX_ex_real`, `sqrt_error_N_FLX_round_ex_real`, `sqrt_error_N_FLT_ex_real`, `sqrt_error_N_FLT_round_ex_real` with Rocq's statements (`Real.sqrt`, ` | · | `,`round` on `ℝ`) |

`lake build CCLibReal` succeeds; the new files contain no `sorry`, and the
theorems above depend only on `propext`, `Classical.choice` and `Quot.sound`.

Differences from Rocq:

* Inputs of the IEEE and error-bound theorems are rational, as in the rest of
  the port (they are float values). `roundR`, `magR` and `generic_formatR`
  accept any real.
* `roundR` takes a rounding function `ℝ → ℤ`; the five IEEE modes are given by
  `round_modeR`. The bridge to the rational theory needs `Rnd_ext rnd rndR`:
  `rndR` agrees with `rnd` on rationals and is locally constant at
  irrationals. This holds for `Zfloor`, `Zceil`, `Ztrunc`, `Zaway` and every
  `Znearest choice`, but not for an arbitrary `Valid_rnd` function.
* The general rounding theory of `Generic_fmt.v` (monotonicity, error bounds,
  `ulp`) for real, possibly irrational arguments is still proved only over
  `Rat`; on `ℝ` only the facts above are available.

## Status update 70 (Flocq rounding theory over `ℝ` for every real argument; duplicates of Mathlib/Batteries/core)

**Mathlib.** It was already installed by Status update 69, at revision
`520045ab14e26149ee970e2e617ca04b09bde5d6`, which matches `lean-toolchain`
(`leanprover/lean4:v4.32.1`). No change was needed.

**Porting continued: the rounding theory of Flocq for arbitrary real
arguments.** Status update 69 listed as open: "the general rounding theory of
`Generic_fmt.v` (monotonicity, error bounds, `ulp`) for real, possibly
irrational arguments is still proved only over `Rat`". The new files are
named after their Rocq sources, like the existing `*Real.lean` files:

| Rocq source | Lean file (new) | Content |
| --- | --- | --- |
| `flocq/Core/Generic_fmt.v` | `flocq/Core/Generic_fmtRealRound.lean` | `Valid_rndR` (Rocq's `Valid_rnd` for `ℝ → ℤ`) with instances for `ZfloorR`, `ZceilR`, `ZtruncR`, `ZawayR`, `ZnearestR choice`, `Zrnd_oppR`; `ZrndR_DN_or_UP`; `generic_formatR_iff`, `generic_formatR_0`, `generic_formatR_opp`, `generic_formatR_F2R`, `generic_formatR_bpow`, `generic_formatR_rat` (format numbers are rational); `roundR_generic`, `roundR_0`, `roundR_opp`, `roundR_nonneg`/`roundR_nonpos`, `roundR_bounded_large_pos`, `roundR_bounded_small_pos`, `roundR_le_pos`, `roundR_le` (monotonicity), `roundR_DN_or_UP`, `generic_formatR_round_pos`, `generic_formatR_round`, `roundR_DN_pt`, `roundR_UP_pt`, `roundR_N_pt` |
| `flocq/Core/Ulp.v` | `flocq/Core/UlpReal.lean` | `ulpR` with `ulpR_cast` (agrees with the rational `ulp`), `ulpR_neq_0`, `ulpR_ge_0`; `error_lt_ulpR`, `error_le_ulpR`, `error_le_half_ulpR` |
| `flocq/Prop/Relative.v` | `flocq/Prop/RelativeReal.lean` | `relative_ulpR_le`, `relative_errorR`, `relative_error_NR`, `relative_error_conversionR(_lt)`; FLX: `relative_error_FLXR`, `relative_error_FLXR_ex`, `relative_error_N_FLXR`, `relative_error_N_FLXR_ex`; FLT: `relative_error_FLTR`, `relative_error_N_FLTR` |

The proofs are direct proofs over `ℝ`, so they hold for every real argument
and every `Valid_rndR` rounding function, not only for the five IEEE modes
(unlike the `Rnd_ext` bridge of Status update 69). `lake build CCLibReal`
succeeds. The new files contain no `sorry`, and the theorems depend only on
`propext`, `Classical.choice` and `Quot.sound`.

**Duplicates of Mathlib, Batteries and Lean core.** `MATHLIB_DUPLICATION.md`
(repository root) lists the definitions of the port that duplicate library
ones. For each one it gives the library counterpart and a recommendation.
Where the definitions coincide, the two new bridge files prove it:
`lib/MathlibEquiv.lean` (`ListForall2` ↔ `List.Forall₂`, `OptionRel` ↔
`Option.Rel`, `zdiv`/`floorZ`/`align` ↔ `⌊·⌋`/`⌈·⌉`, `list_disjoint` ↔
`List.Disjoint`, `lex_ord` ↔ `Prod.Lex`, `list_fold_left` ↔ `List.foldl`,
`list_nth_z` ↔ `l[n]?`, `Positive ≃ PosNum`, `Zbits.testbit`/`land`/`lor`/
`lnot`/`div2`/`shiftl`/`shiftr`/`eqmod`/`log2`/`Zsize` ↔ `Int.testBit`/
`Int.land`/`Int.lor`/`Int.lnot`/`Int.div2`/`<<<`/`>>>`/`Int.ModEq`/`Nat.log 2`/
`Nat.size`, `Intv.In` ↔ `Set.Ico`, `Parmov.Star` ↔ `Relation.ReflTransGen`).
The other is `flocq/Core/MathlibEquiv.lean` (`Zpower`, `Zeven` ↔ `Even`,
`Zdiv_eucl`, `Rabs` ↔ `|·|`, `Rcompare` ↔ `compare`, `Zfloor`/`Zceil`,
`bpow` ↔ `zpow`, `mag` ↔ `Int.log`, `Znearest (fun _ => true)` ↔ `round`,
`Zdigits` ↔ `(Nat.digits b n).length`). The `CCLib` root itself still does
not import Mathlib, so these definitions are not replaced in place. The
bridge theorems are the rewriting lemmas a replacement would need.

## Status update 71 (Flocq rounding to odd and double rounding over `ℝ`; per-target duplication)

**Mathlib.** Already installed (Status update 69) at revision
`520045ab14e26149ee970e2e617ca04b09bde5d6`, which matches `lean-toolchain`
(`leanprover/lean4:v4.32.1`); no change. A full `lake build` from the
repository root succeeds.

**Porting continued: the remaining real-number statements of `Round_odd.v`
and `Double_rounding.v`.** In the rational port, `round_N_odd` was proved
only for rational inputs, and the square-root double-rounding theorems were
stated with the relation `is_round_sqrt` instead of `round (sqrt x)`.

| Rocq source | Lean file (new) | Content |
| --- | --- | --- |
| (support) | `flocq/Core/Generic_fmtRealTransfer.lean` | `Rnd_ext_opp`; `roundR_near_irrational'` (the sign-free version of `roundR_near_irrational`); `roundR_roundR_of_rat`: an identity `round f1 r1 (round f2 r2 x) = round f1 r1 x` that holds for every rational `x` holds for every real `x` |
| `flocq/Prop/Round_odd.v` | `flocq/Prop/Round_oddReal.lean` | `Zrnd_oddR` (Rocq's `Zrnd_odd` on `R`), `Rnd_ext_Zrnd_odd`, `Valid_rndR_odd` (`valid_rnd_odd`), `Zrnd_oppR_odd` (`Zrnd_odd_opp`), `roundR_opp_odd` (`round_odd_opp`), `round_N_oddR` (`round_N_odd`, for every real `x`), `round_N_oddR_FLX`, `round_N_oddR_FLT` |
| `flocq/Prop/Double_rounding.v` | `flocq/Prop/Double_roundingReal.lean` | `round_round_eqR` (`round_round_eq` on `R`), `round_round_eqR_cast`; `round_round_sqrtR` (`round_round_sqrt`, with `Real.sqrt`) and its FLX/FLT/FTZ instances; `round_round_sqrt_radix_ge_4R` and its FLX/FLT/FTZ instances; `round_round_plusR`, `round_round_minusR`, `round_round_multR`, `round_round_divR` |

`lake build CCLibReal` succeeds; the new files contain no `sorry`, and the
theorems depend only on `propext`, `Classical.choice` and `Quot.sound`.
Differences from Rocq: the float arguments `x`, `y` are rational (as in the
rest of the port); `round_round_sqrtR_FTZ` drops Rocq's unused hypothesis
`4 ≤ beta`; the FLX/FLT instances of `round_N_odd` (not in the Rocq file)
assume `1 < prec`, which gives the `Exists_NE` instances.

**Duplication.** Besides the library duplicates already listed,
`MATHLIB_DUPLICATION.md` now records the largest duplication inside the port:
the target-independent back-end passes and proofs exist once per target
(`backend/`, `arm/`, `powerpc/`, `riscV/`, `x86/`). `TARGET_DUPLICATION.md`
lists the 163 affected file names with a similarity score; 58 of them are
at least 95% identical across copies (about 63,000 extra non-blank lines).

## 1. Fidelity bugs found (reproducers: `export/examples/FloatConvGaps.lean`)

These are differences from CompCert's specification, not gaps in coverage.
All of them are in `CCLib/lib/Floats.lean`, and the differential corpus does not
catch them.

| # | Function(s) | CompCert (`lib/Floats.v`) | Port | Effect |
| --- | --- | --- | --- | --- |
| 1 | `Float.toLong`, `Float.toLongu`, `Float32.toLong`, `Float32.toLongu` | `None` when the truncated value is out of range | it computes `x.toInt64` (which **saturates**) and then range-checks the saturated value | `toLong 2^63`, `toLong 1e30`, `toLongu 1e30` return `some 0x7fff…ffff` where CompCert gives `none`. `toLongu 1e19` returns `2^63-1` where CompCert gives `10^19` |
| 2 | `Float32.ofLong`, `Float32.ofLongu` | one rounding, straight to binary32 (`BofZ 24 128`) | rounds to binary64 first, then to binary32 (two roundings) | `ofLong (2^62+2^38+1)` gives `2^62`; CompCert gives `2^62+2^39` |
| 3 | `Float.abs`, `Float32.abs` | `Babs`, which clears the sign bit | `if x < 0 then -x else x` | `abs(-0.0) = -0.0` where CompCert gives `+0.0` |

Bug 1 reaches the semantics: `Cop.semCast (Vfloat 1e30) tdouble tlong m`
returns `some (Vlong LLONG_MAX)`, so the Lean Clight `Step` takes a step on
`(long)1e30`. In CompCert that conversion is undefined behaviour and the
program is stuck. Because the program logic gives total correctness, a Lean
proof could show such a program "safe" when CompCert considers it undefined.
This is the only soundness-relevant difference from CompCert that I found.

Suggested fixes: range-check the *real* value before converting (for example
`lo ≤ x.floor`-style checks against exact powers of two, or decode the bits
yourself); for int64 → binary32, round from the integer directly (split the
integer, or implement round-to-odd followed by a single rounding); for `abs`,
clear bit 63 or bit 31 of the bit pattern.

## 2. Not ported: `lib/`

| Rocq file | Lines | Lean status |
| --- | --- | --- |
| `Integers.v` | 5012 | **Operations ported** onto `BitVec` (`Int`, `Int64`, `Byte`, `Ptrofs`). **About 400 theorems are not ported**: the ring and bit algebra, `eqm`, the `repr`/`unsigned`/`signed` round-trip and range lemmas, shift/rotate identities, `divs`/`mods` lemmas, and so on. Users must re-derive them from `BitVec` lemmas each time. Missing operations: `shrx`, `shr_carry`, `add_carry`, `add_overflow`, `sub_borrow`, `sub_overflow`, `negative`, `one_bits`, `is_power2`, `divmodu2`/`divmods2`, the `Int64` `shl'`/`shru'`/`shr'`/`rol'`/`ror'`/`shrx'`/`mul'` family, `Int64.rolm`, `Int.of_int64*`, and most of `Ptrofs` (`divs`, `mods`, shifts, `sign_ext`, `agree32`/`agree64`). Clight does not need any of these, but the backend does |
| `Zbits.v` | 1187 | **Ported** in Status update 44 (`CCLib/lib/Zbits.lean`, all 102 items). The machine integers still use `BitVec` |
| `Floats.v` | 1464 | **Swapped for host IEEE (Lean's native `Float`)**, not ported. Missing: `sqrt`, `fma`, `compare`/`ordered`, `from_parsed`, `from_words`, `exact_inverse`, the explicit NaN machinery (`choose_nan`, `unop_nan`/`binop_nan`, `of_single_nan`, `to_single_nan`), and **all 77 theorems**. Native `Float` operations are opaque to the kernel, so **no proof can reason about float arithmetic** (`decide` gets stuck; checked). Only the bit-level path through memory can be reasoned about |
| `IEEE754_extra.v` | 1492 | **Ported** over Flocq in Status update 50 (`lib/IEEE754_extra*.lean`) |
| `flocq/` | ~31k | **Ported** over `Rat` (Status updates 48–51, 59 and 60); results about real square roots are stated over any ordered field containing `ℚ` with a square root (Status update 60). `lib/Floats.lean` still runs on its own float model, not on this port |
| `Maps.v` | 2023 | Partly ported: `PTree` (a non-canonical 3-constructor trie), `PMap`, `ZMap` with `empty/get/set/remove/map1/elements`. Missing: canonical trees (so `PTree` extensionality fails), `fold`/`fold1`, `map` with keys, `combine`, `filter1`, `beq`, `xkeys`, `ITree`/`NTree`, the `IMap`/`EMap` functors, `tree_ind`. Theorems: about 17 here against 104 in Rocq. The port has `gempty`/`gss`/`gso`/`gi` (`PTree`, `PMap`, `ZMap`) and `PMap.gsspec`. It has no `remove` lemmas (`grs`/`gro`/`grspec`), no `elements_correct`/`elements_complete`/`elements_keys_norepet`, no `gmap`/`gmap1`, no `fold` lemmas and no extensionality |
| `Coqlib.v` | 1426 | Not ported. Lean core covers part of it; there is no `list_norepet` theory beyond `Clight.listNorepet` |
| `Axioms.v` | 51 | Not needed (Lean has definitional proof irrelevance and `funext`) |
| `Lattice.v`, `Iteration.v`, `Ordered.v`, `FSetAVLplus.v`, `Heaps.v`, `IntvSets.v`, `Intv.v`, `Parmov.v`, `Postorder.v`, `UnionFind.v`, `Wfsimpl.v`, `Decidableplus.v`, `BoolEqual.v` | ~6.5k | **Not ported.** These support the optimizer and backend (dataflow, register allocation, parallel moves), which this port does not cover |

## 3. Not ported: `common/`, `cfrontend/`, the target

### Semantics layer (ported, but only partly)

* **`Values.v`**: the operations are present. Missing: `lessdef`,
  `inject`/`meminj`/`inject_incr`/`compose_meminj`, `has_type_list`,
  `has_rettype`, `maketotal`, `select`, `cmplu`, the 64-bit backend helpers
  (`mullhs`, `mullhu`, `shrxl`, `roll`, `rorl`, carry and overflow), and
  single↔long conversions (`singleoflong`, `longofsingle`, …). All 168
  theorems are missing.
* **`Memdata.v`**: the definitions are present. Missing: `memval_inject`,
  `memval_lessdef`, `shape_encoding`/`decoding`, and most of the 69 theorems
  (the general `decode_encode_val` case analysis across different chunks,
  `encode_val_inject`, the overlap and `proj_bytes`/`inj_bytes` lemmas, …).
  About 45 theorems exist (`Memdata.lean` + `MemdataLemmas.lean`). They focus
  on the same-chunk round trip `decodeVal_encodeVal` and integer
  encode/decode.
* **`Memory.v` / `Memtype.v`**: the operational core is faithful (the `Mem`
  record keeps all three invariants). Missing: memory **injections**
  (`mem_inj`, `inject`, `flat_inj`, `inject_neutral`), **extensions**
  (`extends`), `unchanged_on`, and most of the 266 theorems (the port has about 56, in `Memory.lean` + `MemoryLemmas.lean`). Among the
  missing theorems: `load_store` for overlapping or mismatched chunks,
  `store` vs `alloc`/`free`/`drop_perm` commutation, `loadv`/`storev`
  lemmas, `free_list` lemmas, `drop_perm` lemmas, `valid_block` preservation
  for every operation, `nextblock` facts, and `loadbytes`/`load` agreement.
  The existing lemmas cover the store/load/alloc/free/storebytes cases the separation logic needs.
* **`Globalenvs.v`**: `globalenv`, `init_mem` (`allocGlobals`, matching
  Rocq), lookups and symbol injectivity are present. Missing: the dropped
  `Genv.t` invariants (only `SymbBelow`/`SymbInjective` are recovered),
  `init_mem` properties (`init_mem_characterization`, `globals_initialized`,
  `find_funct_ptr_inversion`, …), `match_genvs`, and nearly all of the 84 theorems (7 symbol-table lemmas exist).
* **`Events.v`** (about 250 of 1819 lines): traces and the eight interpreted
  builtins are present. Missing: **infinite traces** (`traceinf`,
  `Eappinf`), `extcall_properties` (only the determinism fields, as axioms),
  `eval_builtin_arg(s)`, `symbols_inject`, `inject_separated`,
  `external_call_*` preservation lemmas, `output_trace`. In addition,
  **`Builtins0.v`/`Builtins1.v` are not ported**: CompCert gives
  `__builtin_bswap*`, `__builtin_fabs`, `__builtin_fsqrt`,
  `__builtin_clz/ctz`, `__builtin_fmin/fmax` and so on fixed semantics
  through `known_builtin_sem`, but here they are uninterpreted
  `externalFunctionsSem` (documented).
* **`Smallstep.v`** (`LEAN.md` lists it as ported): only `Star`/`Plus` exist.
  Missing: the `semantics` record, `nostep`, `starN`, `forever`/`forever_N`
  (divergence), `safe`, `determinate`/`receptive` as records, and
  forward/backward simulations.
* **`Behaviors.v`**: not ported. There is no `program_behaves` (terminates,
  diverges, reacts, goes wrong), so the port has no notion of divergence or
  "goes wrong".
* **`Linking.v`**: a Clight-specific `linkProgram` exists. The generic
  `Linker` class, `linkorder`, `match_program` and pass composition are not
  ported.
* **`AST.v`** *(the rest is now ported, see Status update 6)*: core types are present. Missing: `transform_program`,
  `transform_partial_program`, `builtin_arg`/`builtin_res`, `rpair`,
  `prog_defmap`, `ef_inline`/`ef_reloads`, `signature_main`, and 17 lemmas.
* **`Ctypes.v`**: syntax and layout are present (`sizeof`/`alignof` match
  Rocq). Missing: the composite invariants (`co_sizeof_pos`,
  `co_alignof_two_p`, `co_sizeof_alignof`, `composite_env_consistent`), the
  attribute operations (`attr_union`, `merge_attributes`,
  `change_attributes`), `default_argument_conversion`, composite linking
  (`link_composite_defs`, `linkorder_program`), and all 62 theorems (the only lemmas here concern `tyBeq`)
  (`sizeof_pos`, `alignof_two_p`, `field_offset_in_range`, `sizeof_struct`
  monotonicity, …).
* **`Cop.v`**: all operators used by Clight are present. Missing:
  `sem_incrdecr` (CompCert C only), `val_casted`, `usual_arithmetic_conversion`
  and related helpers, and all 17 theorems (`cast_val_casted`,
  `sem_binary_operation_inj`, `bool_val_inj`, …).
* **`Clight.v`**: **complete at the definition level.** All 25 `step_*` rules
  and all `eval_*` rules are present, along with `function_entry1/2`,
  `initial_state` and `final_state`. Missing: `semantics1`/`semantics2` (the
  `Smallstep.semantics` instances) and `semantics_receptive`.
  `semantics_determinate` is ported as `step_determ`.

### Not ported at all

* *(Now ported, see Status update 6.)* `cfrontend/ClightBigstep.v` (big-step semantics and its equivalence with
  the small-step one).
* `cfrontend/Ctyping.v` (the CompCert C type checker and type-soundness
  results). *(The type system, the checker and its soundness are now ported,
  see Status update 10; subject reduction is still missing.)*
* CompCert C *(`Csyntax.v`, `Csem.v`, `Cstrategy.v` and `Initializers.v`
  are now ported, see Status updates 9 and 10, and `Cexec.v` (the reference
  interpreter), see Status update 13)*. `clightgen -lean -csyntax` is rejected.
* Every compiler pass and its correctness proof (`SimplExpr`, `SimplLocals`,
  `Cshmgen`, `Cminorgen`, and all of `backend/`). *(The `SimplExpr` pass and
  its specification `SimplExprspec.v`, and the `SimplLocals`, `Cshmgen` and
  `Cminorgen` passes (with the Csharpminor and Cminor syntax) are now
  ported, see Status update 14; the semantic-preservation proofs and the
  `backend/` passes are not.)* Nothing links a Lean proof
  to compiled code (documented).
* **Targets other than aarch64**: `CCLib/aarch64/Archi.lean` hard-codes aarch64
  (`ptr64`, little-endian). There is no x86_32/x86_64/arm/riscV/powerpc
  configuration and no `abi` parameter. *(Partly addressed: see Status
  update 22. The x86-64 and RV64 back-end definitions are ported, and the
  parameters of all targets are in `CCLib/targets/Archi.lean`.)* Its header says the NaN parameters
  (`default_nan_*`, `choose_nan_*`, `fma_order`,
  `float_of_single_preserves_sNaN`, …) are "handled in `CCLib.lib.Floats`", but
  they are not. NaN payloads come from whatever host machine runs Lean.

### Missing on the program-logic side (from `LEAN.md` §9, confirmed)

Interpreter completeness, external-call specifications (`malloc`/`free`/
`memcpy` as Hoare specs), volatile accesses, partial correctness and
divergence, fractional permissions, the magic wand, frame inference, and
invariant inference.

## 4. Inconsistencies in the documentation

* `README.md` says "~6.5k lines of Lean". `LEAN.md` says ~15k, and
  `wc -l export/CCLib/*.lean` gives about 15.3k (including `CCLib.lean`).
* `README.md` says "526 whole-program comparisons". `LEAN.md` says
  16 + 500 = 516.
* `CCLib/lib/Floats.lean` says "the differential test corpus is integer-only".
  `LEAN.md` says a floating-point program agrees exactly. Neither covers
  out-of-range conversions, int64 → float32 rounding, or `fabs(-0.0)`, which
  is why §1 went unnoticed.
* The `CCLib/lib/Integers.lean` header credits `bv_decide` with replacing the
  Rocq proofs. `LEAN.md` says `bv_decide` is never used, and that is correct.
* `LEAN.md` says "CompCert 3.18", but `VERSION` and `main.lean` say 3.17.
* The `CCLib/aarch64/Archi.lean` header promises `@[irreducible]`-style opacity, but
  the definitions are plain `def`s.
* `LEAN.md` says the development has no Mathlib dependency. That holds for
  `export/`, but the root `lakefile.toml` requires Mathlib (see §0).

## 5. Suggested priorities

1. Fix the three float bugs in §1, and add out-of-range and edge cases to the
   differential suite.
2. Repair or remove the root `lakefile.toml` so the port builds from the
   repository root (for example: one `CCLib` library with `srcDir = "export"`).
3. Port the theorem layers most needed for verification work: `Maps` (`gss`,
   `gempty`, remove, `elements`), the general `Memory` load/store/alloc/free
   algebra, and the `Integers` `repr`/`unsigned`/`signed` lemmas.
4. Port `Builtins0/1` so the common builtins get semantics.
5. Port `Smallstep.semantics`, `forever` and `Behaviors` to support
   divergence and "goes wrong"; then `Ctyping`.
6. If proofs about float arithmetic are wanted, replace the host-`Float`
   substitution with a kernel-reducible IEEE model (a Flocq-style port, or a
   bit-level softfloat proved against a real-number spec).
