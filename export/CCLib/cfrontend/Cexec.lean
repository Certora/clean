/-
  Animating the CompCert C semantics — port of `cfrontend/Cexec.v`, the
  reference interpreter behind `ccomp -interp`: the definitions.

  This file has the executable part of `Cexec.v`:
  * `isVal`/`isLoc`/`isValList`/`isSkip`;
  * conversions between values and event values (`eventvalOfVal`,
    `listEventvalOfVal`, `valOfEventval`);
  * volatile accesses and memory accesses at a location (`doVolatileLoad`,
    `doVolatileStore`, `doDerefLoc`, `doAssignLoc`);
  * external functions and builtins (`doExternal` and the `doEf*` functions);
  * the reduction of expressions: the type `Reduction`, reduct lists and
    `stepExpr`/`stepExprlist`, which list *every* possible reduct of an
    expression (the semantics leaves evaluation order unspecified);
  * function entry (`doAllocVariables`, `semBindParameters`);
  * the transition function `doStep`, which lists every transition of a state,
    and `doInitialState`/`atFinalState`.

  Its theorems are in `CCLib.cfrontend.CexecEvents` (events, memory accesses, external
  calls), `CCLib.cfrontend.CexecExpr` (inversion lemmas and the reduct invariants),
  `CCLib.cfrontend.CexecExprSound` (`stepExpr_sound`), `CCLib.cfrontend.CexecComplete`
  (`step_expr_context`, `not_imm_safe_t`) and `CCLib.cfrontend.CexecStep`
  (`do_step_sound`, `do_step_complete`).

  Notes on faithfulness:
  * Rocq's `Section EXEC` has the variables `do_external_function` and
    `do_inline_assembly` (how to run an external function or an inline
    assembly statement in a given world).  Here they are the two fields of an
    `ExtOracle`, passed explicitly; the hypotheses Rocq states about them are
    the structures `ExtOracle.Sound` and `ExtOracle.Complete` (in
    `CCLib.cfrontend.CexecEvents`).  `ExtOracle.none` is the oracle that runs nothing.
  * Worlds are the state machines of `CCLib.common.Worlds` (Rocq: a coinductive type).
  * `free`: the port's `Events.ExtcallFreeSem` accepts a pointer `Vptr b lo`
    with any offset `lo` (the size is read at `lo - size_chunk Mptr`), a
    slightly more general rule than the one in this CompCert version (which
    requires `lo = 0`).  `doEfFree` follows the port's semantics, so that it is
    sound and complete for it.
  * `memcpy`: likewise `memcpyArgsOk` uses `sz % al = 0` (the port's
    `ExtcallMemcpySem`) where Rocq writes `(al | sz)`; the two are equivalent.
  * The non-volatile cases of `doVolatileLoad`/`doVolatileStore` use
    `Mem.load`/`Mem.store` where Rocq writes `Mem.loadv`/`Mem.storev`: the
    port's `loadv`/`storev` add a check that the access does not wrap around
    the address space, which `Events.volatile_load`/`volatile_store` (stated
    with `Mem.load`/`Mem.store`, here as in Rocq) do not have.  In Rocq the two
    forms are equal.
  * The soundness and completeness theorems assume
    `Genv.SymbInjective ge.genv_genv` (distinct identifiers have distinct
    blocks), which Rocq gets from `Genv.find_invert_symbol`; it holds for every
    environment built by `Genv.globalenv`.
  * Decisions that Rocq takes with `sumbool`s (`type_eq`, `check_assign_copy`,
    `Decidable` instances) are decidable propositions here.
-/
import CCLib.cfrontend.Csem
import CCLib.common.Worlds

namespace CC
namespace Cexec

open Csyntax Csem

/-! ## Recognizing values and locations -/

/-- `Cexec.is_val` -/
def isVal : Csyntax.Expr → Option (Val × Ty)
  | .Eval v ty => some (v, ty)
  | _ => none

/-- `Cexec.is_loc` -/
def isLoc : Csyntax.Expr → Option (Block × Integers.Ptrofs × Bitfield × Ty)
  | .Eloc b ofs bf ty => some (b, ofs, bf, ty)
  | _ => none

/-- `Cexec.is_val_list` -/
def isValList : Csyntax.ExprList → Option (List (Val × Ty))
  | .Enil => some []
  | .Econs a1 al =>
      match isVal a1 with
      | some vt1 =>
          match isValList al with
          | some vtl => some (vt1 :: vtl)
          | none => none
      | none => none

/-- `Cexec.is_skip` -/
def isSkip : Csyntax.Stmt → Bool
  | .Sskip => true
  | _ => false

/-! ## External functions run by an oracle -/

/-- The type of `do_external_function` and `do_inline_assembly`: given a name
    (or assembly text), a signature, a symbol environment, a world, the
    arguments and the memory, either get stuck or return the new world, the
    trace, the result and the new memory. -/
abbrev ExtDo :=
  String → Signature → Senv → World → List Val → Mem → Option (World × Trace × Val × Mem)

/-- The section variables `do_external_function` and `do_inline_assembly` of
    `Cexec.v`. -/
structure ExtOracle where
  doExternalFunction : ExtDo
  doInlineAssembly : ExtDo

/-- The oracle that runs no external function and no inline assembly. -/
def ExtOracle.none : ExtOracle :=
  { doExternalFunction := fun _ _ _ _ _ _ => Option.none
    doInlineAssembly := fun _ _ _ _ _ _ => Option.none }

section EXEC

variable (ge : Csem.CGenv)

/-! ## Events -/

/-- `Cexec.eventval_of_val` -/
def eventvalOfVal (v : Val) (t : ATyp) : Option EventVal :=
  match v with
  | .Vint i => if t = .Tint then some (.EVint i) else none
  | .Vfloat f => if t = .Tfloat then some (.EVfloat f) else none
  | .Vsingle f => if t = .Tsingle then some (.EVsingle f) else none
  | .Vlong n => if t = .Tlong then some (.EVlong n) else none
  | .Vptr b ofs =>
      match Genv.invertSymbol ge.genv_genv b with
      | some id =>
          if Genv.publicSymbol ge.genv_genv id then
            if t = Tptr then some (.EVptr_global id ofs) else none
          else none
      | none => none
  | _ => none

/-- `Cexec.list_eventval_of_val` -/
def listEventvalOfVal : List Val → List ATyp → Option (List EventVal)
  | [], [] => some []
  | v1 :: vl, t1 :: tl =>
      match eventvalOfVal ge v1 t1 with
      | some ev1 =>
          match listEventvalOfVal vl tl with
          | some evl => some (ev1 :: evl)
          | none => none
      | none => none
  | _, _ => none

/-- `Cexec.val_of_eventval` -/
def valOfEventval (ev : EventVal) (t : ATyp) : Option Val :=
  match ev with
  | .EVint i => if t = .Tint then some (.Vint i) else none
  | .EVfloat f => if t = .Tfloat then some (.Vfloat f) else none
  | .EVsingle f => if t = .Tsingle then some (.Vsingle f) else none
  | .EVlong n => if t = .Tlong then some (.Vlong n) else none
  | .EVptr_global id ofs =>
      if Genv.publicSymbol ge.genv_genv id then
        if t = Tptr then
          match Genv.findSymbol ge.genv_genv id with
          | some b => some (.Vptr b ofs)
          | none => none
        else none
      else none

/-! ## Volatile memory accesses -/

/-- `Cexec.do_volatile_load` -/
def doVolatileLoad (w : World) (chunk : Chunk) (m : Mem) (b : Block) (ofs : Integers.Ptrofs) :
    Option (World × Trace × Val) :=
  if Genv.blockIsVolatile ge.genv_genv b then
    match Genv.invertSymbol ge.genv_genv b with
    | some id =>
        match nextworldVload w chunk id ofs with
        | none => none
        | some (res, w') =>
            match valOfEventval ge res (Chunk.typ chunk) with
            | some vres => some (w', [Event.Event_vload chunk id ofs res], Val.loadResult chunk vres)
            | none => none
    | none => none
  else
    match Mem.load chunk m b (Integers.Ptrofs.unsigned ofs) with
    | some v => some (w, E0, v)
    | none => none

/-- `Cexec.do_volatile_store` -/
def doVolatileStore (w : World) (chunk : Chunk) (m : Mem) (b : Block) (ofs : Integers.Ptrofs)
    (v : Val) : Option (World × Trace × Mem × Val) :=
  if Genv.blockIsVolatile ge.genv_genv b then
    match Genv.invertSymbol ge.genv_genv b with
    | some id =>
        match eventvalOfVal ge (Val.loadResult chunk v) (Chunk.typ chunk) with
        | some ev =>
            match nextworldVstore w chunk id ofs ev with
            | some w' => some (w', [Event.Event_vstore chunk id ofs ev], m, v)
            | none => none
        | none => none
    | none => none
  else
    match Mem.store chunk m b (Integers.Ptrofs.unsigned ofs) v with
    | some m' => some (w, E0, m', v)
    | none => none

/-! ## Accessing locations -/

/-- The side conditions on a bitfield access shared by `do_deref_loc` and
    `do_assign_loc` (Rocq writes them as a `&&` of `proj_sumbool`s). -/
def bitfieldRangeOk (sz : IntSize) (pos width : Z) : Prop :=
  0 ≤ pos ∧ 0 < width ∧ width ≤ bitsizeIntsize sz ∧ pos + width ≤ Cop.bitsizeCarrier sz

instance (sz : IntSize) (pos width : Z) : Decidable (bitfieldRangeOk sz pos width) := by
  unfold bitfieldRangeOk; infer_instance

/-- `Cexec.do_deref_loc` -/
def doDerefLoc (w : World) (ty : Ty) (m : Mem) (b : Block) (ofs : Integers.Ptrofs)
    (bf : Bitfield) : Option (World × Trace × Val) :=
  match bf with
  | .Full =>
      match accessMode ty with
      | .By_value chunk =>
          match typeIsVolatile ty with
          | false =>
              match Mem.loadv chunk m (.Vptr b ofs) with
              | some v => some (w, E0, v)
              | none => none
          | true => doVolatileLoad ge w chunk m b ofs
      | .By_reference => some (w, E0, .Vptr b ofs)
      | .By_copy => some (w, E0, .Vptr b ofs)
      | _ => none
  | .Bits sz sg pos width =>
      match ty with
      | .Tint sz1 sg1 _ =>
          if sz1 = sz ∧ sg1 = (if width < bitsizeIntsize sz then Signedness.Signed else sg)
              ∧ bitfieldRangeOk sz pos width then
            match Mem.loadv (Cop.chunkForCarrier sz) m (.Vptr b ofs) with
            | some (.Vint c) => some (w, E0, .Vint (Cop.bitfieldExtract sz sg pos width c))
            | _ => none
          else none
      | _ => none

/-- `Cexec.assign_copy_ok` -/
def AssignCopyOk (ty : Ty) (b : Block) (ofs : Integers.Ptrofs) (b' : Block)
    (ofs' : Integers.Ptrofs) : Prop :=
  alignofBlockcopy ge.genv_cenv ty ∣ Integers.Ptrofs.unsigned ofs' ∧
  alignofBlockcopy ge.genv_cenv ty ∣ Integers.Ptrofs.unsigned ofs ∧
  (b' ≠ b ∨ Integers.Ptrofs.unsigned ofs' = Integers.Ptrofs.unsigned ofs
    ∨ Integers.Ptrofs.unsigned ofs' + sizeof ge.genv_cenv ty ≤ Integers.Ptrofs.unsigned ofs
    ∨ Integers.Ptrofs.unsigned ofs + sizeof ge.genv_cenv ty ≤ Integers.Ptrofs.unsigned ofs')

/-- `Cexec.check_assign_copy` -/
instance (ty : Ty) (b : Block) (ofs : Integers.Ptrofs) (b' : Block) (ofs' : Integers.Ptrofs) :
    Decidable (AssignCopyOk ge ty b ofs b' ofs') := by
  unfold AssignCopyOk; infer_instance

/-- `Cexec.do_assign_loc` -/
def doAssignLoc (w : World) (ty : Ty) (m : Mem) (b : Block) (ofs : Integers.Ptrofs)
    (bf : Bitfield) (v : Val) : Option (World × Trace × Mem × Val) :=
  match bf with
  | .Full =>
      match accessMode ty with
      | .By_value chunk =>
          match typeIsVolatile ty with
          | false =>
              match Mem.storev chunk m (.Vptr b ofs) v with
              | some m' => some (w, E0, m', v)
              | none => none
          | true => doVolatileStore ge w chunk m b ofs v
      | .By_copy =>
          match v with
          | .Vptr b' ofs' =>
              if AssignCopyOk ge ty b ofs b' ofs' then
                match Mem.loadbytes m b' (Integers.Ptrofs.unsigned ofs') (sizeof ge.genv_cenv ty) with
                | some bytes =>
                    match Mem.storebytes m b (Integers.Ptrofs.unsigned ofs) bytes with
                    | some m' => some (w, E0, m', v)
                    | none => none
                | none => none
              else none
          | _ => none
      | _ => none
  | .Bits sz sg pos width =>
      if bitfieldRangeOk sz pos width then
        match ty, v, Mem.loadv (Cop.chunkForCarrier sz) m (.Vptr b ofs) with
        | .Tint sz1 sg1 _, .Vint n, some (.Vint c) =>
            if sz1 = sz ∧ sg1 = (if width < bitsizeIntsize sz then Signedness.Signed else sg) then
              match Mem.storev (Cop.chunkForCarrier sz) m (.Vptr b ofs)
                  (.Vint (Integers.Int.bitfield_insert (Cop.firstBit sz pos width).toNat
                    width.toNat c n)) with
              | some m' => some (w, E0, m', .Vint (Cop.bitfieldNormalize sz sg width n))
              | none => none
            else none
        | _, _, _ => none
      else none

/-! ## External calls -/

variable (ox : ExtOracle)

/-- `Cexec.do_ef_volatile_load` -/
def doEfVolatileLoad (chunk : Chunk) (w : World) (vargs : List Val) (m : Mem) :
    Option (World × Trace × Val × Mem) :=
  match vargs with
  | [.Vptr b ofs] =>
      match doVolatileLoad ge w chunk m b ofs with
      | some (w', t, v) => some (w', t, v, m)
      | none => none
  | _ => none

/-- `Cexec.do_ef_volatile_store` -/
def doEfVolatileStore (chunk : Chunk) (w : World) (vargs : List Val) (m : Mem) :
    Option (World × Trace × Val × Mem) :=
  match vargs with
  | [.Vptr b ofs, v] =>
      match doVolatileStore ge w chunk m b ofs v with
      | some (w', t, m', _) => some (w', t, .Vundef, m')
      | none => none
  | _ => none

/-- `Cexec.do_ef_volatile_load_global` -/
def doEfVolatileLoadGlobal (chunk : Chunk) (id : Ident) (ofs : Integers.Ptrofs) (w : World)
    (vargs : List Val) (m : Mem) : Option (World × Trace × Val × Mem) :=
  match Genv.findSymbol ge.genv_genv id with
  | some b => doEfVolatileLoad ge chunk w (.Vptr b ofs :: vargs) m
  | none => none

/-- `Cexec.do_ef_volatile_store_global` -/
def doEfVolatileStoreGlobal (chunk : Chunk) (id : Ident) (ofs : Integers.Ptrofs) (w : World)
    (vargs : List Val) (m : Mem) : Option (World × Trace × Val × Mem) :=
  match Genv.findSymbol ge.genv_genv id with
  | some b => doEfVolatileStore ge chunk w (.Vptr b ofs :: vargs) m
  | none => none

/-- `Cexec.do_alloc_size` -/
def doAllocSize : Val → Option Integers.Ptrofs
  | .Vint n => if Archi.ptr64 then none else some (Integers.Ptrofs.of_intu n)
  | .Vlong n => if Archi.ptr64 then some (Integers.Ptrofs.of_int64 n) else none
  | _ => none

/-- `Cexec.do_ef_malloc` -/
def doEfMalloc (w : World) (vargs : List Val) (m : Mem) : Option (World × Trace × Val × Mem) :=
  match vargs with
  | [v] =>
      match doAllocSize v with
      | some sz =>
          let (m', b) := Mem.alloc m (- sizeChunk Mptr) (Integers.Ptrofs.unsigned sz)
          match Mem.store Mptr m' b (- sizeChunk Mptr) v with
          | some m'' => some (w, E0, .Vptr b Integers.Ptrofs.zero, m'')
          | none => none
      | none => none
  | _ => none

/-- `Cexec.do_ef_free` (for the port's `ExtcallFreeSem`, see the header). -/
def doEfFree (w : World) (vargs : List Val) (m : Mem) : Option (World × Trace × Val × Mem) :=
  match vargs with
  | [.Vptr b lo] =>
      match Mem.load Mptr m b (Integers.Ptrofs.unsigned lo - sizeChunk Mptr) with
      | some vsz =>
          match doAllocSize vsz with
          | some sz =>
              match Mem.free m b (Integers.Ptrofs.unsigned lo - sizeChunk Mptr)
                  (Integers.Ptrofs.unsigned lo + Integers.Ptrofs.unsigned sz) with
              | some m' => some (w, E0, .Vundef, m')
              | none => none
          | none => none
      | none => none
  | [.Vint n] =>
      if n = Integers.Int.zero ∧ Archi.ptr64 = false then some (w, E0, .Vundef, m) else none
  | [.Vlong n] =>
      if n = Integers.Int64.zero ∧ Archi.ptr64 = true then some (w, E0, .Vundef, m) else none
  | _ => none

/-- `Cexec.memcpy_args_ok` -/
def MemcpyArgsOk (sz al : Z) (bdst : Block) (odst : Z) (bsrc : Block) (osrc : Z) : Prop :=
  (al = 1 ∨ al = 2 ∨ al = 4 ∨ al = 8)
  ∧ sz ≥ 0 ∧ sz % al = 0
  ∧ (sz > 0 → osrc % al = 0)
  ∧ (sz > 0 → odst % al = 0)
  ∧ (bsrc ≠ bdst ∨ osrc = odst ∨ osrc + sz ≤ odst ∨ odst + sz ≤ osrc)

instance (sz al : Z) (bdst : Block) (odst : Z) (bsrc : Block) (osrc : Z) :
    Decidable (MemcpyArgsOk sz al bdst odst bsrc osrc) := by
  unfold MemcpyArgsOk; infer_instance

/-- `Cexec.do_ef_memcpy` -/
def doEfMemcpy (sz al : Z) (w : World) (vargs : List Val) (m : Mem) :
    Option (World × Trace × Val × Mem) :=
  match vargs with
  | [.Vptr bdst odst, .Vptr bsrc osrc] =>
      if MemcpyArgsOk sz al bdst (Integers.Ptrofs.unsigned odst) bsrc
          (Integers.Ptrofs.unsigned osrc) then
        match Mem.loadbytes m bsrc (Integers.Ptrofs.unsigned osrc) sz with
        | some bytes =>
            match Mem.storebytes m bdst (Integers.Ptrofs.unsigned odst) bytes with
            | some m' => some (w, E0, .Vundef, m')
            | none => none
        | none => none
      else none
  | _ => none

/-- `Cexec.do_ef_annot` -/
def doEfAnnot (text : String) (targs : List ATyp) (w : World) (vargs : List Val) (m : Mem) :
    Option (World × Trace × Val × Mem) :=
  match listEventvalOfVal ge vargs targs with
  | some args => some (w, [Event.Event_annot text args], .Vundef, m)
  | none => none

/-- `Cexec.do_ef_annot_val` -/
def doEfAnnotVal (text : String) (targ : ATyp) (w : World) (vargs : List Val) (m : Mem) :
    Option (World × Trace × Val × Mem) :=
  match vargs with
  | [varg] =>
      match eventvalOfVal ge varg targ with
      | some arg => some (w, [Event.Event_annot text [arg]], varg, m)
      | none => none
  | _ => none

/-- `Cexec.do_ef_debug` -/
def doEfDebug (w : World) (_vargs : List Val) (m : Mem) : Option (World × Trace × Val × Mem) :=
  some (w, E0, .Vundef, m)

/-- `Cexec.do_builtin_or_external` -/
def doBuiltinOrExternal (name : String) (sg : Signature) (w : World) (vargs : List Val)
    (m : Mem) : Option (World × Trace × Val × Mem) :=
  match Builtins.lookupBuiltinFunction name sg with
  | some bf =>
      match (Builtins.builtinFunctionSem bf).sem vargs with
      | some v => some (w, E0, v, m)
      | none => none
  | none => ox.doExternalFunction name sg ge.genv_genv.toSenv w vargs m

/-- `Cexec.do_external` -/
def doExternal (ef : ExtFun) : World → List Val → Mem → Option (World × Trace × Val × Mem) :=
  match ef with
  | .EF_external name sg => ox.doExternalFunction name sg ge.genv_genv.toSenv
  | .EF_builtin name sg => doBuiltinOrExternal ge ox name sg
  | .EF_runtime name sg => doBuiltinOrExternal ge ox name sg
  | .EF_vload chunk => doEfVolatileLoad ge chunk
  | .EF_vstore chunk => doEfVolatileStore ge chunk
  | .EF_malloc => doEfMalloc
  | .EF_free => doEfFree
  | .EF_memcpy sz al => doEfMemcpy sz al
  | .EF_annot _ text targs => doEfAnnot ge text targs
  | .EF_annot_val _ text targ => doEfAnnotVal ge text targ
  | .EF_inline_asm text sg _ => ox.doInlineAssembly text sg ge.genv_genv.toSenv
  | .EF_debug _ _ _ => doEfDebug

end EXEC

/-! ## Reduction of expressions -/

/-- `Cexec.reduction`: one way of reducing an expression; the string names the
    rule of `Csem` that was used. -/
inductive Reduction where
  | Lred (rule : String) (l' : Csyntax.Expr) (m' : Mem)
  | Rred (rule : String) (r' : Csyntax.Expr) (m' : Mem) (t : Trace)
  | Callred (rule : String) (fd : Csyntax.FunDef) (args : List Val) (tyres : Ty) (m' : Mem)
  | Stuckred

/-- `Cexec.sem_cast_arguments` -/
def semCastArguments : List (Val × Ty) → List Ty → Mem → Option (List Val)
  | [], [], _ => some []
  | (v1, t1) :: vtl, t1' :: tl, m =>
      match Cop.semCast v1 t1 t1' m with
      | some v =>
          match semCastArguments vtl tl m with
          | some vl => some (v :: vl)
          | none => none
      | none => none
  | _, _, _ => none

/-- `Cexec.reducts`: the result of stepping an expression, a list of pairs of
    a context and a reduction to apply in this context.  The list is empty if
    the expression is fully reduced (`Eval` for an r-value, `Eloc` for an
    l-value). -/
abbrev Reducts (A : Type) : Type := List ((Csyntax.Expr → A) × Reduction)

/-- `Cexec.topred` -/
def topred (r : Reduction) : Reducts Csyntax.Expr := [(fun x => x, r)]

/-- `Cexec.stuck` -/
def stuck : Reducts Csyntax.Expr := [(fun x => x, .Stuckred)]

/-- `Cexec.incontext` -/
def incontext {A B : Type} (ctx : A → B) (ll : Reducts A) : Reducts B :=
  ll.map fun z => (fun x => ctx (z.1 x), z.2)

/-- `Cexec.incontext2` -/
def incontext2 {A1 A2 B : Type} (ctx1 : A1 → B) (ll1 : Reducts A1)
    (ctx2 : A2 → B) (ll2 : Reducts A2) : Reducts B :=
  incontext ctx1 ll1 ++ incontext ctx2 ll2

section EXPRS

variable (ge : Csem.CGenv) (ox : ExtOracle) (e : Env) (w : World)

mutual
/-- `Cexec.step_expr`: all the reducts of expression `a` (of kind `k`) in
    memory `m`. -/
def stepExpr (k : Csem.Kind) (a : Csyntax.Expr) (m : Mem) : Reducts Csyntax.Expr :=
  match k, a with
  | .LV, .Eloc _ _ _ _ => []
  | .LV, .Evar x ty =>
      match e.get x with
      | some (b, ty') =>
          if ty = ty' then topred (.Lred "red_var_local" (.Eloc b Integers.Ptrofs.zero .Full ty) m)
          else stuck
      | none =>
          match Genv.findSymbol ge.genv_genv x with
          | some b => topred (.Lred "red_var_global" (.Eloc b Integers.Ptrofs.zero .Full ty) m)
          | none => stuck
  | .LV, .Ederef r ty =>
      match isVal r with
      | some (.Vptr b ofs, _) => topred (.Lred "red_deref" (.Eloc b ofs .Full ty) m)
      | some _ => stuck
      | none => incontext (fun x => .Ederef x ty) (stepExpr .RV r m)
  | .LV, .Efield r f ty =>
      match isVal r with
      | some (.Vptr b ofs, ty') =>
          match ty' with
          | .Tstruct id _ =>
              match ge.genv_cenv.get id with
              | some co =>
                  match fieldOffset ge.genv_cenv f co.co_members with
                  | .Error _ => stuck
                  | .OK (delta, bf) =>
                      topred (.Lred "red_field_struct"
                        (.Eloc b (Integers.Ptrofs.add ofs (Integers.Ptrofs.repr delta)) bf ty) m)
              | none => stuck
          | .Tunion id _ =>
              match ge.genv_cenv.get id with
              | some co =>
                  match unionFieldOffset ge.genv_cenv f co.co_members with
                  | .Error _ => stuck
                  | .OK (delta, bf) =>
                      topred (.Lred "red_field_union"
                        (.Eloc b (Integers.Ptrofs.add ofs (Integers.Ptrofs.repr delta)) bf ty) m)
              | none => stuck
          | _ => stuck
      | some _ => stuck
      | none => incontext (fun x => .Efield x f ty) (stepExpr .RV r m)
  | .RV, .Eval _ _ => []
  | .RV, .Evalof l ty =>
      match isLoc l with
      | some (b, ofs, bf, ty') =>
          if ty = ty' then
            match doDerefLoc ge w ty m b ofs bf with
            | some (_, t, v) => topred (.Rred "red_rvalof" (.Eval v ty) m t)
            | none => stuck
          else stuck
      | none => incontext (fun x => .Evalof x ty) (stepExpr .LV l m)
  | .RV, .Eaddrof l ty =>
      match isLoc l with
      | some (b, ofs, bf, _) =>
          match bf with
          | .Full => topred (.Rred "red_addrof" (.Eval (.Vptr b ofs) ty) m E0)
          | .Bits _ _ _ _ => stuck
      | none => incontext (fun x => .Eaddrof x ty) (stepExpr .LV l m)
  | .RV, .Eunop op r1 ty =>
      match isVal r1 with
      | some (v1, ty1) =>
          match Cop.semUnaryOperation op v1 ty1 m with
          | some v => topred (.Rred "red_unop" (.Eval v ty) m E0)
          | none => stuck
      | none => incontext (fun x => .Eunop op x ty) (stepExpr .RV r1 m)
  | .RV, .Ebinop op r1 r2 ty =>
      match isVal r1, isVal r2 with
      | some (v1, ty1), some (v2, ty2) =>
          match Cop.semBinaryOperation ge.genv_cenv op v1 ty1 v2 ty2 m with
          | some v => topred (.Rred "red_binop" (.Eval v ty) m E0)
          | none => stuck
      | _, _ =>
          incontext2 (fun x => .Ebinop op x r2 ty) (stepExpr .RV r1 m)
            (fun x => .Ebinop op r1 x ty) (stepExpr .RV r2 m)
  | .RV, .Ecast r1 ty =>
      match isVal r1 with
      | some (v1, ty1) =>
          match Cop.semCast v1 ty1 ty m with
          | some v => topred (.Rred "red_cast" (.Eval v ty) m E0)
          | none => stuck
      | none => incontext (fun x => .Ecast x ty) (stepExpr .RV r1 m)
  | .RV, .Eseqand r1 r2 ty =>
      match isVal r1 with
      | some (v1, ty1) =>
          match Cop.boolVal v1 ty1 m with
          | some b =>
              if b then topred (.Rred "red_seqand_true" (.Eparen r2 type_bool ty) m E0)
              else topred (.Rred "red_seqand_false" (.Eval (.Vint Integers.Int.zero) ty) m E0)
          | none => stuck
      | none => incontext (fun x => .Eseqand x r2 ty) (stepExpr .RV r1 m)
  | .RV, .Eseqor r1 r2 ty =>
      match isVal r1 with
      | some (v1, ty1) =>
          match Cop.boolVal v1 ty1 m with
          | some b =>
              if b then topred (.Rred "red_seqor_true" (.Eval (.Vint Integers.Int.one) ty) m E0)
              else topred (.Rred "red_seqor_false" (.Eparen r2 type_bool ty) m E0)
          | none => stuck
      | none => incontext (fun x => .Eseqor x r2 ty) (stepExpr .RV r1 m)
  | .RV, .Econdition r1 r2 r3 ty =>
      match isVal r1 with
      | some (v1, ty1) =>
          match Cop.boolVal v1 ty1 m with
          | some b => topred (.Rred "red_condition" (.Eparen (if b then r2 else r3) ty ty) m E0)
          | none => stuck
      | none => incontext (fun x => .Econdition x r2 r3 ty) (stepExpr .RV r1 m)
  | .RV, .Esizeof ty' ty =>
      topred (.Rred "red_sizeof"
        (.Eval (Val.Vptrofs (Integers.Ptrofs.repr (sizeof ge.genv_cenv ty'))) ty) m E0)
  | .RV, .Ealignof ty' ty =>
      topred (.Rred "red_alignof"
        (.Eval (Val.Vptrofs (Integers.Ptrofs.repr (alignof ge.genv_cenv ty'))) ty) m E0)
  | .RV, .Eassign l1 r2 ty =>
      match isLoc l1, isVal r2 with
      | some (b, ofs, bf, ty1), some (v2, ty2) =>
          if ty1 = ty then
            match Cop.semCast v2 ty2 ty1 m with
            | some v =>
                match doAssignLoc ge w ty1 m b ofs bf v with
                | some (_, t, m', v') => topred (.Rred "red_assign" (.Eval v' ty) m' t)
                | none => stuck
            | none => stuck
          else stuck
      | _, _ =>
          incontext2 (fun x => .Eassign x r2 ty) (stepExpr .LV l1 m)
            (fun x => .Eassign l1 x ty) (stepExpr .RV r2 m)
  | .RV, .Eassignop op l1 r2 tyres ty =>
      match isLoc l1, isVal r2 with
      | some (b, ofs, bf, ty1), some (v2, ty2) =>
          if ty1 = ty then
            match doDerefLoc ge w ty1 m b ofs bf with
            | some (_, t, v1) =>
                topred (.Rred "red_assignop"
                  (.Eassign (.Eloc b ofs bf ty1) (.Ebinop op (.Eval v1 ty1) (.Eval v2 ty2) tyres) ty1)
                  m t)
            | none => stuck
          else stuck
      | _, _ =>
          incontext2 (fun x => .Eassignop op x r2 tyres ty) (stepExpr .LV l1 m)
            (fun x => .Eassignop op l1 x tyres ty) (stepExpr .RV r2 m)
  | .RV, .Epostincr id l ty =>
      match isLoc l with
      | some (b, ofs, bf, ty1) =>
          if ty1 = ty then
            match doDerefLoc ge w ty m b ofs bf with
            | some (_, t, v1) =>
                let op := match id with | .Incr => Binop.Oadd | .Decr => Binop.Osub
                topred (.Rred "red_postincr"
                  (.Ecomma (.Eassign (.Eloc b ofs bf ty)
                      (.Ebinop op (.Eval v1 ty) (.Eval (.Vint Integers.Int.one) type_int32s)
                        (Cop.incrdecrType ty)) ty)
                    (.Eval v1 ty) ty) m t)
            | none => stuck
          else stuck
      | none => incontext (fun x => .Epostincr id x ty) (stepExpr .LV l m)
  | .RV, .Ecomma r1 r2 ty =>
      match isVal r1 with
      | some _ =>
          if Csyntax.typeof r2 = ty then topred (.Rred "red_comma" r2 m E0) else stuck
      | none => incontext (fun x => .Ecomma x r2 ty) (stepExpr .RV r1 m)
  | .RV, .Eparen r1 tycast ty =>
      match isVal r1 with
      | some (v1, ty1) =>
          match Cop.semCast v1 ty1 tycast m with
          | some v => topred (.Rred "red_paren" (.Eval v ty) m E0)
          | none => stuck
      | none => incontext (fun x => .Eparen x tycast ty) (stepExpr .RV r1 m)
  | .RV, .Ecall r1 rargs ty =>
      match isVal r1, isValList rargs with
      | some (vf, tyf), some vtl =>
          match Cop.classifyFun tyf with
          | .f tyargs tyres cconv =>
              match Genv.findFunct ge.genv_genv vf with
              | some fd =>
                  match semCastArguments vtl tyargs m with
                  | some vargs =>
                      if Csyntax.typeOfFundef fd = .Tfunction tyargs tyres cconv then
                        topred (.Callred "red_call" fd vargs ty m)
                      else stuck
                  | none => stuck
              | none => stuck
          | _ => stuck
      | _, _ =>
          incontext2 (fun x => .Ecall x rargs ty) (stepExpr .RV r1 m)
            (fun x => .Ecall r1 x ty) (stepExprlist rargs m)
  | .RV, .Ebuiltin ef tyargs rargs ty =>
      match isValList rargs with
      | some vtl =>
          match semCastArguments vtl tyargs m with
          | some vargs =>
              match doExternal ge ox ef w vargs m with
              | none => stuck
              | some (_, t, v, m') => topred (.Rred "red_builtin" (.Eval v ty) m' t)
          | none => stuck
      | none => incontext (fun x => .Ebuiltin ef tyargs x ty) (stepExprlist rargs m)
  | _, _ => stuck

/-- `Cexec.step_exprlist` -/
def stepExprlist (rl : Csyntax.ExprList) (m : Mem) : Reducts Csyntax.ExprList :=
  match rl with
  | .Enil => []
  | .Econs r1 rs =>
      incontext2 (fun x => .Econs x rs) (stepExpr .RV r1 m)
        (fun x => .Econs r1 x) (stepExprlist rs m)
end

end EXPRS

/-! ## Transitions over states -/

/-- `Cexec.do_alloc_variables` -/
def doAllocVariables (ge : Csem.CGenv) : Env → Mem → List (Ident × Ty) → Env × Mem
  | e, m, [] => (e, m)
  | e, m, (id, ty) :: l' =>
      let (m1, b1) := Mem.alloc m 0 (sizeof ge.genv_cenv ty)
      doAllocVariables ge (e.set id (b1, ty)) m1 l'

/-- `Cexec.sem_bind_parameters` -/
def semBindParameters (ge : Csem.CGenv) (w : World) (e : Env) :
    Mem → List (Ident × Ty) → List Val → Option Mem
  | m, [], [] => some m
  | m, (id, ty) :: params, v1 :: lv =>
      match e.get id with
      | some (b, ty') =>
          if ty = ty' then
            match doAssignLoc ge w ty m b Integers.Ptrofs.zero .Full v1 with
            | some (_, t, m1, _) =>
                match t with
                | [] => semBindParameters ge w e m1 params lv
                | _ => none
            | none => none
          else none
      | none => none
  | _, _, _ => none

/-- `Cexec.transition`: a transition, named by the rule of `Csem` it uses. -/
inductive Transition where
  | TR (rule : String) (t : Trace) (S' : Csem.State)

/-- `Cexec.expr_final_state` -/
def exprFinalState (f : Csyntax.Function) (k : Csem.Cont) (e : Env)
    (C_rd : (Csyntax.Expr → Csyntax.Expr) × Reduction) : Transition :=
  match C_rd.2 with
  | .Lred rule a m => .TR rule E0 (.ExprState f (C_rd.1 a) k e m)
  | .Rred rule a m t => .TR rule t (.ExprState f (C_rd.1 a) k e m)
  | .Callred rule fd vargs ty m => .TR rule E0 (.Callstate fd vargs (.Kcall f e C_rd.1 ty k) m)
  | .Stuckred => .TR "step_stuck" E0 .Stuckstate

/-- `Cexec.ret` -/
def ret (rule : String) (S : Csem.State) : List Transition := [.TR rule E0 S]

/-- `Cexec.do_step`: all the transitions of state `s` in world `w`. -/
def doStep (ge : Csem.CGenv) (ox : ExtOracle) (w : World) (s : Csem.State) : List Transition :=
  match s with
  | .ExprState f a k e m =>
      match isVal a with
      | some (v, ty) =>
          match k with
          | .Kdo k => ret "step_do_2" (.State f .Sskip k e m)
          | .Kifthenelse s1 s2 k =>
              match Cop.boolVal v ty m with
              | some b => ret "step_ifthenelse_2" (.State f (if b then s1 else s2) k e m)
              | none => []
          | .Kwhile1 x s k =>
              match Cop.boolVal v ty m with
              | some b =>
                  if b then ret "step_while_true" (.State f s (.Kwhile2 x s k) e m)
                  else ret "step_while_false" (.State f .Sskip k e m)
              | none => []
          | .Kdowhile2 x s k =>
              match Cop.boolVal v ty m with
              | some b =>
                  if b then ret "step_dowhile_true" (.State f (.Sdowhile x s) k e m)
                  else ret "step_dowhile_false" (.State f .Sskip k e m)
              | none => []
          | .Kfor2 a2 a3 s k =>
              match Cop.boolVal v ty m with
              | some b =>
                  if b then ret "step_for_true" (.State f s (.Kfor3 a2 a3 s k) e m)
                  else ret "step_for_false" (.State f .Sskip k e m)
              | none => []
          | .Kreturn k =>
              match Cop.semCast v ty f.fn_return m with
              | some v' =>
                  match Mem.freeList m (blocksOfEnv ge.genv_cenv e) with
                  | some m' => ret "step_return_2" (.Returnstate v' (Csem.callCont k) m')
                  | none => []
              | none => []
          | .Kswitch1 sl k =>
              match Cop.semSwitchArg v ty with
              | some n =>
                  ret "step_expr_switch"
                    (.State f (Csem.seqOfLabeledStatement (Csem.selectSwitch n sl)) (.Kswitch2 k) e m)
              | none => []
          | _ => []
      | none => (stepExpr ge ox e w .RV a m).map (exprFinalState f k e)
  | .State f (.Sdo x) k e m => ret "step_do_1" (.ExprState f x (.Kdo k) e m)
  | .State f (.Ssequence s1 s2) k e m => ret "step_seq" (.State f s1 (.Kseq s2 k) e m)
  | .State f .Sskip (.Kseq s k) e m => ret "step_skip_seq" (.State f s k e m)
  | .State f .Scontinue (.Kseq _ k) e m => ret "step_continue_seq" (.State f .Scontinue k e m)
  | .State f .Sbreak (.Kseq _ k) e m => ret "step_break_seq" (.State f .Sbreak k e m)
  | .State f (.Sifthenelse a s1 s2) k e m =>
      ret "step_ifthenelse_1" (.ExprState f a (.Kifthenelse s1 s2 k) e m)
  | .State f (.Swhile x s) k e m => ret "step_while" (.ExprState f x (.Kwhile1 x s k) e m)
  | .State f .Sskip (.Kwhile2 x s k) e m =>
      ret "step_skip_or_continue_while" (.State f (.Swhile x s) k e m)
  | .State f .Scontinue (.Kwhile2 x s k) e m =>
      ret "step_skip_or_continue_while" (.State f (.Swhile x s) k e m)
  | .State f .Sbreak (.Kwhile2 _ _ k) e m => ret "step_break_while" (.State f .Sskip k e m)
  | .State f (.Sdowhile a s) k e m => ret "step_dowhile" (.State f s (.Kdowhile1 a s k) e m)
  | .State f .Sskip (.Kdowhile1 x s k) e m =>
      ret "step_skip_or_continue_dowhile" (.ExprState f x (.Kdowhile2 x s k) e m)
  | .State f .Scontinue (.Kdowhile1 x s k) e m =>
      ret "step_skip_or_continue_dowhile" (.ExprState f x (.Kdowhile2 x s k) e m)
  | .State f .Sbreak (.Kdowhile1 _ _ k) e m => ret "step_break_dowhile" (.State f .Sskip k e m)
  | .State f (.Sfor a1 a2 a3 s) k e m =>
      if isSkip a1 then ret "step_for" (.ExprState f a2 (.Kfor2 a2 a3 s k) e m)
      else ret "step_for_start" (.State f a1 (.Kseq (.Sfor .Sskip a2 a3 s) k) e m)
  | .State f .Sskip (.Kfor3 a2 a3 s k) e m =>
      ret "step_skip_or_continue_for3" (.State f a3 (.Kfor4 a2 a3 s k) e m)
  | .State f .Scontinue (.Kfor3 a2 a3 s k) e m =>
      ret "step_skip_or_continue_for3" (.State f a3 (.Kfor4 a2 a3 s k) e m)
  | .State f .Sbreak (.Kfor3 _ _ _ k) e m => ret "step_break_for3" (.State f .Sskip k e m)
  | .State f .Sskip (.Kfor4 a2 a3 s k) e m =>
      ret "step_skip_for4" (.State f (.Sfor .Sskip a2 a3 s) k e m)
  | .State _ (.Sreturn none) k e m =>
      match Mem.freeList m (blocksOfEnv ge.genv_cenv e) with
      | some m' => ret "step_return_0" (.Returnstate .Vundef (Csem.callCont k) m')
      | none => []
  | .State f (.Sreturn (some x)) k e m => ret "step_return_1" (.ExprState f x (.Kreturn k) e m)
  | .State _ .Sskip .Kstop e m =>
      match Mem.freeList m (blocksOfEnv ge.genv_cenv e) with
      | some m' => ret "step_skip_call" (.Returnstate .Vundef .Kstop m')
      | none => []
  | .State _ .Sskip (.Kcall f' e' C ty k) e m =>
      match Mem.freeList m (blocksOfEnv ge.genv_cenv e) with
      | some m' => ret "step_skip_call" (.Returnstate .Vundef (.Kcall f' e' C ty k) m')
      | none => []
  | .State f (.Sswitch x sl) k e m => ret "step_switch" (.ExprState f x (.Kswitch1 sl k) e m)
  | .State f .Sskip (.Kswitch2 k) e m => ret "step_skip_break_switch" (.State f .Sskip k e m)
  | .State f .Sbreak (.Kswitch2 k) e m => ret "step_skip_break_switch" (.State f .Sskip k e m)
  | .State f .Scontinue (.Kswitch2 k) e m =>
      ret "step_continue_switch" (.State f .Scontinue k e m)
  | .State f (.Slabel _ s) k e m => ret "step_label" (.State f s k e m)
  | .State f (.Sgoto lbl) k e m =>
      match Csem.findLabel lbl f.fn_body (Csem.callCont k) with
      | some (s', k') => ret "step_goto" (.State f s' k' e m)
      | none => []
  | .Callstate (.Internal f) vargs k m =>
      if listNorepet (Csyntax.varNames f.fn_params ++ Csyntax.varNames f.fn_vars) then
        let (e, m1) := doAllocVariables ge emptyEnv m (f.fn_params ++ f.fn_vars)
        match semBindParameters ge w e m1 f.fn_params vargs with
        | some m2 => ret "step_internal_function" (.State f f.fn_body k e m2)
        | none => []
      else []
  | .Callstate (.External ef _ _ _) vargs k m =>
      match doExternal ge ox ef w vargs m with
      | none => []
      | some (_, t, v, m') => [.TR "step_external_function" t (.Returnstate v k m')]
  | .Returnstate v (.Kcall f e C ty k) m =>
      ret "step_returnstate" (.ExprState f (C (.Eval v ty)) k e m)
  | _ => []

/-- `Cexec.do_initial_state` -/
def doInitialState (p : Csyntax.Program) : Option (Csem.CGenv × Csem.State) :=
  let ge := globalenv p
  match initMem p with
  | some m0 =>
      match Genv.findSymbol ge.genv_genv p.prog_main with
      | some b =>
          match Genv.findFunctPtr ge.genv_genv b with
          | some f =>
              if Csyntax.typeOfFundef f = .Tfunction [] type_int32s cc_default then
                some (ge, .Callstate f [] .Kstop m0)
              else none
          | none => none
      | none => none
  | none => none

/-- `Cexec.at_final_state` -/
def atFinalState : Csem.State → Option Integers.Int
  | .Returnstate (.Vint r) .Kstop _ => some r
  | _ => none

end Cexec
end CC
