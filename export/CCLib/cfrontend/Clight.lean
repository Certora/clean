/-
  The Clight language: abstract syntax and operational semantics — port of
  `cfrontend/Clight.v` (757 lines, ~97 % definitions; the file contains exactly
  one lemma, `semantics_receptive`, which is pass-proof support and is skipped).

  The *syntax* below (`Expr`, `Stmt`, `Function`, `Program`, `mkprogram`, …) moved
  here from `Clightdefs.lean` so that the semantics can refer to it; every name
  is unchanged, so files emitted by `clightgen -lean` are unaffected.

  The semantics is a small-step relation `Step`, exactly as in Rocq, and is
  parameterized over `functionEntry` so that the two calling conventions
  (parameters as stack variables vs. as temporaries) share one relation.

  Notes on faithfulness:
  * `Clight.genv` in Rocq is a record with *two* `:>` coercions (to `Genv.t` and
    to `composite_env`).  Lean cannot express that, so `CGenv` below has plain
    projections and every use is explicit — mechanical but pervasive.
  * Clight has no volatile handling of its own: volatile accesses arrive already
    reified as `Sbuiltin` with `EF_vload`/`EF_vstore`, so all of that lives in
    `CCLib.common.Events`.
  * `is_call_cont` is a `Prop` in Rocq; here it is a `Bool`, which is equivalent
    and keeps `step_skip_call` decidable.
-/
import CCLib.cfrontend.Cop
import CCLib.common.Events

namespace CC

/-! ## Clight syntax (cfrontend/Clight.v) -/

/-- `Clight.expr` -/
inductive Expr where
  | Econst_int (n : Integers.Int) (t : Ty)
  | Econst_float (n : Floats.Float) (t : Ty)
  | Econst_single (n : Floats.Float32) (t : Ty)
  | Econst_long (n : Integers.Int64) (t : Ty)
  | Evar (id : Ident) (t : Ty)
  | Etempvar (id : Ident) (t : Ty)
  | Ederef (a : Expr) (t : Ty)
  | Eaddrof (a : Expr) (t : Ty)
  | Eunop (op : Unop) (a : Expr) (t : Ty)
  | Ebinop (op : Binop) (a1 : Expr) (a2 : Expr) (t : Ty)
  | Ecast (a : Expr) (t : Ty)
  | Efield (a : Expr) (f : Ident) (t : Ty)
  | Esizeof (t1 : Ty) (t : Ty)
  | Ealignof (t1 : Ty) (t : Ty)

-- `Clight.statement` and `Clight.labeled_statements` (mutually recursive).
mutual
inductive Stmt where
  | Sskip
  | Sassign (e1 : Expr) (e2 : Expr)
  | Sset (id : Ident) (e2 : Expr)
  | Scall (optid : Option Ident) (e1 : Expr) (el : List Expr)
  | Sbuiltin (optid : Option Ident) (ef : ExtFun) (tyl : List Ty) (el : List Expr)
  | Ssequence (s1 : Stmt) (s2 : Stmt)
  | Sifthenelse (e : Expr) (s1 : Stmt) (s2 : Stmt)
  | Sloop (s1 : Stmt) (s2 : Stmt)
  | Sbreak
  | Scontinue
  | Sreturn (e : Option Expr)
  | Sswitch (e : Expr) (cases : LStmts)
  | Slabel (lbl : Ident) (s1 : Stmt)
  | Sgoto (lbl : Ident)

inductive LStmts where
  | LSnil
  | LScons (lbl : Option Int) (s : Stmt) (ls : LStmts)
end

/-- The C `while` loop as a derived form (mirror of `Clight.Swhile`). -/
def swhile (e : Expr) (s : Stmt) : Stmt :=
  Stmt.Sloop (Stmt.Ssequence (Stmt.Sifthenelse e Stmt.Sskip Stmt.Sbreak) s) Stmt.Sskip

/-- `Clight.function` -/
structure Function where
  fn_return : Ty
  fn_callconv : CallConv
  fn_params : List (Ident × Ty)
  fn_vars : List (Ident × Ty)
  fn_temps : List (Ident × Ty)
  fn_body : Stmt

/-- `Clight.fundef` = `Ctypes.fundef function` -/
inductive FunDef where
  | Internal (f : Function)
  | External (ef : ExtFun) (targs : List Ty) (tres : Ty) (cc : CallConv)

/-- `Clight.program` = `Ctypes.program function`.

    Now that `CCLib.cfrontend.Ctypes` provides `buildCompositeEnv`, the program carries its
    composite environment, which `sizeof`/`fieldOffset` — and hence the
    semantics — need.

    CompCert's record additionally carries the *proof*
    `prog_comp_env_eq : build_composite_env prog_types = OK prog_comp_env`,
    which its `mkprogram` discharges from a `wf_composites` argument (the
    generated `.v` files pass `Logic.I`).  We instead store the computed
    environment and expose `compositesWellFormed` as a decidable check, so that
    `mkprogram` keeps the 4-argument shape the `clightgen -lean` printers emit.
    A malformed composite list yields an empty environment rather than a type
    error; `clightgen` only ever emits well-formed ones, and the check below
    lets a test assert it. -/
structure Program where
  prog_defs : List (Ident × GlobDef FunDef Ty)
  prog_public : List Ident
  prog_main : Ident
  prog_types : List CompositeDef
  prog_comp_env : CompositeEnv

/-- Mirror of `Clightdefs.mkprogram`: computes the composite environment from
    the composite definitions. -/
def mkprogram (types : List CompositeDef)
              (defs : List (Ident × GlobDef FunDef Ty))
              (pub : List Ident)
              (main : Ident) : Program :=
  { prog_defs := defs, prog_public := pub, prog_main := main, prog_types := types,
    prog_comp_env := (buildCompositeEnv types).toOption.getD PTree.empty }

/-- Did the composite definitions actually build?  This is the decidable
    counterpart of CompCert's `wf_composites` obligation. -/
def compositesWellFormed (p : Program) : Bool := (buildCompositeEnv p.prog_types).isOK

/-- `sizeof` in a program's own composite environment. -/
def Program.sizeof (p : Program) (t : Ty) : Z := CC.sizeof p.prog_comp_env t
/-- `alignof` in a program's own composite environment. -/
def Program.alignof (p : Program) (t : Ty) : Z := CC.alignof p.prog_comp_env t

/-! ## Global environments for Clight

`Clight.genv` bundles a `Genv` with the program's composite environment.  In Rocq
both fields are `:>` coercions; here the projections are explicit. -/

/-- `Clight.genv` -/
structure CGenv where
  genv_genv : Genv FunDef Ty
  genv_cenv : CompositeEnv

/-- `Ctypes.type_of_params` -/
def typeOfParams (params : List (Ident × Ty)) : List Ty := params.map (·.2)
/-- `Clight.type_of_function` -/
def typeOfFunction (f : Function) : Ty :=
  .Tfunction (typeOfParams f.fn_params) f.fn_return f.fn_callconv
/-- `Clight.type_of_fundef` -/
def typeOfFundef : FunDef → Ty
  | .Internal fd => typeOfFunction fd
  | .External _ args res cc => .Tfunction args res cc

/-- `Clight.globalenv` -/
def Program.globalenv (p : Program) : CGenv :=
  { genv_genv :=
      Genv.addGlobals (Genv.emptyGenv p.prog_public) p.prog_defs
    genv_cenv := p.prog_comp_env }

/-- `Genv.init_mem` for a Clight program. -/
def Program.initMem (p : Program) : Option Mem :=
  Genv.allocGlobals p.globalenv.genv_genv Mem.empty p.prog_defs

/-! ## Local environments -/

/-- `Clight.env` — variable ↦ (block, type). -/
abbrev Env := PTree (Block × Ty)
/-- `Clight.empty_env` -/
def emptyEnv : Env := PTree.empty
/-- `Clight.temp_env` — temporary ↦ value. -/
abbrev TempEnv := PTree Val

/-- `Clight.typeof` — the type annotation carried by an expression. -/
def typeof : Expr → Ty
  | .Econst_int _ ty | .Econst_float _ ty | .Econst_single _ ty
  | .Econst_long _ ty | .Evar _ ty | .Etempvar _ ty
  | .Ederef _ ty | .Eaddrof _ ty | .Eunop _ _ ty | .Ebinop _ _ _ ty
  | .Ecast _ ty | .Efield _ _ ty | .Esizeof _ ty | .Ealignof _ ty => ty

/-! ## Reading and writing a datum at a location -/

/-- `Clight.deref_loc` — the value of the datum of type `ty` at `b, ofs`.
    Access by reference or by copy yields the address itself. -/
inductive DerefLoc (ty : Ty) (m : Mem) (b : Block) (ofs : Integers.Ptrofs) :
    Bitfield → Val → Prop where
  | value (chunk v) :
      accessMode ty = .By_value chunk →
      Mem.loadv chunk m (.Vptr b ofs) = some v →
      DerefLoc ty m b ofs .Full v
  | reference :
      accessMode ty = .By_reference →
      DerefLoc ty m b ofs .Full (.Vptr b ofs)
  | copy :
      accessMode ty = .By_copy →
      DerefLoc ty m b ofs .Full (.Vptr b ofs)
  | bitfield (sz sg pos width v) :
      Cop.LoadBitfield ty sz sg pos width m (.Vptr b ofs) v →
      DerefLoc ty m b ofs (.Bits sz sg pos width) v

/-- `Clight.assign_loc` — store `v` into the datum of type `ty` at `b, ofs`.
    The `copy` case is a block copy with alignment and non-overlap conditions. -/
inductive AssignLoc (ce : CompositeEnv) (ty : Ty) (m : Mem) (b : Block)
    (ofs : Integers.Ptrofs) : Bitfield → Val → Mem → Prop where
  | value (v chunk m') :
      accessMode ty = .By_value chunk →
      Mem.storev chunk m (.Vptr b ofs) v = some m' →
      AssignLoc ce ty m b ofs .Full v m'
  | copy (b' ofs' bytes m') :
      accessMode ty = .By_copy →
      (sizeof ce ty > 0 → Integers.Ptrofs.unsigned ofs' % alignofBlockcopy ce ty = 0) →
      (sizeof ce ty > 0 → Integers.Ptrofs.unsigned ofs % alignofBlockcopy ce ty = 0) →
      (b' ≠ b
        ∨ Integers.Ptrofs.unsigned ofs' = Integers.Ptrofs.unsigned ofs
        ∨ Integers.Ptrofs.unsigned ofs' + sizeof ce ty ≤ Integers.Ptrofs.unsigned ofs
        ∨ Integers.Ptrofs.unsigned ofs + sizeof ce ty ≤ Integers.Ptrofs.unsigned ofs') →
      Mem.loadbytes m b' (Integers.Ptrofs.unsigned ofs') (sizeof ce ty) = some bytes →
      Mem.storebytes m b (Integers.Ptrofs.unsigned ofs) bytes = some m' →
      AssignLoc ce ty m b ofs .Full (.Vptr b' ofs') m'
  | bitfield (sz sg pos width v m' v') :
      Cop.StoreBitfield ty sz sg pos width m (.Vptr b ofs) v m' v' →
      AssignLoc ce ty m b ofs (.Bits sz sg pos width) v m'

/-! ## Function entry: allocating locals and binding parameters -/

/-- `Clight.alloc_variables` -/
inductive AllocVariables (ce : CompositeEnv) :
    Env → Mem → List (Ident × Ty) → Env → Mem → Prop where
  | nil (e m) : AllocVariables ce e m [] e m
  | cons (e m id ty vars m1 b1 m2 e2) :
      Mem.alloc m 0 (sizeof ce ty) = (m1, b1) →
      AllocVariables ce (e.set id (b1, ty)) m1 vars e2 m2 →
      AllocVariables ce e m ((id, ty) :: vars) e2 m2

/-- `Clight.bind_parameters` -/
inductive BindParameters (ce : CompositeEnv) (e : Env) :
    Mem → List (Ident × Ty) → List Val → Mem → Prop where
  | nil (m) : BindParameters ce e m [] [] m
  | cons (m id ty params v1 vl b m1 m2) :
      e.get id = some (b, ty) →
      AssignLoc ce ty m b Integers.Ptrofs.zero .Full v1 m1 →
      BindParameters ce e m1 params vl m2 →
      BindParameters ce e m ((id, ty) :: params) (v1 :: vl) m2

/-- `Clight.create_undef_temps` -/
def createUndefTemps : List (Ident × Ty) → TempEnv
  | [] => PTree.empty
  | (id, _) :: temps' => (createUndefTemps temps').set id .Vundef

/-- `Clight.bind_parameter_temps` -/
def bindParameterTemps : List (Ident × Ty) → List Val → TempEnv → Option TempEnv
  | [], [], le => some le
  | (id, _) :: xl, v :: vl, le => bindParameterTemps xl vl (le.set id v)
  | _, _, _ => none

/-- `Clight.block_of_binding` -/
def blockOfBinding (ce : CompositeEnv) (p : Ident × (Block × Ty)) : Block × Z × Z :=
  (p.2.1, 0, sizeof ce p.2.2)

/-- `Clight.blocks_of_env` — what a `return` must free. -/
def blocksOfEnv (ce : CompositeEnv) (e : Env) : List (Block × Z × Z) :=
  e.elements.map (blockOfBinding ce)

/-- `Clight.set_opttemp` -/
def setOpttemp (optid : Option Ident) (v : Val) (le : TempEnv) : TempEnv :=
  match optid with
  | none => le
  | some id => le.set id v

/-! ## Switch selection -/

/-- `Clight.select_switch_default` -/
def selectSwitchDefault : LStmts → LStmts
  | .LSnil => .LSnil
  | sl@(.LScons none _ _) => sl
  | .LScons (some _) _ sl' => selectSwitchDefault sl'

/-- `Clight.select_switch_case` -/
def selectSwitchCase (n : Z) : LStmts → Option LStmts
  | .LSnil => none
  | .LScons none _ sl' => selectSwitchCase n sl'
  | sl@(.LScons (some c) _ sl') => if c = n then some sl else selectSwitchCase n sl'

/-- `Clight.select_switch` -/
def selectSwitch (n : Z) (sl : LStmts) : LStmts :=
  match selectSwitchCase n sl with
  | some sl' => sl'
  | none => selectSwitchDefault sl

/-- `Clight.seq_of_labeled_statement` -/
def seqOfLabeledStatement : LStmts → Stmt
  | .LSnil => .Sskip
  | .LScons _ s sl' => .Ssequence s (seqOfLabeledStatement sl')

/-! ## Evaluation of expressions

`EvalExpr` and `EvalLvalue` are mutually inductive, as in Rocq.  `Elvalue` is the
rule that turns an l-value into an r-value by dereferencing it. -/

mutual
inductive EvalExpr (ge : CGenv) (e : Env) (le : TempEnv) (m : Mem) :
    Expr → Val → Prop where
  | Econst_int (i ty) : EvalExpr ge e le m (.Econst_int i ty) (.Vint i)
  | Econst_float (f ty) : EvalExpr ge e le m (.Econst_float f ty) (.Vfloat f)
  | Econst_single (f ty) : EvalExpr ge e le m (.Econst_single f ty) (.Vsingle f)
  | Econst_long (i ty) : EvalExpr ge e le m (.Econst_long i ty) (.Vlong i)
  | Etempvar (id ty v) :
      le.get id = some v → EvalExpr ge e le m (.Etempvar id ty) v
  | Eaddrof (a ty loc ofs) :
      EvalLvalue ge e le m a loc ofs .Full →
      EvalExpr ge e le m (.Eaddrof a ty) (.Vptr loc ofs)
  | Eunop (op a ty v1 v) :
      EvalExpr ge e le m a v1 →
      Cop.semUnaryOperation op v1 (typeof a) m = some v →
      EvalExpr ge e le m (.Eunop op a ty) v
  | Ebinop (op a1 a2 ty v1 v2 v) :
      EvalExpr ge e le m a1 v1 →
      EvalExpr ge e le m a2 v2 →
      Cop.semBinaryOperation ge.genv_cenv op v1 (typeof a1) v2 (typeof a2) m
        = some v →
      EvalExpr ge e le m (.Ebinop op a1 a2 ty) v
  | Ecast (a ty v1 v) :
      EvalExpr ge e le m a v1 →
      Cop.semCast v1 (typeof a) ty m = some v →
      EvalExpr ge e le m (.Ecast a ty) v
  | Esizeof (ty1 ty) :
      EvalExpr ge e le m (.Esizeof ty1 ty)
        (Val.Vptrofs (Integers.Ptrofs.repr (sizeof ge.genv_cenv ty1)))
  | Ealignof (ty1 ty) :
      EvalExpr ge e le m (.Ealignof ty1 ty)
        (Val.Vptrofs (Integers.Ptrofs.repr (alignof ge.genv_cenv ty1)))
  | Elvalue (a loc ofs bf v) :
      EvalLvalue ge e le m a loc ofs bf →
      DerefLoc (typeof a) m loc ofs bf v →
      EvalExpr ge e le m a v

inductive EvalLvalue (ge : CGenv) (e : Env) (le : TempEnv) (m : Mem) :
    Expr → Block → Integers.Ptrofs → Bitfield → Prop where
  | Evar_local (id l ty) :
      e.get id = some (l, ty) →
      EvalLvalue ge e le m (.Evar id ty) l Integers.Ptrofs.zero .Full
  | Evar_global (id l ty) :
      e.get id = none →
      Genv.findSymbol ge.genv_genv id = some l →
      EvalLvalue ge e le m (.Evar id ty) l Integers.Ptrofs.zero .Full
  | Ederef (a ty l ofs) :
      EvalExpr ge e le m a (.Vptr l ofs) →
      EvalLvalue ge e le m (.Ederef a ty) l ofs .Full
  | Efield_struct (a i ty l ofs id co att delta bf) :
      EvalExpr ge e le m a (.Vptr l ofs) →
      typeof a = .Tstruct id att →
      ge.genv_cenv.get id = some co →
      fieldOffset ge.genv_cenv i co.co_members = .OK (delta, bf) →
      EvalLvalue ge e le m (.Efield a i ty) l
        (Integers.Ptrofs.add ofs (Integers.Ptrofs.repr delta)) bf
  | Efield_union (a i ty l ofs id co att delta bf) :
      EvalExpr ge e le m a (.Vptr l ofs) →
      typeof a = .Tunion id att →
      ge.genv_cenv.get id = some co →
      unionFieldOffset ge.genv_cenv i co.co_members = .OK (delta, bf) →
      EvalLvalue ge e le m (.Efield a i ty) l
        (Integers.Ptrofs.add ofs (Integers.Ptrofs.repr delta)) bf
end

/-- `Clight.eval_exprlist` — evaluate call arguments and cast them to the
    parameter types. -/
inductive EvalExprlist (ge : CGenv) (e : Env) (le : TempEnv) (m : Mem) :
    List Expr → List Ty → List Val → Prop where
  | nil : EvalExprlist ge e le m [] [] []
  | cons (a bl ty tyl v1 v2 vl) :
      EvalExpr ge e le m a v1 →
      Cop.semCast v1 (typeof a) ty m = some v2 →
      EvalExprlist ge e le m bl tyl vl →
      EvalExprlist ge e le m (a :: bl) (ty :: tyl) (v2 :: vl)

/-! ## Continuations and states -/

/-- `Clight.cont` -/
inductive Cont where
  | Kstop
  | Kseq (s : Stmt) (k : Cont)
  | Kloop1 (s1 s2 : Stmt) (k : Cont)
  | Kloop2 (s1 s2 : Stmt) (k : Cont)
  | Kswitch (k : Cont)
  | Kcall (optid : Option Ident) (f : Function) (e : Env) (le : TempEnv) (k : Cont)

/-- `Clight.call_cont` — pop continuations up to the enclosing call. -/
def callCont : Cont → Cont
  | .Kseq _ k => callCont k
  | .Kloop1 _ _ k => callCont k
  | .Kloop2 _ _ k => callCont k
  | .Kswitch k => callCont k
  | k => k

/-- `Clight.is_call_cont` (a `Bool` here; a `Prop` in Rocq). -/
def isCallCont : Cont → Bool
  | .Kstop => true
  | .Kcall _ _ _ _ _ => true
  | _ => false

/-- `Clight.state` -/
inductive State where
  | State (f : Function) (s : Stmt) (k : Cont) (e : Env) (le : TempEnv) (m : Mem)
  | Callstate (fd : FunDef) (args : List Val) (k : Cont) (m : Mem)
  | Returnstate (res : Val) (k : Cont) (m : Mem)

-- `Clight.find_label` / `find_label_ls` — locate a `goto` target and rebuild
-- the continuation that reaching it implies.
mutual
def findLabel (lbl : Ident) : Stmt → Cont → Option (Stmt × Cont)
  | .Ssequence s1 s2, k =>
      match findLabel lbl s1 (.Kseq s2 k) with
      | some sk => some sk
      | none => findLabel lbl s2 k
  | .Sifthenelse _ s1 s2, k =>
      match findLabel lbl s1 k with
      | some sk => some sk
      | none => findLabel lbl s2 k
  | .Sloop s1 s2, k =>
      match findLabel lbl s1 (.Kloop1 s1 s2 k) with
      | some sk => some sk
      | none => findLabel lbl s2 (.Kloop2 s1 s2 k)
  | .Sswitch _ sl, k => findLabelLs lbl sl (.Kswitch k)
  | .Slabel lbl' s', k => if lbl = lbl' then some (s', k) else findLabel lbl s' k
  | _, _ => none

def findLabelLs (lbl : Ident) : LStmts → Cont → Option (Stmt × Cont)
  | .LSnil, _ => none
  | .LScons _ s sl', k =>
      match findLabel lbl s (.Kseq (seqOfLabeledStatement sl') k) with
      | some sk => some sk
      | none => findLabelLs lbl sl' k
end

/-! ## The transition relation

Parameterized over `functionEntry`, exactly as in Rocq, so that both calling
conventions share one relation. -/

/-- `Clight.step` — 26 rules, in CompCert's order. -/
inductive Step (ge : CGenv)
    (functionEntry : Function → List Val → Mem → Env → TempEnv → Mem → Prop) :
    State → Trace → State → Prop where
  | assign (f a1 a2 k e le m loc ofs bf v2 v m') :
      EvalLvalue ge e le m a1 loc ofs bf →
      EvalExpr ge e le m a2 v2 →
      Cop.semCast v2 (typeof a2) (typeof a1) m = some v →
      AssignLoc ge.genv_cenv (typeof a1) m loc ofs bf v m' →
      Step ge functionEntry (.State f (.Sassign a1 a2) k e le m) E0
        (.State f .Sskip k e le m')
  | set (f id a k e le m v) :
      EvalExpr ge e le m a v →
      Step ge functionEntry (.State f (.Sset id a) k e le m) E0
        (.State f .Sskip k e (le.set id v) m)
  | call (f optid a al k e le m tyargs tyres cconv vf vargs fd) :
      Cop.classifyFun (typeof a) = .f tyargs tyres cconv →
      EvalExpr ge e le m a vf →
      EvalExprlist ge e le m al tyargs vargs →
      Genv.findFunct ge.genv_genv vf = some fd →
      typeOfFundef fd = .Tfunction tyargs tyres cconv →
      Step ge functionEntry (.State f (.Scall optid a al) k e le m) E0
        (.Callstate fd vargs (.Kcall optid f e le k) m)
  | builtin (f optid ef tyargs al k e le m vargs t vres m') :
      EvalExprlist ge e le m al tyargs vargs →
      externalCall ef ge.genv_genv.toSenv vargs m t vres m' →
      Step ge functionEntry (.State f (.Sbuiltin optid ef tyargs al) k e le m) t
        (.State f .Sskip k e (setOpttemp optid vres le) m')
  | seq (f s1 s2 k e le m) :
      Step ge functionEntry (.State f (.Ssequence s1 s2) k e le m) E0
        (.State f s1 (.Kseq s2 k) e le m)
  | skip_seq (f s k e le m) :
      Step ge functionEntry (.State f .Sskip (.Kseq s k) e le m) E0
        (.State f s k e le m)
  | continue_seq (f s k e le m) :
      Step ge functionEntry (.State f .Scontinue (.Kseq s k) e le m) E0
        (.State f .Scontinue k e le m)
  | break_seq (f s k e le m) :
      Step ge functionEntry (.State f .Sbreak (.Kseq s k) e le m) E0
        (.State f .Sbreak k e le m)
  | ifthenelse (f a s1 s2 k e le m v1 b) :
      EvalExpr ge e le m a v1 →
      Cop.boolVal v1 (typeof a) m = some b →
      Step ge functionEntry (.State f (.Sifthenelse a s1 s2) k e le m) E0
        (.State f (if b then s1 else s2) k e le m)
  | loop (f s1 s2 k e le m) :
      Step ge functionEntry (.State f (.Sloop s1 s2) k e le m) E0
        (.State f s1 (.Kloop1 s1 s2 k) e le m)
  | skip_or_continue_loop1 (f s1 s2 k e le m x) :
      (x = Stmt.Sskip ∨ x = Stmt.Scontinue) →
      Step ge functionEntry (.State f x (.Kloop1 s1 s2 k) e le m) E0
        (.State f s2 (.Kloop2 s1 s2 k) e le m)
  | break_loop1 (f s1 s2 k e le m) :
      Step ge functionEntry (.State f .Sbreak (.Kloop1 s1 s2 k) e le m) E0
        (.State f .Sskip k e le m)
  | skip_loop2 (f s1 s2 k e le m) :
      Step ge functionEntry (.State f .Sskip (.Kloop2 s1 s2 k) e le m) E0
        (.State f (.Sloop s1 s2) k e le m)
  | break_loop2 (f s1 s2 k e le m) :
      Step ge functionEntry (.State f .Sbreak (.Kloop2 s1 s2 k) e le m) E0
        (.State f .Sskip k e le m)
  | return_0 (f k e le m m') :
      Mem.freeList m (blocksOfEnv ge.genv_cenv e) = some m' →
      Step ge functionEntry (.State f (.Sreturn none) k e le m) E0
        (.Returnstate .Vundef (callCont k) m')
  | return_1 (f a k e le m v v' m') :
      EvalExpr ge e le m a v →
      Cop.semCast v (typeof a) f.fn_return m = some v' →
      Mem.freeList m (blocksOfEnv ge.genv_cenv e) = some m' →
      Step ge functionEntry (.State f (.Sreturn (some a)) k e le m) E0
        (.Returnstate v' (callCont k) m')
  | skip_call (f k e le m m') :
      isCallCont k = true →
      Mem.freeList m (blocksOfEnv ge.genv_cenv e) = some m' →
      Step ge functionEntry (.State f .Sskip k e le m) E0
        (.Returnstate .Vundef k m')
  | switch (f a sl k e le m v n) :
      EvalExpr ge e le m a v →
      Cop.semSwitchArg v (typeof a) = some n →
      Step ge functionEntry (.State f (.Sswitch a sl) k e le m) E0
        (.State f (seqOfLabeledStatement (selectSwitch n sl)) (.Kswitch k) e le m)
  | skip_break_switch (f x k e le m) :
      (x = Stmt.Sskip ∨ x = Stmt.Sbreak) →
      Step ge functionEntry (.State f x (.Kswitch k) e le m) E0
        (.State f .Sskip k e le m)
  | continue_switch (f k e le m) :
      Step ge functionEntry (.State f .Scontinue (.Kswitch k) e le m) E0
        (.State f .Scontinue k e le m)
  | label (f lbl s k e le m) :
      Step ge functionEntry (.State f (.Slabel lbl s) k e le m) E0
        (.State f s k e le m)
  | goto (f lbl k e le m s' k') :
      findLabel lbl f.fn_body (callCont k) = some (s', k') →
      Step ge functionEntry (.State f (.Sgoto lbl) k e le m) E0
        (.State f s' k' e le m)
  | internal_function (f vargs k m e le m1) :
      functionEntry f vargs m e le m1 →
      Step ge functionEntry (.Callstate (.Internal f) vargs k m) E0
        (.State f f.fn_body k e le m1)
  | external_function (ef targs tres cconv vargs k m vres t m') :
      externalCall ef ge.genv_genv.toSenv vargs m t vres m' →
      Step ge functionEntry (.Callstate (.External ef targs tres cconv) vargs k m) t
        (.Returnstate vres k m')
  | returnstate (v optid f e le k m) :
      Step ge functionEntry (.Returnstate v (.Kcall optid f e le k) m) E0
        (.State f .Sskip k e (setOpttemp optid v le) m)

/-! ## Whole-program semantics -/

/-- `Coqlib.list_norepet` -/
def listNorepet {A : Type} (l : List A) : Prop := l.Nodup
/-- `Coqlib.list_disjoint` -/
def listDisjoint {A : Type} (l1 l2 : List A) : Prop := ∀ x ∈ l1, x ∉ l2

instance {A : Type} [DecidableEq A] (l : List A) : Decidable (listNorepet l) := by
  unfold listNorepet; infer_instance
instance {A : Type} [DecidableEq A] (l1 l2 : List A) : Decidable (listDisjoint l1 l2) := by
  unfold listDisjoint; infer_instance
/-- `Clight.var_names` -/
def varNames (vars : List (Ident × Ty)) : List Ident := vars.map (·.1)

/-- `Ctypes.type_int32s` -/
def type_int32s : Ty := .Tint .I32 .Signed noattr

/-- `Clight.initial_state` — call `main` with no arguments in the initial
    memory. -/
inductive InitialState (p : Program) : State → Prop where
  | intro (b f m0) :
      p.initMem = some m0 →
      Genv.findSymbol p.globalenv.genv_genv p.prog_main = some b →
      Genv.findFunctPtr p.globalenv.genv_genv b = some f →
      typeOfFundef f = .Tfunction [] type_int32s cc_default →
      InitialState p (.Callstate f [] .Kstop m0)

/-- `Clight.final_state` — a return to the empty continuation. -/
inductive FinalState : State → Integers.Int → Prop where
  | intro (r m) : FinalState (.Returnstate (.Vint r) .Kstop m) r

/-- `Clight.function_entry1` — parameters are stack-allocated variables, so
    their address can be taken. -/
inductive FunctionEntry1 (ge : CGenv) (f : Function) (vargs : List Val) (m : Mem)
    (e : Env) (le : TempEnv) (m' : Mem) : Prop where
  | intro (m1) :
      listNorepet (varNames f.fn_params ++ varNames f.fn_vars) →
      AllocVariables ge.genv_cenv emptyEnv m (f.fn_params ++ f.fn_vars) e m1 →
      BindParameters ge.genv_cenv e m1 f.fn_params vargs m' →
      le = createUndefTemps f.fn_temps →
      FunctionEntry1 ge f vargs m e le m'

/-- `Clight.function_entry2` — parameters are temporaries, not in memory. -/
inductive FunctionEntry2 (ge : CGenv) (f : Function) (vargs : List Val) (m : Mem)
    (e : Env) (le : TempEnv) (m' : Mem) : Prop where
  | intro :
      listNorepet (varNames f.fn_vars) →
      listNorepet (varNames f.fn_params) →
      listDisjoint (varNames f.fn_params) (varNames f.fn_temps) →
      AllocVariables ge.genv_cenv emptyEnv m f.fn_vars e m' →
      bindParameterTemps f.fn_params vargs (createUndefTemps f.fn_temps) = some le →
      FunctionEntry2 ge f vargs m e le m'

/-- `Clight.step1` -/
def Step1 (ge : CGenv) : State → Trace → State → Prop :=
  Step ge (FunctionEntry1 ge)
/-- `Clight.step2` -/
def Step2 (ge : CGenv) : State → Trace → State → Prop :=
  Step ge (FunctionEntry2 ge)

/-! ## Reflexive-transitive closure (the slice of `common/Smallstep.v` we need) -/

/-- `Smallstep.star` -/
inductive Star (R : State → Trace → State → Prop) : State → Trace → State → Prop where
  | refl (s) : Star R s E0 s
  | step (s1 t1 s2 t2 s3 t) :
      R s1 t1 s2 → Star R s2 t2 s3 → t = Eapp t1 t2 → Star R s1 t s3

/-- `Smallstep.plus` -/
inductive Plus (R : State → Trace → State → Prop) : State → Trace → State → Prop where
  | intro (s1 t1 s2 t2 s3 t) :
      R s1 t1 s2 → Star R s2 t2 s3 → t = Eapp t1 t2 → Plus R s1 t s3

end CC
