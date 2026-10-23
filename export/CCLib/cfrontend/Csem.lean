/-
  Dynamic semantics of the CompCert C language — port of `cfrontend/Csem.v`
  (the whole file).

  The semantics is a small-step reduction semantics.  Expressions are reduced
  one redex at a time, at any position allowed by a *reduction context*, so the
  evaluation order is not fixed: `step` is nondeterministic.  An expression
  that contains a subexpression that can neither reduce nor is a value goes to
  `Stuckstate` (`step_stuck`), which makes every evaluation order observable.

  Contents: `deref_loc`, `assign_loc` (with the volatile cases that Clight does
  not have), `alloc_variables`, `bind_parameters`, `blocks_of_env`,
  `select_switch`, `cast_arguments`; head reductions `lred`/`rred`/`callred`;
  contexts `context`/`contextlist`; `imm_safe`, `not_stuck`; the derived-form
  lemmas `red_selection` and `ctx_selection_1/2/3`; continuations, states,
  `find_label`; the two groups of transitions `estep`/`sstep` and `step`;
  `initial_state`, `final_state`, `semantics`, and `semantics_single_events`.

  Notes on faithfulness:
  * Rocq's `Csem.genv` has two `:>` coercions; as for Clight, `CGenv` has plain
    projections.
  * `is_call_cont` is a `Prop`, as in Rocq.
  * `local_env`/`empty_env`, `blocks_of_env` and `select_switch` have the same
    definitions as in Clight; the port's `blocksOfEnv`/`emptyEnv` are reused,
    while `select_switch` is restated for CompCert C's `LStmts`.
-/
import CCLib.cfrontend.Csyntax
import CCLib.common.Smallstep
import CCLib.common.Determinism
import CCLib.common.ValuesTheory

namespace CC
namespace Csem

open Csyntax

/-! ## Global and local environments -/

/-- `Csem.genv` -/
structure CGenv where
  genv_genv : Genv Csyntax.FunDef Ty
  genv_cenv : CompositeEnv

/-- `Csem.globalenv` -/
def globalenv (p : Csyntax.Program) : CGenv :=
  { genv_genv := Genv.addGlobals (Genv.emptyGenv p.prog_public) p.prog_defs
    genv_cenv := p.prog_comp_env }

/-- `Genv.init_mem` for a CompCert C program. -/
def initMem (p : Csyntax.Program) : Option Mem :=
  Genv.allocGlobals (globalenv p).genv_genv Mem.empty p.prog_defs

section SEMANTICS

variable (ge : CGenv)

/-! ## Reading and writing a datum at a location -/

/-- `Csem.deref_loc`: the value `v` of the datum of type `ty` at `b, ofs` (and
    bitfield `bf`), and the trace `t` of observable events (nonempty for a
    volatile access). -/
inductive DerefLoc (ty : Ty) (m : Mem) (b : Block) (ofs : Integers.Ptrofs) :
    Bitfield → Trace → Val → Prop where
  | value (chunk v) :
      accessMode ty = .By_value chunk →
      typeIsVolatile ty = false →
      Mem.loadv chunk m (.Vptr b ofs) = some v →
      DerefLoc ty m b ofs .Full E0 v
  | volatile (chunk t v) :
      accessMode ty = .By_value chunk →
      typeIsVolatile ty = true →
      VolatileLoad ge.genv_genv.toSenv chunk m b ofs t v →
      DerefLoc ty m b ofs .Full t v
  | reference :
      accessMode ty = .By_reference →
      DerefLoc ty m b ofs .Full E0 (.Vptr b ofs)
  | copy :
      accessMode ty = .By_copy →
      DerefLoc ty m b ofs .Full E0 (.Vptr b ofs)
  | bitfield (sz sg pos width v) :
      Cop.LoadBitfield ty sz sg pos width m (.Vptr b ofs) v →
      DerefLoc ty m b ofs (.Bits sz sg pos width) E0 v

/-- `Csem.assign_loc`: storing `v` in the datum of type `ty` at `b, ofs` gives
    memory `m'`, trace `t` and the value `v'` of the assignment (`v`
    normalized to the bitfield's width for a bitfield). -/
inductive AssignLoc (ty : Ty) (m : Mem) (b : Block) (ofs : Integers.Ptrofs) :
    Bitfield → Val → Trace → Mem → Val → Prop where
  | value (v chunk m') :
      accessMode ty = .By_value chunk →
      typeIsVolatile ty = false →
      Mem.storev chunk m (.Vptr b ofs) v = some m' →
      AssignLoc ty m b ofs .Full v E0 m' v
  | volatile (v chunk t m') :
      accessMode ty = .By_value chunk →
      typeIsVolatile ty = true →
      VolatileStore ge.genv_genv.toSenv chunk m b ofs v t m' →
      AssignLoc ty m b ofs .Full v t m' v
  | copy (b' ofs' bytes m') :
      accessMode ty = .By_copy →
      alignofBlockcopy ge.genv_cenv ty ∣ Integers.Ptrofs.unsigned ofs' →
      alignofBlockcopy ge.genv_cenv ty ∣ Integers.Ptrofs.unsigned ofs →
      (b' ≠ b
        ∨ Integers.Ptrofs.unsigned ofs' = Integers.Ptrofs.unsigned ofs
        ∨ Integers.Ptrofs.unsigned ofs' + sizeof ge.genv_cenv ty ≤ Integers.Ptrofs.unsigned ofs
        ∨ Integers.Ptrofs.unsigned ofs + sizeof ge.genv_cenv ty ≤ Integers.Ptrofs.unsigned ofs') →
      Mem.loadbytes m b' (Integers.Ptrofs.unsigned ofs') (sizeof ge.genv_cenv ty) = some bytes →
      Mem.storebytes m b (Integers.Ptrofs.unsigned ofs) bytes = some m' →
      AssignLoc ty m b ofs .Full (.Vptr b' ofs') E0 m' (.Vptr b' ofs')
  | bitfield (sz sg pos width v m' v') :
      Cop.StoreBitfield ty sz sg pos width m (.Vptr b ofs) v m' v' →
      AssignLoc ty m b ofs (.Bits sz sg pos width) v E0 m' v'

/-! ## Function entry -/

/-- `Csem.alloc_variables` -/
inductive AllocVariables : Env → Mem → List (Ident × Ty) → Env → Mem → Prop where
  | nil (e m) : AllocVariables e m [] e m
  | cons (e m id ty vars m1 b1 m2 e2) :
      Mem.alloc m 0 (sizeof ge.genv_cenv ty) = (m1, b1) →
      AllocVariables (e.set id (b1, ty)) m1 vars e2 m2 →
      AllocVariables e m ((id, ty) :: vars) e2 m2

/-- `Csem.bind_parameters` -/
inductive BindParameters (e : Env) : Mem → List (Ident × Ty) → List Val → Mem → Prop where
  | nil (m) : BindParameters e m [] [] m
  | cons (m id ty params v1 vl v1' b m1 m2) :
      e.get id = some (b, ty) →
      AssignLoc ge ty m b Integers.Ptrofs.zero .Full v1 E0 m1 v1' →
      BindParameters e m1 params vl m2 →
      BindParameters e m ((id, ty) :: params) (v1 :: vl) m2

end SEMANTICS

/-! ## `switch` -/

/-- `Csem.select_switch_default` -/
def selectSwitchDefault : Csyntax.LStmts → Csyntax.LStmts
  | .LSnil => .LSnil
  | sl@(.LScons none _ _) => sl
  | .LScons (some _) _ sl' => selectSwitchDefault sl'

/-- `Csem.select_switch_case` -/
def selectSwitchCase (n : Z) : Csyntax.LStmts → Option Csyntax.LStmts
  | .LSnil => none
  | .LScons none _ sl' => selectSwitchCase n sl'
  | sl@(.LScons (some c) _ sl') => if c = n then some sl else selectSwitchCase n sl'

/-- `Csem.select_switch` -/
def selectSwitch (n : Z) (sl : Csyntax.LStmts) : Csyntax.LStmts :=
  match selectSwitchCase n sl with
  | some sl' => sl'
  | none => selectSwitchDefault sl

/-- `Csem.seq_of_labeled_statement` -/
def seqOfLabeledStatement : Csyntax.LStmts → Csyntax.Stmt
  | .LSnil => .Sskip
  | .LScons _ s sl' => .Ssequence s (seqOfLabeledStatement sl')

/-- `Csem.cast_arguments`: the arguments must already be values; each is cast
    to the corresponding parameter type. -/
inductive CastArguments (m : Mem) : Csyntax.ExprList → List Ty → List Val → Prop where
  | nil : CastArguments m .Enil [] []
  | cons (v ty el targ1 targs v1 vl) :
      Cop.semCast v ty targ1 m = some v1 →
      CastArguments m el targs vl →
      CastArguments m (.Econs (.Eval v ty) el) (targ1 :: targs) (v1 :: vl)

/-! ## Head reductions -/

section EXPR

variable (ge : CGenv) (e : Env)

/-- `Csem.lred`: head reduction of l-values. -/
inductive Lred : Csyntax.Expr → Mem → Csyntax.Expr → Mem → Prop where
  | var_local (x ty m b) :
      e.get x = some (b, ty) →
      Lred (.Evar x ty) m (.Eloc b Integers.Ptrofs.zero .Full ty) m
  | var_global (x ty m b) :
      e.get x = none →
      Genv.findSymbol ge.genv_genv x = some b →
      Lred (.Evar x ty) m (.Eloc b Integers.Ptrofs.zero .Full ty) m
  | deref (b ofs ty1 ty m) :
      Lred (.Ederef (.Eval (.Vptr b ofs) ty1) ty) m (.Eloc b ofs .Full ty) m
  | field_struct (b ofs id co a f ty m delta bf) :
      ge.genv_cenv.get id = some co →
      fieldOffset ge.genv_cenv f co.co_members = .OK (delta, bf) →
      Lred (.Efield (.Eval (.Vptr b ofs) (.Tstruct id a)) f ty) m
        (.Eloc b (Integers.Ptrofs.add ofs (Integers.Ptrofs.repr delta)) bf ty) m
  | field_union (b ofs id co a f ty m delta bf) :
      ge.genv_cenv.get id = some co →
      unionFieldOffset ge.genv_cenv f co.co_members = .OK (delta, bf) →
      Lred (.Efield (.Eval (.Vptr b ofs) (.Tunion id a)) f ty) m
        (.Eloc b (Integers.Ptrofs.add ofs (Integers.Ptrofs.repr delta)) bf ty) m

/-- `Csem.rred`: head reduction of r-values. -/
inductive Rred : Csyntax.Expr → Mem → Trace → Csyntax.Expr → Mem → Prop where
  | rvalof (b ofs bf ty m t v) :
      DerefLoc ge ty m b ofs bf t v →
      Rred (.Evalof (.Eloc b ofs bf ty) ty) m t (.Eval v ty) m
  | addrof (b ofs ty1 ty m) :
      Rred (.Eaddrof (.Eloc b ofs .Full ty1) ty) m E0 (.Eval (.Vptr b ofs) ty) m
  | unop (op v1 ty1 ty m v) :
      Cop.semUnaryOperation op v1 ty1 m = some v →
      Rred (.Eunop op (.Eval v1 ty1) ty) m E0 (.Eval v ty) m
  | binop (op v1 ty1 v2 ty2 ty m v) :
      Cop.semBinaryOperation ge.genv_cenv op v1 ty1 v2 ty2 m = some v →
      Rred (.Ebinop op (.Eval v1 ty1) (.Eval v2 ty2) ty) m E0 (.Eval v ty) m
  | cast (ty v1 ty1 m v) :
      Cop.semCast v1 ty1 ty m = some v →
      Rred (.Ecast (.Eval v1 ty1) ty) m E0 (.Eval v ty) m
  | seqand_true (v1 ty1 r2 ty m) :
      Cop.boolVal v1 ty1 m = some true →
      Rred (.Eseqand (.Eval v1 ty1) r2 ty) m E0 (.Eparen r2 type_bool ty) m
  | seqand_false (v1 ty1 r2 ty m) :
      Cop.boolVal v1 ty1 m = some false →
      Rred (.Eseqand (.Eval v1 ty1) r2 ty) m E0 (.Eval (.Vint Integers.Int.zero) ty) m
  | seqor_true (v1 ty1 r2 ty m) :
      Cop.boolVal v1 ty1 m = some true →
      Rred (.Eseqor (.Eval v1 ty1) r2 ty) m E0 (.Eval (.Vint Integers.Int.one) ty) m
  | seqor_false (v1 ty1 r2 ty m) :
      Cop.boolVal v1 ty1 m = some false →
      Rred (.Eseqor (.Eval v1 ty1) r2 ty) m E0 (.Eparen r2 type_bool ty) m
  | condition (v1 ty1 r1 r2 ty b m) :
      Cop.boolVal v1 ty1 m = some b →
      Rred (.Econdition (.Eval v1 ty1) r1 r2 ty) m E0 (.Eparen (if b then r1 else r2) ty ty) m
  | sizeof (ty1 ty m) :
      Rred (.Esizeof ty1 ty) m E0
        (.Eval (Val.Vptrofs (Integers.Ptrofs.repr (sizeof ge.genv_cenv ty1))) ty) m
  | alignof (ty1 ty m) :
      Rred (.Ealignof ty1 ty) m E0
        (.Eval (Val.Vptrofs (Integers.Ptrofs.repr (alignof ge.genv_cenv ty1))) ty) m
  | assign (b ofs ty1 bf v2 ty2 m v t m' v') :
      Cop.semCast v2 ty2 ty1 m = some v →
      AssignLoc ge ty1 m b ofs bf v t m' v' →
      Rred (.Eassign (.Eloc b ofs bf ty1) (.Eval v2 ty2) ty1) m t (.Eval v' ty1) m'
  | assignop (op b ofs ty1 bf v2 ty2 tyres m t v1) :
      DerefLoc ge ty1 m b ofs bf t v1 →
      Rred (.Eassignop op (.Eloc b ofs bf ty1) (.Eval v2 ty2) tyres ty1) m t
        (.Eassign (.Eloc b ofs bf ty1) (.Ebinop op (.Eval v1 ty1) (.Eval v2 ty2) tyres) ty1) m
  | postincr (id b ofs ty bf m t v1 op) :
      DerefLoc ge ty m b ofs bf t v1 →
      op = (match id with | .Incr => Binop.Oadd | .Decr => Binop.Osub) →
      Rred (.Epostincr id (.Eloc b ofs bf ty) ty) m t
        (.Ecomma (.Eassign (.Eloc b ofs bf ty)
                    (.Ebinop op (.Eval v1 ty) (.Eval (.Vint Integers.Int.one) type_int32s)
                      (Cop.incrdecrType ty))
                    ty)
          (.Eval v1 ty) ty) m
  | comma (v ty1 r2 ty m) :
      Csyntax.typeof r2 = ty →
      Rred (.Ecomma (.Eval v ty1) r2 ty) m E0 r2 m
  | paren (v1 ty1 ty2 ty m v) :
      Cop.semCast v1 ty1 ty2 m = some v →
      Rred (.Eparen (.Eval v1 ty1) ty2 ty) m E0 (.Eval v ty) m
  | builtin (ef tyargs el ty m vargs t vres m') :
      CastArguments m el tyargs vargs →
      externalCall ef ge.genv_genv.toSenv vargs m t vres m' →
      Rred (.Ebuiltin ef tyargs el ty) m t (.Eval vres ty) m'

/-- `Csem.callred`: function calls that can reduce. -/
inductive Callred : Csyntax.Expr → Mem → Csyntax.FunDef → List Val → Ty → Prop where
  | call (vf tyf m tyargs tyres cconv el ty fd vargs) :
      Genv.findFunct ge.genv_genv vf = some fd →
      CastArguments m el tyargs vargs →
      Csyntax.typeOfFundef fd = .Tfunction tyargs tyres cconv →
      Cop.classifyFun tyf = .f tyargs tyres cconv →
      Callred (.Ecall (.Eval vf tyf) el ty) m fd vargs ty

end EXPR

/-! ## Reduction contexts -/

/-- `Csem.kind`: l-value or r-value position. -/
inductive Kind where
  | LV
  | RV
  deriving DecidableEq, Repr

mutual
/-- `Csem.context from to C`: `C` is a reduction context whose hole has kind
    `from` and whose result has kind `to`.  Reductions inside `a ? b : c`,
    `a && b`, `a || b` and `a, b` only take place in `a`. -/
inductive Context : Kind → Kind → (Csyntax.Expr → Csyntax.Expr) → Prop where
  | top (k) : Context k k (fun x => x)
  | deref (k C ty) : Context k .RV C → Context k .LV (fun x => .Ederef (C x) ty)
  | field (k C f ty) : Context k .RV C → Context k .LV (fun x => .Efield (C x) f ty)
  | rvalof (k C ty) : Context k .LV C → Context k .RV (fun x => .Evalof (C x) ty)
  | addrof (k C ty) : Context k .LV C → Context k .RV (fun x => .Eaddrof (C x) ty)
  | unop (k C op ty) : Context k .RV C → Context k .RV (fun x => .Eunop op (C x) ty)
  | binop_left (k C op e2 ty) :
      Context k .RV C → Context k .RV (fun x => .Ebinop op (C x) e2 ty)
  | binop_right (k C op e1 ty) :
      Context k .RV C → Context k .RV (fun x => .Ebinop op e1 (C x) ty)
  | cast (k C ty) : Context k .RV C → Context k .RV (fun x => .Ecast (C x) ty)
  | seqand (k C r2 ty) : Context k .RV C → Context k .RV (fun x => .Eseqand (C x) r2 ty)
  | seqor (k C r2 ty) : Context k .RV C → Context k .RV (fun x => .Eseqor (C x) r2 ty)
  | condition (k C r2 r3 ty) :
      Context k .RV C → Context k .RV (fun x => .Econdition (C x) r2 r3 ty)
  | assign_left (k C e2 ty) :
      Context k .LV C → Context k .RV (fun x => .Eassign (C x) e2 ty)
  | assign_right (k C e1 ty) :
      Context k .RV C → Context k .RV (fun x => .Eassign e1 (C x) ty)
  | assignop_left (k C op e2 tyres ty) :
      Context k .LV C → Context k .RV (fun x => .Eassignop op (C x) e2 tyres ty)
  | assignop_right (k C op e1 tyres ty) :
      Context k .RV C → Context k .RV (fun x => .Eassignop op e1 (C x) tyres ty)
  | postincr (k C id ty) :
      Context k .LV C → Context k .RV (fun x => .Epostincr id (C x) ty)
  | call_left (k C el ty) :
      Context k .RV C → Context k .RV (fun x => .Ecall (C x) el ty)
  | call_right (k C e1 ty) :
      ContextList k C → Context k .RV (fun x => .Ecall e1 (C x) ty)
  | builtin (k C ef tyargs ty) :
      ContextList k C → Context k .RV (fun x => .Ebuiltin ef tyargs (C x) ty)
  | comma (k C e2 ty) : Context k .RV C → Context k .RV (fun x => .Ecomma (C x) e2 ty)
  | paren (k C tycast ty) :
      Context k .RV C → Context k .RV (fun x => .Eparen (C x) tycast ty)

/-- `Csem.contextlist` -/
inductive ContextList : Kind → (Csyntax.Expr → Csyntax.ExprList) → Prop where
  | head (k C el) : Context k .RV C → ContextList k (fun x => .Econs (C x) el)
  | tail (k C e1) : ContextList k C → ContextList k (fun x => .Econs e1 (C x))
end

/-! ## Safe expressions -/

section SAFE

variable (ge : CGenv) (e : Env)

/-- `Csem.imm_safe`: the expression is a value of the right kind, or can
    reduce at some position. -/
inductive ImmSafe : Kind → Csyntax.Expr → Mem → Prop where
  | val (v ty m) : ImmSafe .RV (.Eval v ty) m
  | loc (b ofs bf ty m) : ImmSafe .LV (.Eloc b ofs bf ty) m
  | lred (to C e' m e'' m') :
      Lred ge e e' m e'' m' → Context .LV to C → ImmSafe to (C e') m
  | rred (to C e' m t e'' m') :
      Rred ge e' m t e'' m' → Context .RV to C → ImmSafe to (C e') m
  | callred (to C e' m fd args ty) :
      Callred ge e' m fd args ty → Context .RV to C → ImmSafe to (C e') m

/-- `Csem.not_stuck`: no subexpression is immediately stuck. -/
def NotStuck (a : Csyntax.Expr) (m : Mem) : Prop :=
  ∀ k C a', Context k .RV C → a = C a' → ImmSafe ge e k a' m

end SAFE

/-! ## Derived forms -/

/-- `__builtin_sel` at the machine type of any C type is the standard
    `select` builtin. -/
theorem lookup_sel (ty : Ty) :
    Builtins.lookupBuiltinFunction "__builtin_sel"
      (mksignature [.Xint, (typOfType ty).inj, (typOfType ty).inj] (typOfType ty).inj cc_default) =
      some (.BI_standard (.BI_select (typOfType ty))) := by
  rcases ty with _ | ⟨sz, si, a⟩ | ⟨si, a⟩ | ⟨_ | _, a⟩ | ⟨t, a⟩ | ⟨t, n, a⟩ |
      ⟨ta, tr, cc⟩ | ⟨id, a⟩ | ⟨id, a⟩ <;> simp only [typOfType] <;> decide

/-- `__builtin_sel` on a Boolean selector. -/
theorem selectFn_ofBool (t : ATyp) (b : Bool) (v2 v3 : Val) :
    Builtins.selectFn t (Val.ofBool b) v2 v3 = some (Val.normalize (if b then v2 else v3) t) := by
  cases b <;> rfl

/-- `Csem.red_selection`: `Eselection` evaluates both arms and picks one. -/
theorem red_selection (ge : CGenv) {v1 : Val} {ty1 : Ty} {v2 : Val} {ty2 : Ty} {v3 : Val}
    {ty3 ty : Ty} {m : Mem} {b : Bool} {v2' v3' : Val}
    (hty : ty ≠ .Tvoid)
    (hb : Cop.boolVal v1 ty1 m = some b)
    (h2 : Cop.semCast v2 ty2 ty m = some v2')
    (h3 : Cop.semCast v3 ty3 ty m = some v3') :
    Rred ge (Eselection (.Eval v1 ty1) (.Eval v2 ty2) (.Eval v3 ty3) ty) m
      E0 (.Eval (if b then v2' else v3') ty) m := by
  have hC : Cop.ValCasted (if b then v2' else v3') ty := by
    cases b
    · exact Cop.cast_val_is_casted h3
    · exact Cop.cast_val_is_casted h2
  have hN : Val.normalize (if b then v2' else v3') (typOfType ty) = (if b then v2' else v3') :=
    Val.normalize_idem (Cop.val_casted_hasType hC hty)
  refine .builtin _ _ _ _ _ [Val.ofBool b, v2', v3'] _ _ _ ?_ ?_
  · refine .cons _ _ _ _ _ _ _ ?_ (.cons _ _ _ _ _ _ _ h2 (.cons _ _ _ _ _ _ _ h3 .nil))
    show Cop.semCast v1 ty1 (.Tint .IBool .Signed noattr) m = _
    rw [Cop.cast_bool_bool_val, hb]; rfl
  · show builtinOrExternalSem _ _ _ _ _ _ _ _
    unfold builtinOrExternalSem
    rw [lookup_sel ty]
    refine .intro _ _ _ _ ?_
    show Builtins.selectFn (typOfType ty) (Val.ofBool b) v2' v3' = _
    rw [selectFn_ofBool, hN]

/-- `Csem.ctx_selection_1` -/
theorem ctx_selection_1 {k C r2 r3 ty} (h : Context k .RV C) :
    Context k .RV (fun x => Eselection (C x) r2 r3 ty) :=
  .builtin _ _ _ _ _ (.head _ _ _ h)

/-- `Csem.ctx_selection_2` -/
theorem ctx_selection_2 {k r1 C r3 ty} (h : Context k .RV C) :
    Context k .RV (fun x => Eselection r1 (C x) r3 ty) :=
  .builtin _ _ _ _ _ (.tail _ _ _ (.head _ _ _ h))

/-- `Csem.ctx_selection_3` -/
theorem ctx_selection_3 {k r1 r2 C ty} (h : Context k .RV C) :
    Context k .RV (fun x => Eselection r1 r2 (C x) ty) :=
  .builtin _ _ _ _ _ (.tail _ _ _ (.tail _ _ _ (.head _ _ _ h)))

/-! ## Continuations and states -/

/-- `Csem.cont` -/
inductive Cont where
  | Kstop
  /-- after `x` in `x;` -/
  | Kdo (k : Cont)
  /-- after `s1` in `s1; s2` -/
  | Kseq (s : Csyntax.Stmt) (k : Cont)
  /-- after `x` in `if (x) { s1 } else { s2 }` -/
  | Kifthenelse (s1 s2 : Csyntax.Stmt) (k : Cont)
  /-- after `x` in `while (x) s` -/
  | Kwhile1 (x : Csyntax.Expr) (s : Csyntax.Stmt) (k : Cont)
  /-- after `s` in `while (x) s` -/
  | Kwhile2 (x : Csyntax.Expr) (s : Csyntax.Stmt) (k : Cont)
  /-- after `s` in `do s while (x)` -/
  | Kdowhile1 (x : Csyntax.Expr) (s : Csyntax.Stmt) (k : Cont)
  /-- after `x` in `do s while (x)` -/
  | Kdowhile2 (x : Csyntax.Expr) (s : Csyntax.Stmt) (k : Cont)
  /-- after `e2` in `for (e1; e2; e3) s` -/
  | Kfor2 (e2 : Csyntax.Expr) (e3 s : Csyntax.Stmt) (k : Cont)
  /-- after `s` in `for (e1; e2; e3) s` -/
  | Kfor3 (e2 : Csyntax.Expr) (e3 s : Csyntax.Stmt) (k : Cont)
  /-- after `e3` in `for (e1; e2; e3) s` -/
  | Kfor4 (e2 : Csyntax.Expr) (e3 s : Csyntax.Stmt) (k : Cont)
  /-- after `e` in `switch (e) { ls }` -/
  | Kswitch1 (ls : Csyntax.LStmts) (k : Cont)
  /-- catches `break` statements arising out of `switch` -/
  | Kswitch2 (k : Cont)
  /-- after `e` in `return e;` -/
  | Kreturn (k : Cont)
  /-- calling function, its local environment, the context of the call and
      the type of the call expression -/
  | Kcall (f : Csyntax.Function) (e : Env) (C : Csyntax.Expr → Csyntax.Expr) (ty : Ty) (k : Cont)

/-- `Csem.call_cont` -/
def callCont : Cont → Cont
  | .Kstop => .Kstop
  | .Kdo k => k
  | .Kseq _ k | .Kifthenelse _ _ k | .Kwhile1 _ _ k | .Kwhile2 _ _ k
  | .Kdowhile1 _ _ k | .Kdowhile2 _ _ k | .Kfor2 _ _ _ k | .Kfor3 _ _ _ k
  | .Kfor4 _ _ _ k | .Kswitch1 _ k | .Kswitch2 k | .Kreturn k => callCont k
  | k@(.Kcall _ _ _ _ _) => k

/-- `Csem.is_call_cont` -/
def IsCallCont : Cont → Prop
  | .Kstop => True
  | .Kcall _ _ _ _ _ => True
  | _ => False

/-- `Csem.state` -/
inductive State where
  /-- execution of a statement -/
  | State (f : Csyntax.Function) (s : Csyntax.Stmt) (k : Cont) (e : Env) (m : Mem)
  /-- reduction of an expression -/
  | ExprState (f : Csyntax.Function) (r : Csyntax.Expr) (k : Cont) (e : Env) (m : Mem)
  /-- calling a function -/
  | Callstate (fd : Csyntax.FunDef) (args : List Val) (k : Cont) (m : Mem)
  /-- returning from a function -/
  | Returnstate (res : Val) (k : Cont) (m : Mem)
  /-- undefined behavior occurred -/
  | Stuckstate

mutual
/-- `Csem.find_label` -/
def findLabel (lbl : Label) : Csyntax.Stmt → Cont → Option (Csyntax.Stmt × Cont)
  | .Ssequence s1 s2, k =>
      match findLabel lbl s1 (.Kseq s2 k) with
      | some sk => some sk
      | none => findLabel lbl s2 k
  | .Sifthenelse _ s1 s2, k =>
      match findLabel lbl s1 k with
      | some sk => some sk
      | none => findLabel lbl s2 k
  | .Swhile a s1, k => findLabel lbl s1 (.Kwhile2 a s1 k)
  | .Sdowhile a s1, k => findLabel lbl s1 (.Kdowhile1 a s1 k)
  | .Sfor a1 a2 a3 s1, k =>
      match findLabel lbl a1 (.Kseq (.Sfor .Sskip a2 a3 s1) k) with
      | some sk => some sk
      | none =>
          match findLabel lbl s1 (.Kfor3 a2 a3 s1 k) with
          | some sk => some sk
          | none => findLabel lbl a3 (.Kfor4 a2 a3 s1 k)
  | .Sswitch _ sl, k => findLabelLs lbl sl (.Kswitch2 k)
  | .Slabel lbl' s', k => if lbl = lbl' then some (s', k) else findLabel lbl s' k
  | _, _ => none

/-- `Csem.find_label_ls` -/
def findLabelLs (lbl : Label) : Csyntax.LStmts → Cont → Option (Csyntax.Stmt × Cont)
  | .LSnil, _ => none
  | .LScons _ s sl', k =>
      match findLabel lbl s (.Kseq (seqOfLabeledStatement sl') k) with
      | some sk => some sk
      | none => findLabelLs lbl sl' k
end

/-! ## Transitions -/

section STEP

variable (ge : CGenv)

/-- `Csem.estep`: reductions inside expressions. -/
inductive Estep : State → Trace → State → Prop where
  | lred (C f a k e m a' m') :
      Lred ge e a m a' m' → Context .LV .RV C →
      Estep (.ExprState f (C a) k e m) E0 (.ExprState f (C a') k e m')
  | rred (C f a k e m t a' m') :
      Rred ge a m t a' m' → Context .RV .RV C →
      Estep (.ExprState f (C a) k e m) t (.ExprState f (C a') k e m')
  | call (C f a k e m fd vargs ty) :
      Callred ge a m fd vargs ty → Context .RV .RV C →
      Estep (.ExprState f (C a) k e m) E0 (.Callstate fd vargs (.Kcall f e C ty k) m)
  | stuck (C f a k e m K) :
      Context K .RV C → ¬ ImmSafe ge e K a m →
      Estep (.ExprState f (C a) k e m) E0 .Stuckstate

/-- `Csem.sstep`: all other transitions (statements, calls and returns). -/
inductive Sstep : State → Trace → State → Prop where
  | do_1 (f x k e m) :
      Sstep (.State f (.Sdo x) k e m) E0 (.ExprState f x (.Kdo k) e m)
  | do_2 (f v ty k e m) :
      Sstep (.ExprState f (.Eval v ty) (.Kdo k) e m) E0 (.State f .Sskip k e m)
  | seq (f s1 s2 k e m) :
      Sstep (.State f (.Ssequence s1 s2) k e m) E0 (.State f s1 (.Kseq s2 k) e m)
  | skip_seq (f s k e m) :
      Sstep (.State f .Sskip (.Kseq s k) e m) E0 (.State f s k e m)
  | continue_seq (f s k e m) :
      Sstep (.State f .Scontinue (.Kseq s k) e m) E0 (.State f .Scontinue k e m)
  | break_seq (f s k e m) :
      Sstep (.State f .Sbreak (.Kseq s k) e m) E0 (.State f .Sbreak k e m)
  | ifthenelse_1 (f a s1 s2 k e m) :
      Sstep (.State f (.Sifthenelse a s1 s2) k e m) E0
        (.ExprState f a (.Kifthenelse s1 s2 k) e m)
  | ifthenelse_2 (f v ty s1 s2 k e m b) :
      Cop.boolVal v ty m = some b →
      Sstep (.ExprState f (.Eval v ty) (.Kifthenelse s1 s2 k) e m) E0
        (.State f (if b then s1 else s2) k e m)
  | while (f x s k e m) :
      Sstep (.State f (.Swhile x s) k e m) E0 (.ExprState f x (.Kwhile1 x s k) e m)
  | while_false (f v ty x s k e m) :
      Cop.boolVal v ty m = some false →
      Sstep (.ExprState f (.Eval v ty) (.Kwhile1 x s k) e m) E0 (.State f .Sskip k e m)
  | while_true (f v ty x s k e m) :
      Cop.boolVal v ty m = some true →
      Sstep (.ExprState f (.Eval v ty) (.Kwhile1 x s k) e m) E0
        (.State f s (.Kwhile2 x s k) e m)
  | skip_or_continue_while (f s0 x s k e m) :
      (s0 = Csyntax.Stmt.Sskip ∨ s0 = Csyntax.Stmt.Scontinue) →
      Sstep (.State f s0 (.Kwhile2 x s k) e m) E0 (.State f (.Swhile x s) k e m)
  | break_while (f x s k e m) :
      Sstep (.State f .Sbreak (.Kwhile2 x s k) e m) E0 (.State f .Sskip k e m)
  | dowhile (f a s k e m) :
      Sstep (.State f (.Sdowhile a s) k e m) E0 (.State f s (.Kdowhile1 a s k) e m)
  | skip_or_continue_dowhile (f s0 x s k e m) :
      (s0 = Csyntax.Stmt.Sskip ∨ s0 = Csyntax.Stmt.Scontinue) →
      Sstep (.State f s0 (.Kdowhile1 x s k) e m) E0 (.ExprState f x (.Kdowhile2 x s k) e m)
  | dowhile_false (f v ty x s k e m) :
      Cop.boolVal v ty m = some false →
      Sstep (.ExprState f (.Eval v ty) (.Kdowhile2 x s k) e m) E0 (.State f .Sskip k e m)
  | dowhile_true (f v ty x s k e m) :
      Cop.boolVal v ty m = some true →
      Sstep (.ExprState f (.Eval v ty) (.Kdowhile2 x s k) e m) E0
        (.State f (.Sdowhile x s) k e m)
  | break_dowhile (f a s k e m) :
      Sstep (.State f .Sbreak (.Kdowhile1 a s k) e m) E0 (.State f .Sskip k e m)
  | for_start (f a1 a2 a3 s k e m) :
      a1 ≠ Csyntax.Stmt.Sskip →
      Sstep (.State f (.Sfor a1 a2 a3 s) k e m) E0
        (.State f a1 (.Kseq (.Sfor .Sskip a2 a3 s) k) e m)
  | for (f a2 a3 s k e m) :
      Sstep (.State f (.Sfor .Sskip a2 a3 s) k e m) E0
        (.ExprState f a2 (.Kfor2 a2 a3 s k) e m)
  | for_false (f v ty a2 a3 s k e m) :
      Cop.boolVal v ty m = some false →
      Sstep (.ExprState f (.Eval v ty) (.Kfor2 a2 a3 s k) e m) E0 (.State f .Sskip k e m)
  | for_true (f v ty a2 a3 s k e m) :
      Cop.boolVal v ty m = some true →
      Sstep (.ExprState f (.Eval v ty) (.Kfor2 a2 a3 s k) e m) E0
        (.State f s (.Kfor3 a2 a3 s k) e m)
  | skip_or_continue_for3 (f x a2 a3 s k e m) :
      (x = Csyntax.Stmt.Sskip ∨ x = Csyntax.Stmt.Scontinue) →
      Sstep (.State f x (.Kfor3 a2 a3 s k) e m) E0 (.State f a3 (.Kfor4 a2 a3 s k) e m)
  | break_for3 (f a2 a3 s k e m) :
      Sstep (.State f .Sbreak (.Kfor3 a2 a3 s k) e m) E0 (.State f .Sskip k e m)
  | skip_for4 (f a2 a3 s k e m) :
      Sstep (.State f .Sskip (.Kfor4 a2 a3 s k) e m) E0 (.State f (.Sfor .Sskip a2 a3 s) k e m)
  | return_0 (f k e m m') :
      Mem.freeList m (blocksOfEnv ge.genv_cenv e) = some m' →
      Sstep (.State f (.Sreturn none) k e m) E0 (.Returnstate .Vundef (callCont k) m')
  | return_1 (f x k e m) :
      Sstep (.State f (.Sreturn (some x)) k e m) E0 (.ExprState f x (.Kreturn k) e m)
  | return_2 (f v1 ty k e m v2 m') :
      Cop.semCast v1 ty f.fn_return m = some v2 →
      Mem.freeList m (blocksOfEnv ge.genv_cenv e) = some m' →
      Sstep (.ExprState f (.Eval v1 ty) (.Kreturn k) e m) E0 (.Returnstate v2 (callCont k) m')
  | skip_call (f k e m m') :
      IsCallCont k →
      Mem.freeList m (blocksOfEnv ge.genv_cenv e) = some m' →
      Sstep (.State f .Sskip k e m) E0 (.Returnstate .Vundef k m')
  | switch (f x sl k e m) :
      Sstep (.State f (.Sswitch x sl) k e m) E0 (.ExprState f x (.Kswitch1 sl k) e m)
  | expr_switch (f ty sl k e m v n) :
      Cop.semSwitchArg v ty = some n →
      Sstep (.ExprState f (.Eval v ty) (.Kswitch1 sl k) e m) E0
        (.State f (seqOfLabeledStatement (selectSwitch n sl)) (.Kswitch2 k) e m)
  | skip_break_switch (f x k e m) :
      (x = Csyntax.Stmt.Sskip ∨ x = Csyntax.Stmt.Sbreak) →
      Sstep (.State f x (.Kswitch2 k) e m) E0 (.State f .Sskip k e m)
  | continue_switch (f k e m) :
      Sstep (.State f .Scontinue (.Kswitch2 k) e m) E0 (.State f .Scontinue k e m)
  | label (f lbl s k e m) :
      Sstep (.State f (.Slabel lbl s) k e m) E0 (.State f s k e m)
  | goto (f lbl k e m s' k') :
      findLabel lbl f.fn_body (callCont k) = some (s', k') →
      Sstep (.State f (.Sgoto lbl) k e m) E0 (.State f s' k' e m)
  | internal_function (f vargs k m e m1 m2) :
      listNorepet (Csyntax.varNames f.fn_params ++ Csyntax.varNames f.fn_vars) →
      AllocVariables ge emptyEnv m (f.fn_params ++ f.fn_vars) e m1 →
      BindParameters ge e m1 f.fn_params vargs m2 →
      Sstep (.Callstate (.Internal f) vargs k m) E0 (.State f f.fn_body k e m2)
  | external_function (ef targs tres cc vargs k m vres t m') :
      externalCall ef ge.genv_genv.toSenv vargs m t vres m' →
      Sstep (.Callstate (.External ef targs tres cc) vargs k m) t (.Returnstate vres k m')
  | returnstate (v f e C ty k m) :
      Sstep (.Returnstate v (.Kcall f e C ty k) m) E0 (.ExprState f (C (.Eval v ty)) k e m)

/-- `Csem.step` -/
def Step (S : State) (t : Trace) (S' : State) : Prop :=
  Estep ge S t S' ∨ Sstep ge S t S'

end STEP

/-! ## Whole-program semantics -/

/-- `Csem.initial_state` -/
inductive InitialState (p : Csyntax.Program) : State → Prop where
  | intro (b f m0) :
      initMem p = some m0 →
      Genv.findSymbol (globalenv p).genv_genv p.prog_main = some b →
      Genv.findFunctPtr (globalenv p).genv_genv b = some f →
      Csyntax.typeOfFundef f = .Tfunction [] type_int32s cc_default →
      InitialState p (.Callstate f [] .Kstop m0)

/-- `Csem.final_state` -/
inductive FinalState : State → Integers.Int → Prop where
  | intro (r m) : FinalState (.Returnstate (.Vint r) .Kstop m) r

/-- `Csem.semantics` -/
def semantics (p : Csyntax.Program) : Smallstep.Semantics where
  state := State
  step := Step (globalenv p)
  initial_state := InitialState p
  final_state := FinalState
  symbolenv := Genv.toSenv (globalenv p).genv_genv

/-- A dereference emits at most one event. -/
theorem derefLoc_traceLength {ge : CGenv} {ty m b ofs bf t v}
    (h : DerefLoc ge ty m b ofs bf t v) : t.length ≤ 1 := by
  cases h with
  | volatile _ _ _ _ _ hv => cases hv <;> simp [E0]
  | _ => simp [E0]

/-- An assignment emits at most one event. -/
theorem assignLoc_traceLength {ge : CGenv} {ty m b ofs bf v t m' v'}
    (h : AssignLoc ge ty m b ofs bf v t m' v') : t.length ≤ 1 := by
  cases h with
  | volatile _ _ _ _ _ _ hv => cases hv <;> simp [E0]
  | _ => simp [E0]

/-- A head reduction emits at most one event. -/
theorem rred_traceLength {ge : CGenv} (hinj : ge.genv_genv.toSenv.SymbolsInjective)
    {a m t a' m'} (h : Rred ge a m t a' m') : t.length ≤ 1 := by
  cases h with
  | rvalof _ _ _ _ _ _ _ hd => exact derefLoc_traceLength hd
  | assign _ _ _ _ _ _ _ _ _ _ _ _ ha => exact assignLoc_traceLength ha
  | assignop _ _ _ _ _ _ _ _ _ _ _ hd => exact derefLoc_traceLength hd
  | postincr _ _ _ _ _ _ _ _ _ hd _ => exact derefLoc_traceLength hd
  | builtin ef _ _ _ _ _ _ _ _ _ he => exact (externalCall_determ ef hinj).traceLength _ _ _ _ _ he
  | _ => simp [E0]

/-- `Csem.semantics_single_events`: every step emits at most one event. -/
theorem semantics_single_events (p : Csyntax.Program) : Smallstep.SingleEvents (semantics p) := by
  have hinj : (globalenv p).genv_genv.toSenv.SymbolsInjective :=
    Genv.toSenv_symbolsInjective (Genv.symbInjective_globalenv p.prog_public p.prog_defs)
  intro s t s' h
  rcases h with h | h
  · cases h with
    | rred _ _ _ _ _ _ _ _ _ hr _ => exact rred_traceLength hinj hr
    | _ => simp [E0]
  · cases h with
    | external_function ef _ _ _ _ _ _ _ _ _ he =>
      exact (externalCall_determ ef hinj).traceLength _ _ _ _ _ he
    | _ => simp [E0]

end Csem
end CC
