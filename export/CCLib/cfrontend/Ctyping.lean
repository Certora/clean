/-
  Typing rules and a type-checker for CompCert C — port of the first part of
  `cfrontend/Ctyping.v` (operations over types, the specification of the type
  system, and the type-checker built from smart constructors).

  * operations over types: `type_unop`, `type_binop`, `type_deref`,
    `type_combine`, `type_conditional`, `type_of_member`, …;
  * the type system: `wt_val`, `wt_int`, `wt_cast`, `wt_bool`,
    `wt_arguments`, `subtype`, and the mutually inductive `wt_rvalue`,
    `wt_lvalue`, `wt_exprlist`, `wt_stmt`, `wt_lblstmts`; `wt_function`,
    `wt_fundef`, `wt_program`;
  * the checker: `check_*`, the smart constructors (`evar`, `ederef`,
    `efield`, …, `sswitch`), `retype_expr`, `retype_stmt`, `retype_function`,
    `retype_fundef`, `typecheck_program`.

  The soundness of the checker is in `CCLib.cfrontend.CtypingSound`; the
  subject-reduction half of `Ctyping.v` (`wt_rred`, `wt_lred`, `preservation`,
  …) is in `CCLib.cfrontend.CtypingPreservation` and `CCLib.cfrontend.CtypingSubjectReduction`.

  Differences from Rocq: error messages are plain strings; `strict` is the
  constant `false` (as in CompCert, where it is opaque); `change_attributes`
  (from `Ctypes.v`, not previously in the port) is defined here.
-/
import CCLib.cfrontend.Csem

namespace CC
namespace Ctyping

/-- `Ctypes.change_attributes` -/
def changeAttributes (f : Attr → Attr) : Ty → Ty
  | .Tvoid => .Tvoid
  | .Tint sz si a => .Tint sz si (f a)
  | .Tlong si a => .Tlong si (f a)
  | .Tfloat sz a => .Tfloat sz (f a)
  | .Tpointer elt a => .Tpointer elt (f a)
  | .Tarray elt sz a => .Tarray elt sz (f a)
  | ty@(.Tfunction _ _ _) => ty
  | .Tstruct id a => .Tstruct id (f a)
  | .Tunion id a => .Tunion id (f a)

/-- `Ctyping.strict`: reject calls with too many arguments (off, as in
    CompCert). -/
def strict : Bool := false

/-- `Ctyping.size_t` -/
def size_t : Ty := if Archi.ptr64 then .Tlong .Unsigned noattr else .Tint .I32 .Unsigned noattr

/-- `Ctyping.ptrdiff_t` -/
def ptrdiff_t : Ty := if Archi.ptr64 then .Tlong .Signed noattr else .Tint .I32 .Signed noattr

/-! ## Operations over types -/

/-- `Ctyping.attr_add_volatile` -/
def attrAddVolatile (vol : Bool) (a : Attr) : Attr :=
  { attr_volatile := a.attr_volatile || vol, attr_alignas := a.attr_alignas }

/-- `Ctyping.type_of_member`: the type of member `f`; the `volatile`
    attribute of the composite propagates to it. -/
def typeOfMember (a : Attr) (f : Ident) (m : List Member) : Res Ty := do
  let ty ← fieldType f m
  .OK (changeAttributes (attrAddVolatile a.attr_volatile) ty)

/-- `Ctyping.type_unop` -/
def typeUnop (op : Unop) (ty : Ty) : Res Ty :=
  match op with
  | .Onotbool =>
      match Cop.classifyBool ty with
      | .default => .Error "operator !"
      | _ => .OK (.Tint .I32 .Signed noattr)
  | .Onotint =>
      match Cop.classifyNotint ty with
      | .i sg => .OK (.Tint .I32 sg noattr)
      | .l sg => .OK (.Tlong sg noattr)
      | .default => .Error "operator ~"
  | .Oneg =>
      match Cop.classifyNeg ty with
      | .i sg => .OK (.Tint .I32 sg noattr)
      | .f => .OK (.Tfloat .F64 noattr)
      | .s => .OK (.Tfloat .F32 noattr)
      | .l sg => .OK (.Tlong sg noattr)
      | .default => .Error "operator prefix -"
  | .Oabsfloat =>
      match Cop.classifyNeg ty with
      | .default => .Error "operator __builtin_fabs"
      | _ => .OK (.Tfloat .F64 noattr)

/-- `Ctyping.binarith_type` -/
def binarithType (ty1 ty2 : Ty) (m : String) : Res Ty :=
  match Cop.classifyBinarith ty1 ty2 with
  | .i sg => .OK (.Tint .I32 sg noattr)
  | .l sg => .OK (.Tlong sg noattr)
  | .f => .OK (.Tfloat .F64 noattr)
  | .s => .OK (.Tfloat .F32 noattr)
  | .default => .Error m

/-- `Ctyping.binarith_int_type` -/
def binarithIntType (ty1 ty2 : Ty) (m : String) : Res Ty :=
  match Cop.classifyBinarith ty1 ty2 with
  | .i sg => .OK (.Tint .I32 sg noattr)
  | .l sg => .OK (.Tlong sg noattr)
  | _ => .Error m

/-- `Ctyping.shift_op_type` -/
def shiftOpType (ty1 ty2 : Ty) (m : String) : Res Ty :=
  match Cop.classifyShift ty1 ty2 with
  | .ii sg | .il sg => .OK (.Tint .I32 sg noattr)
  | .li sg | .ll sg => .OK (.Tlong sg noattr)
  | .default => .Error m

/-- `Ctyping.comparison_type` -/
def comparisonType (ty1 ty2 : Ty) (m : String) : Res Ty :=
  match Cop.classifyCmp ty1 ty2 with
  | .default =>
      match Cop.classifyBinarith ty1 ty2 with
      | .default => .Error m
      | _ => .OK (.Tint .I32 .Signed noattr)
  | _ => .OK (.Tint .I32 .Signed noattr)

/-- `Ctyping.type_binop` -/
def typeBinop (op : Binop) (ty1 ty2 : Ty) : Res Ty :=
  match op with
  | .Oadd =>
      match Cop.classifyAdd ty1 ty2 with
      | .pi ty _ | .ip _ ty | .pl ty | .lp ty => .OK (.Tpointer ty noattr)
      | .default => binarithType ty1 ty2 "operator +"
  | .Osub =>
      match Cop.classifySub ty1 ty2 with
      | .pi ty _ | .pl ty => .OK (.Tpointer ty noattr)
      | .pp _ => .OK ptrdiff_t
      | .default => binarithType ty1 ty2 "operator infix -"
  | .Omul => binarithType ty1 ty2 "operator infix *"
  | .Odiv => binarithType ty1 ty2 "operator /"
  | .Omod => binarithIntType ty1 ty2 "operator %"
  | .Oand => binarithIntType ty1 ty2 "operator &"
  | .Oor => binarithIntType ty1 ty2 "operator |"
  | .Oxor => binarithIntType ty1 ty2 "operator ^"
  | .Oshl => shiftOpType ty1 ty2 "operator <<"
  | .Oshr => shiftOpType ty1 ty2 "operator >>"
  | .Oeq => comparisonType ty1 ty2 "operator =="
  | .One => comparisonType ty1 ty2 "operator !="
  | .Olt => comparisonType ty1 ty2 "operator <"
  | .Ogt => comparisonType ty1 ty2 "operator >"
  | .Ole => comparisonType ty1 ty2 "operator <="
  | .Oge => comparisonType ty1 ty2 "operator >="

/-- `Ctyping.type_deref` -/
def typeDeref (ty : Ty) : Res Ty :=
  match ty with
  | .Tpointer tyelt _ => .OK tyelt
  | .Tarray tyelt _ _ => .OK tyelt
  | .Tfunction _ _ _ => .OK ty
  | _ => .Error "operator prefix *"

/-- `Ctyping.attr_combine` -/
def attrCombine (a1 a2 : Attr) : Attr :=
  { attr_volatile := a1.attr_volatile || a2.attr_volatile
    attr_alignas :=
      match a1.attr_alignas, a2.attr_alignas with
      | none, al2 => al2
      | al1, none => al1
      | some n1, some n2 => some (max n1 n2) }

/-- `Ctyping.callconv_combine` -/
def callconvCombine (cc1 cc2 : CallConv) : Res CallConv :=
  if cc1.cc_vararg = cc2.cc_vararg then
    .OK { cc_vararg := cc1.cc_vararg, cc_unproto := cc1.cc_unproto && cc2.cc_unproto,
          cc_structret := cc1.cc_structret }
  else .Error "incompatible calling conventions"

mutual
/-- `Ctyping.type_combine`: the merge of two compatible types. -/
def typeCombine : Ty → Ty → Res Ty
  | .Tvoid, .Tvoid => .OK .Tvoid
  | .Tint sz1 sg1 a1, .Tint sz2 sg2 a2 =>
      if sz1 = sz2 ∧ sg1 = sg2 then .OK (.Tint sz1 sg1 (attrCombine a1 a2))
      else .Error "incompatible int types"
  | .Tlong sg1 a1, .Tlong sg2 a2 =>
      if sg1 = sg2 then .OK (.Tlong sg1 (attrCombine a1 a2))
      else .Error "incompatible long types"
  | .Tfloat sz1 a1, .Tfloat sz2 a2 =>
      if sz1 = sz2 then .OK (.Tfloat sz1 (attrCombine a1 a2))
      else .Error "incompatible float types"
  | .Tpointer t1 a1, .Tpointer t2 a2 => do
      let t ← typeCombine t1 t2
      .OK (.Tpointer t (attrCombine a1 a2))
  | .Tarray t1 sz1 a1, .Tarray t2 sz2 a2 => do
      let t ← typeCombine t1 t2
      if sz1 = sz2 then .OK (.Tarray t sz1 (attrCombine a1 a2))
      else .Error "incompatible array types"
  | .Tfunction args1 res1 cc1, .Tfunction args2 res2 cc2 => do
      let res ← typeCombine res1 res2
      let args ←
        if cc1.cc_unproto then .OK args2 else
        if cc2.cc_unproto then .OK args1 else
        typelistCombine args1 args2
      let cc ← callconvCombine cc1 cc2
      .OK (.Tfunction args res cc)
  | .Tstruct id1 a1, .Tstruct id2 a2 =>
      if id1 = id2 then .OK (.Tstruct id1 (attrCombine a1 a2))
      else .Error "incompatible struct types"
  | .Tunion id1 a1, .Tunion id2 a2 =>
      if id1 = id2 then .OK (.Tunion id1 (attrCombine a1 a2))
      else .Error "incompatible union types"
  | _, _ => .Error "incompatible types"

/-- The local `fix typelist_combine` of `Ctyping.type_combine`. -/
def typelistCombine : List Ty → List Ty → Res (List Ty)
  | [], [] => .OK []
  | t1 :: tl1, t2 :: tl2 => do
      let t ← typeCombine t1 t2
      let tl ← typelistCombine tl1 tl2
      .OK (t :: tl)
  | _, _ => .Error "incompatible function types"
end

/-- `Ctyping.is_void` -/
def isVoid : Ty → Bool
  | .Tvoid => true
  | _ => false

/-- `Ctyping.type_conditional`: the type of `r1 ? r2 : r3` from the types of
    the arms. -/
def typeConditional (ty1 ty2 : Ty) : Res Ty :=
  match typeconv ty1, typeconv ty2 with
  | .Tint _ _ _, .Tint _ _ _ | .Tint _ _ _, .Tlong _ _ | .Tint _ _ _, .Tfloat _ _
  | .Tlong _ _, .Tint _ _ _ | .Tlong _ _, .Tlong _ _ | .Tlong _ _, .Tfloat _ _
  | .Tfloat _ _, .Tint _ _ _ | .Tfloat _ _, .Tlong _ _ | .Tfloat _ _, .Tfloat _ _ =>
      binarithType ty1 ty2 "conditional expression"
  | .Tpointer t1 _, .Tpointer t2 _ =>
      let t :=
        if isVoid t1 || isVoid t2 then .Tvoid else
          match typeCombine t1 t2 with
          | .OK t => t
          | .Error _ => .Tvoid
      .OK (.Tpointer t noattr)
  | .Tpointer t1 _, .Tint _ _ _ => .OK (.Tpointer t1 noattr)
  | .Tint _ _ _, .Tpointer t2 _ => .OK (.Tpointer t2 noattr)
  | t1, t2 => typeCombine t1 t2

/-! ## Specification of the type system -/

/-- `Ctyping.typenv` -/
abbrev Typenv := PTree Ty

/-- `Ctyping.wt_cast` -/
def WtCast (from_ to : Ty) : Prop := Cop.classifyCast from_ to ≠ .default

/-- `Ctyping.wt_bool` -/
def WtBool (ty : Ty) : Prop := Cop.classifyBool ty ≠ .default

/-- `Ctyping.wt_int`: `n` is a normalized integer of size `sz`. -/
def WtInt (n : Integers.Int) (sz : IntSize) (sg : Signedness) : Prop :=
  match sz, sg with
  | .IBool, _ => n = Integers.Int.zero ∨ n = Integers.Int.one
  | .I8, .Unsigned => Integers.Int.zero_ext 8 n = n
  | .I8, .Signed => Integers.Int.sign_ext 8 n = n
  | .I16, .Unsigned => Integers.Int.zero_ext 16 n = n
  | .I16, .Signed => Integers.Int.sign_ext 16 n = n
  | .I32, _ => True

/-- `Ctyping.wt_val` -/
inductive WtVal : Val → Ty → Prop where
  | int (n sz sg a) : WtInt n sz sg → WtVal (.Vint n) (.Tint sz sg a)
  | ptr_int (b ofs sg a) : Archi.ptr64 = false → WtVal (.Vptr b ofs) (.Tint .I32 sg a)
  | long (n sg a) : WtVal (.Vlong n) (.Tlong sg a)
  | ptr_long (b ofs sg a) : Archi.ptr64 = true → WtVal (.Vptr b ofs) (.Tlong sg a)
  | float (f a) : WtVal (.Vfloat f) (.Tfloat .F64 a)
  | single (f a) : WtVal (.Vsingle f) (.Tfloat .F32 a)
  | pointer (b ofs ty a) : WtVal (.Vptr b ofs) (.Tpointer ty a)
  | int_pointer (n ty a) : Archi.ptr64 = false → WtVal (.Vint n) (.Tpointer ty a)
  | long_pointer (n ty a) : Archi.ptr64 = true → WtVal (.Vlong n) (.Tpointer ty a)
  | array (b ofs ty sz a) : WtVal (.Vptr b ofs) (.Tarray ty sz a)
  | function (b ofs tyargs tyres cc) : WtVal (.Vptr b ofs) (.Tfunction tyargs tyres cc)
  | struct (b ofs id a) : WtVal (.Vptr b ofs) (.Tstruct id a)
  | union (b ofs id a) : WtVal (.Vptr b ofs) (.Tunion id a)
  | undef (ty) : WtVal .Vundef ty
  | void (v) : WtVal v .Tvoid

/-- `Ctyping.wt_arguments` -/
inductive WtArguments : Csyntax.ExprList → List Ty → Prop where
  | nil : WtArguments .Enil []
  | cons (a al ty tyl) :
      WtCast (Csyntax.typeof a) ty → WtArguments al tyl → WtArguments (.Econs a al) (ty :: tyl)
  /-- tolerance for varargs -/
  | extra (a al) : strict = false → WtArguments (.Econs a al) []

/-- `Ctyping.subtype` -/
def Subtype (t1 t2 : Ty) : Prop := ∀ v, WtVal v t1 → WtVal v t2

section WT_EXPR_STMT

variable (ce : CompositeEnv) (e : Typenv)

mutual
/-- `Ctyping.wt_rvalue` -/
inductive WtRvalue : Csyntax.Expr → Prop where
  | val (v ty) : WtVal v ty → WtRvalue (.Eval v ty)
  | valof (l) : WtLvalue l → WtRvalue (.Evalof l (Csyntax.typeof l))
  | addrof (l) : WtLvalue l → WtRvalue (.Eaddrof l (.Tpointer (Csyntax.typeof l) noattr))
  | unop (op r ty) :
      WtRvalue r → typeUnop op (Csyntax.typeof r) = .OK ty → WtRvalue (.Eunop op r ty)
  | binop (op r1 r2 ty) :
      WtRvalue r1 → WtRvalue r2 →
      typeBinop op (Csyntax.typeof r1) (Csyntax.typeof r2) = .OK ty →
      WtRvalue (.Ebinop op r1 r2 ty)
  | cast (r ty) : WtRvalue r → WtCast (Csyntax.typeof r) ty → WtRvalue (.Ecast r ty)
  | seqand (r1 r2) :
      WtRvalue r1 → WtRvalue r2 → WtBool (Csyntax.typeof r1) → WtBool (Csyntax.typeof r2) →
      WtRvalue (.Eseqand r1 r2 (.Tint .I32 .Signed noattr))
  | seqor (r1 r2) :
      WtRvalue r1 → WtRvalue r2 → WtBool (Csyntax.typeof r1) → WtBool (Csyntax.typeof r2) →
      WtRvalue (.Eseqor r1 r2 (.Tint .I32 .Signed noattr))
  | condition (r1 r2 r3 ty) :
      WtRvalue r1 → WtRvalue r2 → WtRvalue r3 → WtBool (Csyntax.typeof r1) →
      WtCast (Csyntax.typeof r2) ty → WtCast (Csyntax.typeof r3) ty →
      WtRvalue (.Econdition r1 r2 r3 ty)
  | sizeof (ty) : WtRvalue (.Esizeof ty size_t)
  | alignof (ty) : WtRvalue (.Ealignof ty size_t)
  | assign (l r) :
      WtLvalue l → WtRvalue r → WtCast (Csyntax.typeof r) (Csyntax.typeof l) →
      WtRvalue (.Eassign l r (Csyntax.typeof l))
  | assignop (op l r ty) :
      WtLvalue l → WtRvalue r →
      typeBinop op (Csyntax.typeof l) (Csyntax.typeof r) = .OK ty →
      WtCast ty (Csyntax.typeof l) →
      WtRvalue (.Eassignop op l r ty (Csyntax.typeof l))
  | postincr (id l ty) :
      WtLvalue l →
      typeBinop (match id with | .Incr => .Oadd | .Decr => .Osub)
        (Csyntax.typeof l) (.Tint .I32 .Signed noattr) = .OK ty →
      WtCast (Cop.incrdecrType (Csyntax.typeof l)) (Csyntax.typeof l) →
      WtRvalue (.Epostincr id l (Csyntax.typeof l))
  | comma (r1 r2) : WtRvalue r1 → WtRvalue r2 → WtRvalue (.Ecomma r1 r2 (Csyntax.typeof r2))
  | call (r1 rargs tyargs tyres cconv) :
      WtRvalue r1 → WtExprlist rargs →
      Cop.classifyFun (Csyntax.typeof r1) = .f tyargs tyres cconv →
      WtArguments rargs tyargs →
      WtRvalue (.Ecall r1 rargs tyres)
  | builtin (ef tyargs rargs ty) :
      WtExprlist rargs → WtArguments rargs tyargs →
      ((ty = .Tvoid ∧ ef.sig.sig_res = .Xvoid) ∨
       (tyargs = [type_bool, ty, ty] ∧
        let x := (typOfType ty).inj
        ef = .EF_builtin "__builtin_sel" (mksignature [.Xint, x, x] x cc_default))) →
      WtRvalue (.Ebuiltin ef tyargs rargs ty)
  | paren (r tycast ty) :
      WtRvalue r → WtCast (Csyntax.typeof r) tycast → Subtype tycast ty →
      WtRvalue (.Eparen r tycast ty)

/-- `Ctyping.wt_lvalue` -/
inductive WtLvalue : Csyntax.Expr → Prop where
  | loc (b ofs bf ty) : WtLvalue (.Eloc b ofs bf ty)
  | var (x ty) : e.get x = some ty → WtLvalue (.Evar x ty)
  | deref (r ty) : WtRvalue r → typeDeref (Csyntax.typeof r) = .OK ty → WtLvalue (.Ederef r ty)
  | field (r f id a co ty) :
      WtRvalue r →
      (Csyntax.typeof r = .Tstruct id a ∨ Csyntax.typeof r = .Tunion id a) →
      ce.get id = some co →
      typeOfMember a f co.co_members = .OK ty →
      WtLvalue (.Efield r f ty)

/-- `Ctyping.wt_exprlist` -/
inductive WtExprlist : Csyntax.ExprList → Prop where
  | nil : WtExprlist .Enil
  | cons (r1 rl) : WtRvalue r1 → WtExprlist rl → WtExprlist (.Econs r1 rl)
end

/-- `Ctyping.wt_expr_kind` -/
def WtExprKind : Csem.Kind → Csyntax.Expr → Prop
  | .RV, a => WtRvalue ce e a
  | .LV, a => WtLvalue ce e a

/-- `Ctyping.expr_kind` -/
def exprKind : Csyntax.Expr → Csem.Kind
  | .Eloc _ _ _ _ | .Evar _ _ | .Ederef _ _ | .Efield _ _ _ => .LV
  | _ => .RV

/-- `Ctyping.wt_expr` -/
def WtExpr (a : Csyntax.Expr) : Prop :=
  match exprKind a with
  | .RV => WtRvalue ce e a
  | .LV => WtLvalue ce e a

variable (rt : Ty)

mutual
/-- `Ctyping.wt_stmt` -/
inductive WtStmt : Csyntax.Stmt → Prop where
  | skip : WtStmt .Sskip
  | do_ (r) : WtRvalue ce e r → WtStmt (.Sdo r)
  | sequence (s1 s2) : WtStmt s1 → WtStmt s2 → WtStmt (.Ssequence s1 s2)
  | ifthenelse (r s1 s2) :
      WtRvalue ce e r → WtStmt s1 → WtStmt s2 → WtBool (Csyntax.typeof r) →
      WtStmt (.Sifthenelse r s1 s2)
  | while_ (r s) :
      WtRvalue ce e r → WtStmt s → WtBool (Csyntax.typeof r) → WtStmt (.Swhile r s)
  | dowhile (r s) :
      WtRvalue ce e r → WtStmt s → WtBool (Csyntax.typeof r) → WtStmt (.Sdowhile r s)
  | for_ (s1 r s2 s3) :
      WtRvalue ce e r → WtStmt s1 → WtStmt s2 → WtStmt s3 → WtBool (Csyntax.typeof r) →
      WtStmt (.Sfor s1 r s2 s3)
  | break_ : WtStmt .Sbreak
  | continue_ : WtStmt .Scontinue
  | return_none : WtStmt (.Sreturn none)
  | return_some (r) :
      WtRvalue ce e r → WtCast (Csyntax.typeof r) rt → WtStmt (.Sreturn (some r))
  | switch (r ls sg sz a) :
      WtRvalue ce e r →
      (Csyntax.typeof r = .Tint sz sg a ∨ Csyntax.typeof r = .Tlong sg a) →
      WtLblstmts ls →
      WtStmt (.Sswitch r ls)
  | label (lbl s) : WtStmt s → WtStmt (.Slabel lbl s)
  | goto (lbl) : WtStmt (.Sgoto lbl)

/-- `Ctyping.wt_lblstmts` -/
inductive WtLblstmts : Csyntax.LStmts → Prop where
  | nil : WtLblstmts .LSnil
  | cons (case s ls) : WtStmt s → WtLblstmts ls → WtLblstmts (.LScons case s ls)
end

end WT_EXPR_STMT

/-- `Ctyping.bind_vars` -/
def bindVars (e : Typenv) : List (Ident × Ty) → Typenv
  | [] => e
  | (id, ty) :: l => bindVars (e.set id ty) l

/-- `Ctyping.wt_function` -/
inductive WtFunction (ce : CompositeEnv) (e : Typenv) : Csyntax.Function → Prop where
  | intro (f : Csyntax.Function) :
      WtStmt ce (bindVars (bindVars e f.fn_params) f.fn_vars) f.fn_return f.fn_body →
      WtFunction ce e f

/-- `Ctyping.bind_globdef` -/
def bindGlobdef (e : Typenv) : List (Ident × GlobDef Csyntax.FunDef Ty) → Typenv
  | [] => e
  | (id, .Gfun fd) :: l => bindGlobdef (e.set id (Csyntax.typeOfFundef fd)) l
  | (id, .Gvar v) :: l => bindGlobdef (e.set id v.gvar_info) l

/-- `Ctyping.wt_fundef` -/
inductive WtFundef (ce : CompositeEnv) (e : Typenv) : Csyntax.FunDef → Prop where
  | internal (f) : WtFunction ce e f → WtFundef ce e (.Internal f)
  | external (ef targs tres cc) :
      ef.sig.sig_res = rettypeOfType tres → WtFundef ce e (.External ef targs tres cc)

/-- `Ctyping.wt_program`: every function of the program is well typed in the
    global type environment. -/
def WtProgram (p : Csyntax.Program) : Prop :=
  ∀ id fd, (id, GlobDef.Gfun fd) ∈ p.prog_defs →
    WtFundef p.prog_comp_env (bindGlobdef PTree.empty p.prog_defs) fd

/-! ## Type checking -/

/-- `assertion` of the error monad. -/
@[inline] def assertion {A : Type} (b : Bool) (k : Res A) : Res A :=
  if b then k else .Error "Assertion failed"

/-- `Ctyping.check_cast` -/
def checkCast (t1 t2 : Ty) : Res Unit :=
  match Cop.classifyCast t1 t2 with
  | .default => .Error "illegal cast"
  | _ => .OK ()

/-- `Ctyping.check_bool` -/
def checkBool (t : Ty) : Res Unit :=
  match Cop.classifyBool t with
  | .default => .Error "not a boolean"
  | _ => .OK ()

/-- `Ctyping.check_literal` -/
def checkLiteral (v : Val) (t : Ty) : Res Unit :=
  match v, t with
  | .Vint _, .Tint .I32 _ _ => .OK ()
  | .Vint _, .Tpointer _ _ => .OK ()
  | .Vlong _, .Tlong _ _ => .OK ()
  | .Vsingle _, .Tfloat .F32 _ => .OK ()
  | .Vfloat _, .Tfloat .F64 _ => .OK ()
  | _, _ => .Error "wrong literal"

/-- `Ctyping.check_arguments` -/
def checkArguments : Csyntax.ExprList → List Ty → Res Unit
  | .Enil, [] => .OK ()
  | .Enil, _ => .Error "not enough arguments"
  | _, [] => if strict then .Error "too many arguments" else .OK ()
  | .Econs e1 el, ty1 :: tyl => do
      checkCast (Csyntax.typeof e1) ty1
      checkArguments el tyl

/-- `Ctyping.check_rval` -/
def checkRval : Csyntax.Expr → Res Unit
  | .Eloc _ _ _ _ | .Evar _ _ | .Ederef _ _ | .Efield _ _ _ => .Error "not a r-value"
  | _ => .OK ()

/-- `Ctyping.check_lval` -/
def checkLval : Csyntax.Expr → Res Unit
  | .Eloc _ _ _ _ | .Evar _ _ | .Ederef _ _ | .Efield _ _ _ => .OK ()
  | _ => .Error "not a l-value"

/-- `Ctyping.check_rvals` -/
def checkRvals : Csyntax.ExprList → Res Unit
  | .Enil => .OK ()
  | .Econs e1 el => do
      checkRval e1
      checkRvals el

/-! ### Smart constructors -/

/-- `Ctyping.evar` -/
def evar (e : Typenv) (x : Ident) : Res Csyntax.Expr :=
  match e.get x with
  | some ty => .OK (.Evar x ty)
  | none => .Error "unbound variable"

/-- `Ctyping.ederef` -/
def ederef (r : Csyntax.Expr) : Res Csyntax.Expr := do
  checkRval r
  let ty ← typeDeref (Csyntax.typeof r)
  .OK (.Ederef r ty)

/-- `Ctyping.efield` -/
def efield (ce : CompositeEnv) (r : Csyntax.Expr) (f : Ident) : Res Csyntax.Expr := do
  checkRval r
  match Csyntax.typeof r with
  | .Tstruct id a | .Tunion id a =>
      match ce.get id with
      | none => .Error "unbound composite"
      | some co => do
          let ty ← typeOfMember a f co.co_members
          .OK (.Efield r f ty)
  | _ => .Error "argument of . is not a struct or union"

/-- `Ctyping.econst_int` -/
def econstInt (n : Integers.Int) (sg : Signedness) : Csyntax.Expr :=
  .Eval (.Vint n) (.Tint .I32 sg noattr)

/-- `Ctyping.econst_ptr_int` -/
def econstPtrInt (n : Integers.Int) (ty : Ty) : Csyntax.Expr :=
  .Eval (if Archi.ptr64 then .Vlong (Integers.Int64.repr (Integers.Int.unsigned n)) else .Vint n)
    (.Tpointer ty noattr)

/-- `Ctyping.econst_long` -/
def econstLong (n : Integers.Int64) (sg : Signedness) : Csyntax.Expr :=
  .Eval (.Vlong n) (.Tlong sg noattr)

/-- `Ctyping.econst_ptr_long` -/
def econstPtrLong (n : Integers.Int64) (ty : Ty) : Csyntax.Expr :=
  .Eval (if Archi.ptr64 then .Vlong n else .Vint (Integers.Int64.loword n)) (.Tpointer ty noattr)

/-- `Ctyping.econst_float` -/
def econstFloat (n : Floats.Float) : Csyntax.Expr := .Eval (.Vfloat n) (.Tfloat .F64 noattr)

/-- `Ctyping.econst_single` -/
def econstSingle (n : Floats.Float32) : Csyntax.Expr := .Eval (.Vsingle n) (.Tfloat .F32 noattr)

/-- `Ctyping.evalof` -/
def evalof (l : Csyntax.Expr) : Res Csyntax.Expr := do
  checkLval l
  .OK (.Evalof l (Csyntax.typeof l))

/-- `Ctyping.eaddrof` -/
def eaddrof (l : Csyntax.Expr) : Res Csyntax.Expr := do
  checkLval l
  .OK (.Eaddrof l (.Tpointer (Csyntax.typeof l) noattr))

/-- `Ctyping.eunop` -/
def eunop (op : Unop) (r : Csyntax.Expr) : Res Csyntax.Expr := do
  checkRval r
  let ty ← typeUnop op (Csyntax.typeof r)
  .OK (.Eunop op r ty)

/-- `Ctyping.ebinop` -/
def ebinop (op : Binop) (r1 r2 : Csyntax.Expr) : Res Csyntax.Expr := do
  checkRval r1
  checkRval r2
  let ty ← typeBinop op (Csyntax.typeof r1) (Csyntax.typeof r2)
  .OK (.Ebinop op r1 r2 ty)

/-- `Ctyping.ecast` -/
def ecast (ty : Ty) (r : Csyntax.Expr) : Res Csyntax.Expr := do
  checkRval r
  checkCast (Csyntax.typeof r) ty
  .OK (.Ecast r ty)

/-- `Ctyping.eseqand` -/
def eseqand (r1 r2 : Csyntax.Expr) : Res Csyntax.Expr := do
  checkRval r1
  checkRval r2
  checkBool (Csyntax.typeof r1)
  checkBool (Csyntax.typeof r2)
  .OK (.Eseqand r1 r2 type_int32s)

/-- `Ctyping.eseqor` -/
def eseqor (r1 r2 : Csyntax.Expr) : Res Csyntax.Expr := do
  checkRval r1
  checkRval r2
  checkBool (Csyntax.typeof r1)
  checkBool (Csyntax.typeof r2)
  .OK (.Eseqor r1 r2 type_int32s)

/-- `Ctyping.econdition` -/
def econdition (r1 r2 r3 : Csyntax.Expr) : Res Csyntax.Expr := do
  checkRval r1
  checkRval r2
  checkRval r3
  checkBool (Csyntax.typeof r1)
  let ty ← typeConditional (Csyntax.typeof r2) (Csyntax.typeof r3)
  .OK (.Econdition r1 r2 r3 ty)

/-- `Ctyping.econdition'` -/
def econdition' (r1 r2 r3 : Csyntax.Expr) (ty : Ty) : Res Csyntax.Expr := do
  checkRval r1
  checkRval r2
  checkRval r3
  checkBool (Csyntax.typeof r1)
  checkCast (Csyntax.typeof r2) ty
  checkCast (Csyntax.typeof r3) ty
  .OK (.Econdition r1 r2 r3 ty)

/-- `Ctyping.esizeof` -/
def esizeof (ty : Ty) : Csyntax.Expr := .Esizeof ty size_t

/-- `Ctyping.ealignof` -/
def ealignof (ty : Ty) : Csyntax.Expr := .Ealignof ty size_t

/-- `Ctyping.eassign` -/
def eassign (l r : Csyntax.Expr) : Res Csyntax.Expr := do
  checkLval l
  checkRval r
  checkCast (Csyntax.typeof r) (Csyntax.typeof l)
  .OK (.Eassign l r (Csyntax.typeof l))

/-- `Ctyping.eassignop` -/
def eassignop (op : Binop) (l r : Csyntax.Expr) : Res Csyntax.Expr := do
  checkLval l
  checkRval r
  let ty ← typeBinop op (Csyntax.typeof l) (Csyntax.typeof r)
  checkCast ty (Csyntax.typeof l)
  .OK (.Eassignop op l r ty (Csyntax.typeof l))

/-- `Ctyping.epostincrdecr` -/
def epostincrdecr (id : Cop.IncrOrDecr) (l : Csyntax.Expr) : Res Csyntax.Expr := do
  checkLval l
  let _ ← typeBinop (match id with | .Incr => .Oadd | .Decr => .Osub) (Csyntax.typeof l) type_int32s
  checkCast (Cop.incrdecrType (Csyntax.typeof l)) (Csyntax.typeof l)
  .OK (.Epostincr id l (Csyntax.typeof l))

/-- `Ctyping.epostincr` -/
def epostincr (l : Csyntax.Expr) : Res Csyntax.Expr := epostincrdecr .Incr l
/-- `Ctyping.epostdecr` -/
def epostdecr (l : Csyntax.Expr) : Res Csyntax.Expr := epostincrdecr .Decr l
/-- `Ctyping.epreincr` -/
def epreincr (l : Csyntax.Expr) : Res Csyntax.Expr :=
  eassignop .Oadd l (.Eval (.Vint Integers.Int.one) type_int32s)
/-- `Ctyping.epredecr` -/
def epredecr (l : Csyntax.Expr) : Res Csyntax.Expr :=
  eassignop .Osub l (.Eval (.Vint Integers.Int.one) type_int32s)

/-- `Ctyping.ecomma` -/
def ecomma (r1 r2 : Csyntax.Expr) : Res Csyntax.Expr := do
  checkRval r1
  checkRval r2
  .OK (.Ecomma r1 r2 (Csyntax.typeof r2))

/-- `Ctyping.ecall` -/
def ecall (fn : Csyntax.Expr) (args : Csyntax.ExprList) : Res Csyntax.Expr := do
  checkRval fn
  checkRvals args
  match Cop.classifyFun (Csyntax.typeof fn) with
  | .f tyargs tyres _ => do
      checkArguments args tyargs
      .OK (.Ecall fn args tyres)
  | _ => .Error "call: not a function"

/-- `Ctyping.ebuiltin` -/
def ebuiltin (ef : ExtFun) (tyargs : List Ty) (args : Csyntax.ExprList) (tyres : Ty) :
    Res Csyntax.Expr := do
  checkRvals args
  checkArguments args tyargs
  if decide (tyres = .Tvoid) && decide (ef.sig.sig_res = .Xvoid)
  then .OK (.Ebuiltin ef tyargs args tyres)
  else .Error "builtin: wrong type decoration"

/-- `Ctyping.eselection` -/
def eselection (r1 r2 r3 : Csyntax.Expr) : Res Csyntax.Expr := do
  checkRval r1
  checkRval r2
  checkRval r3
  checkBool (Csyntax.typeof r1)
  let ty ← typeConditional (Csyntax.typeof r2) (Csyntax.typeof r3)
  .OK (Csyntax.Eselection r1 r2 r3 ty)

/-- `Ctyping.sdo` -/
def sdo (a : Csyntax.Expr) : Res Csyntax.Stmt := do
  checkRval a
  .OK (.Sdo a)

/-- `Ctyping.sifthenelse` -/
def sifthenelse (a : Csyntax.Expr) (s1 s2 : Csyntax.Stmt) : Res Csyntax.Stmt := do
  checkRval a
  checkBool (Csyntax.typeof a)
  .OK (.Sifthenelse a s1 s2)

/-- `Ctyping.swhile` -/
def swhile (a : Csyntax.Expr) (s : Csyntax.Stmt) : Res Csyntax.Stmt := do
  checkRval a
  checkBool (Csyntax.typeof a)
  .OK (.Swhile a s)

/-- `Ctyping.sdowhile` -/
def sdowhile (a : Csyntax.Expr) (s : Csyntax.Stmt) : Res Csyntax.Stmt := do
  checkRval a
  checkBool (Csyntax.typeof a)
  .OK (.Sdowhile a s)

/-- `Ctyping.sfor` -/
def sfor (s1 : Csyntax.Stmt) (a : Csyntax.Expr) (s2 s3 : Csyntax.Stmt) : Res Csyntax.Stmt := do
  checkRval a
  checkBool (Csyntax.typeof a)
  .OK (.Sfor s1 a s2 s3)

/-- `Ctyping.sreturn` -/
def sreturn (rt : Ty) (a : Csyntax.Expr) : Res Csyntax.Stmt := do
  checkRval a
  checkCast (Csyntax.typeof a) rt
  .OK (.Sreturn (some a))

/-- `Ctyping.sswitch` -/
def sswitch (a : Csyntax.Expr) (sl : Csyntax.LStmts) : Res Csyntax.Stmt := do
  checkRval a
  match Csyntax.typeof a with
  | .Tint _ _ _ | .Tlong _ _ => .OK (.Sswitch a sl)
  | _ => .Error "wrong type for argument of switch"

/-! ### The type-checker -/

mutual
/-- `Ctyping.retype_expr`: rebuild `a` with correct type annotations. -/
def retypeExpr (ce : CompositeEnv) (e : Typenv) : Csyntax.Expr → Res Csyntax.Expr
  | .Eval (.Vint n) (.Tint _ sg _) => .OK (econstInt n sg)
  | .Eval (.Vint n) (.Tpointer ty _) => .OK (econstPtrInt n ty)
  | .Eval (.Vlong n) (.Tlong sg _) => .OK (econstLong n sg)
  | .Eval (.Vfloat n) _ => .OK (econstFloat n)
  | .Eval (.Vsingle n) _ => .OK (econstSingle n)
  | .Eval _ _ => .Error "bad literal"
  | .Evar x _ => evar e x
  | .Efield r f _ => do
      let r' ← retypeExpr ce e r
      efield ce r' f
  | .Evalof l _ => do
      let l' ← retypeExpr ce e l
      evalof l'
  | .Ederef r _ => do
      let r' ← retypeExpr ce e r
      ederef r'
  | .Eaddrof l _ => do
      let l' ← retypeExpr ce e l
      eaddrof l'
  | .Eunop op r _ => do
      let r' ← retypeExpr ce e r
      eunop op r'
  | .Ebinop op r1 r2 _ => do
      let r1' ← retypeExpr ce e r1
      let r2' ← retypeExpr ce e r2
      ebinop op r1' r2'
  | .Ecast r ty => do
      let r' ← retypeExpr ce e r
      ecast ty r'
  | .Eseqand r1 r2 _ => do
      let r1' ← retypeExpr ce e r1
      let r2' ← retypeExpr ce e r2
      eseqand r1' r2'
  | .Eseqor r1 r2 _ => do
      let r1' ← retypeExpr ce e r1
      let r2' ← retypeExpr ce e r2
      eseqor r1' r2'
  | .Econdition r1 r2 r3 _ => do
      let r1' ← retypeExpr ce e r1
      let r2' ← retypeExpr ce e r2
      let r3' ← retypeExpr ce e r3
      econdition r1' r2' r3'
  | .Esizeof ty _ => .OK (esizeof ty)
  | .Ealignof ty _ => .OK (ealignof ty)
  | .Eassign l r _ => do
      let l' ← retypeExpr ce e l
      let r' ← retypeExpr ce e r
      eassign l' r'
  | .Eassignop op l r _ _ => do
      let l' ← retypeExpr ce e l
      let r' ← retypeExpr ce e r
      eassignop op l' r'
  | .Epostincr id l _ => do
      let l' ← retypeExpr ce e l
      epostincrdecr id l'
  | .Ecomma r1 r2 _ => do
      let r1' ← retypeExpr ce e r1
      let r2' ← retypeExpr ce e r2
      ecomma r1' r2'
  | .Ecall r1 rl _ => do
      let r1' ← retypeExpr ce e r1
      let rl' ← retypeExprlist ce e rl
      ecall r1' rl'
  | .Ebuiltin ef tyargs rl tyres => do
      let rl' ← retypeExprlist ce e rl
      ebuiltin ef tyargs rl' tyres
  | .Eloc _ _ _ _ => .Error "Eloc in source"
  | .Eparen _ _ _ => .Error "Eparen in source"

/-- `Ctyping.retype_exprlist` -/
def retypeExprlist (ce : CompositeEnv) (e : Typenv) : Csyntax.ExprList → Res Csyntax.ExprList
  | .Enil => .OK .Enil
  | .Econs a1 al => do
      let a1' ← retypeExpr ce e a1
      let al' ← retypeExprlist ce e al
      checkRval a1'
      .OK (.Econs a1' al')
end

mutual
/-- `Ctyping.retype_stmt` -/
def retypeStmt (ce : CompositeEnv) (e : Typenv) (rt : Ty) : Csyntax.Stmt → Res Csyntax.Stmt
  | .Sskip => .OK .Sskip
  | .Sdo a => do
      let a' ← retypeExpr ce e a
      sdo a'
  | .Ssequence s1 s2 => do
      let s1' ← retypeStmt ce e rt s1
      let s2' ← retypeStmt ce e rt s2
      .OK (.Ssequence s1' s2')
  | .Sifthenelse a s1 s2 => do
      let a' ← retypeExpr ce e a
      let s1' ← retypeStmt ce e rt s1
      let s2' ← retypeStmt ce e rt s2
      sifthenelse a' s1' s2'
  | .Swhile a s => do
      let a' ← retypeExpr ce e a
      let s' ← retypeStmt ce e rt s
      swhile a' s'
  | .Sdowhile a s => do
      let a' ← retypeExpr ce e a
      let s' ← retypeStmt ce e rt s
      sdowhile a' s'
  | .Sfor s1 a s2 s3 => do
      let a' ← retypeExpr ce e a
      let s1' ← retypeStmt ce e rt s1
      let s2' ← retypeStmt ce e rt s2
      let s3' ← retypeStmt ce e rt s3
      sfor s1' a' s2' s3'
  | .Sbreak => .OK .Sbreak
  | .Scontinue => .OK .Scontinue
  | .Sreturn none => .OK (.Sreturn none)
  | .Sreturn (some a) => do
      let a' ← retypeExpr ce e a
      sreturn rt a'
  | .Sswitch a sl => do
      let a' ← retypeExpr ce e a
      let sl' ← retypeLblstmts ce e rt sl
      sswitch a' sl'
  | .Slabel lbl s => do
      let s' ← retypeStmt ce e rt s
      .OK (.Slabel lbl s')
  | .Sgoto lbl => .OK (.Sgoto lbl)

/-- `Ctyping.retype_lblstmts` -/
def retypeLblstmts (ce : CompositeEnv) (e : Typenv) (rt : Ty) : Csyntax.LStmts → Res Csyntax.LStmts
  | .LSnil => .OK .LSnil
  | .LScons case s sl => do
      let s' ← retypeStmt ce e rt s
      let sl' ← retypeLblstmts ce e rt sl
      .OK (.LScons case s' sl')
end

/-- `Ctyping.retype_function` -/
def retypeFunction (ce : CompositeEnv) (e : Typenv) (f : Csyntax.Function) :
    Res Csyntax.Function := do
  let e := bindVars (bindVars e f.fn_params) f.fn_vars
  let s ← retypeStmt ce e f.fn_return f.fn_body
  .OK { f with fn_body := s }

/-- `Ctyping.retype_fundef` -/
def retypeFundef (ce : CompositeEnv) (e : Typenv) (fd : Csyntax.FunDef) : Res Csyntax.FunDef :=
  match fd with
  | .Internal f => do
      let f' ← retypeFunction ce e f
      .OK (.Internal f')
  | .External ef _ res _ =>
      assertion (decide (ef.sig.sig_res = rettypeOfType res)) (.OK fd)

/-- `Ctyping.typecheck_program`: re-type-check every function of `p`. -/
def typecheckProgram (p : Csyntax.Program) : Res Csyntax.Program := do
  let e := bindGlobdef PTree.empty p.prog_defs
  let ce := p.prog_comp_env
  let defs ← transfGlobdefs (fun _ f => retypeFundef ce e f) (fun _ v => .OK v) p.prog_defs
  .OK { p with prog_defs := defs }

end Ctyping
end CC
