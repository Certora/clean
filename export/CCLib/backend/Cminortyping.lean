/-
  Type inference for Cminor — port of the executable parts of
  `backend/Cminortyping.v`: `type_constant`, `type_unop`, `type_binop`,
  `RTLtypes`/`S` (the unification solver at machine types), `expect`,
  `type_expr`, `type_exprlist`, `type_assign`, `opt_set`, `type_stmt`,
  `typenv`, `type_function`; and the "safe expressions" used by
  `Selection`'s if-conversion: `known_idents`, `is_known`, `known_id`,
  `safe_unop`, `safe_binop`, `safe_expr`, with `known_id_sound_1/2`.

  The relational type system, the soundness of type inference and subject
  reduction are in `CCLib.backend.CminortypingSpec` and `CCLib.backend.CminortypingSubject`.
-/
import CCLib.backend.Cminor
import CCLib.common.Unityping

namespace CC
namespace Cminortyping

open Cminor

/-- `Cminortyping.type_constant` -/
def typeConstant (c : Constant) : ATyp :=
  match c with
  | .Ointconst _ => .Tint
  | .Ofloatconst _ => .Tfloat
  | .Osingleconst _ => .Tsingle
  | .Olongconst _ => .Tlong
  | .Oaddrsymbol _ _ => Tptr
  | .Oaddrstack _ => Tptr

/-- `Cminortyping.type_unop` -/
def typeUnop (op : UnaryOperation) : ATyp × ATyp :=
  match op with
  | .Ocast8unsigned | .Ocast8signed | .Ocast16unsigned | .Ocast16signed
  | .Onegint | .Onotint => (.Tint, .Tint)
  | .Onegf | .Oabsf => (.Tfloat, .Tfloat)
  | .Onegfs | .Oabsfs => (.Tsingle, .Tsingle)
  | .Osingleoffloat => (.Tfloat, .Tsingle)
  | .Ofloatofsingle => (.Tsingle, .Tfloat)
  | .Ointoffloat | .Ointuoffloat => (.Tfloat, .Tint)
  | .Ofloatofint | .Ofloatofintu => (.Tint, .Tfloat)
  | .Ointofsingle | .Ointuofsingle => (.Tsingle, .Tint)
  | .Osingleofint | .Osingleofintu => (.Tint, .Tsingle)
  | .Onegl | .Onotl => (.Tlong, .Tlong)
  | .Ointoflong => (.Tlong, .Tint)
  | .Olongofint | .Olongofintu => (.Tint, .Tlong)
  | .Olongoffloat | .Olonguoffloat => (.Tfloat, .Tlong)
  | .Ofloatoflong | .Ofloatoflongu => (.Tlong, .Tfloat)
  | .Olongofsingle | .Olonguofsingle => (.Tsingle, .Tlong)
  | .Osingleoflong | .Osingleoflongu => (.Tlong, .Tsingle)

/-- `Cminortyping.type_binop` -/
def typeBinop (op : BinaryOperation) : ATyp × ATyp × ATyp :=
  match op with
  | .Oadd | .Osub | .Omul | .Odiv | .Odivu | .Omod | .Omodu
  | .Oand | .Oor | .Oxor | .Oshl | .Oshr | .Oshru => (.Tint, .Tint, .Tint)
  | .Oaddf | .Osubf | .Omulf | .Odivf => (.Tfloat, .Tfloat, .Tfloat)
  | .Oaddfs | .Osubfs | .Omulfs | .Odivfs => (.Tsingle, .Tsingle, .Tsingle)
  | .Oaddl | .Osubl | .Omull | .Odivl | .Odivlu | .Omodl | .Omodlu
  | .Oandl | .Oorl | .Oxorl => (.Tlong, .Tlong, .Tlong)
  | .Oshll | .Oshrl | .Oshrlu => (.Tlong, .Tint, .Tlong)
  | .Ocmp _ | .Ocmpu _ => (.Tint, .Tint, .Tint)
  | .Ocmpf _ => (.Tfloat, .Tfloat, .Tint)
  | .Ocmpfs _ => (.Tsingle, .Tsingle, .Tint)
  | .Ocmpl _ | .Ocmplu _ => (.Tlong, .Tlong, .Tint)

/-- `Cminortyping.S.typenv` (`UniSolver(RTLtypes).typenv`) -/
abbrev STypenv := UniSolver.Typenv ATyp

/-- `Cminortyping.expect` -/
def expect (e : STypenv) (t1 t2 : ATyp) : Res STypenv :=
  if t1 = t2 then .OK e else .Error "type mismatch"

/-- `Cminortyping.type_expr` -/
def typeExpr (e : STypenv) : Cminor.Expr → ATyp → Res STypenv
  | .Evar id, t => UniSolver.set e id t
  | .Econst c, t => expect e (typeConstant c) t
  | .Eunop op a1, t =>
      let (targ1, tres) := typeUnop op
      match typeExpr e a1 targ1 with
      | .OK e1 => expect e1 tres t
      | .Error m => .Error m
  | .Ebinop op a1 a2, t =>
      let (targ1, targ2, tres) := typeBinop op
      match typeExpr e a1 targ1 with
      | .OK e1 =>
          match typeExpr e1 a2 targ2 with
          | .OK e2 => expect e2 tres t
          | .Error m => .Error m
      | .Error m => .Error m
  | .Eload chunk a1, t =>
      match typeExpr e a1 Tptr with
      | .OK e1 => expect e1 chunk.typ t
      | .Error m => .Error m

/-- `Cminortyping.type_exprlist` -/
def typeExprlist : STypenv → List Cminor.Expr → List ATyp → Res STypenv
  | e, [], [] => .OK e
  | e, a :: al, t :: tl =>
      match typeExpr e a t with
      | .OK e1 => typeExprlist e1 al tl
      | .Error m => .Error m
  | _, _, _ => .Error "arity mismatch"

/-- `Cminortyping.type_assign` -/
def typeAssign (e : STypenv) (id : Ident) (a : Cminor.Expr) : Res STypenv :=
  match a with
  | .Evar id' =>
      match UniSolver.move e id id' with
      | .OK (_, e1) => .OK e1
      | .Error m => .Error m
  | .Econst c => UniSolver.set e id (typeConstant c)
  | .Eunop op a1 =>
      let (targ1, tres) := typeUnop op
      match typeExpr e a1 targ1 with
      | .OK e1 => UniSolver.set e1 id tres
      | .Error m => .Error m
  | .Ebinop op a1 a2 =>
      let (targ1, targ2, tres) := typeBinop op
      match typeExpr e a1 targ1 with
      | .OK e1 =>
          match typeExpr e1 a2 targ2 with
          | .OK e2 => UniSolver.set e2 id tres
          | .Error m => .Error m
      | .Error m => .Error m
  | .Eload chunk a1 =>
      match typeExpr e a1 Tptr with
      | .OK e1 => UniSolver.set e1 id chunk.typ
      | .Error m => .Error m

/-- `Cminortyping.opt_set` -/
def optSet (e : STypenv) (optid : Option Ident) (ty : ATyp) : Res STypenv :=
  match optid with
  | none => .OK e
  | some id => UniSolver.set e id ty

/-- `AST.proj_sig_args` -/
def projSigArgs (sg : Signature) : List ATyp := sg.sig_args.map XType.proj
/-- `AST.proj_sig_res` -/
def projSigRes (sg : Signature) : ATyp := sg.sig_res.proj

/-- `Cminortyping.type_stmt` -/
def typeStmt (tret : XType) (e : STypenv) : Stmt → Res STypenv
  | .Sskip => .OK e
  | .Sassign id a => typeAssign e id a
  | .Sstore chunk a1 a2 =>
      match typeExpr e a1 Tptr with
      | .OK e1 => typeExpr e1 a2 chunk.typ
      | .Error m => .Error m
  | .Scall optid sg fn args =>
      match typeExpr e fn Tptr with
      | .OK e1 =>
          match typeExprlist e1 args (projSigArgs sg) with
          | .OK e2 => optSet e2 optid (projSigRes sg)
          | .Error m => .Error m
      | .Error m => .Error m
  | .Stailcall sg fn args =>
      if sg.sig_res = tret then
        match typeExpr e fn Tptr with
        | .OK e1 => typeExprlist e1 args (projSigArgs sg)
        | .Error m => .Error m
      else .Error "assertion failed"
  | .Sbuiltin optid ef args =>
      let sg := ef.sig
      match typeExprlist e args (projSigArgs sg) with
      | .OK e1 => optSet e1 optid (projSigRes sg)
      | .Error m => .Error m
  | .Sseq s1 s2 =>
      match typeStmt tret e s1 with
      | .OK e1 => typeStmt tret e1 s2
      | .Error m => .Error m
  | .Sifthenelse a s1 s2 =>
      match typeExpr e a .Tint with
      | .OK e1 =>
          match typeStmt tret e1 s1 with
          | .OK e2 => typeStmt tret e2 s2
          | .Error m => .Error m
      | .Error m => .Error m
  | .Sloop s1 => typeStmt tret e s1
  | .Sblock s1 => typeStmt tret e s1
  | .Sexit _ => .OK e
  | .Sswitch sz a _ _ => typeExpr e a (if sz then .Tlong else .Tint)
  | .Sreturn opta =>
      match opta with
      | none => .OK e
      | some a => typeExpr e a tret.proj
  | .Slabel _ s1 => typeStmt tret e s1
  | .Sgoto _ => .OK e

/-- `Cminortyping.typenv` -/
abbrev Typenv := Ident → ATyp

/-- `Cminortyping.type_function` -/
def typeFunction (f : Cminor.Function) : Res Typenv :=
  match UniSolver.setList UniSolver.initial f.fn_params (projSigArgs f.fn_sig) with
  | .OK e1 =>
      match typeStmt f.fn_sig.sig_res e1 f.fn_body with
      | .OK e2 => UniSolver.solve .Tint e2
      | .Error m => .Error m
  | .Error m => .Error m

/-! ## Safe expressions -/

/-- `Cminortyping.known_idents` -/
abbrev KnownIdents := PTree Unit

/-- `Cminortyping.is_known` -/
def isKnown (ki : KnownIdents) (id : Ident) : Bool :=
  match ki.get id with
  | some _ => true
  | none => false

/-- `Cminortyping.known_id` -/
def knownId (f : Cminor.Function) : KnownIdents :=
  let add (ki : KnownIdents) (id : Ident) := ki.set id ()
  f.fn_vars.foldl add (f.fn_params.foldl add PTree.empty)

/-- `Cminortyping.safe_unop` -/
def safeUnop (op : UnaryOperation) : Bool :=
  match op with
  | .Ointoffloat | .Ointuoffloat | .Ofloatofint | .Ofloatofintu => false
  | .Ointofsingle | .Ointuofsingle | .Osingleofint | .Osingleofintu => false
  | .Olongoffloat | .Olonguoffloat | .Ofloatoflong | .Ofloatoflongu => false
  | .Olongofsingle | .Olonguofsingle | .Osingleoflong | .Osingleoflongu => false
  | _ => true

/-- `Cminortyping.safe_binop` -/
def safeBinop (op : BinaryOperation) : Bool :=
  match op with
  | .Odiv | .Odivu | .Omod | .Omodu => false
  | .Odivl | .Odivlu | .Omodl | .Omodlu => false
  | .Ocmpl _ | .Ocmplu _ => false
  | _ => true

/-- `Cminortyping.safe_expr` -/
def safeExpr (ki : KnownIdents) : Cminor.Expr → Bool
  | .Evar v => isKnown ki v
  | .Econst _ => true
  | .Eunop op e1 => safeUnop op && safeExpr ki e1
  | .Ebinop op e1 e2 => safeBinop op && safeExpr ki e1 && safeExpr ki e2
  | .Eload _ _ => false

theorem foldl_set_sound (id : Ident) (x : Unit) :
    ∀ (l : List Ident) (ki : KnownIdents),
      (l.foldl (fun ki id => ki.set id ()) ki).get id = some x → id ∈ l ∨ ki.get id = some x
  | [], _, h => .inr h
  | i :: l, ki, h => by
    rcases foldl_set_sound id x l _ h with h | h
    · exact .inl (List.mem_cons_of_mem _ h)
    · by_cases hi : id = i
      · exact .inl (hi ▸ List.mem_cons_self)
      · exact .inr ((PTree.gso i id () ki (Ne.symm hi)).symm.trans h)

/-- `Cminortyping.known_id_sound_1` -/
theorem knownId_sound_1 (f : Cminor.Function) (id : Ident) (x : Unit)
    (h : (knownId f).get id = some x) : id ∈ f.fn_params ∨ id ∈ f.fn_vars := by
  rcases foldl_set_sound id x _ _ h with h | h
  · exact .inr h
  · rcases foldl_set_sound id x _ _ h with h | h
    · exact .inl h
    · simp [PTree.empty] at h

/-- `Cminortyping.known_id_sound_2` -/
theorem knownId_sound_2 (f : Cminor.Function) (id : Ident) (h : isKnown (knownId f) id = true) :
    id ∈ f.fn_params ∨ id ∈ f.fn_vars := by
  unfold isKnown at h
  split at h
  · next x hx => exact knownId_sound_1 f id x hx
  · cases h

end Cminortyping
end CC
