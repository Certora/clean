/-
  Port of `cparser/Ceval.ml`: evaluation and recognition of compile-time
  constants.

  The local exception `Notconst` becomes `OptionT M` (`failure`).  OCaml's
  `Int64` operations are Lean's `Int64` operations: `/` and `%` truncate
  toward zero as `Int64.div`/`Int64.rem`, `>>>` is the arithmetic shift, and
  the logical shift goes through `UInt64`.
-/
import CCLib.cparser.Cutil

namespace CC
namespace CParser
namespace Ceval

open C Cutil

/-! Extra arith on int64 -/

/-- Unsigned comparison: do signed comparison after shifting range -/
def int64_unsigned_compare (x y : Int64) : Ordering :=
  compare (x + Int64.minValue) (y + Int64.minValue)

def shift_right_logical (n : Int64) (k : Nat) : Int64 :=
  (n.toUInt64 >>> k.toUInt64).toInt64

/-- Unsigned division (Hacker's Delight, section 9.3). -/
def int64_unsigned_div (n d : Int64) : Int64 :=
  if d < 0 then
    if int64_unsigned_compare n d == .lt then 0 else 1
  else
    let q := (shift_right_logical n 1 / d) <<< 1
    let r := n - q * d
    if int64_unsigned_compare r d != .lt then q + 1 else q

def int64_unsigned_mod (n d : Int64) : Int64 :=
  if d < 0 then
    if int64_unsigned_compare n d == .lt then n else n - d
  else
    let q := (shift_right_logical n 1 / d) <<< 1
    let r := n - q * d
    if int64_unsigned_compare r d != .lt then r - d else r

/-- The monad of constant evaluation: `failure` is OCaml's `Notconst`. -/
abbrev EvalM := OptionT M

def notconst {α} : EvalM α := failure

/-- Reduce `n` to the range of representable integers of the given kind -/
def normalize_int (n : Int64) (ik : IKind) : M Int64 := do
  if ik == .IBool then return (if n == 0 then 0 else 1)
  let bitsize := (← sizeof_ikind ik) * 8
  let signed ← is_signed_ikind ik
  if bitsize ≥ 64 then return n
  let a := 64 - bitsize
  let p := n <<< (Int64.ofInt a)
  if signed then return p >>> (Int64.ofInt a)
  else return shift_right_logical p a.toNat

inductive Value where
  | I (n : Int64)
  | S (s : String)
  | WS (l : List Int64) (ik : IKind)
  deriving BEq, Inhabited, Repr

def boolean_value : Value → Bool
  | .I n => n != 0
  | .S _ | .WS .. => true

def constant : Constant → EvalM Value
  | .CInt v ik _ => do return .I (← normalize_int v ik)
  | .CFloat .. => notconst
  | .CStr s => return .S s
  | .CWStr s ik => return .WS s ik
  | .CEnum _ v => return .I v

def is_signed (env : Env.T) (ty : Typ) : M Bool := do
  match ← unroll env ty with
  | .TInt ik _ => is_signed_ikind ik
  | .TEnum .. => is_signed_ikind enum_ikind
  | _ => return false

def int_bit_size (env : Env.T) (ty : Typ) : M Int64 := do
  let byte_size ← match ← unroll env ty with
    | .TInt ik _ => sizeof_ikind ik
    | .TEnum .. => sizeof_ikind enum_ikind
    | _ => pure 0
  return Int64.ofInt (byte_size * 8)

def cast (env : Env.T) (ty_to : Typ) (v : Value) : EvalM Value := do
  match ← (unroll env ty_to : M Typ), v with
  | .TInt .IBool _, _ => return if boolean_value v then .I 1 else .I 0
  | .TInt ik _, .I n => return .I (← normalize_int n ik)
  | .TInt ik _, _ =>
      if (← sizeof_ikind ik) ≥ (← getConfig).sizeof_ptr then return v else notconst
  | .TPtr .., .I n => return .I (← normalize_int n (← ptr_t_ikind))
  | .TArray .., .S _ | .TArray .., .WS .. | .TPtr .., .S _ | .TPtr .., .WS .. => return v
  | .TEnum .., .I n => return .I (← normalize_int n enum_ikind)
  | _, _ => notconst

def unop (env : Env.T) (op : UnaryOperator) (tyres : Typ) (v : Value) : EvalM Value := do
  let res ← match op, tyres, v with
    | .Ominus, .TInt .., .I n => pure (Value.I (-n))
    | .Oplus, .TInt .., .I n => pure (.I n)
    | .Olognot, _, _ => pure (if boolean_value v then .I 0 else .I 1)
    | .Onot, _, .I n => pure (.I (~~~n))
    | _, _, _ => notconst
  cast env tyres res

/-- `tyop` = type at which the comparison is done. -/
def comparison (env : Env.T) (direction : Ordering → Bool) (ptraction : Option Bool)
    (tyop : Typ) (v1 v2 : Value) : EvalM Value := do
  let b ← match v1, v2 with
    | .I n1, .I n2 =>
        if ← is_signed env tyop then pure (direction (compare n1 n2))
        else pure (direction (int64_unsigned_compare n1 n2))
    | .S _, .I 0 | .WS .., .I 0 | .I 0, .S _ | .I 0, .WS .. =>
        match ptraction with
        | none => notconst
        | some b => pure b
    | _, _ => notconst
  return if b then .I 1 else .I 0

/-- `tyop` = type at which the computation is done, `tyres` = expected
    result type. -/
def binop (env : Env.T) (op : BinaryOperator) (tyop tyres ty1 : Typ) (v1 : Value) (ty2 : Typ)
    (v2 : Value) : EvalM Value := do
  let v1 ← cast env tyop v1
  let v2 ← cast env tyop v2
  let ints : EvalM (Int64 × Int64) := match v1, v2 with
    | .I n1, .I n2 => pure (n1, n2)
    | _, _ => notconst
  let res ← match op with
    | .Oadd =>
        if (← is_arith_type env ty1) && (← is_arith_type env ty2) then do
          let (n1, n2) ← ints; pure (Value.I (n1 + n2))
        else notconst
    | .Osub =>
        if (← is_arith_type env ty1) && (← is_arith_type env ty2) then do
          let (n1, n2) ← ints; pure (.I (n1 - n2))
        else notconst
    | .Omul => do let (n1, n2) ← ints; pure (.I (n1 * n2))
    | .Odiv => do
        let (n1, n2) ← ints
        if n2 == 0 then notconst
        if ← is_signed env tyop then pure (.I (n1 / n2))
        else pure (.I (int64_unsigned_div n1 n2))
    | .Omod => do
        let (n1, n2) ← ints
        if n2 == 0 then notconst
        if ← is_signed env tyop then pure (.I (n1 % n2))
        else pure (.I (int64_unsigned_mod n1 n2))
    | .Oand => do let (n1, n2) ← ints; pure (.I (n1 &&& n2))
    | .Oor => do let (n1, n2) ← ints; pure (.I (n1 ||| n2))
    | .Oxor => do let (n1, n2) ← ints; pure (.I (n1 ^^^ n2))
    | .Oshl => do
        let (n1, n2) ← ints
        if n2 ≥ 0 && n2 < (← int_bit_size env tyop) then pure (.I (n1 <<< n2))
        else notconst
    | .Oshr => do
        let (n1, n2) ← ints
        if n2 ≥ 0 && n2 < (← int_bit_size env tyop) then
          if ← is_signed env tyop then pure (.I (n1 >>> n2))
          else pure (.I (shift_right_logical n1 n2.toInt.toNat))
        else notconst
    | .Oeq => comparison env (· == .eq) (some false) tyop v1 v2
    | .One => comparison env (· != .eq) (some true) tyop v1 v2
    | .Olt => comparison env (· == .lt) none tyop v1 v2
    | .Ogt => comparison env (· == .gt) none tyop v1 v2
    | .Ole => comparison env (· != .gt) none tyop v1 v2
    | .Oge => comparison env (· != .lt) none tyop v1 v2
    | .Ologand =>
        pure (if boolean_value v1 then (if boolean_value v2 then .I 1 else .I 0) else .I 0)
    | .Ologor =>
        pure (if boolean_value v1 then .I 1 else if boolean_value v2 then .I 1 else .I 0)
    | _ => notconst
  -- force normalization of result
  cast env tyres res

partial def expr (env : Env.T) (e : Exp) : EvalM Value := do
  match e.edesc with
  | .EConst c => constant c
  | .ESizeof ty =>
      match ← OptionT.lift (sizeof env ty) with
      | none => notconst
      | some n => return .I (Int64.ofInt n)
  | .EAlignof ty =>
      match ← OptionT.lift (alignof env ty) with
      | none => notconst
      | some n => return .I (Int64.ofInt n)
  | .EVar _ => notconst
  | .EUnop op e1 => unop env op e.etyp (← expr env e1)
  | .EBinop op e1 e2 ty =>
      binop env op ty e.etyp e1.etyp (← expr env e1) e2.etyp (← expr env e2)
  | .EConditional e1 e2 e3 =>
      if boolean_value (← expr env e1) then cast env e.etyp (← expr env e2)
      else cast env e.etyp (← expr env e3)
  | .ECast ty e1 => cast env ty (← expr env e1)
  | .ECompound .. => notconst
  | .ECall .. => notconst

def integer_expr (env : Env.T) (e : Exp) : M (Option Int64) := do
  match ← (do cast env (.TInt .ILongLong []) (← expr env e) : EvalM Value).run with
  | some (.I n) => return some n
  | _ => return none

def constant_expr (env : Env.T) (ty : Typ) (e : Exp) : M (Option Constant) := do
  let r ← (do
    let t ← (unroll env ty : M Typ)
    let v ← cast env ty (← expr env e)
    match t, v with
    | .TInt ik _, .I n => return some (Constant.CInt n ik "")
    | .TPtr .., .I n => return some (.CInt n (← ptr_t_ikind) "")
    | .TArray .., .S s | .TPtr .., .S s => return some (.CStr s)
    | .TArray .., .WS s ik | .TPtr .., .WS s ik => return some (.CWStr s ik)
    | .TEnum .., .I n => return some (.CInt n enum_ikind "")
    | _, _ => return none : EvalM (Option Constant)).run
  return r.join

/-! Recognition of constant initializers and constant expressions (ISO C99
    section 6.6).  Just a check: no evaluation is done. -/

private def findIdentOpt (env : Env.T) (id : Ident) : M (Option Env.IdentInfo) :=
  tryCatch (do return some (← Env.find_ident env id)) fun
    | .EnvError _ => pure none
    | e => throw e

mutual
partial def is_constant_init (env : Env.T) : Init → M Bool
  | .Init_single e => is_constant_expr env e
  | .Init_array il => il.allM (is_constant_init env)
  | .Init_struct _ fil => fil.allM fun (_, i) => is_constant_init env i
  | .Init_union _ _ i => is_constant_init env i

partial def is_constant_expr (env : Env.T) (e : Exp) : M Bool := do
  match e.edesc with
  | .EConst _ | .ESizeof _ | .EAlignof _ => return true
  | .EVar id =>
      match ← findIdentOpt env id with
      | some (.II_ident ..) => is_constant_rval_of_lval env e
      | some (.II_enum _) => return true
      | none => return false
  | .EUnop op e1 =>
      match op with
      | .Ominus | .Oplus | .Olognot | .Onot => is_constant_expr env e1
      | .Oderef | .Odot _ | .Oarrow _ => is_constant_rval_of_lval env e
      | .Oaddrof => is_constant_lval env e1
      | .Opreincr | .Opredecr | .Opostincr | .Opostdecr => return false
  | .EBinop op e1 e2 _ =>
      match op with
      | .Oadd | .Osub | .Omul | .Odiv | .Omod | .Oand | .Oor | .Oxor | .Oshl | .Oshr
      | .Oeq | .One | .Olt | .Ogt | .Ole | .Oge | .Ologand | .Ologor =>
          return (← is_constant_expr env e1) && (← is_constant_expr env e2)
      | .Oindex => is_constant_rval_of_lval env e
      | .Oassign | .Oadd_assign | .Osub_assign | .Omul_assign | .Odiv_assign
      | .Omod_assign | .Oand_assign | .Oor_assign | .Oxor_assign | .Oshl_assign
      | .Oshr_assign => return false
      | .Ocomma => return false
  | .EConditional e1 e2 e3 =>
      return (← is_constant_expr env e1) && (← is_constant_expr env e2)
        && (← is_constant_expr env e3)
  | .ECast _ e1 => is_constant_expr env e1
  | .ECompound _ i => is_constant_init env i
  | .ECall .. => return false

partial def is_constant_rval_of_lval (env : Env.T) (e : Exp) : M Bool := do
  match ← unroll env e.etyp with
  | .TArray .. | .TFun .. => is_constant_lval env e
  | _ => return false

partial def is_constant_lval (env : Env.T) (e : Exp) : M Bool := do
  match e.edesc with
  | .EConst (.CStr _) | .EConst (.CWStr ..) => return true
  | .EVar id =>
      match ← findIdentOpt env id with
      | some (.II_ident sto _) =>
          match sto with
          | .Storage_default | .Storage_extern | .Storage_static => return true
          | .Storage_auto | .Storage_register => return false
      | some (.II_enum _) => return false
      | none => return false
  | .EUnop .Oderef e1 => is_constant_expr env e1
  | .EUnop (.Odot _) e1 => is_constant_lval env e1
  | .EUnop (.Oarrow _) e1 => is_constant_expr env e1
  | .EBinop .Oindex e1 e2 _ => return (← is_constant_expr env e1) && (← is_constant_expr env e2)
  | .ECompound _ i => is_constant_init env i
  | _ => return false
end

end Ceval
end CParser
end CC
