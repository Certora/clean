/-
  Translation from CompCert C to Clight — port of `cfrontend/SimplExpr.v`
  (the whole file).

  This is the first pass of CompCert's compiler.  Side effects (assignments,
  calls, `++`/`--`, `&&`/`||`/`?:`) are pulled out of CompCert C expressions:
  every expression `a` becomes a list of Clight statements `sl` that perform
  its effects, followed by a pure Clight expression that computes its value.
  Fresh temporaries are drawn from a state monad (`Mon`), whose result type
  records, as in Rocq, that the generator only moves forward.

  Differences from Rocq:
  * Rocq's `Parameter first_unused_ident : unit -> ident` (implemented in
    OCaml) is an explicit argument `firstUnused` of `translFunction`,
    `translFundef` and `translProgram`.  Nothing in the correctness argument
    depends on its value.
  * Error messages are plain strings (the port's `Res`), so
    `MSG … :: CTX id :: nil` messages lose the identifier.
  * The monad is a `Monad` instance, so the translation uses Lean's
    `do`-notation; `Mon.bind_eq`/`Mon.pure_eq` turn it back into `Mon.bind`
    and `Mon.ret`.
  * Clight programs in the port do not store `prog_comp_env_eq`; the
    translated program keeps the composite definitions and environment of
    the source.
-/
import CCLib.cfrontend.Csyntax

namespace CC
namespace SimplExpr

/-! ## State and error monad for generating fresh identifiers -/

/-- `SimplExpr.generator` -/
structure Generator where
  gen_next : Ident
  gen_trail : List (Ident × Ty)

/-- `SimplExpr.result`: either an error, or a value together with the new
    generator, which is never behind the old one. -/
inductive Result (A : Type) (g : Generator) where
  | Err (msg : String)
  | Res (a : A) (g' : Generator) (h : g.gen_next ≤ g'.gen_next)

/-- `SimplExpr.mon` -/
def Mon (A : Type) : Type := (g : Generator) → Result A g

namespace Mon

theorem ple_refl (p : Positive) : p ≤ p := Nat.le_refl p.toNat

theorem ple_trans {p q r : Positive} (h1 : p ≤ q) (h2 : q ≤ r) : p ≤ r :=
  Nat.le_trans h1 h2

theorem ple_succ (p : Positive) : p ≤ p.succ := by
  show p.toNat ≤ p.succ.toNat
  rw [Positive.toNat_succ]; exact Nat.le_succ _

/-- `SimplExpr.ret` -/
def ret {A : Type} (x : A) : Mon A := fun g => .Res x g (ple_refl _)

/-- `SimplExpr.error` -/
def error {A : Type} (msg : String) : Mon A := fun _ => .Err msg

/-- `SimplExpr.bind` -/
def bind {A B : Type} (x : Mon A) (f : A → Mon B) : Mon B := fun g =>
  match x g with
  | .Err msg => .Err msg
  | .Res a g' i =>
    match f a g' with
    | .Err msg => .Err msg
    | .Res b g'' i' => .Res b g'' (ple_trans i i')

/-- `SimplExpr.bind2` -/
def bind2 {A B C : Type} (x : Mon (A × B)) (f : A → B → Mon C) : Mon C :=
  bind x (fun p => f p.1 p.2)

instance : Monad Mon where
  pure := ret
  bind := bind

@[simp] theorem bind_eq {A B : Type} (x : Mon A) (f : A → Mon B) :
    (x >>= f) = bind x f := rfl

@[simp] theorem pure_eq {A : Type} (x : A) : (pure x : Mon A) = ret x := rfl

end Mon

open Mon (ret error)

/-- `SimplExpr.initial_generator` -/
def initialGenerator (firstUnused : Ident) : Generator := ⟨firstUnused, []⟩

/-- `SimplExpr.gensym`: a fresh temporary of type `ty`. -/
def gensym (ty : Ty) : Mon Ident := fun g =>
  .Res g.gen_next ⟨g.gen_next.succ, (g.gen_next, ty) :: g.gen_trail⟩ (Mon.ple_succ _)

/-! ## Sequences -/

/-- `SimplExpr.makeseq_rec` -/
def makeseqRec (s : Stmt) : List Stmt → Stmt
  | [] => s
  | s' :: l' => makeseqRec (.Ssequence s s') l'

/-- `SimplExpr.makeseq`: sequence nested to the left, starting with `Sskip`. -/
def makeseq (l : List Stmt) : Stmt := makeseqRec .Sskip l

section SIMPL_EXPR

variable (ce : CompositeEnv)

/-! ## Smart constructors -/

/-- `SimplExpr.eval_simpl_expr`: compile-time evaluation of constants and
    casts of constants. -/
def evalSimplExpr : Expr → Option Val
  | .Econst_int n _ => some (.Vint n)
  | .Econst_float n _ => some (.Vfloat n)
  | .Econst_single n _ => some (.Vsingle n)
  | .Econst_long n _ => some (.Vlong n)
  | .Ecast b ty =>
    match evalSimplExpr b with
    | none => none
    | some v => Cop.semCast v (typeof b) ty Mem.empty
  | _ => none

/-- `SimplExpr.makeif`: `if a then s1 else s2`, simplified when `a` is a
    compile-time constant. -/
def makeif (a : Expr) (s1 s2 : Stmt) : Stmt :=
  match evalSimplExpr a with
  | some v =>
    match Cop.boolVal v (typeof a) Mem.empty with
    | some b => if b then s1 else s2
    | none => .Sifthenelse a s1 s2
  | none => .Sifthenelse a s1 s2

/-- `SimplExpr.Ederef'`: `*&a` becomes `a`. -/
def Ederef' (a : Expr) (t : Ty) : Expr :=
  match a with
  | .Eaddrof a' _ => if t = typeof a' then a' else .Ederef a t
  | _ => .Ederef a t

/-- `SimplExpr.Eaddrof'`: `&*a` becomes `a`. -/
def Eaddrof' (a : Expr) (t : Ty) : Expr :=
  match a with
  | .Ederef a' _ => if t = typeof a' then a' else .Eaddrof a t
  | _ => .Eaddrof a t

/-- `SimplExpr.transl_incrdecr` -/
def translIncrdecr (id : Cop.IncrOrDecr) (a : Expr) (ty : Ty) : Expr :=
  match id with
  | .Incr => .Ebinop .Oadd a (.Econst_int Integers.Int.one type_int32s) (Cop.incrdecrType ty)
  | .Decr => .Ebinop .Osub a (.Econst_int Integers.Int.one type_int32s) (Cop.incrdecrType ty)

/-- `SimplExpr.is_bitfield_access_aux` -/
def isBitfieldAccessAux (fn : CompositeEnv → Ident → List Member → Res (Z × Bitfield))
    (id fld : Ident) : Mon Bitfield :=
  match ce.get id with
  | none => error "unknown composite"
  | some co =>
    match fn ce fld co.co_members with
    | .OK (_, bf) => ret bf
    | .Error _ => error "unknown field"

/-- `SimplExpr.is_bitfield_access`: does the simple l-value `l` designate a
    bitfield? -/
def isBitfieldAccess (l : Expr) : Mon Bitfield :=
  match l with
  | .Efield r f _ =>
    match typeof r with
    | .Tstruct id _ => isBitfieldAccessAux ce fieldOffset id f
    | .Tunion id _ => isBitfieldAccessAux ce unionFieldOffset id f
    | _ => error "is_bitfield_access"
  | _ => ret .Full

end SIMPL_EXPR

/-- `SimplExpr.chunk_for_volatile_type`: `some chunk` if an access to an
    l-value of type `ty` (with bitfield info `bf`) produces a volatile event. -/
def chunkForVolatileType (ty : Ty) (bf : Bitfield) : Option Chunk :=
  if typeIsVolatile ty then
    match accessMode ty with
    | .By_value chunk =>
      match bf with
      | .Full => some chunk
      | .Bits _ _ _ _ => none
    | _ => none
  else none

/-- `SimplExpr.make_set`: read l-value `l` into temporary `id`. -/
def makeSet (bf : Bitfield) (id : Ident) (l : Expr) : Stmt :=
  match chunkForVolatileType (typeof l) bf with
  | none => .Sset id l
  | some chunk =>
    let typtr := Ty.Tpointer (typeof l) noattr
    .Sbuiltin (some id) (.EF_vload chunk) [typtr] [.Eaddrof l typtr]

/-- `SimplExpr.transl_valof`: a volatile read goes through a temporary. -/
def translValof (ce : CompositeEnv) (ty : Ty) (l : Expr) : Mon (List Stmt × Expr) :=
  if typeIsVolatile ty then do
    let t ← gensym ty
    let bf ← isBitfieldAccess ce l
    ret ([makeSet bf t l], .Etempvar t ty)
  else ret ([], l)

/-- `SimplExpr.make_assign` -/
def makeAssign (bf : Bitfield) (l r : Expr) : Stmt :=
  match chunkForVolatileType (typeof l) bf with
  | none => .Sassign l r
  | some chunk =>
    let ty := typeof l
    let typtr := Ty.Tpointer ty noattr
    .Sbuiltin none (.EF_vstore chunk) [typtr, ty] [.Eaddrof l typtr, r]

/-- `Coqlib.two_p` -/
def twoP (x : Z) : Z := if 0 ≤ x then (2 : Z) ^ x.toNat else 0

/-- `SimplExpr.make_normalize`: normalize `r` to the width and signedness of
    a bitfield. -/
def makeNormalize (sz : IntSize) (sg : Signedness) (width : Z) (r : Expr) : Expr :=
  let intconst (n : Z) := Expr.Econst_int (Integers.Int.repr n) type_int32s
  if sz = .IBool ∨ sg = .Unsigned then
    let mask := twoP width - 1
    .Ebinop .Oand r (intconst mask) (typeof r)
  else
    let amount := Integers.Int.zwordsize - width
    .Ebinop .Oshr (.Ebinop .Oshl r (intconst amount) type_int32s) (intconst amount) (typeof r)

/-- `SimplExpr.make_assign_value` -/
def makeAssignValue (bf : Bitfield) (r : Expr) : Expr :=
  match bf with
  | .Full => r
  | .Bits sz sg _ width => makeNormalize sz sg width r

/-! ## Destinations -/

/-- `SimplExpr.set_destination`: a nonempty list of
    (destination type, source type, temporary) triples. -/
inductive SetDestination where
  | SDbase (tycast ty : Ty) (tmp : Ident)
  | SDcons (tycast ty : Ty) (tmp : Ident) (sd : SetDestination)

/-- `SimplExpr.destination` -/
inductive Destination where
  | For_val
  | For_effects
  | For_set (sd : SetDestination)

/-- `SimplExpr.dummy_expr` -/
def dummyExpr : Expr := .Econst_int Integers.Int.zero type_int32s

/-- `SimplExpr.do_set` -/
def doSet : SetDestination → Expr → List Stmt
  | .SDbase tycast _ tmp, a => [.Sset tmp (.Ecast a tycast)]
  | .SDcons tycast ty tmp sd', a => .Sset tmp (.Ecast a tycast) :: doSet sd' (.Etempvar tmp ty)

/-- `SimplExpr.finish` -/
def finish (dst : Destination) (sl : List Stmt) (a : Expr) : List Stmt × Expr :=
  match dst with
  | .For_val => (sl, a)
  | .For_effects => (sl, a)
  | .For_set sd => (sl ++ doSet sd a, a)

/-- `SimplExpr.sd_temp` -/
def sdTemp : SetDestination → Ident
  | .SDbase _ _ tmp => tmp
  | .SDcons _ _ tmp _ => tmp

/-- `SimplExpr.sd_head_type` -/
def sdHeadType : SetDestination → Ty
  | .SDbase _ ty _ => ty
  | .SDcons _ ty _ _ => ty

/-- `SimplExpr.temp_for_sd`: reuse the head temporary when the types agree. -/
def tempForSd (ty : Ty) (sd : SetDestination) : Mon Ident :=
  if ty = sdHeadType sd then ret (sdTemp sd) else gensym ty

/-! ## Translation of expressions -/

section TRANSL

variable (ce : CompositeEnv)

open Destination in
mutual
/-- `SimplExpr.transl_expr`: returns `(sl, a)` where `sl` performs the side
    effects of the CompCert C expression and the pure Clight expression `a`
    computes its value (for `For_val`), or `sl` also stores the value into
    the temporaries of the destination (for `For_set`). -/
def translExpr (dst : Destination) : Csyntax.Expr → Mon (List Stmt × Expr)
  | .Eloc _ _ _ _ => error "SimplExpr.transl_expr: Eloc"
  | .Evar x ty => ret (finish dst [] (.Evar x ty))
  | .Ederef r ty => do
    let (sl, a) ← translExpr For_val r
    ret (finish dst sl (Ederef' a ty))
  | .Efield r f ty => do
    let (sl, a) ← translExpr For_val r
    ret (finish dst sl (.Efield a f ty))
  | .Eval (.Vint n) ty => ret (finish dst [] (.Econst_int n ty))
  | .Eval (.Vfloat n) ty => ret (finish dst [] (.Econst_float n ty))
  | .Eval (.Vsingle n) ty => ret (finish dst [] (.Econst_single n ty))
  | .Eval (.Vlong n) ty => ret (finish dst [] (.Econst_long n ty))
  | .Eval _ _ => error "SimplExpr.transl_expr: Eval"
  | .Esizeof ty' ty => ret (finish dst [] (.Esizeof ty' ty))
  | .Ealignof ty' ty => ret (finish dst [] (.Ealignof ty' ty))
  | .Evalof l _ => do
    let (sl1, a1) ← translExpr For_val l
    let (sl2, a2) ← translValof ce (Csyntax.typeof l) a1
    ret (finish dst (sl1 ++ sl2) a2)
  | .Eaddrof l ty => do
    let (sl, a) ← translExpr For_val l
    ret (finish dst sl (Eaddrof' a ty))
  | .Eunop op r1 ty => do
    let (sl1, a1) ← translExpr For_val r1
    ret (finish dst sl1 (.Eunop op a1 ty))
  | .Ebinop op r1 r2 ty => do
    let (sl1, a1) ← translExpr For_val r1
    let (sl2, a2) ← translExpr For_val r2
    ret (finish dst (sl1 ++ sl2) (.Ebinop op a1 a2 ty))
  | .Ecast r1 ty =>
    match dst with
    | For_val | For_set _ => do
      let (sl1, a1) ← translExpr For_val r1
      ret (finish dst sl1 (.Ecast a1 ty))
    | For_effects => translExpr For_effects r1
  | .Eseqand r1 r2 ty => do
    let (sl1, a1) ← translExpr For_val r1
    match dst with
    | For_val => do
      let t ← gensym ty
      let sd := SetDestination.SDbase type_bool ty t
      let (sl2, _) ← translExpr (For_set sd) r2
      ret (sl1 ++ [makeif a1 (makeseq sl2) (.Sset t (.Econst_int Integers.Int.zero ty))],
           .Etempvar t ty)
    | For_effects => do
      let (sl2, _) ← translExpr For_effects r2
      ret (sl1 ++ [makeif a1 (makeseq sl2) .Sskip], dummyExpr)
    | For_set sd => do
      let t ← tempForSd ty sd
      let sd' := SetDestination.SDcons type_bool ty t sd
      let (sl2, _) ← translExpr (For_set sd') r2
      ret (sl1 ++ [makeif a1 (makeseq sl2)
                    (makeseq (doSet sd (.Econst_int Integers.Int.zero ty)))],
           dummyExpr)
  | .Eseqor r1 r2 ty => do
    let (sl1, a1) ← translExpr For_val r1
    match dst with
    | For_val => do
      let t ← gensym ty
      let sd := SetDestination.SDbase type_bool ty t
      let (sl2, _) ← translExpr (For_set sd) r2
      ret (sl1 ++ [makeif a1 (.Sset t (.Econst_int Integers.Int.one ty)) (makeseq sl2)],
           .Etempvar t ty)
    | For_effects => do
      let (sl2, _) ← translExpr For_effects r2
      ret (sl1 ++ [makeif a1 .Sskip (makeseq sl2)], dummyExpr)
    | For_set sd => do
      let t ← tempForSd ty sd
      let sd' := SetDestination.SDcons type_bool ty t sd
      let (sl2, _) ← translExpr (For_set sd') r2
      ret (sl1 ++ [makeif a1 (makeseq (doSet sd (.Econst_int Integers.Int.one ty)))
                    (makeseq sl2)],
           dummyExpr)
  | .Econdition r1 r2 r3 ty => do
    let (sl1, a1) ← translExpr For_val r1
    match dst with
    | For_val => do
      let t ← gensym ty
      let sd := SetDestination.SDbase ty ty t
      let (sl2, _) ← translExpr (For_set sd) r2
      let (sl3, _) ← translExpr (For_set sd) r3
      ret (sl1 ++ [makeif a1 (makeseq sl2) (makeseq sl3)], .Etempvar t ty)
    | For_effects => do
      let (sl2, _) ← translExpr For_effects r2
      let (sl3, _) ← translExpr For_effects r3
      ret (sl1 ++ [makeif a1 (makeseq sl2) (makeseq sl3)], dummyExpr)
    | For_set sd => do
      let t ← tempForSd ty sd
      let sd' := SetDestination.SDcons ty ty t sd
      let (sl2, _) ← translExpr (For_set sd') r2
      let (sl3, _) ← translExpr (For_set sd') r3
      ret (sl1 ++ [makeif a1 (makeseq sl2) (makeseq sl3)], dummyExpr)
  | .Eassign l1 r2 _ => do
    let (sl1, a1) ← translExpr For_val l1
    let (sl2, a2) ← translExpr For_val r2
    let bf ← isBitfieldAccess ce a1
    let ty1 := Csyntax.typeof l1
    match dst with
    | For_val | For_set _ => do
      let t ← gensym ty1
      ret (finish dst
            (sl1 ++ sl2 ++ [.Sset t (.Ecast a2 ty1), makeAssign bf a1 (.Etempvar t ty1)])
            (makeAssignValue bf (.Etempvar t ty1)))
    | For_effects =>
      ret (sl1 ++ sl2 ++ [makeAssign bf a1 a2], dummyExpr)
  | .Eassignop op l1 r2 tyres _ => do
    let ty1 := Csyntax.typeof l1
    let (sl1, a1) ← translExpr For_val l1
    let (sl2, a2) ← translExpr For_val r2
    let (sl3, a3) ← translValof ce ty1 a1
    let bf ← isBitfieldAccess ce a1
    match dst with
    | For_val | For_set _ => do
      let t ← gensym ty1
      ret (finish dst
            (sl1 ++ sl2 ++ sl3 ++
              [.Sset t (.Ecast (.Ebinop op a3 a2 tyres) ty1),
               makeAssign bf a1 (.Etempvar t ty1)])
            (makeAssignValue bf (.Etempvar t ty1)))
    | For_effects =>
      ret (sl1 ++ sl2 ++ sl3 ++ [makeAssign bf a1 (.Ebinop op a3 a2 tyres)], dummyExpr)
  | .Epostincr id l1 _ => do
    let ty1 := Csyntax.typeof l1
    let (sl1, a1) ← translExpr For_val l1
    let bf ← isBitfieldAccess ce a1
    match dst with
    | For_val | For_set _ => do
      let t ← gensym ty1
      ret (finish dst
            (sl1 ++ [makeSet bf t a1,
                     makeAssign bf a1 (translIncrdecr id (.Etempvar t ty1) ty1)])
            (.Etempvar t ty1))
    | For_effects => do
      let (sl2, a2) ← translValof ce ty1 a1
      ret (sl1 ++ sl2 ++ [makeAssign bf a1 (translIncrdecr id a2 ty1)], dummyExpr)
  | .Ecomma r1 r2 _ => do
    let (sl1, _) ← translExpr For_effects r1
    let (sl2, a2) ← translExpr dst r2
    ret (sl1 ++ sl2, a2)
  | .Ecall r1 rl2 ty => do
    let (sl1, a1) ← translExpr For_val r1
    let (sl2, al2) ← translExprlist rl2
    match dst with
    | For_val | For_set _ => do
      let t ← gensym ty
      ret (finish dst (sl1 ++ sl2 ++ [.Scall (some t) a1 al2]) (.Etempvar t ty))
    | For_effects =>
      ret (sl1 ++ sl2 ++ [.Scall none a1 al2], dummyExpr)
  | .Ebuiltin ef tyargs rl ty => do
    let (sl, al) ← translExprlist rl
    match dst with
    | For_val | For_set _ => do
      let t ← gensym ty
      ret (finish dst (sl ++ [.Sbuiltin (some t) ef tyargs al]) (.Etempvar t ty))
    | For_effects =>
      ret (sl ++ [.Sbuiltin none ef tyargs al], dummyExpr)
  | .Eparen _ _ _ => error "SimplExpr.transl_expr: paren"

/-- `SimplExpr.transl_exprlist` -/
def translExprlist : Csyntax.ExprList → Mon (List Stmt × List Expr)
  | .Enil => ret ([], [])
  | .Econs r1 rl2 => do
    let (sl1, a1) ← translExpr For_val r1
    let (sl2, al2) ← translExprlist rl2
    ret (sl1 ++ sl2, a1 :: al2)
end

/-- `SimplExpr.transl_expression` -/
def translExpression (r : Csyntax.Expr) : Mon (Stmt × Expr) := do
  let (sl, a) ← translExpr ce .For_val r
  ret (makeseq sl, a)

/-- `SimplExpr.transl_expr_stmt` -/
def translExprStmt (r : Csyntax.Expr) : Mon Stmt := do
  let (sl, _) ← translExpr ce .For_effects r
  ret (makeseq sl)

/-- `SimplExpr.transl_if` -/
def translIf (r : Csyntax.Expr) (s1 s2 : Stmt) : Mon Stmt := do
  let (sl, a) ← translExpr ce .For_val r
  ret (makeseq (sl ++ [makeif a s1 s2]))

/-! ## Translation of statements -/

/-- `SimplExpr.expr_true` -/
def exprTrue : Expr := .Econst_int Integers.Int.one type_int32s

/-- `SimplExpr.is_Sskip` (as a Boolean test) -/
def isSskip : Csyntax.Stmt → Bool
  | .Sskip => true
  | _ => false

mutual
/-- `SimplExpr.transl_stmt` -/
def translStmt : Csyntax.Stmt → Mon Stmt
  | .Sskip => ret .Sskip
  | .Sdo e => translExprStmt ce e
  | .Ssequence s1 s2 => do
    let ts1 ← translStmt s1
    let ts2 ← translStmt s2
    ret (.Ssequence ts1 ts2)
  | .Sifthenelse e s1 s2 => do
    let ts1 ← translStmt s1
    let ts2 ← translStmt s2
    let (s', a) ← translExpression ce e
    if isSskip s1 && isSskip s2 then ret (.Ssequence s' .Sskip)
    else ret (.Ssequence s' (.Sifthenelse a ts1 ts2))
  | .Swhile e s1 => do
    let s' ← translIf ce e .Sskip .Sbreak
    let ts1 ← translStmt s1
    ret (.Sloop (.Ssequence s' ts1) .Sskip)
  | .Sdowhile e s1 => do
    let s' ← translIf ce e .Sskip .Sbreak
    let ts1 ← translStmt s1
    ret (.Sloop ts1 s')
  | .Sfor s1 e2 s3 s4 => do
    let ts1 ← translStmt s1
    let s' ← translIf ce e2 .Sskip .Sbreak
    let ts3 ← translStmt s3
    let ts4 ← translStmt s4
    if isSskip s1 then ret (.Sloop (.Ssequence s' ts4) ts3)
    else ret (.Ssequence ts1 (.Sloop (.Ssequence s' ts4) ts3))
  | .Sbreak => ret .Sbreak
  | .Scontinue => ret .Scontinue
  | .Sreturn none => ret (.Sreturn none)
  | .Sreturn (some e) => do
    let (s', a) ← translExpression ce e
    ret (.Ssequence s' (.Sreturn (some a)))
  | .Sswitch e ls => do
    let (s', a) ← translExpression ce e
    let tls ← translLblstmt ls
    ret (.Ssequence s' (.Sswitch a tls))
  | .Slabel lbl s1 => do
    let ts1 ← translStmt s1
    ret (.Slabel lbl ts1)
  | .Sgoto lbl => ret (.Sgoto lbl)

/-- `SimplExpr.transl_lblstmt` -/
def translLblstmt : Csyntax.LStmts → Mon LStmts
  | .LSnil => ret .LSnil
  | .LScons c s ls1 => do
    let ts ← translStmt s
    let tls1 ← translLblstmt ls1
    ret (.LScons c ts tls1)
end

/-! ## Functions and programs -/

/-- `SimplExpr.transl_function`: the generated temporaries become the
    function's `fn_temps`. -/
def translFunction (firstUnused : Ident) (f : Csyntax.Function) : Res Function :=
  match translStmt ce f.fn_body (initialGenerator firstUnused) with
  | .Err msg => .Error msg
  | .Res tbody g _ =>
    .OK { fn_return := f.fn_return, fn_callconv := f.fn_callconv,
          fn_params := f.fn_params, fn_vars := f.fn_vars,
          fn_temps := g.gen_trail, fn_body := tbody }

/-- `SimplExpr.transl_fundef` -/
def translFundef (firstUnused : Ident) (fd : Csyntax.FunDef) : Res FunDef :=
  match fd with
  | .Internal f =>
    match translFunction ce firstUnused f with
    | .OK tf => .OK (.Internal tf)
    | .Error msg => .Error msg
  | .External ef targs tres cc => .OK (.External ef targs tres cc)

end TRANSL

/-- `SimplExpr.transl_program` -/
def translProgram (firstUnused : Ident) (p : Csyntax.Program) : Res Program :=
  match transformPartialProgram (translFundef p.prog_comp_env firstUnused) p.toAST with
  | .Error msg => .Error msg
  | .OK p1 =>
    .OK { prog_defs := p1.prog_defs, prog_public := p1.prog_public,
          prog_main := p1.prog_main, prog_types := p.prog_types,
          prog_comp_env := p.prog_comp_env }

end SimplExpr
end CC
