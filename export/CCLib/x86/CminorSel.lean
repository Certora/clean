/-
  CminorSel for the x86 back end: Cminor after instruction selection —
  port of `backend/CminorSel.v` (syntax, semantics, lifting of let-bound
  variables, `app_exprlist`, `bind_exprs`, and their evaluation lemmas),
  instantiated with the x86 operators (`CCLib/x86/Op.lean`).

  In this port `CCLib/backend/CminorSel.lean` is the aarch64 instance; this
  file is the same development for x86, in namespace `CC.X86.CminorSel`.
  It is the target language of the x86 instruction selection
  (`CCLib/x86/SelectOp.lean`).

  Differences from Rocq: `is_call_cont` is a `Bool`; the minimality scheme
  `eval_expr_ind3` is Lean's mutual structural induction on the three
  evaluation relations; `bind_exprs_rec` (a `Function` by measure in Rocq) is
  defined by well-founded recursion on `lengthExprlist`.
-/
import CCLib.x86.Op
import CCLib.backend.CminorSem
import CCLib.common.LinkingTheory

namespace CC
namespace X86
namespace CminorSel

open Op Smallstep

mutual
/-- `CminorSel.expr` -/
inductive Expr where
  | Evar (id : Ident)
  | Eop (op : Operation) (al : Exprlist)
  | Eload (chunk : Chunk) (addr : Addressing) (al : Exprlist)
  | Econdition (c : Condexpr) (a b : Expr)
  | Elet (a b : Expr)
  | Eletvar (n : Nat)
  | Ebuiltin (ef : ExtFun) (al : Exprlist)
  | Eexternal (id : Ident) (sg : Signature) (al : Exprlist)

/-- `CminorSel.exprlist` -/
inductive Exprlist where
  | Enil
  | Econs (a : Expr) (al : Exprlist)

/-- `CminorSel.condexpr` -/
inductive Condexpr where
  | CEcond (c : Condition) (al : Exprlist)
  | CEcondition (a b c : Condexpr)
  | CElet (a : Expr) (b : Condexpr)
end

/-- `CminorSel.exitexpr` -/
inductive Exitexpr where
  | XEexit (n : Nat)
  | XEjumptable (a : Expr) (tbl : List Nat)
  | XEcondition (c : Condexpr) (a b : Exitexpr)
  | XElet (a : Expr) (b : Exitexpr)

/-- `CminorSel.stmt` -/
inductive Stmt where
  | Sskip
  | Sassign (id : Ident) (a : Expr)
  | Sstore (chunk : Chunk) (addr : Addressing) (al : Exprlist) (b : Expr)
  | Scall (optid : Option Ident) (sg : Signature) (fn : Sum Expr Ident) (args : Exprlist)
  | Stailcall (sg : Signature) (fn : Sum Expr Ident) (args : Exprlist)
  | Sbuiltin (res : BuiltinRes Ident) (ef : ExtFun) (args : List (BuiltinArg Expr))
  | Sseq (s1 s2 : Stmt)
  | Sifthenelse (c : Condexpr) (s1 s2 : Stmt)
  | Sloop (s : Stmt)
  | Sblock (s : Stmt)
  | Sexit (n : Nat)
  | Sswitch (a : Exitexpr)
  | Sreturn (a : Option Expr)
  | Slabel (lbl : Cminor.Label) (s : Stmt)
  | Sgoto (lbl : Cminor.Label)

/-- `CminorSel.function` -/
structure Function where
  fn_sig : Signature
  fn_params : List Ident
  fn_vars : List Ident
  fn_stackspace : Z
  fn_body : Stmt

/-- `CminorSel.fundef` -/
abbrev Fundef := ASTFundef Function
/-- `CminorSel.program` -/
abbrev Program := ASTProgram Fundef Unit

/-- `CminorSel.funsig` -/
def funsig : Fundef → Signature
  | .Internal f => f.fn_sig
  | .External ef => ef.sig

/-- `CminorSel.genv` -/
abbrev CGenv := Genv Fundef Unit
/-- `CminorSel.letenv` -/
abbrev Letenv := List Val

/-- `CminorSel.cont` -/
inductive Cont where
  | Kstop
  | Kseq (s : Stmt) (k : Cont)
  | Kblock (k : Cont)
  | Kcall (optid : Option Ident) (f : Function) (sp : Val) (e : Cminor.Env) (k : Cont)

/-- `CminorSel.state` -/
inductive State where
  | State (f : Function) (s : Stmt) (k : Cont) (sp : Val) (e : Cminor.Env) (m : Mem)
  | Callstate (f : Fundef) (args : List Val) (k : Cont) (m : Mem)
  | Returnstate (v : Val) (k : Cont) (m : Mem)

/-- `Coqlib.list_nth_z` -/
def listNthZ {A : Type} : List A → Z → Option A
  | [], _ => none
  | hd :: tl, n => if n = 0 then some hd else listNthZ tl (n - 1)

theorem listNthZ_mem {A : Type} : ∀ {l : List A} {n : Z} {x : A},
    listNthZ l n = some x → x ∈ l
  | [], _, _, h => by simp [listNthZ] at h
  | _ :: _, _, _, h => by
      simp only [listNthZ] at h
      split at h
      · cases h; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (listNthZ_mem h)

section RELSEM
variable (ge : CGenv)

section EVAL_EXPR
variable (sp : Val) (e : Cminor.Env) (m : Mem)

mutual
/-- `CminorSel.eval_expr` -/
inductive EvalExpr : Letenv → Expr → Val → Prop where
  | Evar (le id v) : e.get id = some v → EvalExpr le (.Evar id) v
  | Eop (le op al vl v) :
      EvalExprlist le al vl → evalOperation ge sp op vl m = some v → EvalExpr le (.Eop op al) v
  | Eload (le chunk addr al vl vaddr v) :
      EvalExprlist le al vl → evalAddressing ge sp addr vl = some vaddr →
      Mem.loadv chunk m vaddr = some v → EvalExpr le (.Eload chunk addr al) v
  | Econdition (le a b c va v) :
      EvalCondexpr le a va → EvalExpr le (if va then b else c) v →
      EvalExpr le (.Econdition a b c) v
  | Elet (le a b v1 v2) :
      EvalExpr le a v1 → EvalExpr (v1 :: le) b v2 → EvalExpr le (.Elet a b) v2
  | Eletvar (le n v) : le[n]? = some v → EvalExpr le (.Eletvar n) v
  | Ebuiltin (le ef al vl v) :
      EvalExprlist le al vl → externalCall ef ge.toSenv vl m E0 v m →
      EvalExpr le (.Ebuiltin ef al) v
  | Eexternal (le id sg al b ef vl v) :
      Genv.findSymbol ge id = some b →
      Genv.findFunctPtr ge b = some (.External ef) →
      ef.sig = sg →
      EvalExprlist le al vl → externalCall ef ge.toSenv vl m E0 v m →
      EvalExpr le (.Eexternal id sg al) v

/-- `CminorSel.eval_exprlist` -/
inductive EvalExprlist : Letenv → Exprlist → List Val → Prop where
  | Enil (le) : EvalExprlist le .Enil []
  | Econs (le a1 al v1 vl) :
      EvalExpr le a1 v1 → EvalExprlist le al vl → EvalExprlist le (.Econs a1 al) (v1 :: vl)

/-- `CminorSel.eval_condexpr` -/
inductive EvalCondexpr : Letenv → Condexpr → Bool → Prop where
  | CEcond (le cond al vl vb) :
      EvalExprlist le al vl → evalCondition cond vl m = some vb →
      EvalCondexpr le (.CEcond cond al) vb
  | CEcondition (le a b c va v) :
      EvalCondexpr le a va → EvalCondexpr le (if va then b else c) v →
      EvalCondexpr le (.CEcondition a b c) v
  | CElet (le a b v1 v2) :
      EvalExpr le a v1 → EvalCondexpr (v1 :: le) b v2 → EvalCondexpr le (.CElet a b) v2
end

/-- `CminorSel.eval_exitexpr` -/
inductive EvalExitexpr : Letenv → Exitexpr → Nat → Prop where
  | XEexit (le x) : EvalExitexpr le (.XEexit x) x
  | XEjumptable (le a tbl n x) :
      EvalExpr ge sp e m le a (.Vint n) → listNthZ tbl (Integers.Int.unsigned n) = some x →
      EvalExitexpr le (.XEjumptable a tbl) x
  | XEcondition (le a b c va x) :
      EvalCondexpr ge sp e m le a va → EvalExitexpr le (if va then b else c) x →
      EvalExitexpr le (.XEcondition a b c) x
  | XElet (le a b v x) :
      EvalExpr ge sp e m le a v → EvalExitexpr (v :: le) b x → EvalExitexpr le (.XElet a b) x

/-- `CminorSel.eval_expr_or_symbol` -/
inductive EvalExprOrSymbol : Letenv → Sum Expr Ident → Val → Prop where
  | e (le a v) : EvalExpr ge sp e m le a v → EvalExprOrSymbol le (.inl a) v
  | s (le id b) : Genv.findSymbol ge id = some b →
      EvalExprOrSymbol le (.inr id) (.Vptr b Integers.Ptrofs.zero)

/-- `CminorSel.eval_builtin_arg` -/
inductive EvalBuiltinArg : BuiltinArg Expr → Val → Prop where
  | BA (a v) : EvalExpr ge sp e m [] a v → EvalBuiltinArg (.BA a) v
  | BA_int (n) : EvalBuiltinArg (.BA_int n) (.Vint n)
  | BA_long (n) : EvalBuiltinArg (.BA_long n) (.Vlong n)
  | BA_float (n) : EvalBuiltinArg (.BA_float n) (.Vfloat n)
  | BA_single (n) : EvalBuiltinArg (.BA_single n) (.Vsingle n)
  | BA_loadstack (chunk ofs v) :
      Mem.loadv chunk m (Val.offsetPtr sp ofs) = some v →
      EvalBuiltinArg (.BA_loadstack chunk ofs) v
  | BA_addrstack (ofs) : EvalBuiltinArg (.BA_addrstack ofs) (Val.offsetPtr sp ofs)
  | BA_loadglobal (chunk id ofs v) :
      Mem.loadv chunk m (Genv.symbolAddress ge id ofs) = some v →
      EvalBuiltinArg (.BA_loadglobal chunk id ofs) v
  | BA_addrglobal (id ofs) :
      EvalBuiltinArg (.BA_addrglobal id ofs) (Genv.symbolAddress ge id ofs)
  | BA_splitlong (a1 a2 v1 v2) :
      EvalExpr ge sp e m [] a1 v1 → EvalExpr ge sp e m [] a2 v2 →
      EvalBuiltinArg (.BA_splitlong (.BA a1) (.BA a2)) (Val.longofwords v1 v2)
  | BA_addptr (a1 v1 a2 v2) :
      EvalBuiltinArg a1 v1 → EvalBuiltinArg a2 v2 →
      EvalBuiltinArg (.BA_addptr a1 a2) (if Archi.ptr64 then Val.addl v1 v2 else Val.add v1 v2)

end EVAL_EXPR

/-- `CminorSel.set_builtin_res` -/
def setBuiltinRes (res : BuiltinRes Ident) (v : Val) (e : Cminor.Env) : Cminor.Env :=
  match res with
  | .BR id => e.set id v
  | _ => e

/-- `CminorSel.call_cont` -/
def callCont : Cont → Cont
  | .Kseq _ k => callCont k
  | .Kblock k => callCont k
  | k => k

/-- `CminorSel.is_call_cont` -/
def isCallCont : Cont → Bool
  | .Kstop => true
  | .Kcall .. => true
  | _ => false

/-- `CminorSel.find_label` -/
def findLabel (lbl : Cminor.Label) : Stmt → Cont → Option (Stmt × Cont)
  | .Sseq s1 s2, k =>
      match findLabel lbl s1 (.Kseq s2 k) with
      | some sk => some sk
      | none => findLabel lbl s2 k
  | .Sifthenelse _ s1 s2, k =>
      match findLabel lbl s1 k with
      | some sk => some sk
      | none => findLabel lbl s2 k
  | .Sloop s1, k => findLabel lbl s1 (.Kseq (.Sloop s1) k)
  | .Sblock s1, k => findLabel lbl s1 (.Kblock k)
  | .Slabel lbl' s', k => if lbl = lbl' then some (s', k) else findLabel lbl s' k
  | _, _ => none

/-- `CminorSel.step` -/
inductive Step : State → Trace → State → Prop where
  | skip_seq (f s k sp e m) :
      Step (.State f .Sskip (.Kseq s k) sp e m) E0 (.State f s k sp e m)
  | skip_block (f k sp e m) :
      Step (.State f .Sskip (.Kblock k) sp e m) E0 (.State f .Sskip k sp e m)
  | skip_call (f k sp e m m') :
      isCallCont k = true →
      Mem.free m sp 0 f.fn_stackspace = some m' →
      Step (.State f .Sskip k (.Vptr sp Integers.Ptrofs.zero) e m) E0 (.Returnstate .Vundef k m')
  | assign (f id a k sp e m v) :
      EvalExpr ge sp e m [] a v →
      Step (.State f (.Sassign id a) k sp e m) E0 (.State f .Sskip k sp (e.set id v) m)
  | store (f chunk addr al b k sp e m vl v vaddr m') :
      EvalExprlist ge sp e m [] al vl →
      EvalExpr ge sp e m [] b v →
      evalAddressing ge sp addr vl = some vaddr →
      Mem.storev chunk m vaddr v = some m' →
      Step (.State f (.Sstore chunk addr al b) k sp e m) E0 (.State f .Sskip k sp e m')
  | call (f optid sig a bl k sp e m vf vargs fd) :
      EvalExprOrSymbol ge sp e m [] a vf →
      EvalExprlist ge sp e m [] bl vargs →
      Genv.findFunct ge vf = some fd →
      funsig fd = sig →
      Step (.State f (.Scall optid sig a bl) k sp e m) E0
        (.Callstate fd vargs (.Kcall optid f sp e k) m)
  | tailcall (f sig a bl k sp e m vf vargs fd m') :
      EvalExprOrSymbol ge (.Vptr sp Integers.Ptrofs.zero) e m [] a vf →
      EvalExprlist ge (.Vptr sp Integers.Ptrofs.zero) e m [] bl vargs →
      Genv.findFunct ge vf = some fd →
      funsig fd = sig →
      Mem.free m sp 0 f.fn_stackspace = some m' →
      Step (.State f (.Stailcall sig a bl) k (.Vptr sp Integers.Ptrofs.zero) e m) E0
        (.Callstate fd vargs (callCont k) m')
  | builtin (f res ef al k sp e m vl t v m') :
      ListForall2 (EvalBuiltinArg ge sp e m) al vl →
      externalCall ef ge.toSenv vl m t v m' →
      Step (.State f (.Sbuiltin res ef al) k sp e m) t
        (.State f .Sskip k sp (setBuiltinRes res v e) m')
  | seq (f s1 s2 k sp e m) :
      Step (.State f (.Sseq s1 s2) k sp e m) E0 (.State f s1 (.Kseq s2 k) sp e m)
  | ifthenelse (f c s1 s2 k sp e m b) :
      EvalCondexpr ge sp e m [] c b →
      Step (.State f (.Sifthenelse c s1 s2) k sp e m) E0
        (.State f (if b then s1 else s2) k sp e m)
  | loop (f s k sp e m) :
      Step (.State f (.Sloop s) k sp e m) E0 (.State f s (.Kseq (.Sloop s) k) sp e m)
  | block (f s k sp e m) :
      Step (.State f (.Sblock s) k sp e m) E0 (.State f s (.Kblock k) sp e m)
  | exit_seq (f n s k sp e m) :
      Step (.State f (.Sexit n) (.Kseq s k) sp e m) E0 (.State f (.Sexit n) k sp e m)
  | exit_block_0 (f k sp e m) :
      Step (.State f (.Sexit 0) (.Kblock k) sp e m) E0 (.State f .Sskip k sp e m)
  | exit_block_S (f n k sp e m) :
      Step (.State f (.Sexit (n + 1)) (.Kblock k) sp e m) E0 (.State f (.Sexit n) k sp e m)
  | switch (f a k sp e m n) :
      EvalExitexpr ge sp e m [] a n →
      Step (.State f (.Sswitch a) k sp e m) E0 (.State f (.Sexit n) k sp e m)
  | return_0 (f k sp e m m') :
      Mem.free m sp 0 f.fn_stackspace = some m' →
      Step (.State f (.Sreturn none) k (.Vptr sp Integers.Ptrofs.zero) e m) E0
        (.Returnstate .Vundef (callCont k) m')
  | return_1 (f a k sp e m v m') :
      EvalExpr ge (.Vptr sp Integers.Ptrofs.zero) e m [] a v →
      Mem.free m sp 0 f.fn_stackspace = some m' →
      Step (.State f (.Sreturn (some a)) k (.Vptr sp Integers.Ptrofs.zero) e m) E0
        (.Returnstate v (callCont k) m')
  | label (f lbl s k sp e m) :
      Step (.State f (.Slabel lbl s) k sp e m) E0 (.State f s k sp e m)
  | goto (f lbl k sp e m s' k') :
      findLabel lbl f.fn_body (callCont k) = some (s', k') →
      Step (.State f (.Sgoto lbl) k sp e m) E0 (.State f s' k' sp e m)
  | internal_function (f vargs k m m' sp e) :
      Val.HasArgtypeList vargs f.fn_sig.sig_args →
      Mem.alloc m 0 f.fn_stackspace = (m', sp) →
      Cminor.setLocals f.fn_vars (Cminor.setParams vargs f.fn_params) = e →
      Step (.Callstate (.Internal f) vargs k m) E0
        (.State f f.fn_body k (.Vptr sp Integers.Ptrofs.zero) e m')
  | external_function (ef vargs k m t vres m') :
      externalCall ef ge.toSenv vargs m t vres m' →
      Step (.Callstate (.External ef) vargs k m) t (.Returnstate vres k m')
  | return (v optid f sp e k m) :
      Step (.Returnstate v (.Kcall optid f sp e k) m) E0
        (.State f .Sskip k sp (Cminor.setOptvar optid v e) m)

end RELSEM

/-- `CminorSel.initial_state` -/
inductive InitialState (p : Program) : State → Prop where
  | intro (b f m0) :
      p.initMem = some m0 →
      Genv.findSymbol p.globalenv p.prog_main = some b →
      Genv.findFunctPtr p.globalenv b = some f →
      funsig f = signature_main →
      InitialState p (.Callstate f [] .Kstop m0)

/-- `CminorSel.final_state` -/
inductive FinalState : State → Integers.Int → Prop where
  | intro (r m) : FinalState (.Returnstate (.Vint r) .Kstop m) r

/-- `CminorSel.semantics` -/
def semantics (p : Program) : Semantics where
  state := State
  step := Step p.globalenv
  initial_state := InitialState p
  final_state := FinalState
  symbolenv := Genv.toSenv p.globalenv

/-! ## Lifting of let-bound variables -/

mutual
/-- `CminorSel.lift_expr` -/
def liftExpr (p : Nat) : Expr → Expr
  | .Evar id => .Evar id
  | .Eop op bl => .Eop op (liftExprlist p bl)
  | .Eload chunk addr bl => .Eload chunk addr (liftExprlist p bl)
  | .Econdition a b c => .Econdition (liftCondexpr p a) (liftExpr p b) (liftExpr p c)
  | .Elet b c => .Elet (liftExpr p b) (liftExpr (p + 1) c)
  | .Eletvar n => if p ≤ n then .Eletvar (n + 1) else .Eletvar n
  | .Ebuiltin ef bl => .Ebuiltin ef (liftExprlist p bl)
  | .Eexternal id sg bl => .Eexternal id sg (liftExprlist p bl)

/-- `CminorSel.lift_exprlist` -/
def liftExprlist (p : Nat) : Exprlist → Exprlist
  | .Enil => .Enil
  | .Econs b cl => .Econs (liftExpr p b) (liftExprlist p cl)

/-- `CminorSel.lift_condexpr` -/
def liftCondexpr (p : Nat) : Condexpr → Condexpr
  | .CEcond c al => .CEcond c (liftExprlist p al)
  | .CEcondition a b c => .CEcondition (liftCondexpr p a) (liftCondexpr p b) (liftCondexpr p c)
  | .CElet a b => .CElet (liftExpr p a) (liftCondexpr (p + 1) b)
end

/-- `CminorSel.lift` -/
def lift (a : Expr) : Expr := liftExpr 0 a
/-- `CminorSel.lift_list` -/
def liftList (al : Exprlist) : Exprlist := liftExprlist 0 al

/-- `CminorSel.insert_lenv` -/
inductive InsertLenv : Letenv → Nat → Val → Letenv → Prop where
  | zero (le v) : InsertLenv le 0 v (v :: le)
  | succ (le p w le' v) : InsertLenv le p w le' → InsertLenv (v :: le) (p + 1) w (v :: le')

theorem insertLenv_lookup1 {le p w le'} (h : InsertLenv le p w le') :
    ∀ {n v}, le[n]? = some v → n < p → le'[n]? = some v := by
  induction h with
  | zero => intro n v _ hp; omega
  | succ le p w le' v' _ ih =>
    intro n v hn hp
    cases n with
    | zero => simpa using hn
    | succ n => simp only [List.getElem?_cons_succ] at hn ⊢; exact ih hn (by omega)

theorem insertLenv_lookup2 {le p w le'} (h : InsertLenv le p w le') :
    ∀ {n v}, le[n]? = some v → p ≤ n → le'[n + 1]? = some v := by
  induction h with
  | zero => intro n v hn _; simpa using hn
  | succ le p w le' v' _ ih =>
    intro n v hn hp
    cases n with
    | zero => omega
    | succ n => simp only [List.getElem?_cons_succ] at hn ⊢; exact ih hn (by omega)

section LIFT
variable {ge : CGenv} {sp : Val} {e : Cminor.Env} {m : Mem} {w : Val}

mutual
theorem eval_liftExpr {le a v} (h : EvalExpr ge sp e m le a v) :
    ∀ {p le'}, InsertLenv le p w le' → EvalExpr ge sp e m le' (liftExpr p a) v := by
  intro p le' hi
  cases h with
  | Evar _ _ _ h1 => exact .Evar _ _ _ h1
  | Eop _ _ _ _ _ h1 h2 => exact .Eop _ _ _ _ _ (eval_liftExprlist h1 hi) h2
  | Eload _ _ _ _ _ _ _ h1 h2 h3 => exact .Eload _ _ _ _ _ _ _ (eval_liftExprlist h1 hi) h2 h3
  | Econdition _ _ b c va _ h1 h2 =>
    refine .Econdition _ _ _ _ va _ (eval_liftCondexpr h1 hi) ?_
    cases va <;> exact eval_liftExpr h2 hi
  | Elet _ _ _ _ _ h1 h2 =>
    exact .Elet _ _ _ _ _ (eval_liftExpr h1 hi) (eval_liftExpr h2 (.succ _ _ _ _ _ hi))
  | Eletvar _ n _ h1 =>
    simp only [liftExpr]
    split
    · exact .Eletvar _ _ _ (insertLenv_lookup2 hi h1 (by omega))
    · exact .Eletvar _ _ _ (insertLenv_lookup1 hi h1 (by omega))
  | Ebuiltin _ _ _ _ _ h1 h2 => exact .Ebuiltin _ _ _ _ _ (eval_liftExprlist h1 hi) h2
  | Eexternal _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
    exact .Eexternal _ _ _ _ _ _ _ _ h1 h2 h3 (eval_liftExprlist h4 hi) h5

theorem eval_liftExprlist {le al vl} (h : EvalExprlist ge sp e m le al vl) :
    ∀ {p le'}, InsertLenv le p w le' → EvalExprlist ge sp e m le' (liftExprlist p al) vl := by
  intro p le' hi
  cases h with
  | Enil => exact .Enil _
  | Econs _ _ _ _ _ h1 h2 => exact .Econs _ _ _ _ _ (eval_liftExpr h1 hi) (eval_liftExprlist h2 hi)

theorem eval_liftCondexpr {le a b} (h : EvalCondexpr ge sp e m le a b) :
    ∀ {p le'}, InsertLenv le p w le' → EvalCondexpr ge sp e m le' (liftCondexpr p a) b := by
  intro p le' hi
  cases h with
  | CEcond _ _ _ _ _ h1 h2 => exact .CEcond _ _ _ _ _ (eval_liftExprlist h1 hi) h2
  | CEcondition _ _ b c va _ h1 h2 =>
    refine .CEcondition _ _ _ _ va _ (eval_liftCondexpr h1 hi) ?_
    cases va <;> exact eval_liftCondexpr h2 hi
  | CElet _ _ _ _ _ h1 h2 =>
    exact .CElet _ _ _ _ _ (eval_liftExpr h1 hi) (eval_liftCondexpr h2 (.succ _ _ _ _ _ hi))
end

/-- `CminorSel.eval_lift` -/
theorem eval_lift {le a v} (h : EvalExpr ge sp e m le a v) :
    EvalExpr ge sp e m (w :: le) (lift a) v :=
  eval_liftExpr h (.zero _ _)

/-- `CminorSel.eval_lift_list` -/
theorem eval_liftList {le al vl} (h : EvalExprlist ge sp e m le al vl) :
    EvalExprlist ge sp e m (w :: le) (liftList al) vl :=
  eval_liftExprlist h (.zero _ _)

end LIFT

/-! ## Operations over `exprlist` -/

/-- `CminorSel.length_exprlist` -/
def lengthExprlist : Exprlist → Nat
  | .Enil => 0
  | .Econs _ al => lengthExprlist al + 1

/-- `CminorSel.app_exprlist` -/
def appExprlist : Exprlist → Exprlist → Exprlist
  | .Enil, bl => bl
  | .Econs a al, bl => .Econs a (appExprlist al bl)

theorem eval_appExprlist {ge : CGenv} {sp e m le al2 vl2}
    (h2 : EvalExprlist ge sp e m le al2 vl2) : ∀ {al1 vl1},
    EvalExprlist ge sp e m le al1 vl1 →
    EvalExprlist ge sp e m le (appExprlist al1 al2) (vl1 ++ vl2)
  | .Enil, _, h1 => by cases h1; exact h2
  | .Econs _ _, _, h1 => by
    cases h1 with
    | Econs _ _ _ _ _ ha hl => exact .Econs _ _ _ _ _ ha (eval_appExprlist h2 hl)

theorem lengthExprlist_lift (p : Nat) :
    ∀ al : Exprlist, lengthExprlist (liftExprlist p al) = lengthExprlist al
  | .Enil => rfl
  | .Econs _ al => by simp [liftExprlist, lengthExprlist, lengthExprlist_lift p al]

/-- `CminorSel.bind_exprs_rec` -/
def bindExprsRec (al : Exprlist) (args : Exprlist) (f : Exprlist → Expr) : Expr :=
  match al with
  | .Enil => f args
  | .Econs a al =>
      .Elet a (bindExprsRec (liftList al)
                 (appExprlist (liftList args) (.Econs (.Eletvar 0) .Enil)) f)
termination_by lengthExprlist al
decreasing_by simp [liftList, lengthExprlist_lift, lengthExprlist]

/-- `CminorSel.bind_exprs` -/
def bindExprs (al : Exprlist) (f : Exprlist → Expr) : Expr := bindExprsRec al .Enil f

/-- `CminorSel.eval_bind_exprs_gen` -/
theorem eval_bindExprs_gen (P : Val → Prop) {ge : CGenv} {sp e m le al vl}
    {f : Exprlist → Expr}
    (h : EvalExprlist ge sp e m le al vl)
    (hf : ∀ args, EvalExprlist ge sp e m (vl.reverse ++ le) args vl →
      ∃ v, EvalExpr ge sp e m (vl.reverse ++ le) (f args) v ∧ P v) :
    ∃ v, EvalExpr ge sp e m le (bindExprs al f) v ∧ P v := by
  have REC : ∀ n al args le vl1 vl2, lengthExprlist al = n →
      (∀ args', EvalExprlist ge sp e m (vl2.reverse ++ le) args' (vl1 ++ vl2) →
        ∃ v, EvalExpr ge sp e m (vl2.reverse ++ le) (f args') v ∧ P v) →
      EvalExprlist ge sp e m le args vl1 →
      EvalExprlist ge sp e m le al vl2 →
      ∃ v, EvalExpr ge sp e m le (bindExprsRec al args f) v ∧ P v := by
    intro n
    induction n with
    | zero =>
      intro al args le vl1 vl2 hn F A B
      cases B with
      | Enil =>
        rw [bindExprsRec]
        apply F
        simpa using A
      | Econs => simp [lengthExprlist] at hn
    | succ n ih =>
      intro al args le vl1 vl2 hn F A B
      cases B with
      | Enil => simp [lengthExprlist] at hn
      | Econs _ a al v1 vl hv hl =>
        obtain ⟨v, X, Y⟩ := ih (liftList al) _ (v1 :: le) (vl1 ++ [v1]) vl
          (by simp only [liftList, lengthExprlist_lift]; simp [lengthExprlist] at hn; exact hn)
          (by
            intro args' hargs
            have EQ : vl.reverse ++ v1 :: le = (v1 :: vl).reverse ++ le := by simp
            rw [EQ]
            apply F
            rw [← EQ]
            simpa using hargs)
          (eval_appExprlist (.Econs _ _ _ _ _ (.Eletvar _ 0 _ rfl) (.Enil _)) (eval_liftList A))
          (eval_liftList hl)
        refine ⟨v, ?_, Y⟩
        rw [bindExprsRec]
        exact .Elet _ _ _ _ _ hv X
  exact REC _ al .Enil le [] vl rfl (by simpa using hf) (.Enil _) h

/-- `CminorSel.eval_bind_exprs` -/
theorem eval_bindExprs {ge : CGenv} {sp e m le al vl} {f : Exprlist → Expr} {v}
    (h : EvalExprlist ge sp e m le al vl)
    (hf : ∀ args, EvalExprlist ge sp e m (vl.reverse ++ le) args vl →
      EvalExpr ge sp e m (vl.reverse ++ le) (f args) v) :
    EvalExpr ge sp e m le (bindExprs al f) v := by
  obtain ⟨v', A, B⟩ := eval_bindExprs_gen (fun v' => v' = v) h (fun args ha => ⟨v, hf args ha, rfl⟩)
  subst B; exact A

end CminorSel
end X86
end CC
