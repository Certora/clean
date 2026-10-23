/-
  **Calls through function pointers** (Phase-9 Step 7).

  The Phase-7.5 plan scoped function pointers *out*, and the Phase-9 survey
  predicted that `Sep.triple_call` would already permit them.  It does: the rule
  asks for `Genv.findFunct ge (Vptr b 0) = some fd` plus a proof that the callee
  *expression evaluates* to that pointer, and nothing anywhere requires the
  expression to be an `Evar`.  So the missing pieces were never the call rule —
  they are (a) the three ways clightgen writes a callee, and (b) a resource
  predicate for a memory cell that holds one.  Both are here.

  ## The three callee shapes, as `clightgen -lean -normalize` emits them

  | C | Clight callee expression | resolved by |
  |---|---|---|
  | `f(x)` | `Evar f (Tfunction …)` | `eval_callee_global` |
  | `g(x)`, `g` a pointer | `Etempvar g (tptr (Tfunction …))` | `eval_callee_temp` |
  | `(*p)(x)` — zlib's `ZALLOC` | `Ederef (Etempvar p (tptr (Tfunction …))) (Tfunction …)` | `eval_callee_deref` |

  `Cop.classifyFun` already accepts both `Tfunction` and `Tpointer (Tfunction …)`
  (`CCLib/cfrontend/Cop.lean:859`), so no operator work was needed either.

  ## What is *not* a resource

  Function code is not owned: `FuncPtr` is a plain `Prop` about the global
  environment, not an `HProp`.  Only the memory cell that *names* a function is a
  resource, and that is `funcPtrAt` (VST's `func_ptr`).  This is why an indirect
  call composes with the frame rule for free — the callee's identity is
  duplicable, its arguments are not.
-/
import CCLib.logic.Funspec
import CCLib.logic.Temps

namespace CC.Sep
open CC.HProp

/-! ## Resolving a callee -/

/-- Block `fb` is the entry point of `fd`.  A *pure* fact about the global
    environment — see the header. -/
def FuncPtr (ge : CGenv) (fb : Block) (fd : FunDef) : Prop :=
  Genv.findFunct ge.genv_genv (.Vptr fb Integers.Ptrofs.zero) = some fd

/-- A directly named callee: `f(…)`. -/
theorem eval_callee_global {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem}
    {fid : Ident} {ty : Ty} {fb : Block}
    (hloc : e.get fid = none)
    (hsym : Genv.findSymbol ge.genv_genv fid = some fb)
    (hacc : accessMode ty = .By_reference) :
    EvalExpr ge e le m (.Evar fid ty) (.Vptr fb Integers.Ptrofs.zero) :=
  EvalExpr.Elvalue _ fb Integers.Ptrofs.zero .Full _
    (EvalLvalue.Evar_global fid fb ty hloc hsym) (DerefLoc.reference hacc)

/-- A callee held in a temporary: `g(…)` where `g` has function-pointer type.
    Nothing to do — the pointer is already the value. -/
theorem eval_callee_temp {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem}
    {pid : Ident} {ty : Ty} {fb : Block}
    (h : le.get pid = some (.Vptr fb Integers.Ptrofs.zero)) :
    EvalExpr ge e le m (.Etempvar pid ty) (.Vptr fb Integers.Ptrofs.zero) :=
  EvalExpr.Etempvar pid ty _ h

/-- A dereferenced function pointer: `(*p)(…)`, which is how zlib writes
    `ZALLOC`/`ZFREE`.  The dereference does **not** load: a function type's
    `accessMode` is `By_reference`, so `*p` is the function *designator* at the
    same address and the value is unchanged. -/
theorem eval_callee_deref {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem}
    {a : Expr} {tyargs : List Ty} {tyres : Ty} {cc : CallConv}
    {fb : Block} {ofs : Integers.Ptrofs}
    (h : EvalExpr ge e le m a (.Vptr fb ofs)) :
    EvalExpr ge e le m (.Ederef a (.Tfunction tyargs tyres cc)) (.Vptr fb ofs) :=
  EvalExpr.Elvalue _ fb ofs .Full _
    (EvalLvalue.Ederef a _ fb ofs h) (DerefLoc.reference rfl)

/-- `accessMode` of a function type really is `By_reference` — the fact the two
    lemmas above turn on. -/
theorem accessMode_fun (tyargs : List Ty) (tyres : Ty) (cc : CallConv) :
    accessMode (.Tfunction tyargs tyres cc) = .By_reference := rfl

/-- …and `classifyFun` accepts both the function type and the pointer to it, so a
    direct and an indirect call classify identically. -/
theorem classifyFun_ptr (tyargs : List Ty) (tyres : Ty) (cc : CallConv) :
    Cop.classifyFun (tptr (.Tfunction tyargs tyres cc)) = .f tyargs tyres cc := rfl

theorem classifyFun_fun (tyargs : List Ty) (tyres : Ty) (cc : CallConv) :
    Cop.classifyFun (.Tfunction tyargs tyres cc) = .f tyargs tyres cc := rfl

/-! ## A cell holding a function pointer

VST's `func_ptr`.  Needed for zlib's `z_stream.zalloc`/`zfree` and for
`configuration_table[level].func`. -/

def funcPtrAt (ge : CGenv) (fd : FunDef) (pm : Permission) (b : Block) (ofs : Z) :
    HProp :=
  hexists fun fb => mapsto Mptr pm b ofs (.Vptr fb Integers.Ptrofs.zero)
                      ∗ ⌜FuncPtr ge fb fd⌝

/-- Loading the cell yields a pointer that `findFunct` resolves.  `Mptr` is
    `Mint64` here, and `Val.loadResult Mint64 (Vptr …) = Vptr …` because
    `Archi.ptr64`, so the pointer survives the load unchanged. -/
theorem funcPtrAt_load {ge : CGenv} {fd : FunDef} {pm : Permission} {b : Block}
    {ofs : _root_.Int} {h : Heap} {m : Mem}
    (hpr : permOrder pm .Readable = true)
    (hf : funcPtrAt ge fd pm b ofs h) (hag : Heap.Agrees h m) :
    ∃ fb, Mem.load Mptr m b ofs = some (.Vptr fb Integers.Ptrofs.zero)
          ∧ FuncPtr ge fb fd := by
  obtain ⟨fb, h1, h2, _, heq, hm, hfind, h2e⟩ := hf
  subst h2e
  rw [Heap.union_emp] at heq
  subst heq
  refine ⟨fb, ?_, hfind⟩
  have := mapsto_load hpr hm hag
  simpa [Mptr, Val.loadResult, Archi.ptr64] using this

/-! ## A packaged call rule

`triple_call` is general but asks the caller to do the heap split, the callee
resolution and the postcondition plumbing in one `hsplit`.  This is the same rule
in the `LocalSt` style of `CCLib.logic.Temps`: the precondition's heap is `Hpre ∗
Hkeep`, the callee is lent `Hpre` and `Hkeep` rides through untouched by the
frame discipline, and the result lands in a tracked temporary.

The one restriction: the specification must *determine* the return value
(`hpost` returns `v = vret`).  Every spec written so far does — a postcondition
that did not could not name the value in the caller's tracked list anyway, and
would have to go through `triple_call` directly. -/

/-- The general form: the return value is whatever the callee produced, so the
    postcondition is existential.  Needed whenever the callee's specification is
    *abstract* — a higher-order function like `apply` below cannot name the value
    its argument returns, and that is exactly the case function pointers exist
    for. -/
theorem triple_call_local_ex (ge fe f) (S : FunSpec) (id : Ident)
    (callee : Expr) (al : List Expr) (E : Env) (l₀ l : List (Ident × Val))
    (Hpre Hkeep : HProp) (vargs : List Val) (fb : Block) (fd : FunDef)
    (hspec : ∀ vs, SatisfiesAt ge fe fd S vs)
    (hfind : FuncPtr ge fb fd)
    (hty : typeOfFundef fd = .Tfunction S.tyargs S.tyres S.cc)
    (hclass : Cop.classifyFun (typeof callee) = .f S.tyargs S.tyres S.cc)
    (hsub : ∀ p ∈ l, p ∈ l₀)
    (hne : ∀ p ∈ l, p.1 ≠ id)
    (hcallee : ∀ le m, TempsHold l₀ le →
                 EvalExpr ge E le m callee (.Vptr fb Integers.Ptrofs.zero))
    (hargs : ∀ le m, TempsHold l₀ le → EvalExprlist ge E le m al S.tyargs vargs)
    (hpre : ∀ h, Hpre h → S.pre vargs h) :
    Triple ge fe f (LocalSt E l₀ (Hpre ∗ Hkeep)) (.Scall (some id) callee al)
      (.only (fun e le hp => ∃ v, e = E ∧ TempsHold ((id, v) :: l) le
                                  ∧ (S.post v ∗ Hkeep) hp)) := by
  refine triple_call ge fe f S (some id) callee al _ _ fb fd hspec hfind hty hclass
    (fun e le hp m hP hag => ?_)
  obtain ⟨he, hT, h1, h2, hd12, heq, hH1, hH2⟩ := hP
  subst he
  refine ⟨vargs, h1, h2, hd12, heq, hcallee le m hT, hargs le m hT, hpre h1 hH1, ?_⟩
  intro v h1' hS hd'
  exact ⟨v, rfl, TempsHold_set hne (TempsHold_mono hsub hT),
         h1', h2, hd', rfl, hS, hH2⟩

/-- The common case: the specification *determines* the return value, so the
    postcondition stays in `LocalSt` shape and chains with `triple_seq_fwd`. -/
theorem triple_call_local (ge fe f) (S : FunSpec) (id : Ident)
    (callee : Expr) (al : List Expr) (E : Env) (l₀ l : List (Ident × Val))
    (Hpre Hkeep Hpost : HProp) (vargs : List Val) (vret : Val)
    (fb : Block) (fd : FunDef)
    (hspec : ∀ vs, SatisfiesAt ge fe fd S vs)
    (hfind : FuncPtr ge fb fd)
    (hty : typeOfFundef fd = .Tfunction S.tyargs S.tyres S.cc)
    (hclass : Cop.classifyFun (typeof callee) = .f S.tyargs S.tyres S.cc)
    (hsub : ∀ p ∈ l, p ∈ l₀)
    (hne : ∀ p ∈ l, p.1 ≠ id)
    (hcallee : ∀ le m, TempsHold l₀ le →
                 EvalExpr ge E le m callee (.Vptr fb Integers.Ptrofs.zero))
    (hargs : ∀ le m, TempsHold l₀ le → EvalExprlist ge E le m al S.tyargs vargs)
    (hpre : ∀ h, Hpre h → S.pre vargs h)
    (hpost : ∀ v h, S.post v h → v = vret ∧ Hpost h) :
    Triple ge fe f (LocalSt E l₀ (Hpre ∗ Hkeep)) (.Scall (some id) callee al)
      (.only (LocalSt E ((id, vret) :: l) (Hpost ∗ Hkeep))) := by
  refine triple_call ge fe f S (some id) callee al _ _ fb fd hspec hfind hty hclass
    (fun e le hp m hP hag => ?_)
  obtain ⟨he, hT, h1, h2, hd12, heq, hH1, hH2⟩ := hP
  subst he
  refine ⟨vargs, h1, h2, hd12, heq, hcallee le m hT, hargs le m hT, hpre h1 hH1, ?_⟩
  intro v h1' hS hd'
  obtain ⟨hv, hHp⟩ := hpost v h1' hS
  subst hv
  exact ⟨rfl, TempsHold_set hne (TempsHold_mono hsub hT),
         h1', h2, hd', rfl, hHp, hH2⟩

end CC.Sep
