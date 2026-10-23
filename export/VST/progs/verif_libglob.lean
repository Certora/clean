/-
  Port of VST's `progs/verif_libglob.v`: the module `LG` of
  `vst/progs/libglob.c`, an abstract data type implemented in two global
  variables,

      int LG_n = 3;
      struct foo { int initialized; int m; } LG_foo = {0};

  whose operations `LG_init`, `LG_bump`, `LG_get` are used by `client`.

  VST's abstraction (`Module LG`):

      data_ok n gv := !!(0 <= n <= Int.max_signed) &&
        data_at Ews tint (Vint (Int.repr n)) (gv _LG_n) *
        data_at Ews (Tstruct _foo noattr) (Vint Int.one, Vint (Int.repr n)) (gv _LG_foo)
      data n gv := data_ok n gv ||
        (!!(n = 3) && data_at Ews tint (Vint (Int.repr n)) (gv _LG_n) *
          data_at Ews (Tstruct _foo noattr) (Vint Int.zero, Vundef) (gv _LG_foo))

  Here `gv _LG_n` and `gv _LG_foo` are the blocks `bn` and `bf` the symbols
  resolve to, and the two `data_at`s are the three `int` cells `cells`: `LG_n`
  at `bn + 0`, `LG_foo.initialized` at `bf + 0` and `LG_foo.m` at `bf + 4`
  (the layout of `struct foo` in the program's composite environment), owned
  at a writable permission `p`.  `n` is a natural number.

  VST's specifications, proved here (`init_satisfies`, `bump_satisfies`,
  `get_satisfies`, `client_satisfies`, `main_satisfies`):

      init_spec   : PRE data n          POST data_ok n
      bump_spec   : PRE n < max_signed, data n   POST data (n+1)
      get_spec    : PRE data n          POST RETURN (Vint (Int.repr n)), data n
      client_spec : PRE n < 1000000000, data n   POST RETURN (Vint (Int.repr (n+2))), data (n+2)
      main_spec   : PRE main_pre        POST RETURN (Vint (Int.repr 5))

  In `data`, VST's `Vundef` for `LG_foo.m` means "any content"; here it is an
  existentially quantified value.  `main_pre` is the initial content of the
  globals: `LG_n = 3` and `LG_foo` zero-initialized, which is `data 3`
  (`initial`, VST's `LG.initial`).  The theorems assume that the
  global function symbols are the program's functions (VST's `Gprog`) and that
  `ge` uses the program's composite environment (`hcenv`).
-/
import VST.progs.libglob
import CCLib
open CC CC.Sep CC.HProp
open Libglob

namespace VST.Verif.Libglob

/-! ## The layout of `struct foo` -/

def coFoo : Composite :=
  match prog.prog_comp_env.get _foo with
  | some co => co
  | none => { co_su := .Struct, co_members := [], co_attr := noattr,
              co_sizeof := 0, co_alignof := 1, co_rank := 0 }

theorem get_foo : prog.prog_comp_env.get _foo = some coFoo := rfl
theorem off_initialized :
    fieldOffset prog.prog_comp_env _initialized coFoo.co_members = .OK (0, .Full) := by decide
theorem off_m : fieldOffset prog.prog_comp_env _m coFoo.co_members = .OK (4, .Full) := by decide

/-! ## The abstraction -/

/-- `Int.max_signed` -/
def maxSigned : Nat := 2147483647

/-- `Vint (Int.repr n)` -/
abbrev vint (n : Nat) : Val := .Vint (Integers.Int.repr n)

/-- The three cells: `LG_n = vn`, `LG_foo.initialized = vi`, `LG_foo.m = vm`. -/
def cells (p : Permission) (bn bf : Block) (vn vi vm : Val) : HProp :=
  mapsto .Mint32 p bn 0 vn ∗ mapsto .Mint32 p bf 0 vi ∗ mapsto .Mint32 p bf 4 vm

theorem cells_initialized_front (p : Permission) (bn bf : Block) (vn vi vm : Val) :
    cells p bn bf vn vi vm
      = mapsto .Mint32 p bf 0 vi ∗ (mapsto .Mint32 p bn 0 vn ∗ mapsto .Mint32 p bf 4 vm) :=
  sep_left_comm_eq _ _ _

theorem cells_m_front (p : Permission) (bn bf : Block) (vn vi vm : Val) :
    cells p bn bf vn vi vm
      = mapsto .Mint32 p bf 4 vm ∗ (mapsto .Mint32 p bn 0 vn ∗ mapsto .Mint32 p bf 0 vi) := by
  rw [cells, sep_comm_eq (mapsto .Mint32 p bf 0 vi), sep_left_comm_eq]

/-- `LG.data_ok n gv` -/
def dataOk (p : Permission) (bn bf : Block) (n : Nat) : HProp :=
  fun h => n ≤ maxSigned ∧ cells p bn bf (vint n) (.Vint Integers.Int.one) (vint n) h

/-- `LG.data n gv` -/
def data (p : Permission) (bn bf : Block) (n : Nat) : HProp :=
  fun h => dataOk p bn bf n h
    ∨ (n = 3 ∧ ∃ vm, cells p bn bf (vint 3) (.Vint Integers.Int.zero) vm h)

/-- `LG.initial`: the initial content of the globals (`LG_n = 3`, `LG_foo`
    zero-initialized) is `data 3`. -/
theorem initial (p : Permission) (bn bf : Block) (h : Heap)
    (hinit : cells p bn bf (vint 3) (.Vint Integers.Int.zero) (.Vint Integers.Int.zero) h) :
    data p bn bf 3 h := Or.inr ⟨rfl, _, hinit⟩

/-! ## The specifications -/

/-- `init_spec` -/
def initSpec (p : Permission) (bn bf : Block) (n : Nat) : Sep.FunSpec where
  tyargs := []
  tyres := tvoid
  cc := cc_default
  pre := fun vargs hp => vargs = [] ∧ data p bn bf n hp
  post := fun _ hp => dataOk p bn bf n hp
  measure := fun _ => 0

/-- `bump_spec` -/
def bumpSpec (p : Permission) (bn bf : Block) (n : Nat) : Sep.FunSpec where
  tyargs := []
  tyres := tvoid
  cc := cc_default
  pre := fun vargs hp => vargs = [] ∧ n < maxSigned ∧ data p bn bf n hp
  post := fun _ hp => data p bn bf (n + 1) hp
  measure := fun _ => 0

/-- `get_spec` -/
def getSpec (p : Permission) (bn bf : Block) (n : Nat) : Sep.FunSpec where
  tyargs := []
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [] ∧ data p bn bf n hp
  post := fun v hp => v = vint n ∧ data p bn bf n hp
  measure := fun _ => 0

/-- `client_spec` -/
def clientSpec (p : Permission) (bn bf : Block) (n : Nat) : Sep.FunSpec where
  tyargs := []
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [] ∧ n < 1000000000 ∧ data p bn bf n hp
  post := fun v hp => v = vint (n + 2) ∧ data p bn bf (n + 2) hp
  measure := fun _ => 0

/-- `main_spec`, with `main_pre` restricted to `LG`'s globals (`data 3`). -/
def mainSpec (p : Permission) (bn bf : Block) : Sep.FunSpec where
  tyargs := []
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [] ∧ data p bn bf 3 hp
  post := fun v hp => v = vint 5 ∧ data p bn bf 5 hp
  measure := fun _ => 0

section
variable (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env)
  (p : Permission) (hpw : permOrder p .Writable = true) (bn bf : Block)
  (hsym_n : Genv.findSymbol ge.genv_genv _LG_n = some bn)
  (hsym_f : Genv.findSymbol ge.genv_genv _LG_foo = some bf)

/-! ## Reading and writing the globals -/

include hcenv hsym_f in
theorem lvalue_initialized {le : TempEnv} {m : Mem} :
    EvalLvalue ge emptyEnv le m (.Efield (.Evar _LG_foo (.Tstruct _foo noattr)) _initialized tint)
      bf (Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.repr 0)) .Full :=
  lvalue_global_field (PTree.gempty _) hsym_f (hcenv ▸ get_foo) (hcenv ▸ off_initialized)

include hcenv hsym_f in
theorem lvalue_m {le : TempEnv} {m : Mem} :
    EvalLvalue ge emptyEnv le m (.Efield (.Evar _LG_foo (.Tstruct _foo noattr)) _m tint)
      bf (Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.repr 4)) .Full :=
  lvalue_global_field (PTree.gempty _) hsym_f (hcenv ▸ get_foo) (hcenv ▸ off_m)

include hcenv hsym_f hpw in
/-- `x = LG_foo.initialized;` -/
theorem eval_initialized {le : TempEnv} {m : Mem} {vn vm : Val} {i : Integers.Int} {h : Heap}
    (hc : cells p bn bf vn (.Vint i) vm h) (hag : Heap.Agrees h m) :
    EvalExpr ge emptyEnv le m
      (.Efield (.Evar _LG_foo (.Tstruct _foo noattr)) _initialized tint) (.Vint i) := by
  rw [cells_initialized_front] at hc
  obtain ⟨h1, hm, hag1⟩ := sep_left_agrees hc hag
  exact eval_lvalue_mapsto (chunk := .Mint32) (v := .Vint i) rfl (readable_of_writable hpw)
    (lvalue_initialized ge hcenv bf hsym_f) (by decide) hm hag1

include hcenv hsym_f hpw in
/-- `x = LG_foo.m;` -/
theorem eval_m {le : TempEnv} {m : Mem} {vn vi : Val} {i : Integers.Int} {h : Heap}
    (hc : cells p bn bf vn vi (.Vint i) h) (hag : Heap.Agrees h m) :
    EvalExpr ge emptyEnv le m (.Efield (.Evar _LG_foo (.Tstruct _foo noattr)) _m tint) (.Vint i) := by
  rw [cells_m_front] at hc
  obtain ⟨h1, hm, hag1⟩ := sep_left_agrees hc hag
  exact eval_lvalue_mapsto (chunk := .Mint32) (v := .Vint i) rfl (readable_of_writable hpw)
    (lvalue_m ge hcenv bf hsym_f) (by decide) hm hag1

include hsym_n hpw in
/-- `x = LG_n;` -/
theorem eval_n {le : TempEnv} {m : Mem} {vi vm : Val} {i : Integers.Int} {h : Heap}
    (hc : cells p bn bf (.Vint i) vi vm h) (hag : Heap.Agrees h m) :
    EvalExpr ge emptyEnv le m (.Evar _LG_n tint) (.Vint i) := by
  obtain ⟨h1, hm, hag1⟩ := sep_left_agrees hc hag
  exact eval_global_mapsto (PTree.gempty _) hsym_n rfl (readable_of_writable hpw) hm hag1

/-! ## `LG_init` -/

/-- The exit conditions of a `void` function body with postcondition `Q`. -/
def voidExit (Q : HProp) : Sep.ExitConds :=
  { normal := fun e _ hp => e = emptyEnv ∧ Q hp, brk := Assn.no, cont := Assn.no,
    ret := fun _ hp => Q hp }

include hcenv hpw hsym_f in
/-- `LG_init` on initialized data: nothing happens. -/
theorem init_body_ok (n : Nat) (hn : n ≤ maxSigned) (L : TempEnv) :
    Triple ge (FunctionEntry2 ge) f_LG_init
      (AtH L (cells p bn bf (vint n) (.Vint Integers.Int.one) (vint n)))
      f_LG_init.fn_body (voidExit (dataOk p bn bf n)) := by
  let L1 := L.set _t'1 (.Vint Integers.Int.one)
  refine triple_seq_only ge _ f_LG_init
    (triple_set_atH ge _ f_LG_init L _ _ _ (.Vint Integers.Int.one) fun m hp hc hag =>
      eval_initialized ge hcenv p hpw bn bf hsym_f hc hag) ?_
  refine triple_if ge _ f_LG_init _ Assn.no
    (AtH L1 (cells p bn bf (vint n) (.Vint Integers.Int.one) (vint n))) _ _ _ _
    (fun e le hp m h _ => by
      obtain ⟨rfl, rfl, hc⟩ := h
      exact ⟨_, false, EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (PTree.gss _ _ _)) rfl,
        rfl, rfl, rfl, hc⟩) (triple_vacuous ge _ f_LG_init _ _) ?_
  exact triple_fallthrough ge _ f_LG_init _ _ _ _ (triple_skip ge _ f_LG_init _)
    (fun e le hp h => ⟨h.1, hn, h.2.2⟩)

include hcenv hpw hsym_f in
/-- `LG_init` on uninitialized data: `LG_foo.m = 3; LG_foo.initialized = 1;`. -/
theorem init_body_fresh (L : TempEnv) (vm : Val) :
    Triple ge (FunctionEntry2 ge) f_LG_init
      (AtH L (cells p bn bf (vint 3) (.Vint Integers.Int.zero) vm))
      f_LG_init.fn_body (voidExit (dataOk p bn bf 3)) := by
  let L1 := L.set _t'1 (.Vint Integers.Int.zero)
  refine triple_seq_only ge _ f_LG_init
    (triple_set_atH ge _ f_LG_init L _ _ _ (.Vint Integers.Int.zero) fun m hp hc hag =>
      eval_initialized ge hcenv p hpw bn bf hsym_f hc hag) ?_
  refine triple_if ge _ f_LG_init _
    (AtH L1 (cells p bn bf (vint 3) (.Vint Integers.Int.zero) vm)) Assn.no _ _ _ _
    (fun e le hp m h _ => by
      obtain ⟨rfl, rfl, hc⟩ := h
      exact ⟨_, true, EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (PTree.gss _ _ _)) rfl,
        rfl, rfl, rfl, hc⟩) ?_ (triple_vacuous ge _ f_LG_init _ _)
  rw [cells_m_front]
  refine triple_seq_only ge _ f_LG_init
    (Q := AtH L1 (cells p bn bf (vint 3) (.Vint Integers.Int.zero) (vint 3))) ?_ ?_
  · refine triple_conseq ge _ f_LG_init
      (triple_assign_atE_front ge _ f_LG_init emptyEnv L1 _ _ _ .Mint32 p bf _ 4 vm (vint 3)
        (vint 3) hpw rfl (by decide) (fun _ => lvalue_m ge hcenv bf hsym_f)
        (fun _ => EvalExpr.Econst_int _ _) (fun m => semCast_int m _))
      (fun _ _ _ x => x) (fun e le hp h => ?_) (fun _ _ _ x => x) (fun _ _ _ x => x)
      (fun _ _ x => x)
    rw [cells_m_front]; exact h
  · rw [cells_initialized_front]
    exact triple_fallthrough ge _ f_LG_init _ _ _ _
      (triple_assign_atE_front ge _ f_LG_init emptyEnv L1 _ _ _ .Mint32 p bf _ 0 _
        (.Vint Integers.Int.one) (.Vint Integers.Int.one) hpw rfl (by decide)
        (fun _ => lvalue_initialized ge hcenv bf hsym_f)
        (fun _ => EvalExpr.Econst_int _ _) (fun m => semCast_int m _))
      (fun e le hp h => ⟨h.1, by decide, by rw [cells_initialized_front]; exact h.2.2⟩)

include hcenv hpw hsym_f in
/-- **`LG_init` satisfies `init_spec`** (VST's `body_init`). -/
theorem init_satisfies (n : Nat) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_LG_init) (initSpec p bn bf n) [] := by
  let L : TempEnv := createUndefTemps f_LG_init.fn_temps
  refine satisfies_internal_noVars_void ge _ f_LG_init _ _ (AtH L (data p bn bf n))
    (fun _ => ⟨L, FunctionEntry2.intro (by decide) (by decide) (by decide)
      (AllocVariables.nil _ _) rfl, fun hp h => ⟨rfl, rfl, h.2⟩⟩) ?_
  intro k e le hp hf m hd hag hP
  obtain ⟨he, hl, ⟨hn, hc⟩ | ⟨rfl, vm, hc⟩⟩ := hP
  · exact init_body_ok ge hcenv p hpw bn bf hsym_f n hn L k e le hp hf m hd hag ⟨he, hl, hc⟩
  · exact init_body_fresh ge hcenv p hpw bn bf hsym_f L vm k e le hp hf m hd hag ⟨he, hl, hc⟩

/-! ## Calls without arguments -/

omit hcenv hpw hsym_n hsym_f in
/-- `x = g();` (or `g();`) for a global function `g` meeting `S`, from an
    exactly known local state. -/
theorem triple_call_noargs (f : Function) (S : Sep.FunSpec) (optid : Option Ident) (fid : Ident)
    (fty : Ty) (fb : Block) (fd : FunDef) (L : TempEnv) (H : HProp) (Q : Sep.Assn)
    (hsym : Genv.findSymbol ge.genv_genv fid = some fb)
    (hfind : Genv.findFunct ge.genv_genv (.Vptr fb Integers.Ptrofs.zero) = some fd)
    (hacc : accessMode fty = .By_reference)
    (hty : typeOfFundef fd = .Tfunction S.tyargs S.tyres S.cc)
    (hclass : Cop.classifyFun fty = .f S.tyargs S.tyres S.cc) (htyargs : S.tyargs = [])
    (hsat : Sep.SatisfiesAt ge (FunctionEntry2 ge) fd S [])
    (hpre : ∀ hp, H hp → S.pre [] hp)
    (hpost : ∀ v hp, S.post v hp → Q emptyEnv (setOpttemp optid v L) hp) :
    Triple ge (FunctionEntry2 ge) f (AtH L H) (.Scall optid (.Evar fid fty) []) (.only Q) :=
  triple_call_at ge _ f S optid _ [] _ Q fb fd hfind hty hclass (fun e le hp m hP _ => by
    obtain ⟨rfl, rfl, hH⟩ := hP
    exact ⟨[], hp, Heap.emp, Heap.disjoint_emp_right _, (Heap.union_emp _).symm,
      eval_callee_global (PTree.gempty _) hsym hacc, htyargs ▸ EvalExprlist.nil, hpre hp hH, hsat,
      fun v h1' hp' _ => by rw [Heap.union_emp]; exact hpost v h1' hp'⟩)

omit hcenv hpw hsym_n hsym_f in
/-- `t + 1` for an `int` temporary `t` holding `n`. -/
theorem eval_incr {le : TempEnv} {m : Mem} {x : Ident} {n : Nat} (hx : le.get x = some (vint n)) :
    EvalExpr ge emptyEnv le m
      (.Ebinop .Oadd (.Etempvar x tint) (.Econst_int (Integers.Int.repr 1) tint) tint)
      (vint (n + 1)) :=
  EvalExpr.Ebinop .Oadd _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ hx) (EvalExpr.Econst_int _ _) (by
    simp only [typeof]
    rw [semBinop_add_int, repr_add]
    simp)

/-! ## The functions of the program (VST's `Gprog`) -/

/-- The global function symbols resolve to the program's functions. -/
structure Funs (ge : CGenv) : Type where
  bInit : Block
  bBump : Block
  bGet : Block
  bClient : Block
  sym_init : Genv.findSymbol ge.genv_genv _LG_init = some bInit
  find_init : Genv.findFunct ge.genv_genv (.Vptr bInit Integers.Ptrofs.zero)
    = some (.Internal f_LG_init)
  sym_bump : Genv.findSymbol ge.genv_genv _LG_bump = some bBump
  find_bump : Genv.findFunct ge.genv_genv (.Vptr bBump Integers.Ptrofs.zero)
    = some (.Internal f_LG_bump)
  sym_get : Genv.findSymbol ge.genv_genv _LG_get = some bGet
  find_get : Genv.findFunct ge.genv_genv (.Vptr bGet Integers.Ptrofs.zero)
    = some (.Internal f_LG_get)
  sym_client : Genv.findSymbol ge.genv_genv _client = some bClient
  find_client : Genv.findFunct ge.genv_genv (.Vptr bClient Integers.Ptrofs.zero)
    = some (.Internal f_client)

/-! ## `LG_bump` -/

include hcenv hpw hsym_n hsym_f in
/-- **`LG_bump` satisfies `bump_spec`** (VST's `body_bump`). -/
theorem bump_satisfies (G : Funs ge) (n : Nat) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_LG_bump) (bumpSpec p bn bf n) [] := by
  let L : TempEnv := createUndefTemps f_LG_bump.fn_temps
  have hentry : ∀ m : Mem, FunctionEntry2 ge f_LG_bump [] m emptyEnv L m :=
    fun _ => FunctionEntry2.intro (by decide) (by decide) (by decide) (AllocVariables.nil _ _) rfl
  refine (Classical.em (n < maxSigned)).elim (fun hn => ?_) (fun hn =>
    satisfies_internal_noVars_void ge _ f_LG_bump _ _ Sep.Assn.no
      (fun m => ⟨L, hentry m, fun hp h => absurd h.2.1 hn⟩) (triple_vacuous ge _ f_LG_bump _ _))
  refine satisfies_internal_noVars_void ge _ f_LG_bump _ _ (AtH L (data p bn bf n))
    (fun m => ⟨L, hentry m, fun hp h => ⟨rfl, rfl, h.2.2⟩⟩) ?_
  -- `LG_init();`
  refine triple_seq_only ge _ f_LG_bump
    (Q := AtH L (cells p bn bf (vint n) (.Vint Integers.Int.one) (vint n)))
    (triple_call_noargs ge f_LG_bump (initSpec p bn bf n) none _ _ G.bInit _ L _ _ G.sym_init G.find_init rfl
      rfl rfl rfl (init_satisfies ge hcenv p hpw bn bf hsym_f n) (fun hp h => ⟨rfl, h⟩)
      (fun v hp h => ⟨rfl, rfl, h.2⟩)) ?_
  let L1 := L.set _t'1 (vint n)
  let L2 := L1.set _t'2 (vint n)
  refine triple_seq_only ge _ f_LG_bump
    (Q := AtH L1 (cells p bn bf (vint (n + 1)) (.Vint Integers.Int.one) (vint n))) ?_ ?_
  · -- `t'1 = LG_n; LG_n = t'1 + 1;`
    refine triple_seq_only ge _ f_LG_bump
      (triple_set_atH ge _ f_LG_bump L _ _ _ (vint n) fun m hp hc hag =>
        eval_n ge p hpw bn bf hsym_n hc hag) ?_
    exact triple_assign_atE_front ge _ f_LG_bump emptyEnv L1 _ _ _ .Mint32 p bn
      Integers.Ptrofs.zero 0 (vint n) (vint (n + 1)) (vint (n + 1)) hpw rfl (by decide)
      (fun _ => lvalue_global (PTree.gempty _) hsym_n) (fun _ => eval_incr ge (PTree.gss _ _ _))
      (fun m => semCast_int m _)
  · -- `t'2 = LG_foo.m; LG_foo.m = t'2 + 1;`
    refine triple_seq_only ge _ f_LG_bump
      (triple_set_atH ge _ f_LG_bump L1 _ _ _ (vint n) fun m hp hc hag =>
        eval_m ge hcenv p hpw bn bf hsym_f hc hag) ?_
    rw [cells_m_front]
    exact triple_fallthrough ge _ f_LG_bump _ _ _ _
      (triple_assign_atE_front ge _ f_LG_bump emptyEnv L2 _ _ _ .Mint32 p bf _ 4 (vint n)
        (vint (n + 1)) (vint (n + 1)) hpw rfl (by decide) (fun _ => lvalue_m ge hcenv bf hsym_f)
        (fun _ => eval_incr ge (PTree.gss _ _ _)) (fun m => semCast_int m _))
      (fun e le hp h => ⟨h.1, Or.inl ⟨by unfold maxSigned at hn ⊢; omega,
        by rw [cells_m_front]; exact h.2.2⟩⟩)

/-! ## `LG_get` -/

include hcenv hpw hsym_n hsym_f in
/-- **`LG_get` satisfies `get_spec`** (VST's `body_get`). -/
theorem get_satisfies (G : Funs ge) (n : Nat) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_LG_get) (getSpec p bn bf n) [] := by
  let L : TempEnv := createUndefTemps f_LG_get.fn_temps
  refine satisfies_internal_noVars ge _ f_LG_get _ _ (AtH L (data p bn bf n))
    (fun _ => ⟨L, FunctionEntry2.intro (by decide) (by decide) (by decide)
      (AllocVariables.nil _ _) rfl, fun hp h => ⟨rfl, rfl, h.2⟩⟩) ?_
  -- `LG_init();`
  refine triple_seq_only ge _ f_LG_get (Q := AtH L (dataOk p bn bf n))
    (triple_call_noargs ge f_LG_get (initSpec p bn bf n) none _ _ G.bInit _ L _ _ G.sym_init
      G.find_init rfl rfl rfl rfl (init_satisfies ge hcenv p hpw bn bf hsym_f n)
      (fun hp h => ⟨rfl, h⟩) (fun v hp h => ⟨rfl, rfl, h⟩)) ?_
  -- `i = LG_n;`
  let L1 := L.set _i (vint n)
  refine triple_seq_only ge _ f_LG_get
    (triple_set_atH ge _ f_LG_get L _ _ _ (vint n) fun m hp hc hag =>
      eval_n ge p hpw bn bf hsym_n hc.2 hag) ?_
  -- `if (i & 1) return i; else return LG_foo.m;`: both are `n`
  refine triple_if ge _ f_LG_get _ (AtH L1 (dataOk p bn bf n)) (AtH L1 (dataOk p bn bf n)) _ _ _ _
    (fun e le hp m h _ => ?_) ?_ ?_
  · obtain ⟨rfl, rfl, hc⟩ := h
    refine ⟨_, _, EvalExpr.Ebinop .Oand _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (PTree.gss _ _ _))
      (EvalExpr.Econst_int _ _) rfl, rfl, ?_⟩
    split <;> exact ⟨rfl, rfl, hc⟩
  · exact triple_conseq ge _ f_LG_get
      (triple_return_atH ge _ f_LG_get L1 _ _ (vint n) (vint n)
        (fun _ _ _ _ => EvalExpr.Etempvar _ _ _ (PTree.gss _ _ _)) (fun m => semCast_int m _))
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x)
      (fun _ _ h => ⟨h.1, Or.inl h.2⟩)
  · let L2 := L1.set _t'1 (vint n)
    refine triple_seq_only ge _ f_LG_get
      (triple_set_atH ge _ f_LG_get L1 _ _ _ (vint n) fun m hp hc hag =>
        eval_m ge hcenv p hpw bn bf hsym_f hc.2 hag) ?_
    exact triple_conseq ge _ f_LG_get
      (triple_return_atH ge _ f_LG_get L2 _ _ (vint n) (vint n)
        (fun _ _ _ _ => EvalExpr.Etempvar _ _ _ (PTree.gss _ _ _)) (fun m => semCast_int m _))
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x)
      (fun _ _ h => ⟨h.1, Or.inl h.2⟩)

/-! ## `client` and `main` -/

include hcenv hpw hsym_n hsym_f in
/-- **`client` satisfies `client_spec`** (VST's `body_client`). -/
theorem client_satisfies (G : Funs ge) (n : Nat) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_client) (clientSpec p bn bf n) [] := by
  let L : TempEnv := createUndefTemps f_client.fn_temps
  have hentry : ∀ m : Mem, FunctionEntry2 ge f_client [] m emptyEnv L m :=
    fun _ => FunctionEntry2.intro (by decide) (by decide) (by decide) (AllocVariables.nil _ _) rfl
  refine (Classical.em (n < 1000000000)).elim (fun hn => ?_) (fun hn =>
    satisfies_internal_noVars ge _ f_client _ _ Sep.Assn.no
      (fun m => ⟨L, hentry m, fun hp h => absurd h.2.1 hn⟩) (triple_vacuous ge _ f_client _ _))
  refine satisfies_internal_noVars ge _ f_client _ _ (AtH L (data p bn bf n))
    (fun m => ⟨L, hentry m, fun hp h => ⟨rfl, rfl, h.2.2⟩⟩) ?_
  have hm : n < maxSigned ∧ n + 1 < maxSigned := by unfold maxSigned; omega
  -- `LG_bump(); LG_bump();`
  refine triple_seq_only ge _ f_client (Q := AtH L (data p bn bf (n + 1)))
    (triple_call_noargs ge f_client (bumpSpec p bn bf n) none _ _ G.bBump _ L _ _ G.sym_bump
      G.find_bump rfl rfl rfl rfl (bump_satisfies ge hcenv p hpw bn bf hsym_n hsym_f G n)
      (fun hp h => ⟨rfl, hm.1, h⟩) (fun v hp h => ⟨rfl, rfl, h⟩)) ?_
  refine triple_seq_only ge _ f_client (Q := AtH L (data p bn bf (n + 2)))
    (triple_call_noargs ge f_client (bumpSpec p bn bf (n + 1)) none _ _ G.bBump _ L _ _ G.sym_bump
      G.find_bump rfl rfl rfl rfl (bump_satisfies ge hcenv p hpw bn bf hsym_n hsym_f G (n + 1))
      (fun hp h => ⟨rfl, hm.2, h⟩) (fun v hp h => ⟨rfl, rfl, h⟩)) ?_
  -- `t'1 = LG_get(); return t'1;`
  let L1 := L.set _t'1 (vint (n + 2))
  refine triple_seq_only ge _ f_client (Q := AtH L1 (data p bn bf (n + 2)))
    (triple_call_noargs ge f_client (getSpec p bn bf (n + 2)) (some _t'1) _ _ G.bGet _ L _ _
      G.sym_get G.find_get rfl rfl rfl rfl
      (get_satisfies ge hcenv p hpw bn bf hsym_n hsym_f G (n + 2))
      (fun hp h => ⟨rfl, h⟩) (fun v hp h => by obtain ⟨rfl, h⟩ := h; exact ⟨rfl, rfl, h⟩)) ?_
  exact triple_return_atH ge _ f_client L1 _ _ (vint (n + 2)) (vint (n + 2))
    (fun _ _ _ _ => EvalExpr.Etempvar _ _ _ (PTree.gss _ _ _)) (fun m => semCast_int m _)

include hcenv hpw hsym_n hsym_f in
/-- **`main` satisfies `main_spec`** (VST's `body_main`): from the initial
    content of `LG`'s globals, `main` returns `5`. -/
theorem main_satisfies (G : Funs ge) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_main) (mainSpec p bn bf) [] := by
  let L : TempEnv := createUndefTemps f_main.fn_temps
  let L1 := L.set _t'1 (vint 5)
  refine satisfies_internal_noVars ge _ f_main _ _ (AtH L (data p bn bf 3))
    (fun _ => ⟨L, FunctionEntry2.intro (by decide) (by decide) (by decide)
      (AllocVariables.nil _ _) rfl, fun hp h => ⟨rfl, rfl, h.2⟩⟩) ?_
  refine Sep.triple_seq ge _ f_main _ Sep.Assn.no _ _ _ ?_ (Sep.triple_vacuous ge _ f_main _ _)
  refine triple_seq_only ge _ f_main (Q := AtH L1 (data p bn bf 5))
    (triple_call_noargs ge f_main (clientSpec p bn bf 3) (some _t'1) _ _ G.bClient _ L _ _
      G.sym_client G.find_client rfl rfl rfl rfl
      (client_satisfies ge hcenv p hpw bn bf hsym_n hsym_f G 3)
      (fun hp h => ⟨rfl, by decide, h⟩) (fun v hp h => by obtain ⟨rfl, h⟩ := h; exact ⟨rfl, rfl, h⟩))
    ?_
  exact triple_return_atH ge _ f_main L1 _ _ (vint 5) (vint 5)
    (fun _ _ _ _ => EvalExpr.Etempvar _ _ _ (PTree.gss _ _ _)) (fun m => semCast_int m _)

end

end VST.Verif.Libglob
