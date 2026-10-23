/-
  **Phase-9 Step 7 — calls through function pointers.**

  Exercises `CCLib.logic.FunPtr` on `test/lean/funcptr.c`, in the two shapes that
  matter for zlib:

  * `apply(g, x)` calls a function pointer passed as an argument.  Its proof is
    **higher-order**: it is parameterised over an arbitrary callee specification
    `S`, so it says "`apply` returns whatever `g` returns, on `g`'s own
    precondition" without knowing anything about `g`.  This is the case function
    pointers exist for, and the one `triple_call_local_ex` was added to reach —
    an abstract `S` cannot name its own return value.

  * `callf(o, x)` loads the pointer out of a **struct field** and calls `(*p)(x)`.
    That is character-for-character zlib's
    `ZALLOC(strm,…) = (*((strm)->zalloc))((strm)->opaque, …)`.

  `add1` is proved too, so `apply` can be instantiated at a *concrete* callee and
  the higher-order theorem is shown non-vacuous.
-/
import GenFuncPtr
import CCLib
open CC CC.Sep CC.HProp
open Funcptr   -- the generated module now lives in its own namespace

namespace FuncPtrSep

/-! ## `add1` — a concrete callee -/

def add1Spec (xv : Integers.Int) : Sep.FunSpec where
  tyargs := [tint]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vint xv] ∧ emp hp
  post := fun v hp => v = .Vint (Integers.Int.add xv (Integers.Int.repr 1)) ∧ emp hp
  measure := fun _ => 0

theorem add1_entry_wf :
    listNorepet (varNames f_add1.fn_vars)
    ∧ listNorepet (varNames f_add1.fn_params)
    ∧ listDisjoint (varNames f_add1.fn_params) (varNames f_add1.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem add1_satisfies (ge : CGenv) (xv : Integers.Int) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_add1) (add1Spec xv)
      [.Vint xv] := by
  obtain ⟨hnv, hnp, hdisj⟩ := add1_entry_wf
  refine Sep.satisfies_internal_noVars ge (FunctionEntry2 ge) f_add1 _ _
    (Sep.LocalSt emptyEnv [(_x, .Vint xv)] emp) (fun m => ?_) ?_
  · refine ⟨PTree.set _x (.Vint xv) (createUndefTemps f_add1.fn_temps),
            FunctionEntry2.intro hnv hnp hdisj (AllocVariables.nil _ _) rfl,
            fun hp hpre => ?_⟩
    exact ⟨rfl, Sep.TempsHold_cons (PTree.gss _ _ _) (Sep.TempsHold_nil _), hpre.2⟩
  · refine Sep.triple_return_local ge (FunctionEntry2 ge) f_add1 _ _ _ _
      (.Vint (Integers.Int.add xv (Integers.Int.repr 1)))
      (.Vint (Integers.Int.add xv (Integers.Int.repr 1)))
      (fun le m hp hT _ _ => ?_) (fun _ => rfl) (fun hp hH => ⟨rfl, hH⟩)
    refine EvalExpr.Ebinop .Oadd _ _ _ (.Vint xv) (.Vint (Integers.Int.repr 1)) _
      (EvalExpr.Etempvar _x tint _ (hT.get (by temps_mem)))
      (EvalExpr.Econst_int _ _) ?_
    simp only [typeof]
    exact CC.semBinop_add_int _ _ _ _

/-! ## `apply` — the higher-order case

Parameterised over an arbitrary callee specification.  Note what the statement
does *not* say: nothing about what `g` computes, only that whatever it promises,
`apply` delivers. -/

/-- `apply`'s specification, relative to the callee's.  `xv` is fixed because the
    callee's precondition is stated at a concrete argument list. -/
def applySpec (S : Sep.FunSpec) (fb : Block) (xv : Integers.Int) : Sep.FunSpec where
  tyargs := [tptr (Ty.Tfunction [tint] tint cc_default), tint]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp =>
    vargs = [.Vptr fb Integers.Ptrofs.zero, .Vint xv] ∧ S.pre [.Vint xv] hp
  post := fun v hp => S.post v hp
  measure := fun _ => 0

theorem apply_entry_wf :
    listNorepet (varNames f_apply.fn_vars)
    ∧ listNorepet (varNames f_apply.fn_params)
    ∧ listDisjoint (varNames f_apply.fn_params) (varNames f_apply.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **`apply` is correct for every callee that meets a specification.**  The
    callee is resolved from the temporary holding the pointer; no `Evar` and no
    global name is involved anywhere. -/
theorem apply_satisfies (ge : CGenv) (S : Sep.FunSpec)
    (fb : Block) (fd : FunDef) (xv : Integers.Int)
    (hspec : ∀ vs, Sep.SatisfiesAt ge (FunctionEntry2 ge) fd S vs)
    (hfind : Sep.FuncPtr ge fb fd)
    (hsig : S.tyargs = [tint] ∧ S.tyres = tint ∧ S.cc = cc_default)
    (hty : typeOfFundef fd = .Tfunction S.tyargs S.tyres S.cc)
    -- The callee actually returns an `int`.  Clight's semantics does not enforce
    -- that a returned value matches the declared type, so the cast in `return
    -- t'1;` needs it — the same obligation VST puts on a funspec.
    (hval : ∀ v h, S.post v h → ∃ n : Integers.Int, v = .Vint n) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_apply) (applySpec S fb xv)
      [.Vptr fb Integers.Ptrofs.zero, .Vint xv] := by
  obtain ⟨hnv, hnp, hdisj⟩ := apply_entry_wf
  obtain ⟨hta, htr, htc⟩ := hsig
  refine Sep.satisfies_internal_noVars ge (FunctionEntry2 ge) f_apply _ _
    (Sep.LocalSt emptyEnv
      [(_g, .Vptr fb Integers.Ptrofs.zero), (_x, .Vint xv)] (S.pre [.Vint xv] ∗ emp))
    (fun m => ?_) ?_
  · refine ⟨PTree.set _x (.Vint xv)
              (PTree.set _g (.Vptr fb Integers.Ptrofs.zero)
                (createUndefTemps f_apply.fn_temps)),
            FunctionEntry2.intro hnv hnp hdisj (AllocVariables.nil _ _) rfl,
            fun hp hpre => ?_⟩
    refine ⟨rfl, Sep.TempsHold_cons ?_ (Sep.TempsHold_cons (PTree.gss _ _ _)
              (Sep.TempsHold_nil _)), ?_⟩
    · exact (PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _)
    · exact emp_sep _ _ hpre.2
  · refine Sep.triple_seq_fwd ge (FunctionEntry2 ge) f_apply _
      (fun e le hp => ∃ n : Integers.Int,
          e = emptyEnv
          ∧ Sep.TempsHold [(_t'1, .Vint n), (_g, .Vptr fb Integers.Ptrofs.zero),
                           (_x, .Vint xv)] le
          ∧ (S.post (.Vint n) ∗ emp) hp) _ _ _ ?_ ?_
    -- the indirect call, then narrow its existential to an `int` result
    · refine Sep.triple_conseq ge (FunctionEntry2 ge) f_apply
        (Sep.triple_call_local_ex ge (FunctionEntry2 ge) f_apply S _t'1 _ _ _ _
          [(_g, .Vptr fb Integers.Ptrofs.zero), (_x, .Vint xv)]
          _ emp [.Vint xv] fb fd hspec hfind hty ?_ (by temps_mem) (by temps_ne)
          (fun le m hT => Sep.eval_callee_temp (hT.get (by temps_mem)))
          (fun le m hT => ?_) (fun h hh => hh))
        (fun _ _ _ x => x) (fun e le hp hx => ?_) (fun _ _ _ x => x)
        (fun _ _ _ x => x) (fun _ _ x => x)
      · simp only [typeof, hta, htr, htc]
        exact Sep.classifyFun_ptr _ _ _
      · rw [hta]
        exact EvalExprlist.cons _ _ _ _ _ _ _
          (EvalExpr.Etempvar _x tint _
            (hT.get (by temps_mem : (_x, Val.Vint xv) ∈ _))) rfl EvalExprlist.nil
      · obtain ⟨v, he, hT, hpost⟩ := hx
        obtain ⟨h1, h2, hd, heq, hp1, hp2⟩ := hpost
        obtain ⟨n, hn⟩ := hval v h1 hp1
        subst hn
        exact ⟨n, he, hT, h1, h2, hd, heq, hp1, hp2⟩
    -- `return t'1;`
    · refine Sep.triple_exists ge (FunctionEntry2 ge) f_apply _ _ _ (fun n => ?_)
      exact Sep.triple_return_local ge (FunctionEntry2 ge) f_apply
        [(_t'1, .Vint n), (_g, .Vptr fb Integers.Ptrofs.zero), (_x, .Vint xv)]
        (S.post (.Vint n) ∗ emp) _ (applySpec S fb xv).post (.Vint n) (.Vint n)
        (fun le m hp hT _ _ => EvalExpr.Etempvar _t'1 tint _ (hT.get (by temps_mem)))
        (fun _ => rfl) (fun hp hH => sep_emp _ _ hH)

/-! ## `callf` — zlib's shape

`(*(o->f))(x)`: load a function pointer out of a struct field, then call through
the dereferenced pointer.  Character for character,

    #define ZALLOC(strm, items, size) \
        (*((strm)->zalloc))((strm)->opaque, (items), (size))

The footprint is *only* the `f` field — the `tag` field is never mentioned, which
is the point of owning fields separately. -/

/-- The generated composite for `struct ops`, and the offset of its `f` field.
    Kernel `decide`, since Step 10 made `identOfString` reducible. -/
theorem composite_ops :
    prog.prog_comp_env.get _ops = some
      { co_su := SU.Struct,
        co_members := [Member.Member_plain _f (tptr (Ty.Tfunction [tint] tint cc_default)),
                       Member.Member_plain _tag tint],
        co_attr := noattr, co_sizeof := 16, co_alignof := 8, co_rank := 0 } := by
  decide

theorem offset_f :
    fieldOffset prog.prog_comp_env _f
      [Member.Member_plain _f (tptr (Ty.Tfunction [tint] tint cc_default)),
       Member.Member_plain _tag tint] = .OK (0, .Full) := by
  decide

theorem callf_entry_wf :
    listNorepet (varNames f_callf.fn_vars)
    ∧ listNorepet (varNames f_callf.fn_params)
    ∧ listDisjoint (varNames f_callf.fn_params) (varNames f_callf.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- Reading `o->f`, the function-pointer field.  `Mptr` is `Mint64` here and
    `Val.loadResult Mint64 (Vptr …) = Vptr …` because `Archi.ptr64`, so the
    pointer survives the load. -/
theorem read_field_f (ge : CGenv) (e : Env) (le : TempEnv) (m : Mem)
    (pm : Permission) (b : Block) (ofs : Integers.Ptrofs) (fb : Block) (h : Heap)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hpr : permOrder pm .Readable = true)
    (ho : le.get _o = some (.Vptr b ofs))
    (hm : fieldAt Mptr pm b (Integers.Ptrofs.unsigned ofs) 0
            (.Vptr fb Integers.Ptrofs.zero) h)
    (hag : Heap.Agrees h m)
    (hno : ofs.toNat + 0 < 18446744073709551616) :
    EvalExpr ge e le m
      (.Efield (.Ederef (.Etempvar _o (tptr (Ty.Tstruct _ops noattr)))
                 (Ty.Tstruct _ops noattr)) _f
        (tptr (Ty.Tfunction [tint] tint cc_default)))
      (.Vptr fb Integers.Ptrofs.zero) := by
  have hlr : Val.loadResult Mptr (.Vptr fb Integers.Ptrofs.zero)
           = .Vptr fb Integers.Ptrofs.zero := by
    simp [Mptr, Val.loadResult, Archi.ptr64]
  rw [← hlr]
  refine Sep.eval_field_scalar (sid := _ops) (att := noattr) (delta := 0)
    rfl hpr rfl (hcenv ▸ composite_ops) (hcenv ▸ offset_f) hm hag
    (EvalExpr.Elvalue _ b ofs .Full _
      (EvalLvalue.Ederef _ _ b ofs (EvalExpr.Etempvar _o _ _ ho)) (DerefLoc.copy rfl))
    (CC.ptrofs_add_unsigned ofs 0 hno)

/-- `callf`'s specification, again relative to the callee's: the caller lends the
    `f` field and the callee's precondition, and gets the field back. -/
def callfSpec (S : Sep.FunSpec) (pm : Permission) (b : Block)
    (ofs : Integers.Ptrofs) (fb : Block) (xv : Integers.Int) : Sep.FunSpec where
  tyargs := [tptr (Ty.Tstruct _ops noattr), tint]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp =>
    vargs = [.Vptr b ofs, .Vint xv]
    ∧ (fieldAt Mptr pm b (Integers.Ptrofs.unsigned ofs) 0 (.Vptr fb Integers.Ptrofs.zero)
        ∗ S.pre [.Vint xv]) hp
  post := fun v hp =>
    (S.post v ∗ fieldAt Mptr pm b (Integers.Ptrofs.unsigned ofs) 0
                  (.Vptr fb Integers.Ptrofs.zero)) hp
  measure := fun _ => 0

/-- **zlib's indirect-call shape, proved.**  The `f` field is lent to the call and
    handed back; the `tag` field never appears. -/
theorem callf_satisfies (ge : CGenv) (S : Sep.FunSpec) (pm : Permission) (b : Block)
    (ofs : Integers.Ptrofs) (fb : Block) (fd : FunDef) (xv : Integers.Int)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hpr : permOrder pm .Readable = true)
    (hspec : ∀ vs, Sep.SatisfiesAt ge (FunctionEntry2 ge) fd S vs)
    (hfind : Sep.FuncPtr ge fb fd)
    (hsig : S.tyargs = [tint] ∧ S.tyres = tint ∧ S.cc = cc_default)
    (hty : typeOfFundef fd = .Tfunction S.tyargs S.tyres S.cc)
    (hval : ∀ v h, S.post v h → ∃ n : Integers.Int, v = .Vint n)
    (hno : ofs.toNat + 0 < 18446744073709551616) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_callf)
      (callfSpec S pm b ofs fb xv) [.Vptr b ofs, .Vint xv] := by
  obtain ⟨hnv, hnp, hdisj⟩ := callf_entry_wf
  obtain ⟨hta, htr, htc⟩ := hsig
  refine Sep.satisfies_internal_noVars ge (FunctionEntry2 ge) f_callf _ _
    (Sep.LocalSt emptyEnv [(_o, .Vptr b ofs), (_x, .Vint xv)]
      (fieldAt Mptr pm b (Integers.Ptrofs.unsigned ofs) 0 (.Vptr fb Integers.Ptrofs.zero)
        ∗ S.pre [.Vint xv]))
    (fun m => ?_) ?_
  · refine ⟨PTree.set _x (.Vint xv)
              (PTree.set _o (.Vptr b ofs) (createUndefTemps f_callf.fn_temps)),
            FunctionEntry2.intro hnv hnp hdisj (AllocVariables.nil _ _) rfl,
            fun hp hpre => ?_⟩
    exact ⟨rfl, Sep.TempsHold_cons ((PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _))
              (Sep.TempsHold_cons (PTree.gss _ _ _) (Sep.TempsHold_nil _)), hpre.2⟩
  · refine Sep.triple_seq_fwd ge (FunctionEntry2 ge) f_callf _
      (fun e le hp => ∃ n : Integers.Int,
          e = emptyEnv
          ∧ Sep.TempsHold [(_t'1, .Vint n), (_t'2, .Vptr fb Integers.Ptrofs.zero),
                           (_o, .Vptr b ofs), (_x, .Vint xv)] le
          ∧ (S.post (.Vint n)
              ∗ fieldAt Mptr pm b (Integers.Ptrofs.unsigned ofs) 0
                  (.Vptr fb Integers.Ptrofs.zero)) hp) _ _ _ ?_ ?_
    · -- `t'2 = o->f;`  then  `t'1 = (*t'2)(x);`
      refine Sep.triple_seq_fwd ge (FunctionEntry2 ge) f_callf _
        (Sep.LocalSt emptyEnv
          [(_t'2, .Vptr fb Integers.Ptrofs.zero), (_o, .Vptr b ofs), (_x, .Vint xv)]
          (fieldAt Mptr pm b (Integers.Ptrofs.unsigned ofs) 0
             (.Vptr fb Integers.Ptrofs.zero) ∗ S.pre [.Vint xv])) _ _ _ ?_ ?_
      · refine Sep.triple_set_local ge (FunctionEntry2 ge) f_callf _ _ _ _ _ _
          (.Vptr fb Integers.Ptrofs.zero) (by temps_mem) (by temps_ne)
          (fun le m hp hT hH hag => ?_)
        obtain ⟨h1, h2, hd, heq, hf, _⟩ := hH
        subst heq
        exact read_field_f ge emptyEnv le m pm b ofs fb h1 hcenv hpr
          (hT.get (by temps_mem : (_o, Val.Vptr b ofs) ∈ _)) hf
          (Heap.Agrees_union_left hag) hno
      · -- the call, through the *dereferenced* pointer
        refine Sep.triple_conseq ge (FunctionEntry2 ge) f_callf
          -- `l₀` must be given explicitly: `triple_conseq` leaves the callee's
          -- precondition free, so nothing in the goal pins the tracked list.
          (Sep.triple_call_local_ex ge (FunctionEntry2 ge) f_callf S _t'1 _ _ emptyEnv
            [(_t'2, .Vptr fb Integers.Ptrofs.zero), (_o, .Vptr b ofs), (_x, .Vint xv)]
            [(_t'2, .Vptr fb Integers.Ptrofs.zero), (_o, .Vptr b ofs), (_x, .Vint xv)]
            (S.pre [.Vint xv])
            (fieldAt Mptr pm b (Integers.Ptrofs.unsigned ofs) 0
               (.Vptr fb Integers.Ptrofs.zero))
            [.Vint xv] fb fd hspec hfind hty ?_ (by temps_mem) (by temps_ne)
            (fun le m hT => Sep.eval_callee_deref
              (Sep.eval_callee_temp
                (hT.get (by temps_mem : (_t'2, Val.Vptr fb Integers.Ptrofs.zero) ∈ _))))
            (fun le m hT => ?_) (fun h hh => hh))
          (fun e le hp hx => ?_) (fun e le hp hx => ?_) (fun _ _ _ x => x)
          (fun _ _ _ x => x) (fun _ _ x => x)
        · simp only [typeof, hta, htr, htc]
          exact Sep.classifyFun_fun _ _ _
        · rw [hta]
          exact EvalExprlist.cons _ _ _ _ _ _ _
            (EvalExpr.Etempvar _x tint _
              (hT.get (by temps_mem : (_x, Val.Vint xv) ∈ _))) rfl EvalExprlist.nil
        · exact ⟨hx.1, hx.2.1, sep_comm _ _ _ hx.2.2⟩
        · obtain ⟨v, he, hT, hpost⟩ := hx
          obtain ⟨h1, h2, hd, heq, hp1, hp2⟩ := hpost
          obtain ⟨n, hn⟩ := hval v h1 hp1
          subst hn
          exact ⟨n, he, hT, h1, h2, hd, heq, hp1, hp2⟩
    · refine Sep.triple_exists ge (FunctionEntry2 ge) f_callf _ _ _ (fun n => ?_)
      exact Sep.triple_return_local ge (FunctionEntry2 ge) f_callf
        [(_t'1, .Vint n), (_t'2, .Vptr fb Integers.Ptrofs.zero),
         (_o, .Vptr b ofs), (_x, .Vint xv)]
        (S.post (.Vint n) ∗ fieldAt Mptr pm b (Integers.Ptrofs.unsigned ofs) 0
           (.Vptr fb Integers.Ptrofs.zero))
        _ (callfSpec S pm b ofs fb xv).post (.Vint n) (.Vint n)
        (fun le m hp hT _ _ => EvalExpr.Etempvar _t'1 tint _ (hT.get (by temps_mem)))
        (fun _ => rfl) (fun hp hH => hH)

/-! ## Non-vacuity

`apply_satisfies` and `callf_satisfies` are universally quantified over the
callee's specification, so on their own they say nothing about any *particular*
program.  These instantiate them at `add1`, whose specification is proved above —
so both higher-order theorems are shown to have at least one inhabitant, and the
`hval` / `hsig` side conditions are shown to be dischargeable rather than
vacuously restrictive. -/

/-- `add1` meets its specification at *every* argument list — trivially at the
    wrong ones, where the precondition already pins `vargs`.  `triple_call` asks
    for this form, so it is worth having explicitly. -/
theorem add1_satisfies_all (ge : CGenv) (xv : Integers.Int) :
    ∀ vs, Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_add1) (add1Spec xv) vs := by
  intro vs k m hp hf hk hpre hd hag
  obtain ⟨hvs, hemp⟩ := hpre
  subst hvs
  exact add1_satisfies ge xv k m hp hf hk ⟨rfl, hemp⟩ hd hag

theorem add1_returns_int (xv : Integers.Int) :
    ∀ v h, (add1Spec xv).post v h → ∃ n : Integers.Int, v = .Vint n :=
  fun _ _ hp => ⟨_, hp.1⟩

theorem add1_sig (xv : Integers.Int) :
    (add1Spec xv).tyargs = [tint] ∧ (add1Spec xv).tyres = tint
    ∧ (add1Spec xv).cc = cc_default := ⟨rfl, rfl, rfl⟩

/-- `apply(add1, x)` returns `x + 1`. -/
theorem apply_add1 (ge : CGenv) (fb : Block) (xv : Integers.Int)
    (hfind : Sep.FuncPtr ge fb (.Internal f_add1)) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_apply)
      (applySpec (add1Spec xv) fb xv) [.Vptr fb Integers.Ptrofs.zero, .Vint xv] :=
  apply_satisfies ge (add1Spec xv) fb (.Internal f_add1) xv
    (add1_satisfies_all ge xv) hfind (add1_sig xv) rfl (add1_returns_int xv)

/-- …and so does `callf(o, x)` when `o->f` is `add1` — zlib's shape, at a concrete
    callee. -/
theorem callf_add1 (ge : CGenv) (pm : Permission) (b : Block)
    (ofs : Integers.Ptrofs) (fb : Block) (xv : Integers.Int)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hpr : permOrder pm .Readable = true)
    (hfind : Sep.FuncPtr ge fb (.Internal f_add1))
    (hno : ofs.toNat + 0 < 18446744073709551616) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_callf)
      (callfSpec (add1Spec xv) pm b ofs fb xv) [.Vptr b ofs, .Vint xv] :=
  callf_satisfies ge (add1Spec xv) pm b ofs fb (.Internal f_add1) xv hcenv hpr
    (add1_satisfies_all ge xv) hfind (add1_sig xv) rfl (add1_returns_int xv) hno

/-- The `funcPtrAt` resource is satisfiable: a cell holding a resolvable function
    pointer exists whenever the address is `Mptr`-aligned. -/
theorem funcPtrAt_satisfiable (ge : CGenv) (fd : FunDef) (pm : Permission)
    (b : Block) (ofs : _root_.Int) (fb : Block)
    (halign : ofs % alignChunk Mptr = 0) (hfind : Sep.FuncPtr ge fb fd) :
    ∃ h, Sep.funcPtrAt ge fd pm b ofs h := by
  obtain ⟨h, hh⟩ :=
    bytesPtsTo_exists b pm (encodeVal Mptr (.Vptr fb Integers.Ptrofs.zero)) ofs
  exact ⟨h, fb, h, Heap.emp, Heap.disjoint_emp_right h, (Heap.union_emp h).symm,
         pure_sep_intro halign hh, ⟨hfind, rfl⟩⟩

end FuncPtrSep
