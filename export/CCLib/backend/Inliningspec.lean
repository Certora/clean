/-
  RTL function inlining: relational specification — port of
  `backend/Inliningspec.v`, part 4: soundness of the function environment
  (`funenv_program_compat`), the specification of the translation of a
  function (`tr_function`) and `transf_function_spec`.
-/
import CCLib.backend.InliningspecExpand
import CCLib.common.GlobalenvsTransf

namespace CC
namespace Inlining

open Op RTL

section FUNENV
variable {Info : Type} (inliningAnalysis : RTL.Program → Info)
  (shouldInline : Info → Ident → RTL.Function → Bool)

theorem addGlobdef_compat (io : Info) :
    ∀ (l : List (Ident × GlobDef RTL.Fundef Unit)) (dm : PTree (GlobDef RTL.Fundef Unit))
      (fenv : Funenv),
    (∀ id f, fenv.get id = some f → dm.get id = some (.Gfun (.Internal f))) →
    ∀ id f, (l.foldl (addGlobdef shouldInline io) fenv).get id = some f →
      (l.foldl (fun m idg => m.set idg.1 idg.2) dm).get id = some (.Gfun (.Internal f))
  | [], _, _, h => h
  | (id0, g) :: l, dm, fenv, h => by
    apply addGlobdef_compat io l
    intro id f hf
    have key : ∀ fe' : Funenv, (∀ id f, fe'.get id = some f → dm.get id = some (.Gfun (.Internal f))) →
        (fe'.remove id0).get id = some f → (dm.set id0 g).get id = some (.Gfun (.Internal f)) := by
      intro fe' h' hf'
      by_cases e : id0 = id
      · subst e; simp at hf'
      · rw [PTree.gro _ _ _ e] at hf'
        rw [PTree.gso _ _ _ _ e]
        exact h' _ _ hf'
    match g with
    | .Gfun (.Internal f1) =>
      simp only [addGlobdef] at hf
      split at hf
      · show (dm.set id0 (.Gfun (.Internal f1))).get id = _
        rw [PTree.gsspec] at hf
        rw [PTree.gsspec]
        split at hf
        · cases hf; simp [*]
        · rw [if_neg (by assumption)]; exact h _ _ hf
      · exact key fenv h hf
    | .Gfun (.External ef) => exact key fenv h hf
    | .Gvar v => exact key fenv h hf

/-- `Inliningspec.funenv_program_compat` -/
theorem funenv_program_compat (p : RTL.Program) :
    FenvCompat p (funenvProgram inliningAnalysis shouldInline p) := by
  intro id f h
  rw [ASTProgram.defmap_eq]
  exact addGlobdef_compat shouldInline _ p.prog_defs PTree.empty PTree.empty
    (fun _ _ h => by simp at h) id f h

end FUNENV

/-- `Inliningspec.tr_function` -/
inductive TrFunction (p : RTL.Program) : RTL.Function → RTL.Function → Prop where
  | intro (fenv : Funenv) (f f' : RTL.Function) (ctx : Context) :
      FenvCompat p fenv →
      TrFunbody fenv f'.fn_stacksize ctx f f'.fn_code →
      ctx.dstk = 0 →
      ctx.retinfo = none →
      f'.fn_sig = f.fn_sig →
      f'.fn_params = sregs ctx f.fn_params →
      f'.fn_entrypoint = spc ctx f.fn_entrypoint →
      0 ≤ f'.fn_stacksize →
      f'.fn_stacksize < Integers.Ptrofs.max_unsigned →
      TrFunction p f f'

theorem expandFunction_eq (fenv : Funenv) (f : RTL.Function) :
    (expandFunction fenv f).run initstate =
      (initcontext initstate.st_nextnode initstate.st_nextreg (maxRegFunction f) f.fn_stacksize,
       (expandCfg fenv (initcontext initstate.st_nextnode initstate.st_nextreg (maxRegFunction f)
          f.fn_stacksize) f (reserved initstate f)).2) := rfl

/-- `Inliningspec.transf_function_spec` -/
theorem transf_function_spec {Info : Type} (inliningAnalysis : RTL.Program → Info)
    (shouldInline : Info → Ident → RTL.Function → Bool) (cunit : RTL.Program)
    {f f' : RTL.Function}
    (h : transfFunction (funenvProgram inliningAnalysis shouldInline cunit) f = .OK f') :
    TrFunction cunit f f' := by
  let fenv := funenvProgram inliningAnalysis shouldInline cunit
  let ctx := initcontext initstate.st_nextnode initstate.st_nextreg (maxRegFunction f) f.fn_stacksize
  let s' := (expandCfg fenv ctx f (reserved initstate f)).2
  have E : transfFunction fenv f =
      if s'.st_stksize < Integers.Ptrofs.max_unsigned then
        .OK { fn_sig := f.fn_sig, fn_params := sregs ctx f.fn_params, fn_stacksize := s'.st_stksize,
              fn_code := s'.st_code, fn_entrypoint := spc ctx f.fn_entrypoint }
      else .Error "Inlining: stack too big" := rfl
  rw [E] at h
  split at h
  · next hlt =>
    cases h
    have I := (expandCfgFuel_recIncr (sizeFenv fenv)).incr fenv ctx f (reserved initstate f)
    have I0 := reserved_incr initstate f
    have K : (0 : Z) ≤ s'.st_stksize := Int.le_trans I0.stksize I.stksize
    refine .intro fenv f _ ctx (funenv_program_compat inliningAnalysis shouldInline cunit) ?_
      rfl rfl rfl rfl rfl K hlt
    refine expand_cfg_spec fenv s'.st_stksize fenv fenv ctx f (reserved initstate f) s'.st_code
      (fun _ _ h => h) ?_ rfl ?_ (Int.le_max_right _ _) rfl (Int.dvd_zero _) (Int.le_refl _)
      (Int.le_refl _) (fun _ _ _ => rfl)
    · show Positive.add .xH (maxPcFunction f) ≤ Positive.add .xH (maxPcFunction f)
      exact Nat.le_refl _
    · show Positive.add .xH (maxRegFunction f) ≤ Positive.add .xH (maxRegFunction f)
      exact Nat.le_refl _
  · cases h

end Inlining
end CC
