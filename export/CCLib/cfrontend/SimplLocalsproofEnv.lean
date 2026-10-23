/-
  Pulling local scalar variables into temporaries: semantic preservation —
  port of `cfrontend/SimplLocalsproof.v`, part 1: global environments, the
  matching between environments before and after the transformation
  (`match_var`, `match_envs`) and its invariance lemmas, properties of cast
  values, correctness of `make_cast` and of the debug annotations, and the
  properties of `cenv_for` (`compat_cenv`, …).

  Differences from Rocq:
  * whole-program statement: the hypothesis is `transfProgram opts prog = .OK
    tprog` rather than CompCert's linking-aware `match_prog`;
  * the OCaml parameter `Compopts.debug` is the field `opts.debug`; every
    lemma about debug annotations is proved for both values;
  * `VSet` is a list, so `VSet.In` is replaced by `VSet.mem _ _ = true`.
-/
import CCLib.cfrontend.SimplLocals
import CCLib.common.GlobalenvsTransf
import CCLib.cfrontend.ClightBehaviors
import CCLib.cfrontend.CopTheory
import CCLib.common.EventsInject
import CCLib.common.MemoryInjections
import CCLib.common.MemoryUnchanged
import CCLib.cfrontend.CshmgenproofOps

namespace CC
namespace SimplLocals

open Smallstep

/-! ## Global environments -/

section GENV
variable {opts : Options} {prog tprog : Program} (TRANSF : transfProgram opts prog = .OK tprog)
include TRANSF

/-- The underlying generic programs are related by the transformation. -/
theorem transf_program_match :
    MatchProgram (fun f tf => transfFundef opts f = .OK tf) Eq prog.toAST tprog.toAST := by
  unfold transfProgram at TRANSF
  split at TRANSF
  · cases TRANSF
  · rename_i p1 hp1
    cases TRANSF
    exact match_transform_partial_program hp1

/-- `SimplLocalsproof.comp_env_preserved` -/
theorem comp_env_preserved : tprog.prog_comp_env = prog.prog_comp_env := by
  unfold transfProgram at TRANSF
  split at TRANSF
  · cases TRANSF
  · cases TRANSF; rfl

theorem genv_cenv_preserved : tprog.globalenv.genv_cenv = prog.globalenv.genv_cenv :=
  comp_env_preserved TRANSF

/-- `SimplLocalsproof.symbols_preserved` -/
theorem symbols_preserved (s : Ident) :
    Genv.findSymbol tprog.globalenv.genv_genv s = Genv.findSymbol prog.globalenv.genv_genv s :=
  (transf_program_match TRANSF).find_symbol s

/-- `SimplLocalsproof.senv_preserved` (an equality of symbol environments). -/
theorem senv_preserved :
    Genv.toSenv tprog.globalenv.genv_genv = Genv.toSenv prog.globalenv.genv_genv :=
  (transf_program_match TRANSF).senv

/-- `SimplLocalsproof.functions_translated` -/
theorem functions_translated {v : Val} {f : FunDef}
    (h : Genv.findFunct prog.globalenv.genv_genv v = some f) :
    ∃ tf, Genv.findFunct tprog.globalenv.genv_genv v = some tf ∧ transfFundef opts f = .OK tf :=
  (transf_program_match TRANSF).find_funct h

/-- `SimplLocalsproof.function_ptr_translated` -/
theorem function_ptr_translated {b : Block} {f : FunDef}
    (h : Genv.findFunctPtr prog.globalenv.genv_genv b = some f) :
    ∃ tf, Genv.findFunctPtr tprog.globalenv.genv_genv b = some tf ∧ transfFundef opts f = .OK tf :=
  (transf_program_match TRANSF).find_funct_ptr h

end GENV

/-- `SimplLocalsproof.type_of_fundef_preserved` -/
theorem type_of_fundef_preserved {opts : Options} {fd tfd : FunDef}
    (h : transfFundef opts fd = .OK tfd) : typeOfFundef tfd = typeOfFundef fd := by
  cases fd with
  | Internal f =>
    simp only [transfFundef] at h
    split at h
    · rename_i tf htf
      cases h
      obtain ⟨h1, h2, h3⟩ := transfFunction_sig htf
      simp only [typeOfFundef, typeOfFunction, h1, h2, h3]
    · cases h
  | External ef targs tres cc => simp only [transfFundef] at h; cases h; rfl

/-! ## Matching between environments before and after -/

/-- `SimplLocalsproof.match_var` -/
inductive MatchVar (f : Val.Meminj) (cenv : Compilenv) (e : Env) (m : Mem) (te : Env)
    (tle : TempEnv) (id : Ident) : Prop where
  | lifted (b ty chunk v tv) :
      e.get id = some (b, ty) → te.get id = none → VSet.mem id cenv = true →
      f b = none → accessMode ty = .By_value chunk → Mem.load chunk m b 0 = some v →
      tle.get id = some tv → Val.Inject f v tv →
      MatchVar f cenv e m te tle id
  | not_lifted (b ty b') :
      e.get id = some (b, ty) → te.get id = some (b', ty) → VSet.mem id cenv = false →
      f b = some (b', 0) →
      MatchVar f cenv e m te tle id
  | not_local :
      e.get id = none → te.get id = none → VSet.mem id cenv = false →
      MatchVar f cenv e m te tle id

/-- `SimplLocalsproof.match_envs` -/
structure MatchEnvs (f : Val.Meminj) (cenv : Compilenv) (e : Env) (le : TempEnv) (m : Mem)
    (lo hi : Block) (te : Env) (tle : TempEnv) (tlo thi : Block) : Prop where
  me_vars : ∀ id, MatchVar f cenv e m te tle id
  me_temps : ∀ id v, le.get id = some v →
    (∃ tv, tle.get id = some tv ∧ Val.Inject f v tv) ∧ (VSet.mem id cenv = true → v = .Vundef)
  me_inj : ∀ id1 b1 ty1 id2 b2 ty2, e.get id1 = some (b1, ty1) → e.get id2 = some (b2, ty2) →
    id1 ≠ id2 → b1 ≠ b2
  me_range : ∀ id b ty, e.get id = some (b, ty) → lo ≤ b ∧ b < hi
  me_trange : ∀ id b ty, te.get id = some (b, ty) → tlo ≤ b ∧ b < thi
  me_mapped : ∀ id b' ty, te.get id = some (b', ty) → ∃ b, f b = some (b', 0) ∧ e.get id = some (b, ty)
  me_flat : ∀ id b' ty b delta, te.get id = some (b', ty) → f b = some (b', delta) →
    e.get id = some (b, ty) ∧ delta = 0
  me_incr : lo ≤ hi
  me_tincr : tlo ≤ thi

/-- `SimplLocalsproof.match_envs_invariant` -/
theorem match_envs_invariant {f : Val.Meminj} {cenv : Compilenv} {e : Env} {le : TempEnv}
    {m : Mem} {lo hi : Block} {te : Env} {tle : TempEnv} {tlo thi : Block} {f' : Val.Meminj}
    {m' : Mem} (ME : MatchEnvs f cenv e le m lo hi te tle tlo thi)
    (LD : ∀ b chunk v, f b = none → lo ≤ b ∧ b < hi → Mem.load chunk m b 0 = some v →
      Mem.load chunk m' b 0 = some v)
    (INCR : Val.inject_incr f f')
    (INV1 : ∀ b, lo ≤ b ∧ b < hi → f' b = f b)
    (INV2 : ∀ b b' delta, f' b = some (b', delta) → tlo ≤ b' ∧ b' < thi → f' b = f b) :
    MatchEnvs f' cenv e le m' lo hi te tle tlo thi where
  me_vars id := by
    cases ME.me_vars id with
    | lifted b ty chunk v tv h1 h2 h3 h4 h5 h6 h7 h8 =>
      have hr := ME.me_range id b ty h1
      exact .lifted b ty chunk v tv h1 h2 h3 (by rw [INV1 b hr]; exact h4) h5
        (LD b chunk v h4 hr h6) h7 (Val.inject_incr_inject INCR h8)
    | not_lifted b ty b' h1 h2 h3 h4 => exact .not_lifted b ty b' h1 h2 h3 (INCR _ _ _ h4)
    | not_local h1 h2 h3 => exact .not_local h1 h2 h3
  me_temps id v h := by
    obtain ⟨⟨tv, A, B⟩, C⟩ := ME.me_temps id v h
    exact ⟨⟨tv, A, Val.inject_incr_inject INCR B⟩, C⟩
  me_inj := ME.me_inj
  me_range := ME.me_range
  me_trange := ME.me_trange
  me_mapped id b' ty h := by
    obtain ⟨b, A, B⟩ := ME.me_mapped id b' ty h
    exact ⟨b, INCR _ _ _ A, B⟩
  me_flat id b' ty b delta h1 h2 := by
    have := INV2 b b' delta h2 (ME.me_trange id b' ty h1)
    rw [this] at h2
    exact ME.me_flat id b' ty b delta h1 h2
  me_incr := ME.me_incr
  me_tincr := ME.me_tincr

/-- `SimplLocalsproof.match_envs_extcall` -/
theorem match_envs_extcall {f : Val.Meminj} {cenv : Compilenv} {e : Env} {le : TempEnv}
    {m : Mem} {lo hi : Block} {te : Env} {tle : TempEnv} {tlo thi : Block} {tm : Mem}
    {f' : Val.Meminj} {m' : Mem} (ME : MatchEnvs f cenv e le m lo hi te tle tlo thi)
    (UNCH : Mem.UnchangedOn (locUnmapped f) m m') (INCR : Val.inject_incr f f')
    (SEP : InjectSeparated f f' m tm) (HB : hi ≤ m.nextblock) (THB : thi ≤ tm.nextblock) :
    MatchEnvs f' cenv e le m' lo hi te tle tlo thi := by
  refine match_envs_invariant ME ?_ INCR ?_ ?_
  · intro b chunk v hf _ hl
    exact UNCH.load (fun _ _ _ => hf) hl
  · intro b hb
    cases hfb : f b with
    | some p => obtain ⟨b', d⟩ := p; exact INCR _ _ _ hfb
    | none =>
      cases hf'b : f' b with
      | none => rfl
      | some p =>
        obtain ⟨b', d⟩ := p
        have := (SEP b b' d hfb hf'b).1
        simp only [Mem.validBlock, decide_eq_false_iff_not] at this
        exact absurd (Nat.lt_of_lt_of_le hb.2 HB) this
  · intro b b' delta hf' hb'
    cases hfb : f b with
    | some p => obtain ⟨b'', d⟩ := p; rw [INCR _ _ _ hfb]
    | none =>
      have := (SEP b b' delta hfb hf').2
      simp only [Mem.validBlock, decide_eq_false_iff_not] at this
      exact absurd (Nat.lt_of_lt_of_le hb'.2 THB) this

/-! ## Properties of values resulting from a cast -/

/-- `SimplLocalsproof.val_casted_load_result` -/
theorem val_casted_load_result {v : Val} {ty : Ty} {chunk : Chunk}
    (hc : Cop.ValCasted v ty) (hm : accessMode ty = .By_value chunk) :
    Val.loadResult chunk v = v := by
  cases hc with
  | @int sz si attr n hn =>
    cases sz <;> cases si <;> simp only [accessMode, AccessMode.By_value.injEq] at hm <;>
      subst hm <;> simp only [Cop.castIntInt] at hn <;> simp only [Val.loadResult, hn]
    all_goals
      by_cases h0 : Integers.Int.eq n Integers.Int.zero = true
      · simp only [h0, if_true] at hn; subst hn; decide
      · simp only [h0] at hn; subst hn; decide
  | int_ptr h => simp [Archi.ptr64] at h
  | ptr_int h => simp [Archi.ptr64] at h
  | struct => simp [accessMode] at hm
  | union => simp [accessMode] at hm
  | void => simp [accessMode] at hm
  | _ => simp [accessMode, Mptr, Archi.ptr64] at hm <;> subst hm <;> rfl

/-- `SimplLocalsproof.val_casted_inject` -/
theorem val_casted_inject {f : Val.Meminj} {v v' : Val} {ty : Ty} (hi : Val.Inject f v v')
    (hc : Cop.ValCasted v ty) : Cop.ValCasted v' ty := by
  cases hi with
  | ptr => cases hc <;> constructor <;> assumption
  | undef => cases hc; constructor
  | _ => exact hc

/-- `SimplLocalsproof.val_casted_list` -/
inductive ValCastedList : List Val → List Ty → Prop where
  | nil : ValCastedList [] []
  | cons {v1 vl ty1 tyl} : Cop.ValCasted v1 ty1 → ValCastedList vl tyl →
      ValCastedList (v1 :: vl) (ty1 :: tyl)

theorem cast_typeconv {v : Val} {ty : Ty} (m : Mem) (hc : Cop.ValCasted v ty) :
    Cop.semCast v ty (typeconv ty) m = some v := by
  cases hc with
  | @int sz si attr n hn =>
    cases sz <;> simp [Cop.semCast, Cop.classifyCast, typeconv, tint, removeAttributes, tattr, Archi.ptr64] at hn ⊢ <;> rfl
  | int_ptr h => simp [Archi.ptr64] at h
  | ptr_int h => simp [Archi.ptr64] at h
  | _ => simp [Cop.semCast, Cop.classifyCast, typeconv, removeAttributes, tattr, Archi.ptr64]

theorem step_Sdebug_var {ge : CGenv} {f : Function} {id : Ident} {ty : Ty} {k : Cont} {e : Env}
    {le : TempEnv} {m : Mem} {b : Block} (he : e.get id = some (b, ty)) :
    Step2 ge (.State f (Sdebug_var id ty) k e le m) E0 (.State f .Sskip k e le m) :=
  Step.builtin f none _ _ _ k e le m [.Vptr b Integers.Ptrofs.zero] E0 .Vundef m
    (.cons _ _ _ _ _ _ _ (.Eaddrof _ _ _ _ (.Evar_local _ _ _ he))
      (by simp [Cop.semCast, Cop.classifyCast, typeof]) .nil) (.intro _ _ _)

theorem make_cast_correct {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {a : Expr} {v1 : Val}
    {tto : Ty} {v2 : Val} (he : EvalExpr ge e le m a v1)
    (hc : Cop.semCast v1 (typeof a) tto m = some v2) :
    EvalExpr ge e le m (makeCast a tto) v2 := by
  have DFL : EvalExpr ge e le m (.Ecast a tto) v2 := .Ecast _ _ _ _ he hc
  unfold Cop.semCast at hc
  unfold makeCast
  cases hcl : Cop.classifyCast (typeof a) tto <;> simp only [hcl] at hc ⊢ <;> try exact DFL
  case i2i sz si =>
    cases sz <;> simp only at hc ⊢ <;> try exact DFL
    cases v1 <;> simp [Cop.castIntInt] at hc; subst hc; exact he
  all_goals (cases v1 <;> simp [Archi.ptr64] at hc <;> (try obtain ⟨-, hc⟩ := hc) <;> subst_vars <;> exact he)

theorem step_Sdebug_temp {ge : CGenv} {f : Function} {id : Ident} {ty : Ty} {k : Cont} {e : Env}
    {le : TempEnv} {m : Mem} {v : Val} (hle : le.get id = some v) (hc : Cop.ValCasted v ty) :
    Step2 ge (.State f (Sdebug_temp id ty) k e le m) E0 (.State f .Sskip k e le m) :=
  Step.builtin f none _ _ _ k e le m [v] E0 .Vundef m
    (.cons _ _ _ _ _ _ _ (.Etempvar _ _ _ hle) (cast_typeconv m hc) .nil) (.intro _ _ _)

theorem step_Sset_debug {opts : Options} {ge : CGenv} {f : Function} {id : Ident} {ty : Ty}
    {a : Expr} {k : Cont} {e : Env} {le : TempEnv} {m : Mem} {v v' : Val}
    (he : EvalExpr ge e le m a v) (hc : Cop.semCast v (typeof a) ty m = some v') :
    Smallstep.Plus (Step2 ge) (.State f (Sset_debug opts id ty a) k e le m) E0
      (.State f .Sskip k e (le.set id v') m) := by
  have H : ∀ k, Step2 ge (.State f (.Sset id (makeCast a ty)) k e le m) E0
      (.State f .Sskip k e (le.set id v') m) :=
    fun k => Step.set _ _ _ _ _ _ _ _ (make_cast_correct he hc)
  unfold Sset_debug
  cases opts.debug
  · exact plus_one (H k)
  · exact plus_left (Step.seq _ _ _ _ _ _ _) (star_left (H _) (star_left (Step.skip_seq _ _ _ _ _ _)
      (star_one (step_Sdebug_temp (PTree.gss _ _ _) (Cop.cast_val_is_casted hc))) rfl) rfl) rfl

theorem step_add_debug_vars {opts : Options} {ge : CGenv} {f : Function} {s : Stmt} {e : Env}
    {le : TempEnv} {m : Mem} {k : Cont} :
    ∀ {vars : List (Ident × Ty)}, (∀ id ty, (id, ty) ∈ vars → ∃ b, e.get id = some (b, ty)) →
    Smallstep.Star (Step2 ge) (.State f (addDebugVars opts vars s) k e le m) E0 (.State f s k e le m) := by
  intro vars
  unfold addDebugVars
  cases opts.debug
  · intro _; exact .refl _
  · simp only [if_true]
    induction vars with
    | nil => intro _; exact .refl _
    | cons p vars ih =>
      obtain ⟨id, ty⟩ := p
      intro H
      obtain ⟨b, hb⟩ := H id ty (by simp)
      exact star_left (Step.seq _ _ _ _ _ _ _) (star_left (step_Sdebug_var hb)
        (star_left (Step.skip_seq _ _ _ _ _ _) (ih fun id ty h => H id ty (by simp [h])) rfl) rfl) rfl

/-- `SimplLocalsproof.bind_parameter_temps_inv` -/
theorem bind_parameter_temps_inv {id : Ident} :
    ∀ {params : List (Ident × Ty)} {args : List Val} {le le' : TempEnv},
    bindParameterTemps params args le = some le' → id ∉ varNames params → le'.get id = le.get id
  | [], [], _, _, h, _ => by simp only [bindParameterTemps, Option.some.injEq] at h; subst h; rfl
  | [], _ :: _, _, _, h, _ => by simp [bindParameterTemps] at h
  | _ :: _, [], _, _, h, _ => by simp [bindParameterTemps] at h
  | (id1, _) :: params, v :: args, le, le', h, hn => by
    simp only [bindParameterTemps] at h
    simp only [varNames, List.map_cons, List.mem_cons, not_or] at hn
    rw [bind_parameter_temps_inv h hn.2, PTree.gso _ _ _ _ (fun h => hn.1 (by subst h; rfl))]

theorem step_add_debug_params {opts : Options} {ge : CGenv} {f : Function} {s : Stmt} {k : Cont}
    {e : Env} {le : TempEnv} {m : Mem} :
    ∀ {params : List (Ident × Ty)} {vl : List Val} {le1 : TempEnv},
    listNorepet (varNames params) → ValCastedList vl (typeOfParams params) →
    bindParameterTemps params vl le1 = some le →
    Smallstep.Star (Step2 ge) (.State f (addDebugParams opts params s) k e le m) E0 (.State f s k e le m) := by
  intro params
  unfold addDebugParams
  cases opts.debug
  · intros; exact .refl _
  · simp only [if_true]
    induction params with
    | nil => intros; exact .refl _
    | cons p params ih =>
      obtain ⟨id, ty⟩ := p
      intro vl le1 NR CAST BIND
      cases CAST with
      | cons hc CAST =>
      rename_i a1 vl
      simp only [listNorepet, varNames, List.map_cons, List.nodup_cons] at NR
      simp only [bindParameterTemps] at BIND
      have A : le.get id = some a1 := by
        rw [bind_parameter_temps_inv BIND NR.1, PTree.gss]
      exact star_left (Step.seq _ _ _ _ _ _ _) (star_left (step_Sdebug_temp A hc)
        (star_left (Step.skip_seq _ _ _ _ _ _) (ih NR.2 CAST BIND) rfl) rfl) rfl

theorem ptrofs_unsigned_zero : Integers.Ptrofs.unsigned Integers.Ptrofs.zero = 0 := by decide

/-- `SimplLocalsproof.match_envs_assign_lifted` -/
theorem match_envs_assign_lifted {f : Val.Meminj} {cenv : Compilenv} {e : Env} {le : TempEnv}
    {m : Mem} {lo hi : Block} {te : Env} {tle : TempEnv} {tlo thi : Block} {b : Block} {ty : Ty}
    {v : Val} {m' : Mem} {id : Ident} {tv : Val} {ce : CompositeEnv}
    (ME : MatchEnvs f cenv e le m lo hi te tle tlo thi) (he : e.get id = some (b, ty))
    (hc : Cop.ValCasted v ty) (hvi : Val.Inject f v tv)
    (ha : AssignLoc ce ty m b Integers.Ptrofs.zero .Full v m') (hl : VSet.mem id cenv = true) :
    MatchEnvs f cenv e le m' lo hi te (tle.set id tv) tlo thi := by
  cases hmv : ME.me_vars id with
  | not_lifted _ _ _ _ _ h3 _ => rw [hl] at h3; cases h3
  | not_local h1 _ _ => rw [he] at h1; cases h1
  | lifted b0 ty0 chunk v0 tv0 ENV TENV LIFTED MAPPED MODE LOAD TLENV VINJ =>
  rw [he] at ENV; cases ENV
  cases ha with
  | copy => rename_i h _ _ _ _ _; rw [MODE] at h; cases h
  | value _ chunk' _ hmode hst =>
  rw [MODE] at hmode; cases hmode
  have hst := Mem.storev_store hst
  rw [ptrofs_unsigned_zero] at hst
  refine ⟨?_, ?_, ME.me_inj, ME.me_range, ME.me_trange, ME.me_mapped, ME.me_flat, ME.me_incr,
    ME.me_tincr⟩
  · intro id0
    by_cases hid : id0 = id
    · subst hid
      refine .lifted b ty chunk v tv he TENV hl MAPPED MODE ?_ (PTree.gss _ _ _) hvi
      rw [Mem.load_store_same hst, val_casted_load_result hc MODE]
    · cases ME.me_vars id0 with
      | lifted b1 ty1 chunk1 v1 tv1 h1 h2 h3 h4 h5 h6 h7 h8 =>
        refine .lifted b1 ty1 chunk1 v1 tv1 h1 h2 h3 h4 h5 ?_ (by rw [PTree.gso _ _ _ _ (Ne.symm hid)]; exact h7) h8
        rw [Mem.load_store_other hst _ _ _ (Or.inl ?_)]; exact h6
        intro hb; subst hb
        exact ME.me_inj id0 b1 ty1 id b1 ty h1 he hid rfl
      | not_lifted b1 ty1 b' h1 h2 h3 h4 => exact .not_lifted b1 ty1 b' h1 h2 h3 h4
      | not_local h1 h2 h3 => exact .not_local h1 h2 h3
  · intro id0 v0 h
    obtain ⟨⟨tv1, A, B⟩, C⟩ := ME.me_temps id0 v0 h
    refine ⟨?_, C⟩
    rw [PTree.gsspec]
    split
    · rename_i hid; subst hid; exact ⟨tv, rfl, by rw [C hl]; exact .undef _⟩
    · exact ⟨tv1, A, B⟩

/-- `SimplLocalsproof.match_envs_set_temp` -/
theorem match_envs_set_temp {f : Val.Meminj} {cenv : Compilenv} {e : Env} {le : TempEnv}
    {m : Mem} {lo hi : Block} {te : Env} {tle : TempEnv} {tlo thi : Block} {id : Ident}
    {v tv : Val} {x : Unit} (ME : MatchEnvs f cenv e le m lo hi te tle tlo thi)
    (hvi : Val.Inject f v tv) (hct : checkTemp cenv id = .OK x) :
    MatchEnvs f cenv e (le.set id v) m lo hi te (tle.set id tv) tlo thi := by
  have hl : VSet.mem id cenv = false := by
    unfold checkTemp at hct; split at hct
    · cases hct
    · rename_i h; simpa using h
  refine ⟨?_, ?_, ME.me_inj, ME.me_range, ME.me_trange, ME.me_mapped, ME.me_flat, ME.me_incr,
    ME.me_tincr⟩
  · intro id0
    cases ME.me_vars id0 with
    | lifted b1 ty1 chunk1 v1 tv1 h1 h2 h3 h4 h5 h6 h7 h8 =>
      refine .lifted b1 ty1 chunk1 v1 tv1 h1 h2 h3 h4 h5 h6 ?_ h8
      rw [PTree.gso _ _ _ _ (by rintro rfl; rw [h3] at hl; cases hl)]; exact h7
    | not_lifted b1 ty1 b' h1 h2 h3 h4 => exact .not_lifted b1 ty1 b' h1 h2 h3 h4
    | not_local h1 h2 h3 => exact .not_local h1 h2 h3
  · intro id0 v0 h
    rw [PTree.gsspec] at h ⊢
    split at h
    · rename_i hid; subst hid; cases h
      refine ⟨⟨tv, by simp, hvi⟩, fun h' => by rw [h'] at hl; cases hl⟩
    · rename_i hid; rw [if_neg hid]; exact ME.me_temps id0 v0 h

/-- `SimplLocalsproof.match_envs_set_opttemp` -/
theorem match_envs_set_opttemp {f : Val.Meminj} {cenv : Compilenv} {e : Env} {le : TempEnv}
    {m : Mem} {lo hi : Block} {te : Env} {tle : TempEnv} {tlo thi : Block} {optid : Option Ident}
    {v tv : Val} {x : Unit} (ME : MatchEnvs f cenv e le m lo hi te tle tlo thi)
    (hvi : Val.Inject f v tv) (hct : checkOpttemp cenv optid = .OK x) :
    MatchEnvs f cenv e (setOpttemp optid v le) m lo hi te (setOpttemp optid tv tle) tlo thi := by
  cases optid with
  | none => exact ME
  | some id => exact match_envs_set_temp ME hvi hct

/-- `SimplLocalsproof.match_envs_temps_exten` -/
theorem match_envs_temps_exten {f : Val.Meminj} {cenv : Compilenv} {e : Env} {le : TempEnv}
    {m : Mem} {lo hi : Block} {te : Env} {tle : TempEnv} {tlo thi : Block} {tle' : TempEnv}
    (ME : MatchEnvs f cenv e le m lo hi te tle tlo thi) (H : ∀ id, tle'.get id = tle.get id) :
    MatchEnvs f cenv e le m lo hi te tle' tlo thi := by
  refine ⟨?_, ?_, ME.me_inj, ME.me_range, ME.me_trange, ME.me_mapped, ME.me_flat, ME.me_incr,
    ME.me_tincr⟩
  · intro id0
    cases ME.me_vars id0 with
    | lifted b1 ty1 chunk1 v1 tv1 h1 h2 h3 h4 h5 h6 h7 h8 =>
      exact .lifted b1 ty1 chunk1 v1 tv1 h1 h2 h3 h4 h5 h6 (by rw [H]; exact h7) h8
    | not_lifted b1 ty1 b' h1 h2 h3 h4 => exact .not_lifted b1 ty1 b' h1 h2 h3 h4
    | not_local h1 h2 h3 => exact .not_local h1 h2 h3
  · intro id0 v0 h
    rw [H]; exact ME.me_temps id0 v0 h

/-- `SimplLocalsproof.match_envs_change_temp` -/
theorem match_envs_change_temp {f : Val.Meminj} {cenv : Compilenv} {e : Env} {le : TempEnv}
    {m : Mem} {lo hi : Block} {te : Env} {tle : TempEnv} {tlo thi : Block} {id : Ident} {v : Val}
    (ME : MatchEnvs f cenv e le m lo hi te tle tlo thi) (hle : le.get id = none)
    (hl : VSet.mem id cenv = false) :
    MatchEnvs f cenv e le m lo hi te (tle.set id v) tlo thi := by
  refine ⟨?_, ?_, ME.me_inj, ME.me_range, ME.me_trange, ME.me_mapped, ME.me_flat, ME.me_incr,
    ME.me_tincr⟩
  · intro id0
    cases ME.me_vars id0 with
    | lifted b1 ty1 chunk1 v1 tv1 h1 h2 h3 h4 h5 h6 h7 h8 =>
      refine .lifted b1 ty1 chunk1 v1 tv1 h1 h2 h3 h4 h5 h6 ?_ h8
      rw [PTree.gso _ _ _ _ (by rintro rfl; rw [h3] at hl; cases hl)]; exact h7
    | not_lifted b1 ty1 b' h1 h2 h3 h4 => exact .not_lifted b1 ty1 b' h1 h2 h3 h4
    | not_local h1 h2 h3 => exact .not_local h1 h2 h3
  · intro id0 v0 h
    rw [PTree.gso _ _ _ _ (by rintro rfl; rw [hle] at h; cases h)]
    exact ME.me_temps id0 v0 h

/-! ## Properties of `cenv_for` -/

/-- `SimplLocalsproof.cenv_for_gen` -/
def cenvForGen (atk : VSet) (vars : List (Ident × Ty)) : Compilenv :=
  vars.foldr (addLocalVariable atk) VSet.empty

theorem cenvFor_eq (f : Function) :
    cenvFor f = cenvForGen (addrTakenStmt f.fn_body) (f.fn_params ++ f.fn_vars) := rfl

/-- `SimplLocalsproof.add_local_variable_charact` -/
theorem add_local_variable_charact {id : Ident} {ty : Ty} {atk : VSet} {cenv : Compilenv}
    {id1 : Ident} :
    VSet.mem id1 (addLocalVariable atk (id, ty) cenv) = true ↔
      VSet.mem id1 cenv = true ∨
        ∃ chunk, accessMode ty = .By_value chunk ∧ id = id1 ∧ VSet.mem id atk = false := by
  unfold addLocalVariable
  dsimp only
  split
  · rename_i chunk hm
    by_cases ha : VSet.mem id atk = true
    · simp only [ha, if_true]
      constructor
      · exact Or.inl
      · rintro (h | ⟨_, _, _, h⟩)
        · exact h
        · simp_all
    · simp only [ha, if_false, Bool.false_eq_true]
      rw [VSet.mem_add]
      constructor
      · rintro (rfl | h)
        · exact Or.inr ⟨chunk, hm, rfl, by simp_all⟩
        · exact Or.inl h
      · rintro (h | ⟨_, _, rfl, _⟩)
        · exact Or.inr h
        · exact Or.inl rfl
  · rename_i hm
    constructor
    · exact Or.inl
    · rintro (h | ⟨chunk, h, _⟩)
      · exact h
      · exact absurd h (hm chunk)

/-- `SimplLocalsproof.cenv_for_gen_domain` -/
theorem cenv_for_gen_domain {atk : VSet} {id : Ident} :
    ∀ {vars : List (Ident × Ty)}, VSet.mem id (cenvForGen atk vars) = true → id ∈ varNames vars
  | [], h => by simp [cenvForGen, VSet.empty, VSet.mem] at h
  | (id1, ty1) :: vars, h => by
    simp only [cenvForGen, List.foldr_cons] at h
    rcases add_local_variable_charact.mp h with h | ⟨_, _, rfl, _⟩
    · exact List.mem_cons_of_mem _ (cenv_for_gen_domain h)
    · simp [varNames]

/-- `SimplLocalsproof.cenv_for_gen_by_value` -/
theorem cenv_for_gen_by_value {atk : VSet} {id : Ident} {ty : Ty} :
    ∀ {vars : List (Ident × Ty)}, (id, ty) ∈ vars → listNorepet (varNames vars) →
    VSet.mem id (cenvForGen atk vars) = true → ∃ chunk, accessMode ty = .By_value chunk
  | [], h, _, _ => by cases h
  | (id1, ty1) :: vars, hin, hnr, h => by
    simp only [listNorepet, varNames, List.map_cons, List.nodup_cons] at hnr
    simp only [cenvForGen, List.foldr_cons] at h
    rcases List.mem_cons.mp hin with heq | hin
    · cases heq
      rcases add_local_variable_charact.mp h with h | ⟨chunk, hm, _, _⟩
      · exact absurd (cenv_for_gen_domain h) hnr.1
      · exact ⟨chunk, hm⟩
    · rcases add_local_variable_charact.mp h with h | ⟨_, _, rfl, _⟩
      · exact cenv_for_gen_by_value hin hnr.2 h
      · exact absurd (List.mem_map_of_mem (f := Prod.fst) hin) hnr.1

/-- `SimplLocalsproof.cenv_for_gen_compat` -/
theorem cenv_for_gen_compat {atk : VSet} {id : Ident} :
    ∀ {vars : List (Ident × Ty)}, VSet.mem id (cenvForGen atk vars) = true →
    VSet.mem id atk = false
  | [], h => by simp [cenvForGen, VSet.empty, VSet.mem] at h
  | (id1, ty1) :: vars, h => by
    simp only [cenvForGen, List.foldr_cons] at h
    rcases add_local_variable_charact.mp h with h | ⟨_, _, rfl, h'⟩
    · exact cenv_for_gen_compat h
    · exact h'

/-- `SimplLocalsproof.compat_cenv` -/
def CompatCenv (atk : VSet) (cenv : Compilenv) : Prop :=
  ∀ id, VSet.mem id atk = true → VSet.mem id cenv = true → False

/-- `SimplLocalsproof.compat_cenv_for` -/
theorem compat_cenv_for (f : Function) : CompatCenv (addrTakenStmt f.fn_body) (cenvFor f) := by
  intro id h1 h2
  rw [cenvFor_eq] at h2
  rw [cenv_for_gen_compat h2] at h1
  cases h1

theorem compat_cenv_union_l {atk1 atk2 : VSet} {cenv : Compilenv}
    (h : CompatCenv (VSet.union atk1 atk2) cenv) : CompatCenv atk1 cenv :=
  fun id h1 h2 => h id (VSet.mem_union.mpr (Or.inl h1)) h2

theorem compat_cenv_union_r {atk1 atk2 : VSet} {cenv : Compilenv}
    (h : CompatCenv (VSet.union atk1 atk2) cenv) : CompatCenv atk2 cenv :=
  fun id h1 h2 => h id (VSet.mem_union.mpr (Or.inr h1)) h2

theorem compat_cenv_empty (cenv : Compilenv) : CompatCenv VSet.empty cenv :=
  fun id h1 _ => by rw [VSet.mem_empty] at h1; cases h1

end SimplLocals
end CC
