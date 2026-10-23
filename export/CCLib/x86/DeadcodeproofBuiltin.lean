/-
  [x86-64 instance of `CCLib/backend/DeadcodeproofBuiltin.lean`: the same development, in
  namespace `CC.X86`, over the x86-64 operators, registers and conventions.]

  Elimination of unneeded computations over RTL: correctness proof — port of
  the `Ibuiltin` case of `step_simulation` in CompCert
  `backend/Deadcodeproof.v` (volatile loads and stores, `memcpy`, annotations,
  debug information, known built-in functions, other external calls).

  Rocq proves this case by functional induction on `transfer_builtin`; here
  each branch of `transferBuiltin` is a separate lemma and
  `step_Ibuiltin` dispatches on the external function and its arguments.
-/
import CCLib.x86.DeadcodeproofStep

namespace CC
namespace X86
namespace Deadcodeproof

open ValueDomain ValueAnalysis RTL NeedDomain NeedOp Deadcode Op Smallstep
open Integers (Ptrofs)

section PRESERVATION
variable {o : ValueAOp.Options} {prog : RTL.Program}

theorem sound_state_bc {s : List RTL.Stackframe} {f : RTL.Function} {sp : Block} {pc : Node}
    {e : RTL.Regset} {m : Mem}
    (SOUND : SoundState o  prog (.State s f (.Vptr sp Ptrofs.zero) pc e m)) :
    ∃ bc : BlockClassification, GenvMatch bc prog.globalenv ∧ bc sp = .BCstack := by
  cases SOUND with
  | regular _ _ _ _ _ GE SP => exact ⟨_, GE, SP⟩

theorem lessdef_ptr {b : Block} {ofs : Ptrofs} {v : Val} (h : Val.Lessdef (.Vptr b ofs) v) :
    v = .Vptr b ofs := by
  cases h; rfl

variable {tprog : RTL.Program} (TRANSF : Deadcode.transfProgram o  prog = .OK tprog)
include TRANSF

/-- Common shape of the `Ibuiltin` cases. -/
abbrev BuiltinGoal (o : ValueAOp.Options) (prog tprog : RTL.Program)
    (s ts : List RTL.Stackframe) (f : RTL.Function) (an : PMap NAT) (sp : Block) (pc pc' : Node)
    (te : RTL.Regset) (tm : Mem) (t : Trace) (e' : RTL.Regset) (m' : Mem) : Prop :=
  ∃ S2', RTL.Step tprog.globalenv
      (.State ts (transfFunction' o  prog f an) (.Vptr sp Ptrofs.zero) pc te tm) t S2' ∧
    MatchStates o  prog (.State s f (.Vptr sp Ptrofs.zero) pc' e' m') S2'

/-- Builtins that are kept and whose arguments are all needed, with an
    arbitrary effect on memory (the default case of `transfer_builtin`). -/
theorem builtin_default
    (hext : ∀ name sg ge, ExtcallMemExtends (externalFunctionsSem name sg) ge)
    (hasm : ∀ name sg ge, ExtcallMemExtends (inlineAssemblySem name sg) ge)
    {s ts : List RTL.Stackframe} {f : RTL.Function} {sp : Block} {pc pc' : Node}
    {e te : RTL.Regset} {m tm : Mem} {an : PMap NAT} {ne : Nenv} {nm : Nmem} {ef : ExtFun}
    {args : List (BuiltinArg Reg)} {res : BuiltinRes Reg} {vargs : List Val} {t : Trace}
    {vres : Val} {m' : Mem}
    (STACKS : ListForall2 (MatchStackframe o  prog) s ts)
    (AN : analyzeFn o  prog f = some an)
    (hc : f.fn_code.get pc = some (.Ibuiltin ef args res pc'))
    (ANPC : an.get pc = (ne, nm))
    (SOUND : SoundState o  prog (.State s f (.Vptr sp Ptrofs.zero) pc e m))
    (hargs : EvalBuiltinArgs prog.globalenv.toSenv (fun r => e.get r) (.Vptr sp Ptrofs.zero) m
      args vargs)
    (hcall : externalCall ef prog.globalenv.toSenv vargs m t vres m')
    (TI : (transfFunction' o  prog f an).fn_code.get pc = some (.Ibuiltin ef args res pc'))
    (ENV : eagree e te (transferBuiltinArgs (killBuiltinRes res ne, nmemAll) args).1)
    (MEM : Magree m tm (nlive prog.globalenv sp
      (transferBuiltinArgs (killBuiltinRes res ne, nmemAll) args).2)) :
    BuiltinGoal o  prog tprog s ts f an sp pc pc' te tm t (regmapSetres res vres e) m' := by
  have hsenv := senv_preserved TRANSF
  have hec : ∀ ef, ExtcallMemExtends (externalCall ef) (Genv.toSenv prog.globalenv) :=
    fun ef => externalCall_memExtends ef _ (fun n sg => hext n sg _) (fun n sg => hasm n sg _)
  obtain ⟨bc, GM, SPM⟩ := sound_state_bc SOUND
  rcases TR : transferBuiltinArgs (killBuiltinRes res ne, nmemAll) args with ⟨ne1, nm1⟩
  rw [TR] at ENV MEM
  obtain ⟨tvargs, tvres, tm', A, B, C, D⟩ :=
    transf_external_call prog.globalenv (nm2 := nm) (hec ef) hargs hcall TR ENV MEM GM SPM
  exact ⟨_, .Ibuiltin _ _ _ _ _ _ _ _ _ _ tvargs t tvres tm' TI (by rw [hsenv]; exact A)
    (by rw [hsenv]; exact B),
    match_succ_states STACKS AN hc (by simp [successorsInstr]) (by rw [ANPC]; exact C)
      (by rw [ANPC]; exact D)⟩

/-- Volatile loads. -/
theorem builtin_vload
    {s ts : List RTL.Stackframe} {f : RTL.Function} {sp : Block} {pc pc' : Node}
    {e te : RTL.Regset} {m tm : Mem} {an : PMap NAT} {ne : Nenv} {nm : Nmem}
    {res : BuiltinRes Reg} {vargs : List Val} {t : Trace} {vres : Val} {m' : Mem}
    (STACKS : ListForall2 (MatchStackframe o  prog) s ts)
    (AN : analyzeFn o  prog f = some an)
    (ANPC : an.get pc = (ne, nm))
    (SOUND : SoundState o  prog (.State s f (.Vptr sp Ptrofs.zero) pc e m))
    {chunk : Chunk} {a1 : BuiltinArg Reg}
    (hc : f.fn_code.get pc = some (.Ibuiltin (.EF_vload chunk) [a1] res pc'))
    (hargs : EvalBuiltinArgs prog.globalenv.toSenv (fun r => e.get r) (.Vptr sp Ptrofs.zero) m
      [a1] vargs)
    (hcall : externalCall (.EF_vload chunk) prog.globalenv.toSenv vargs m t vres m')
    (TI : (transfFunction' o  prog f an).fn_code.get pc = some (.Ibuiltin (.EF_vload chunk) [a1] res pc'))
    (ENV : eagree e te (transferBuiltinArg .All (killBuiltinRes res ne, nmemAdd nm (aaddrArg o ((vanalyze o  prog f).get pc) a1) (sizeChunk chunk)) a1).1)
    (MEM : Magree m tm (nlive prog.globalenv sp (transferBuiltinArg .All (killBuiltinRes res ne, nmemAdd nm (aaddrArg o ((vanalyze o  prog f).get pc) a1) (sizeChunk chunk)) a1).2)) :
    BuiltinGoal o  prog tprog s ts f an sp pc pc' te tm t (regmapSetres res vres e) m' := by
  have hsenv := senv_preserved TRANSF
  obtain ⟨bc, GM, SPM⟩ := sound_state_bc SOUND
  cases hcall with
  | intro _ b ofs _ _ _ hvl =>
  cases hargs with
  | cons h1 hnil =>
  cases hnil
  rcases TR : transferBuiltinArg .All (killBuiltinRes res ne,
      nmemAdd nm (aaddrArg o ((vanalyze o  prog f).get pc) a1) (sizeChunk chunk)) a1 with
    ⟨ne1, nm1⟩
  rw [TR] at ENV MEM
  obtain ⟨tv1, A, B, C, D⟩ := transfer_builtin_arg_sound prog.globalenv h1 GM SPM TR ENV MEM
  have E1 := lessdef_ptr (lessdef_vagree B)
  subst E1
  have X : ∃ tvres, VolatileLoad prog.globalenv.toSenv chunk tm b ofs t tvres ∧
      Val.Lessdef vres tvres := by
    cases hvl with
    | vol id ev v hv hf hm => exact ⟨_, .vol _ _ _ _ id ev v hv hf hm, .refl _⟩
    | nonvol v hv hl =>
      obtain ⟨bc', P, GM', SPM'⟩ := aaddr_arg_sound SOUND h1
      obtain ⟨tv, P1, Q1⟩ := magree_load D hl (fun i h1 h2 =>
        nlive_add prog.globalenv sp nm GM' SPM' P ⟨h1, h2⟩)
      exact ⟨tv, .nonvol _ _ _ _ _ hv P1, Q1⟩
  obtain ⟨tvres, P, Q⟩ := X
  exact ⟨_, .Ibuiltin _ _ _ _ _ _ _ _ _ _ [.Vptr b ofs] t tvres tm TI
    (by rw [hsenv]; exact .cons A .nil) (by rw [hsenv]; exact .intro _ _ _ _ _ _ P),
    match_succ_states STACKS AN hc (by simp [successorsInstr])
      (by rw [ANPC]; exact eagree_set_res Q C)
      (by rw [ANPC]; exact magree_monotone D fun _ _ h => incl_nmem_add _ _ _ _ h)⟩

/-- Volatile stores. -/
theorem builtin_vstore
    {s ts : List RTL.Stackframe} {f : RTL.Function} {sp : Block} {pc pc' : Node}
    {e te : RTL.Regset} {m tm : Mem} {an : PMap NAT} {ne : Nenv} {nm : Nmem}
    {res : BuiltinRes Reg} {vargs : List Val} {t : Trace} {vres : Val} {m' : Mem}
    (STACKS : ListForall2 (MatchStackframe o  prog) s ts)
    (AN : analyzeFn o  prog f = some an)
    (ANPC : an.get pc = (ne, nm))
    (SOUND : SoundState o  prog (.State s f (.Vptr sp Ptrofs.zero) pc e m))
    {chunk : Chunk} {a1 a2 : BuiltinArg Reg}
    (hc : f.fn_code.get pc = some (.Ibuiltin (.EF_vstore chunk) [a1, a2] res pc'))
    (hargs : EvalBuiltinArgs prog.globalenv.toSenv (fun r => e.get r) (.Vptr sp Ptrofs.zero) m
      [a1, a2] vargs)
    (hcall : externalCall (.EF_vstore chunk) prog.globalenv.toSenv vargs m t vres m')
    (TI : (transfFunction' o  prog f an).fn_code.get pc = some (.Ibuiltin (.EF_vstore chunk) [a1, a2] res pc'))
    (ENV : eagree e te (transferBuiltinArg .All (transferBuiltinArg (storeArgument chunk) (killBuiltinRes res ne, nm) a2) a1).1)
    (MEM : Magree m tm (nlive prog.globalenv sp (transferBuiltinArg .All (transferBuiltinArg (storeArgument chunk) (killBuiltinRes res ne, nm) a2) a1).2)) :
    BuiltinGoal o  prog tprog s ts f an sp pc pc' te tm t (regmapSetres res vres e) m' := by
  have hsenv := senv_preserved TRANSF
  obtain ⟨bc, GM, SPM⟩ := sound_state_bc SOUND
  cases hargs with
  | cons h1 hl =>
  cases hl with
  | cons h2 hnil =>
  cases hnil
  rcases TR2 : transferBuiltinArg (storeArgument chunk) (killBuiltinRes res ne, nm) a2 with
    ⟨ne2, nm2⟩
  rw [TR2] at ENV MEM
  rcases TR1 : transferBuiltinArg .All (ne2, nm2) a1 with ⟨ne1, nm1⟩
  rw [TR1] at ENV MEM
  obtain ⟨tv1, A1, B1, C1, D1⟩ := transfer_builtin_arg_sound prog.globalenv h1 GM SPM TR1 ENV MEM
  obtain ⟨tv2, A2, B2, C2, D2⟩ := transfer_builtin_arg_sound prog.globalenv h2 GM SPM TR2 C1 D1
  obtain ⟨EQ, tm', P, Q⟩ := transf_volatile_store prog.globalenv hcall (lessdef_vagree B1) B2 D2
  subst EQ
  exact ⟨_, .Ibuiltin _ _ _ _ _ _ _ _ _ _ [tv1, tv2] t .Vundef tm' TI
    (by rw [hsenv]; exact .cons A1 (.cons A2 .nil)) (by rw [hsenv]; exact P),
    match_succ_states STACKS AN hc (by simp [successorsInstr])
      (by rw [ANPC]; exact eagree_set_res (.refl _) C2) (by rw [ANPC]; exact Q)⟩

/-- Annotations. -/
theorem builtin_annot
    {s ts : List RTL.Stackframe} {f : RTL.Function} {sp : Block} {pc pc' : Node}
    {e te : RTL.Regset} {m tm : Mem} {an : PMap NAT} {ne : Nenv} {nm : Nmem}
    {args : List (BuiltinArg Reg)} {res : BuiltinRes Reg} {vargs : List Val} {t : Trace}
    {vres : Val} {m' : Mem} {kind : Positive} {txt : String} {targs : List ATyp}
    (STACKS : ListForall2 (MatchStackframe o  prog) s ts)
    (AN : analyzeFn o  prog f = some an)
    (ANPC : an.get pc = (ne, nm))
    (SOUND : SoundState o  prog (.State s f (.Vptr sp Ptrofs.zero) pc e m))
    (hc : f.fn_code.get pc = some (.Ibuiltin (.EF_annot kind txt targs) args res pc'))
    (hargs : EvalBuiltinArgs prog.globalenv.toSenv (fun r => e.get r) (.Vptr sp Ptrofs.zero) m
      args vargs)
    (hcall : externalCall (.EF_annot kind txt targs) prog.globalenv.toSenv vargs m t vres m')
    (TI : (transfFunction' o  prog f an).fn_code.get pc =
      some (.Ibuiltin (.EF_annot kind txt targs) args res pc'))
    (ENV : eagree e te (transferBuiltinArgs (killBuiltinRes res ne, nm) args).1)
    (MEM : Magree m tm (nlive prog.globalenv sp
      (transferBuiltinArgs (killBuiltinRes res ne, nm) args).2)) :
    BuiltinGoal o  prog tprog s ts f an sp pc pc' te tm t (regmapSetres res vres e) m' := by
  have hsenv := senv_preserved TRANSF
  obtain ⟨bc, GM, SPM⟩ := sound_state_bc SOUND
  rcases TR : transferBuiltinArgs (killBuiltinRes res ne, nm) args with ⟨ne1, nm1⟩
  rw [TR] at ENV MEM
  obtain ⟨tvl, A, B, C, D⟩ := transfer_builtin_args_sound prog.globalenv GM SPM hargs TR ENV MEM
  cases hcall with
  | intro _ _ _ evs hm =>
  exact ⟨_, .Ibuiltin _ _ _ _ _ _ _ _ _ _ tvl _ .Vundef tm TI (by rw [hsenv]; exact A)
    (by rw [hsenv]; exact .intro _ _ _ _ (EventsExtends.eventValListMatch_lessdef hm B)),
    match_succ_states STACKS AN hc (by simp [successorsInstr])
      (by rw [ANPC]; exact eagree_set_res (.refl _) C) (by rw [ANPC]; exact D)⟩

/-- Annotations of a value. -/
theorem builtin_annot_val
    {s ts : List RTL.Stackframe} {f : RTL.Function} {sp : Block} {pc pc' : Node}
    {e te : RTL.Regset} {m tm : Mem} {an : PMap NAT} {ne : Nenv} {nm : Nmem}
    {args : List (BuiltinArg Reg)} {res : BuiltinRes Reg} {vargs : List Val} {t : Trace}
    {vres : Val} {m' : Mem} {kind : Positive} {txt : String} {targ : ATyp}
    (STACKS : ListForall2 (MatchStackframe o  prog) s ts)
    (AN : analyzeFn o  prog f = some an)
    (ANPC : an.get pc = (ne, nm))
    (SOUND : SoundState o  prog (.State s f (.Vptr sp Ptrofs.zero) pc e m))
    (hc : f.fn_code.get pc = some (.Ibuiltin (.EF_annot_val kind txt targ) args res pc'))
    (hargs : EvalBuiltinArgs prog.globalenv.toSenv (fun r => e.get r) (.Vptr sp Ptrofs.zero) m
      args vargs)
    (hcall : externalCall (.EF_annot_val kind txt targ) prog.globalenv.toSenv vargs m t vres m')
    (TI : (transfFunction' o  prog f an).fn_code.get pc =
      some (.Ibuiltin (.EF_annot_val kind txt targ) args res pc'))
    (ENV : eagree e te (transferBuiltinArgs (killBuiltinRes res ne, nm) args).1)
    (MEM : Magree m tm (nlive prog.globalenv sp
      (transferBuiltinArgs (killBuiltinRes res ne, nm) args).2)) :
    BuiltinGoal o  prog tprog s ts f an sp pc pc' te tm t (regmapSetres res vres e) m' := by
  have hsenv := senv_preserved TRANSF
  obtain ⟨bc, GM, SPM⟩ := sound_state_bc SOUND
  rcases TR : transferBuiltinArgs (killBuiltinRes res ne, nm) args with ⟨ne1, nm1⟩
  rw [TR] at ENV MEM
  obtain ⟨tvl, A, B, C, D⟩ := transfer_builtin_args_sound prog.globalenv GM SPM hargs TR ENV MEM
  cases hcall with
  | intro _ _ _ ev hm =>
  cases B with
  | cons hv hl =>
  cases hl
  exact ⟨_, .Ibuiltin _ _ _ _ _ _ _ _ _ _ _ _ _ tm TI (by rw [hsenv]; exact A)
    (by rw [hsenv]; exact .intro _ _ _ _ (EventsExtends.eventValMatch_lessdef hm hv)),
    match_succ_states STACKS AN hc (by simp [successorsInstr])
      (by rw [ANPC]; exact eagree_set_res hv C) (by rw [ANPC]; exact D)⟩

/-- Debugging information. -/
theorem builtin_debug
    {s ts : List RTL.Stackframe} {f : RTL.Function} {sp : Block} {pc pc' : Node}
    {e te : RTL.Regset} {m tm : Mem} {an : PMap NAT} {ne : Nenv} {nm : Nmem}
    {args : List (BuiltinArg Reg)} {res : BuiltinRes Reg} {vargs : List Val} {t : Trace}
    {vres : Val} {m' : Mem} {kind : Positive} {txt : Ident} {targs : List ATyp}
    (STACKS : ListForall2 (MatchStackframe o  prog) s ts)
    (AN : analyzeFn o  prog f = some an)
    (ANPC : an.get pc = (ne, nm))
    (hc : f.fn_code.get pc = some (.Ibuiltin (.EF_debug kind txt targs) args res pc'))
    (hargs : EvalBuiltinArgs prog.globalenv.toSenv (fun r => e.get r) (.Vptr sp Ptrofs.zero) m
      args vargs)
    (hcall : externalCall (.EF_debug kind txt targs) prog.globalenv.toSenv vargs m t vres m')
    (TI : (transfFunction' o  prog f an).fn_code.get pc =
      some (.Ibuiltin (.EF_debug kind txt targs) args res pc'))
    (ENV : eagree e te (killBuiltinRes res ne))
    (MEM : Magree m tm (nlive prog.globalenv sp nm)) :
    BuiltinGoal o  prog tprog s ts f an sp pc pc' te tm t (regmapSetres res vres e) m' := by
  have hsenv := senv_preserved TRANSF
  cases hcall with
  | intro _ _ _ =>
  obtain ⟨vargs', A⟩ := can_eval_builtin_args (gs' := prog.globalenv.toSenv) (e' := te)
    (fun _ => rfl) MEM hargs
  exact ⟨_, .Ibuiltin _ _ _ _ _ _ _ _ _ _ vargs' _ .Vundef tm TI (by rw [hsenv]; exact A)
    (by rw [hsenv]; exact .intro _ _ _),
    match_succ_states STACKS AN hc (by simp [successorsInstr])
      (by rw [ANPC]; exact eagree_set_res (.refl _) ENV) (by rw [ANPC]; exact MEM)⟩

omit TRANSF in
/-- Known built-in functions whose result is not needed: the call is removed. -/
theorem builtin_known_dead
    {s ts : List RTL.Stackframe} {f : RTL.Function} {sp : Block} {pc pc' : Node}
    {e te : RTL.Regset} {m tm : Mem} {an : PMap NAT} {ne : Nenv} {nm : Nmem}
    {args : List (BuiltinArg Reg)} {res : BuiltinRes Reg} {vargs : List Val} {t : Trace}
    {vres : Val} {m' : Mem} {name : String} {sg : Signature} {bf : Builtins.BuiltinFunction}
    (STACKS : ListForall2 (MatchStackframe o  prog) s ts)
    (AN : analyzeFn o  prog f = some an)
    (ANPC : an.get pc = (ne, nm))
    (hc : f.fn_code.get pc = some (.Ibuiltin (.EF_builtin name sg) args res pc'))
    (LK : Builtins.lookupBuiltinFunction name sg = some bf)
    (DEAD : builtinResDead res ne = true)
    (hcall : externalCall (.EF_builtin name sg) prog.globalenv.toSenv vargs m t vres m')
    (TI : (transfFunction' o  prog f an).fn_code.get pc = some (.Inop pc'))
    (ENV : eagree e te ne)
    (MEM : Magree m tm (nlive prog.globalenv sp nm)) :
    BuiltinGoal o  prog tprog s ts f an sp pc pc' te tm t (regmapSetres res vres e) m' := by
  change builtinOrExternalSem name sg _ _ _ _ _ _ at hcall
  simp only [builtinOrExternalSem, LK] at hcall
  cases hcall
  have ENV' : eagree (regmapSetres res vres e) te ne := by
    cases res with
    | BR r => exact eagree_update_dead r (is_dead_sound_1 DEAD) ENV
    | _ => simp [builtinResDead] at DEAD
  exact ⟨_, .Inop _ _ _ _ _ _ _ TI, match_succ_states STACKS AN hc (by simp [successorsInstr])
    (by rw [ANPC]; exact ENV') (by rw [ANPC]; exact MEM)⟩

/-- Known built-in functions whose result is needed. -/
theorem builtin_known_live
    {s ts : List RTL.Stackframe} {f : RTL.Function} {sp : Block} {pc pc' : Node}
    {e te : RTL.Regset} {m tm : Mem} {an : PMap NAT} {ne : Nenv} {nm : Nmem}
    {args : List (BuiltinArg Reg)} {res : BuiltinRes Reg} {vargs : List Val} {t : Trace}
    {vres : Val} {m' : Mem} {name : String} {sg : Signature} {bf : Builtins.BuiltinFunction}
    (STACKS : ListForall2 (MatchStackframe o  prog) s ts)
    (AN : analyzeFn o  prog f = some an)
    (ANPC : an.get pc = (ne, nm))
    (SOUND : SoundState o  prog (.State s f (.Vptr sp Ptrofs.zero) pc e m))
    (hc : f.fn_code.get pc = some (.Ibuiltin (.EF_builtin name sg) args res pc'))
    (LK : Builtins.lookupBuiltinFunction name sg = some bf)
    (hargs : EvalBuiltinArgs prog.globalenv.toSenv (fun r => e.get r) (.Vptr sp Ptrofs.zero) m
      args vargs)
    (hcall : externalCall (.EF_builtin name sg) prog.globalenv.toSenv vargs m t vres m')
    (TI : (transfFunction' o  prog f an).fn_code.get pc =
      some (.Ibuiltin (.EF_builtin name sg) args res pc'))
    (ENV : eagree e te (transferBuiltinArgs (killBuiltinRes res ne, nm) args).1)
    (MEM : Magree m tm (nlive prog.globalenv sp
      (transferBuiltinArgs (killBuiltinRes res ne, nm) args).2)) :
    BuiltinGoal o  prog tprog s ts f an sp pc pc' te tm t (regmapSetres res vres e) m' := by
  have hsenv := senv_preserved TRANSF
  obtain ⟨bc, GM, SPM⟩ := sound_state_bc SOUND
  rcases TR : transferBuiltinArgs (killBuiltinRes res ne, nm) args with ⟨ne1, nm1⟩
  rw [TR] at ENV MEM
  obtain ⟨tvl, A, B, C, D⟩ := transfer_builtin_args_sound prog.globalenv GM SPM hargs TR ENV MEM
  change builtinOrExternalSem name sg _ _ _ _ _ _ at hcall
  simp only [builtinOrExternalSem, LK] at hcall
  cases hcall with
  | intro _ _ _ _ hsem =>
  obtain ⟨vres', P, Q⟩ := Builtins.builtinFunctionSem_lessdef bf hsem B
  refine ⟨_, .Ibuiltin _ _ _ _ _ _ _ _ _ _ tvl _ vres' tm TI (by rw [hsenv]; exact A) ?_,
    match_succ_states STACKS AN hc (by simp [successorsInstr])
      (by rw [ANPC]; exact eagree_set_res Q C) (by rw [ANPC]; exact D)⟩
  change builtinOrExternalSem name sg _ _ _ _ _ _
  simp only [builtinOrExternalSem, LK]
  exact .intro _ _ _ _ P

/-- `memcpy` whose destination is needed. -/
theorem builtin_memcpy
    {s ts : List RTL.Stackframe} {f : RTL.Function} {sp : Block} {pc pc' : Node}
    {e te : RTL.Regset} {m tm : Mem} {an : PMap NAT} {ne : Nenv} {nm : Nmem}
    {res : BuiltinRes Reg} {vargs : List Val} {t : Trace} {vres : Val} {m' : Mem}
    {sz al : Z} {dst src : BuiltinArg Reg}
    (STACKS : ListForall2 (MatchStackframe o  prog) s ts)
    (AN : analyzeFn o  prog f = some an)
    (ANPC : an.get pc = (ne, nm))
    (SOUND : SoundState o  prog (.State s f (.Vptr sp Ptrofs.zero) pc e m))
    (hc : f.fn_code.get pc = some (.Ibuiltin (.EF_memcpy sz al) [dst, src] res pc'))
    (hargs : EvalBuiltinArgs prog.globalenv.toSenv (fun r => e.get r) (.Vptr sp Ptrofs.zero) m
      [dst, src] vargs)
    (hcall : externalCall (.EF_memcpy sz al) prog.globalenv.toSenv vargs m t vres m')
    (TI : (transfFunction' o  prog f an).fn_code.get pc =
      some (.Ibuiltin (.EF_memcpy sz al) [dst, src] res pc'))
    (ENV : eagree e te (transferBuiltinArgs (killBuiltinRes res ne,
      nmemAdd (nmemRemove nm (aaddrArg o ((vanalyze o  prog f).get pc) dst) sz)
        (aaddrArg o ((vanalyze o  prog f).get pc) src) sz) [dst, src]).1)
    (MEM : Magree m tm (nlive prog.globalenv sp (transferBuiltinArgs (killBuiltinRes res ne,
      nmemAdd (nmemRemove nm (aaddrArg o ((vanalyze o  prog f).get pc) dst) sz)
        (aaddrArg o ((vanalyze o  prog f).get pc) src) sz) [dst, src]).2)) :
    BuiltinGoal o  prog tprog s ts f an sp pc pc' te tm t (regmapSetres res vres e) m' := by
  have hsenv := senv_preserved TRANSF
  obtain ⟨bc, GM, SPM⟩ := sound_state_bc SOUND
  rcases TR : transferBuiltinArgs (killBuiltinRes res ne,
      nmemAdd (nmemRemove nm (aaddrArg o ((vanalyze o  prog f).get pc) dst) sz)
        (aaddrArg o ((vanalyze o  prog f).get pc) src) sz) [dst, src] with ⟨ne1, nm1⟩
  rw [TR] at ENV MEM
  obtain ⟨tvl, A, B, C, D⟩ := transfer_builtin_args_sound prog.globalenv GM SPM hargs TR ENV MEM
  cases hcall with
  | intro _ bdst odst bsrc osrc _ bytes _ hal hsz hmod hsa hda hov hl hs =>
  cases hargs with
  | cons h1 hl' =>
  cases hl' with
  | cons h2 hnil =>
  cases hnil
  cases B with
  | cons B1 Bl =>
  cases Bl with
  | cons B2 Bn =>
  cases Bn
  cases B1
  cases B2
  obtain ⟨bc1, P1, GM1, SPM1⟩ := aaddr_arg_sound SOUND h1
  obtain ⟨bc2, P2, GM2, SPM2⟩ := aaddr_arg_sound SOUND h2
  obtain ⟨tbytes, LB, INJ⟩ := magree_loadbytes D hl (fun i h1 h2 =>
    nlive_add prog.globalenv sp _ GM2 SPM2 P2 ⟨h1, h2⟩)
  have hlen : (bytes.length : Z) = sz := by
    rw [Mem.loadbytes_length hl]; exact Int.toNat_of_nonneg hsz
  obtain ⟨tm', SB, MA⟩ := magree_storebytes_parallel (Q := nlive prog.globalenv sp nm)
    (magree_monotone D fun _ _ h => incl_nmem_add _ _ _ _ h) hs
    (fun b' i hq hout => nlive_remove prog.globalenv sp GM1 SPM1 P1 hq (by rw [hlen] at hout; exact hout))
    INJ
  exact ⟨_, .Ibuiltin _ _ _ _ _ _ _ _ _ _ _ _ _ tm' TI (by rw [hsenv]; exact A)
    (by rw [hsenv]; exact .intro _ _ _ _ _ _ _ _ hal hsz hmod hsa hda hov LB SB),
    match_succ_states STACKS AN hc (by simp [successorsInstr])
      (by rw [ANPC]; exact eagree_set_res (.refl _) C) (by rw [ANPC]; exact MA)⟩

omit TRANSF in
/-- `memcpy` whose destination is not needed: the copy is removed. -/
theorem builtin_memcpy_dead
    {s ts : List RTL.Stackframe} {f : RTL.Function} {sp : Block} {pc pc' : Node}
    {e te : RTL.Regset} {m tm : Mem} {an : PMap NAT} {ne : Nenv} {nm : Nmem}
    {res : BuiltinRes Reg} {vargs : List Val} {t : Trace} {vres : Val} {m' : Mem}
    {sz al : Z} {dst src : BuiltinArg Reg}
    (STACKS : ListForall2 (MatchStackframe o  prog) s ts)
    (AN : analyzeFn o  prog f = some an)
    (ANPC : an.get pc = (ne, nm))
    (SOUND : SoundState o  prog (.State s f (.Vptr sp Ptrofs.zero) pc e m))
    (hc : f.fn_code.get pc = some (.Ibuiltin (.EF_memcpy sz al) [dst, src] res pc'))
    (CONT : nmemContains nm (aaddrArg o ((vanalyze o  prog f).get pc) dst) sz = false)
    (hargs : EvalBuiltinArgs prog.globalenv.toSenv (fun r => e.get r) (.Vptr sp Ptrofs.zero) m
      [dst, src] vargs)
    (hcall : externalCall (.EF_memcpy sz al) prog.globalenv.toSenv vargs m t vres m')
    (TI : (transfFunction' o  prog f an).fn_code.get pc = some (.Inop pc'))
    (ENV : eagree e te ne)
    (MEM : Magree m tm (nlive prog.globalenv sp nm)) :
    BuiltinGoal o  prog tprog s ts f an sp pc pc' te tm t (regmapSetres res vres e) m' := by
  cases hcall with
  | intro _ bdst odst bsrc osrc _ bytes _ hal hsz hmod hsa hda hov hl hs =>
  cases hargs with
  | cons h1 _ =>
  obtain ⟨bc1, P1, GM1, SPM1⟩ := aaddr_arg_sound SOUND h1
  have hlen : (bytes.length : Z) = sz := by
    rw [Mem.loadbytes_length hl]; exact Int.toNat_of_nonneg hsz
  have ENV' : eagree (regmapSetres res .Vundef e) te ne := by
    cases res with
    | BR r => exact eagree_set_undef r ENV
    | _ => exact ENV
  have MEM' := magree_storebytes_left MEM hs (fun i h1 h2 =>
      nlive_contains prog.globalenv sp GM1 SPM1 P1 CONT ⟨h1, by rw [hlen] at h2; exact h2⟩)
  exact ⟨_, .Inop _ _ _ _ _ _ _ TI, match_succ_states STACKS AN hc (by simp [successorsInstr])
    (by rw [ANPC]; exact ENV') (by rw [ANPC]; exact MEM')⟩

/-- `step_simulation`, case `Ibuiltin`: dispatch on the external function and
    its arguments, as `functional induction (transfer_builtin …)` in Rocq. -/
theorem step_Ibuiltin
    (hext : ∀ name sg ge, ExtcallMemExtends (externalFunctionsSem name sg) ge)
    (hasm : ∀ name sg ge, ExtcallMemExtends (inlineAssemblySem name sg) ge)
    {s ts : List RTL.Stackframe} {f : RTL.Function} {sp : Block} {pc pc' : Node}
    {e te : RTL.Regset} {m tm : Mem} {an : PMap NAT} {ef : ExtFun}
    {args : List (BuiltinArg Reg)} {res : BuiltinRes Reg} {vargs : List Val} {t : Trace}
    {vres : Val} {m' : Mem}
    (STACKS : ListForall2 (MatchStackframe o  prog) s ts)
    (AN : analyzeFn o  prog f = some an)
    (ENV : eagree e te (transferAt o  prog f an pc).1)
    (MEM : Magree m tm (nlive prog.globalenv sp (transferAt o  prog f an pc).2))
    (SOUND : SoundState o  prog (.State s f (.Vptr sp Ptrofs.zero) pc e m))
    (hc : f.fn_code.get pc = some (.Ibuiltin ef args res pc'))
    (hargs : EvalBuiltinArgs prog.globalenv.toSenv (fun r => e.get r) (.Vptr sp Ptrofs.zero) m
      args vargs)
    (hcall : externalCall ef prog.globalenv.toSenv vargs m t vres m') :
    BuiltinGoal o  prog tprog s ts f an sp pc pc' te tm t (regmapSetres res vres e) m' := by
  have TI := transf_function_at (o := o)  (prog := prog) (an := an) hc
  rcases ANPC : an.get pc with ⟨ne, nm⟩
  simp only [transferAt, Deadcode.transfer, hc, ANPC] at ENV MEM
  cases ef with
  | EF_vload chunk =>
    rcases args with _ | ⟨a1, _ | ⟨a2, rest⟩⟩ <;>
      simp only [Deadcode.transferBuiltin, transfInstr] at ENV MEM TI
    · exact builtin_default TRANSF hext hasm STACKS AN hc ANPC SOUND hargs hcall TI ENV MEM
    · exact builtin_vload TRANSF STACKS AN ANPC SOUND hc hargs hcall TI ENV MEM
    · exact builtin_default TRANSF hext hasm STACKS AN hc ANPC SOUND hargs hcall TI ENV MEM
  | EF_vstore chunk =>
    rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, rest⟩⟩⟩ <;>
      simp only [Deadcode.transferBuiltin, transfInstr] at ENV MEM TI
    · exact builtin_default TRANSF hext hasm STACKS AN hc ANPC SOUND hargs hcall TI ENV MEM
    · exact builtin_default TRANSF hext hasm STACKS AN hc ANPC SOUND hargs hcall TI ENV MEM
    · exact builtin_vstore TRANSF STACKS AN ANPC SOUND hc hargs hcall TI ENV MEM
    · exact builtin_default TRANSF hext hasm STACKS AN hc ANPC SOUND hargs hcall TI ENV MEM
  | EF_memcpy sz al =>
    rcases args with _ | ⟨dst, _ | ⟨src, _ | ⟨a3, rest⟩⟩⟩ <;>
      simp only [Deadcode.transferBuiltin, transfInstr] at ENV MEM TI
    · exact builtin_default TRANSF hext hasm STACKS AN hc ANPC SOUND hargs hcall TI ENV MEM
    · exact builtin_default TRANSF hext hasm STACKS AN hc ANPC SOUND hargs hcall TI ENV MEM
    · rw [ANPC] at TI
      cases CONT : nmemContains nm (aaddrArg o ((vanalyze o  prog f).get pc) dst) sz
      · simp only [CONT] at ENV MEM TI
        exact builtin_memcpy_dead (tprog := tprog) STACKS AN ANPC SOUND hc CONT hargs hcall TI ENV MEM
      · simp only [CONT, if_true] at ENV MEM TI
        exact builtin_memcpy TRANSF STACKS AN ANPC SOUND hc hargs hcall TI ENV MEM
    · exact builtin_default TRANSF hext hasm STACKS AN hc ANPC SOUND hargs hcall TI ENV MEM
  | EF_annot kind txt targs =>
    simp only [Deadcode.transferBuiltin, transfInstr] at ENV MEM TI
    exact builtin_annot TRANSF STACKS AN ANPC SOUND hc hargs hcall TI ENV MEM
  | EF_annot_val kind txt targ =>
    simp only [Deadcode.transferBuiltin, transfInstr] at ENV MEM TI
    exact builtin_annot_val TRANSF STACKS AN ANPC SOUND hc hargs hcall TI ENV MEM
  | EF_debug kind txt targs =>
    simp only [Deadcode.transferBuiltin, transfInstr] at ENV MEM TI
    exact builtin_debug TRANSF STACKS AN ANPC hc hargs hcall TI ENV MEM
  | EF_builtin name sg =>
    simp only [Deadcode.transferBuiltin, transfInstr, ANPC] at ENV MEM TI
    cases LK : Builtins.lookupBuiltinFunction name sg with
    | none =>
      simp only [LK] at ENV MEM TI
      exact builtin_default TRANSF hext hasm STACKS AN hc ANPC SOUND hargs hcall TI ENV MEM
    | some bf =>
      cases DEAD : builtinResDead res ne
      · simp only [LK, DEAD] at ENV MEM TI
        exact builtin_known_live TRANSF STACKS AN ANPC SOUND hc LK hargs hcall TI ENV MEM
      · simp only [LK, DEAD, if_true] at ENV MEM TI
        exact builtin_known_dead (tprog := tprog) STACKS AN ANPC hc LK DEAD hcall TI ENV MEM
  | _ =>
    simp only [Deadcode.transferBuiltin, transfInstr] at ENV MEM TI
    exact builtin_default TRANSF hext hasm STACKS AN hc ANPC SOUND hargs hcall TI ENV MEM

end PRESERVATION

end Deadcodeproof
end X86
end CC
