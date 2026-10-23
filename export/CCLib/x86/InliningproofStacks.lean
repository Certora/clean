/-
  [x86-64 instance of `CCLib/backend/InliningproofStacks.lean`: the same development, in
  namespace `CC.X86`, over the x86-64 operators, registers and conventions.]

  RTL function inlining: semantic preservation — port of
  `backend/Inliningproof.v`, part 2: relating global environments
  (`match_globalenvs`, `find_function_agree`, `find_inlined_function`),
  translation of builtin arguments (`tr_builtin_arg(s)`) and the relation
  between call stacks (`match_stacks`, `match_stacks_inside`) with its
  preservation lemmas.
-/
import CCLib.x86.InliningproofBasic
import CCLib.common.GlobalenvsTransf

namespace CC
namespace X86
namespace Inlining

open Op RTL Smallstep
open Integers (Ptrofs)

/-! ## Relating global environments -/

/-- `Inliningproof.match_globalenvs` -/
structure MatchGlobalenvs (ge : RTL.CGenv) (F : Val.Meminj) (bound : Block) : Prop where
  domain : ∀ b, b < bound → F b = some (b, 0)
  image : ∀ b1 b2 delta, F b1 = some (b2, delta) → b2 < bound → b1 = b2
  symbols : ∀ id b, Genv.findSymbol ge id = some b → b < bound
  functions : ∀ b fd, Genv.findFunctPtr ge b = some fd → b < bound
  varinfos : ∀ b gv, Genv.findVarInfo ge b = some gv → b < bound

theorem MatchGlobalenvs.symbolAddress_inject {ge : RTL.CGenv} {F : Val.Meminj} {bound : Block}
    (h : MatchGlobalenvs ge F bound) (id : Ident) (ofs : Ptrofs) :
    Val.Inject F (Genv.symbolAddress ge id ofs) (Genv.symbolAddress ge id ofs) := by
  unfold Genv.symbolAddress
  split
  · next b hb =>
    exact .ptr 0 (h.domain b (h.symbols id b hb)) (by rw [Ptrofs.repr_zero, Ptrofs.add_zero])
  · exact .undef _

theorem symbolAddress_transf {ge tge : RTL.CGenv}
    (hsym : ∀ id, Genv.findSymbol tge id = Genv.findSymbol ge id) (id : Ident) (ofs : Ptrofs) :
    Genv.symbolAddress tge id ofs = Genv.symbolAddress ge id ofs := by
  unfold Genv.symbolAddress; rw [hsym]

/-- `Inliningproof.find_inlined_function` -/
theorem find_inlined_function {prog : RTL.Program} {fenv : Funenv} {id : Ident} {rs : RTL.Regset}
    {fd : RTL.Fundef} {f : RTL.Function} (hc : FenvCompat prog fenv)
    (hf : findFunction prog.globalenv (.inr id) rs = some fd) (he : fenv.get id = some f) :
    fd = .Internal f := by
  have h1 := hc id f he
  rw [ASTProgram.defmap_eq, Genv.find_def_symbol prog.prog_public] at h1
  obtain ⟨b, A, B⟩ := h1
  have hb : Genv.findFunctPtr prog.globalenv b = some (.Internal f) :=
    (Genv.findFunctPtr_iff _ _ _).2 B
  simp only [findFunction, ASTProgram.globalenv] at hf
  rw [A] at hf
  dsimp only at hf
  rw [ASTProgram.globalenv] at hb
  rw [hb] at hf
  cases hf; rfl

section TRANSL
variable {prog tprog : RTL.Program} {fenv0 : Funenv}
  (TRANSF : transformPartialProgram (transfFundef fenv0) prog = .OK tprog)
include TRANSF

/-- `Inliningproof.symbols_preserved` -/
theorem symbols_preserved (id : Ident) :
    Genv.findSymbol tprog.globalenv id = Genv.findSymbol prog.globalenv id :=
  find_symbol_transf_partial TRANSF id

/-- `Inliningproof.senv_preserved` -/
theorem senv_preserved : Genv.toSenv tprog.globalenv = Genv.toSenv prog.globalenv :=
  senv_transf_partial TRANSF

/-- `Inliningproof.find_function_agree` -/
theorem find_function_agree {ros : Sum Reg Ident} {rs rs' : RTL.Regset} {fd : RTL.Fundef}
    {F : Val.Meminj} {ctx : Context} {bound : Block}
    (hf : findFunction prog.globalenv ros rs = some fd) (hag : AgreeRegs F ctx rs rs')
    (hmg : MatchGlobalenvs prog.globalenv F bound) :
    ∃ fd', findFunction tprog.globalenv (sros ctx ros) rs' = some fd' ∧
      transfFundef fenv0 fd = .OK fd' := by
  cases ros with
  | inl r =>
    simp only [findFunction, sros] at hf ⊢
    obtain ⟨b, hb⟩ := Genv.findFunct_inv hf
    rw [hb, Genv.findFunct_findFunctPtr] at hf
    have A := agree_val_reg r hag
    rw [hb] at A
    generalize rs'.get (sreg ctx r) = v' at A ⊢
    cases A with
    | ptr delta hF ho =>
      rw [hmg.domain b (hmg.functions b fd hf)] at hF
      cases hF
      rw [ho, Ptrofs.repr_zero, Ptrofs.add_zero, Genv.findFunct_findFunctPtr]
      exact find_funct_ptr_transf_partial TRANSF hf
  | inr id =>
    simp only [findFunction, sros] at hf ⊢
    rw [symbols_preserved TRANSF]
    split at hf
    · cases hf
    · exact find_funct_ptr_transf_partial TRANSF hf

/-- `Inliningproof.tr_builtin_arg` -/
theorem tr_builtin_arg {F : Val.Meminj} {bound : Block} {ctx : Context} {rs rs' : RTL.Regset}
    {sp sp' : Block} {m m' : Mem} (hmg : MatchGlobalenvs prog.globalenv F bound)
    (hag : AgreeRegs F ctx rs rs') (hsp : F sp = some (sp', ctx.dstk)) (hm : Mem.Inject F m m')
    {a : BuiltinArg Reg} {v : Val}
    (h : EvalBuiltinArg (Genv.toSenv prog.globalenv) (fun r => rs.get r) (.Vptr sp Ptrofs.zero) m
      a v) :
    ∃ v', EvalBuiltinArg (Genv.toSenv tprog.globalenv) (fun r => rs'.get r)
        (.Vptr sp' Ptrofs.zero) m' (sbuiltinarg ctx a) v' ∧ Val.Inject F v v' := by
  rw [senv_preserved TRANSF]
  have hsym : ∀ id ofs, Val.Inject F ((Genv.toSenv prog.globalenv).symbolAddress id ofs)
      ((Genv.toSenv prog.globalenv).symbolAddress id ofs) := fun id ofs => by
    rw [Genv.toSenv_symbolAddress]; exact hmg.symbolAddress_inject id ofs
  have hstk : ∀ ofs, Val.Inject F (Val.offsetPtr (.Vptr sp Ptrofs.zero) ofs)
      (Val.offsetPtr (.Vptr sp' Ptrofs.zero) (Ptrofs.add ofs (Ptrofs.repr ctx.dstk))) := by
    intro ofs
    simp only [Val.offsetPtr]
    refine .ptr _ hsp ?_
    rw [Ptrofs.add_zero_l, Ptrofs.add_zero_l]
  induction h with
  | BA x => exact ⟨_, .BA _, agree_val_reg x hag⟩
  | BA_int n => exact ⟨_, .BA_int n, .int _⟩
  | BA_long n => exact ⟨_, .BA_long n, .long _⟩
  | BA_float n => exact ⟨_, .BA_float n, .float _⟩
  | BA_single n => exact ⟨_, .BA_single n, .single _⟩
  | BA_loadstack chunk ofs v hl =>
      obtain ⟨v2, h2, hv⟩ := Mem.loadv_inject hm hl (hstk ofs)
      exact ⟨v2, .BA_loadstack _ _ _ h2, hv⟩
  | BA_addrstack ofs => exact ⟨_, .BA_addrstack _, hstk ofs⟩
  | BA_loadglobal chunk id ofs v hl =>
      obtain ⟨v2, h2, hv⟩ := Mem.loadv_inject hm hl (hsym id ofs)
      exact ⟨v2, .BA_loadglobal _ _ _ _ h2, hv⟩
  | BA_addrglobal id ofs => exact ⟨_, .BA_addrglobal id ofs, hsym id ofs⟩
  | BA_splitlong hi lo vhi vlo _ _ ih1 ih2 =>
      obtain ⟨v1', e1', l1⟩ := ih1
      obtain ⟨v2', e2', l2⟩ := ih2
      exact ⟨_, .BA_splitlong _ _ _ _ e1' e2', Val.longofwords_inject l1 l2⟩
  | BA_addptr a1 a2 v1 v2 _ _ ih1 ih2 =>
      obtain ⟨v1', e1', l1⟩ := ih1
      obtain ⟨v2', e2', l2⟩ := ih2
      refine ⟨_, .BA_addptr _ _ _ _ e1' e2', ?_⟩
      simp only [Archi.ptr64, if_true]
      exact Op.addl_inject l1 l2

/-- `Inliningproof.tr_builtin_args` -/
theorem tr_builtin_args {F : Val.Meminj} {bound : Block} {ctx : Context} {rs rs' : RTL.Regset}
    {sp sp' : Block} {m m' : Mem} (hmg : MatchGlobalenvs prog.globalenv F bound)
    (hag : AgreeRegs F ctx rs rs') (hsp : F sp = some (sp', ctx.dstk)) (hm : Mem.Inject F m m') :
    ∀ {al : List (BuiltinArg Reg)} {vl : List Val},
    EvalBuiltinArgs (Genv.toSenv prog.globalenv) (fun r => rs.get r) (.Vptr sp Ptrofs.zero) m
      al vl →
    ∃ vl', EvalBuiltinArgs (Genv.toSenv tprog.globalenv) (fun r => rs'.get r)
        (.Vptr sp' Ptrofs.zero) m' (al.map (sbuiltinarg ctx)) vl' ∧ Val.InjectList F vl vl'
  | [], [], .nil => ⟨[], .nil, .nil⟩
  | _ :: _, _ :: _, .cons h hl => by
      obtain ⟨v2, h2, l2⟩ := tr_builtin_arg TRANSF hmg hag hsp hm h
      obtain ⟨vl2, hl2, ll2⟩ := tr_builtin_args hmg hag hsp hm hl
      exact ⟨v2 :: vl2, .cons h2 hl2, .cons l2 ll2⟩

end TRANSL

end Inlining
end X86
end CC
