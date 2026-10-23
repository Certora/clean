/-
  [RISC-V instance of `CCLib/backend/InliningproofStep.lean`: the same development, in
  namespace `CC.RiscV`, over the RISC-V operators, registers and conventions.]

  RTL function inlining: semantic preservation — port of
  `backend/Inliningproof.v`, part 4: the relation between execution states
  (`match_states`) and the simulation of one step (`step_simulation`).
-/
import CCLib.riscV.InliningproofMatch
import CCLib.riscV.OpTheory
import CCLib.riscV.Conventions
import CCLib.riscV.Renumberproof

namespace CC
namespace RiscV
namespace Inlining

open Op RTL Smallstep
open Integers (Ptrofs)

/-- `Inliningproof.match_globalenvs_preserves_globals`: the injection of a
    `match_globalenvs` relation preserves the symbols of the global
    environment. -/
theorem MatchGlobalenvs.symbolsInject {ge : RTL.CGenv} {F : Val.Meminj} {bound : Block}
    (h : MatchGlobalenvs ge F bound) : SymbolsInject F (Genv.toSenv ge) (Genv.toSenv ge) where
  public_eq _ := rfl
  find_mapped id b1 b2 delta hf hs := by
    have := h.domain b1 (h.symbols id b1 hs)
    rw [hf] at this; cases this
    exact ⟨rfl, hs⟩
  find_public id b1 _ hs := ⟨b1, h.domain b1 (h.symbols id b1 hs), hs⟩
  volatile_eq b1 b2 delta hf := by
    show Genv.blockIsVolatile ge b2 = Genv.blockIsVolatile ge b1
    by_cases hb2 : b2 < bound
    · rw [h.image b1 b2 delta hf hb2]
    · have hb1 : ¬ b1 < bound := fun hb1 => by
        have := h.domain b1 hb1
        rw [hf] at this; cases this; exact hb2 hb1
      have none_of : ∀ b, ¬ b < bound → Genv.blockIsVolatile ge b = false := by
        intro b hb
        unfold Genv.blockIsVolatile
        cases e : Genv.findVarInfo ge b with
        | none => rfl
        | some gv => exact absurd (h.varinfos b gv e) hb
      rw [none_of b1 hb1, none_of b2 hb2]

/-! ## Relating states -/

/-- `Inliningproof.match_states`.  The port states the theorem for whole
    programs, so the function environment `fenv0` used to translate the
    callee of a `Callstate` is the one of the program itself. -/
inductive MatchStates (prog : RTL.Program) (fenv0 : Funenv) : RTL.State → RTL.State → Prop where
  | regular (stk : List RTL.Stackframe) (f : RTL.Function) (sp : Block) (pc : Node)
      (rs : RTL.Regset) (m : Mem) (stk' : List RTL.Stackframe) (f' : RTL.Function) (sp' : Block)
      (rs' : RTL.Regset) (m' : Mem) (F : Val.Meminj) (fenv : Funenv) (ctx : Context) :
      MatchStacksInside prog F m m' stk stk' f' ctx sp' rs' →
      FenvCompat prog fenv →
      TrFunbody fenv f'.fn_stacksize ctx f f'.fn_code →
      AgreeRegs F ctx rs rs' →
      F sp = some (sp', ctx.dstk) →
      Mem.Inject F m m' →
      Mem.validBlock m' sp' = true →
      RangePrivate F m m' sp' (ctx.dstk + ctx.mstk) f'.fn_stacksize →
      0 ≤ f'.fn_stacksize → f'.fn_stacksize < Ptrofs.max_unsigned →
      (∀ ofs, Mem.perm m' sp' ofs .Max .Nonempty = true → 0 ≤ ofs ∧ ofs ≤ f'.fn_stacksize) →
      MatchStates prog fenv0 (.State stk f (.Vptr sp Ptrofs.zero) pc rs m)
        (.State stk' f' (.Vptr sp' Ptrofs.zero) (spc ctx pc) rs' m')
  | call (stk : List RTL.Stackframe) (fd : RTL.Fundef) (args : List Val) (m : Mem)
      (stk' : List RTL.Stackframe) (fd' : RTL.Fundef) (args' : List Val) (m' : Mem)
      (F : Val.Meminj) :
      MatchStacks prog F m m' stk stk' m'.nextblock →
      transfFundef fenv0 fd = .OK fd' →
      Val.InjectList F args args' →
      Mem.Inject F m m' →
      MatchStates prog fenv0 (.Callstate stk fd args m) (.Callstate stk' fd' args' m')
  | call_regular (stk : List RTL.Stackframe) (f : RTL.Function) (vargs : List Val) (m : Mem)
      (stk' : List RTL.Stackframe) (f' : RTL.Function) (sp' : Block) (rs' : RTL.Regset) (m' : Mem)
      (F : Val.Meminj) (fenv : Funenv) (ctx ctx' : Context) (pc' pc1' : Node) (rargs : List Reg) :
      MatchStacksInside prog F m m' stk stk' f' ctx sp' rs' →
      FenvCompat prog fenv →
      TrFunbody fenv f'.fn_stacksize ctx f f'.fn_code →
      ContextBelow ctx' ctx →
      f'.fn_code.get pc' = some (.Inop pc1') →
      TrMoves f'.fn_code pc1' (sregs ctx' rargs) (sregs ctx f.fn_params)
        (spc ctx f.fn_entrypoint) →
      ListForall2 (ValRegCharact F ctx' rs') vargs rargs →
      Mem.Inject F m m' →
      Mem.validBlock m' sp' = true →
      RangePrivate F m m' sp' ctx.dstk f'.fn_stacksize →
      0 ≤ f'.fn_stacksize → f'.fn_stacksize < Ptrofs.max_unsigned →
      (∀ ofs, Mem.perm m' sp' ofs .Max .Nonempty = true → 0 ≤ ofs ∧ ofs ≤ f'.fn_stacksize) →
      MatchStates prog fenv0 (.Callstate stk (.Internal f) vargs m)
        (.State stk' f' (.Vptr sp' Ptrofs.zero) pc' rs' m')
  | ret (stk : List RTL.Stackframe) (v : Val) (m : Mem) (stk' : List RTL.Stackframe) (v' : Val)
      (m' : Mem) (F : Val.Meminj) :
      MatchStacks prog F m m' stk stk' m'.nextblock →
      Val.Inject F v v' →
      Mem.Inject F m m' →
      MatchStates prog fenv0 (.Returnstate stk v m) (.Returnstate stk' v' m')
  | return_regular (stk : List RTL.Stackframe) (v : Val) (m : Mem) (stk' : List RTL.Stackframe)
      (f' : RTL.Function) (sp' : Block) (rs' : RTL.Regset) (m' : Mem) (F : Val.Meminj)
      (ctx : Context) (pc' : Node) (or : Option Reg) (rinfo : Node × Reg) :
      MatchStacksInside prog F m m' stk stk' f' ctx sp' rs' →
      ctx.retinfo = some rinfo →
      f'.fn_code.get pc' = some (inlineReturn ctx or rinfo) →
      (match or with
        | none => v = .Vundef
        | some r => Val.Inject F v (rs'.get (sreg ctx r))) →
      Mem.Inject F m m' →
      Mem.validBlock m' sp' = true →
      RangePrivate F m m' sp' ctx.dstk f'.fn_stacksize →
      0 ≤ f'.fn_stacksize → f'.fn_stacksize < Ptrofs.max_unsigned →
      (∀ ofs, Mem.perm m' sp' ofs .Max .Nonempty = true → 0 ≤ ofs ∧ ofs ≤ f'.fn_stacksize) →
      MatchStates prog fenv0 (.Returnstate stk v m)
        (.State stk' f' (.Vptr sp' Ptrofs.zero) pc' rs' m')

/-- `Inliningproof.measure` -/
def measure : RTL.State → Nat
  | .State .. => 1
  | .Callstate .. => 0
  | .Returnstate .. => 0

/-- `Inliningproof.tr_funbody_inv` -/
theorem tr_funbody_inv {fenv : Funenv} {sz : Z} {ctx : Context} {f : RTL.Function} {c : Code}
    {pc : Node} {i : Instruction} (h : TrFunbody fenv sz ctx f c) (hi : f.fn_code.get pc = some i) :
    TrInstr fenv sz ctx pc i c := by
  cases h with
  | intro _ _ _ _ hins _ _ _ _ => exact hins pc i hi

theorem range_private_concat {F : Val.Meminj} {m m' : Mem} {sp : Block} {lo mid hi : Z}
    (h1 : RangePrivate F m m' sp lo mid) (h2 : RangePrivate F m m' sp mid hi) :
    RangePrivate F m m' sp lo hi := by
  intro ofs hlo hhi
  by_cases h : ofs < mid
  · exact h1 ofs hlo h
  · exact h2 ofs (Int.not_lt.mp h) hhi

theorem range_private_mono {F : Val.Meminj} {m m' : Mem} {sp : Block} {lo hi lo' hi' : Z}
    (h : RangePrivate F m m' sp lo hi) (h1 : lo ≤ lo') (h2 : hi' ≤ hi) :
    RangePrivate F m m' sp lo' hi' :=
  fun ofs a b => h ofs (Int.le_trans h1 a) (Int.lt_of_lt_of_le b h2)

theorem perm_max_nonempty {m : Mem} {b : Block} {ofs : Z} {k : PermKind} {p : Permission}
    (h : Mem.perm m b ofs k p = true) : Mem.perm m b ofs .Max .Nonempty = true :=
  Mem.perm_implies (Mem.perm_max h) (by cases p <;> rfl)

theorem transfFunction_sig {fenv : Funenv} {f f' : RTL.Function}
    (h : transfFunction fenv f = .OK f') : f'.fn_sig = f.fn_sig := by
  unfold transfFunction at h
  generalize (expandFunction fenv f).run initstate = p at h
  obtain ⟨ctx, s⟩ := p
  dsimp only at h
  split at h
  · injection h with h; subst h; rfl
  · cases h

/-- `Inliningproof.sig_function_translated` -/
theorem sig_function_translated {fenv : Funenv} {fd fd' : RTL.Fundef}
    (h : transfFundef fenv fd = .OK fd') : funsig fd' = funsig fd := by
  cases fd with
  | Internal f =>
    simp only [transfFundef, ASTFundef.transfPartial] at h
    split at h
    · next f' hf => cases h; exact transfFunction_sig hf
    · cases h
  | External ef => cases h; rfl

theorem tr_funbody_mstk {fenv : Funenv} {sz : Z} {ctx : Context} {f : RTL.Function} {c : Code}
    (h : TrFunbody fenv sz ctx f c) : ctx.mstk = Max.max f.fn_stacksize 0 := by
  cases h; assumption

theorem tr_funbody_dstk {fenv : Funenv} {sz : Z} {ctx : Context} {f : RTL.Function} {c : Code}
    (h : TrFunbody fenv sz ctx f c) : 0 ≤ ctx.dstk ∧ ctx.dstk + ctx.mstk ≤ sz := by
  cases h with
  | intro _ _ _ _ _ _ _ h1 h2 => exact ⟨h1, h2⟩

theorem tr_funbody_params {fenv : Funenv} {sz : Z} {ctx : Context} {f : RTL.Function} {c : Code}
    (h : TrFunbody fenv sz ctx f c) : ∀ r, r ∈ f.fn_params → r ≤ ctx.mreg := by
  cases h; assumption

theorem tr_funbody_align {fenv : Funenv} {sz : Z} {ctx : Context} {f : RTL.Function} {c : Code}
    (h : TrFunbody fenv sz ctx f c) : minSafeAlignment f.fn_stacksize ∣ ctx.dstk := by
  cases h; assumption

theorem max_stacksize_ge (z : Z) : z ≤ Max.max z 0 ∧ 0 ≤ Max.max z 0 :=
  ⟨Int.le_max_left _ _, Int.le_max_right _ _⟩

/-- In a function that was not inlined (`ctx.dstk = 0`), the target stack block can be freed
    whenever the source one can. -/
theorem free_target_exists {F : Val.Meminj} {m m' m1 : Mem} {sp0 sp' : Block} {ctx : Context}
    {f f' : RTL.Function} (SP : F sp0 = some (sp', ctx.dstk)) (hdstk : ctx.dstk = 0)
    (MINJ : Mem.Inject F m m') (hfree : Mem.free m sp0 0 f.fn_stacksize = some m1)
    (PRIV : RangePrivate F m m' sp' (ctx.dstk + ctx.mstk) f'.fn_stacksize)
    (hmstk : ctx.mstk = Max.max f.fn_stacksize 0) :
    ∃ m1', Mem.free m' sp' 0 f'.fn_stacksize = some m1' := by
  refine Mem.range_perm_free (Mem.rangePerm_intro _ _ _ _ _ _ (fun ofs h1 h2 => ?_))
  by_cases hlt : ofs < f.fn_stacksize
  · have := Mem.perm_inject SP MINJ
      (Mem.rangePerm_perm _ _ _ _ _ _ (Mem.free_range_perm hfree) ofs h1 hlt)
    rwa [hdstk, Int.add_zero] at this
  · have := max_stacksize_ge f.fn_stacksize
    have hmx : Max.max f.fn_stacksize 0 ≤ ofs := Int.max_le.mpr ⟨Int.not_lt.mp hlt, h1⟩
    exact range_private_perms PRIV ofs (by rw [hdstk, hmstk]; zomega) h2

theorem free_inject_both {F : Val.Meminj} {m m' m1 m1' : Mem} {sp0 sp' : Block} {sz sz' : Z}
    (MINJ : Mem.Inject F m m') (hfree : Mem.free m sp0 0 sz = some m1)
    (FREE : Mem.free m' sp' 0 sz' = some m1') (PRIV : RangePrivate F m1 m' sp' 0 sz') :
    Mem.Inject F m1 m1' :=
  Mem.free_right_inject (Mem.free_left_inject MINJ hfree) FREE
    (fun b1 delta ofs _ _ hf hp h1 h2 => (PRIV (ofs + delta) h1 h2).2 b1 delta hf
      (by rw [Int.add_sub_cancel]; exact perm_max_nonempty hp))

theorem perm_free_inv {m m1 : Mem} {b : Block} {lo hi : Z} (hfree : Mem.free m b lo hi = some m1)
    {b' : Block} {ofs : Z} {k : PermKind} {p : Permission} (h : Mem.perm m1 b' ofs k p = true) :
    Mem.perm m b' ofs k p = true := by
  rw [Mem.free_result hfree] at h; exact Mem.perm_free_3 h

/-- `Inliningspec.transf_function_spec`, for any function environment compatible with the
    program. -/
theorem transf_function_spec_compat {cunit : RTL.Program} {fenv : Funenv} {f f' : RTL.Function}
    (hc : FenvCompat cunit fenv) (h : transfFunction fenv f = .OK f') : TrFunction cunit f f' := by
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
    refine .intro fenv f _ ctx hc ?_ rfl rfl rfl rfl rfl K hlt
    refine expand_cfg_spec fenv s'.st_stksize fenv fenv ctx f (reserved initstate f) s'.st_code
      (fun _ _ h => h) ?_ rfl ?_ (Int.le_max_right _ _) rfl (Int.dvd_zero _) (Int.le_refl _)
      (Int.le_refl _) (fun _ _ _ => rfl)
    · show Positive.add .xH (maxPcFunction f) ≤ Positive.add .xH (maxPcFunction f)
      exact Nat.le_refl _
    · show Positive.add .xH (maxRegFunction f) ≤ Positive.add .xH (maxRegFunction f)
      exact Nat.le_refl _
  · cases h

section SIMULATION
variable {prog tprog : RTL.Program} {fenv0 : Funenv}
  (TRANSF : transformPartialProgram (transfFundef fenv0) prog = .OK tprog)
  (COMPAT0 : FenvCompat prog fenv0)
  (hext : ∀ name sg, ExtcallMemInject (externalFunctionsSem name sg))
  (hasm : ∀ name sg, ExtcallMemInject (inlineAssemblySem name sg))
  (hextp : ∀ name sg ge, ExtcallMemProps (externalFunctionsSem name sg) ge)
  (hasmp : ∀ name sg ge, ExtcallMemProps (inlineAssemblySem name sg) ge)

/-- The simulation diagram of `step_simulation`. -/
def SimDiagram (prog tprog : RTL.Program) (fenv0 : Funenv) (S1 : RTL.State) (t : Trace)
    (S2 S1' : RTL.State) : Prop :=
  (∃ S2' : RTL.State, Smallstep.Plus (RTL.Step tprog.globalenv) S1' t S2' ∧ MatchStates prog fenv0 S2 S2') ∨
  (measure S2 < measure S1 ∧ t = E0 ∧ MatchStates prog fenv0 S2 S1')

include TRANSF COMPAT0 hext hasm hextp hasmp in
/-- `Inliningproof.step_simulation` -/
theorem step_simulation {S1 : RTL.State} {t : Trace} {S2 : RTL.State}
    (hstep : RTL.Step prog.globalenv S1 t S2) {S1' : RTL.State}
    (hm : MatchStates prog fenv0 S1 S1') : SimDiagram prog tprog fenv0 S1 t S2 S1' := by
  have hsymb := symbols_preserved TRANSF
  cases hstep with
  | Inop s f sp pc rs m pc' hc =>
    cases hm with
    | regular _ _ sp0 _ _ _ stk' f' sp' rs' m' F fenv ctx MS COMPAT FB AG SP MINJ VB PRIV S1 S2 S3 =>
      have TR := tr_funbody_inv FB hc
      cases TR with
      | nop _ _ _ _ h =>
        exact .inl ⟨_, plus_one (.Inop _ _ _ _ _ _ _ h),
          .regular _ _ _ _ _ _ _ _ _ _ _ _ _ _ MS COMPAT FB AG SP MINJ VB PRIV S1 S2 S3⟩
  | Iop s f sp pc rs m op args res pc' v hc hev =>
    cases hm with
    | regular _ _ sp0 _ _ _ stk' f' sp' rs' m' F fenv ctx MS COMPAT FB AG SP MINJ VB PRIV S1 S2 S3 =>
      have TR := tr_funbody_inv FB hc
      cases TR with
      | op _ _ _ _ _ _ _ hres h =>
        obtain ⟨G, hG⟩ := match_stacks_inside_globalenvs MS
        have hsp : Val.Inject F (.Vptr sp0 Ptrofs.zero) (.Vptr sp' (Ptrofs.repr ctx.dstk)) :=
          .ptr _ SP (Ptrofs.add_zero_l _).symm
        obtain ⟨v', A, B⟩ := evalOperation_inject _ hG.symbolAddress_inject hsp
          (agree_val_regs AG args) MINJ hev
        refine .inl ⟨_, plus_one (.Iop _ _ _ _ _ _ _ _ _ _ _ h ?_),
          .regular _ _ _ _ _ _ _ _ _ _ _ _ _ _ (match_stacks_inside_set_reg _ _ MS) COMPAT FB
            (agree_set_reg AG B hres) SP MINJ VB PRIV S1 S2 S3⟩
        rw [sop, evalOperation_shiftStack, Op.evalOperation_preserved _ _ hsymb]; exact A
  | Iload s f sp pc rs m chunk addr args dst pc' a v hc hev hl =>
    cases hm with
    | regular _ _ sp0 _ _ _ stk' f' sp' rs' m' F fenv ctx MS COMPAT FB AG SP MINJ VB PRIV S1 S2 S3 =>
      have TR := tr_funbody_inv FB hc
      cases TR with
      | load _ _ _ _ _ _ _ _ hres h =>
        obtain ⟨G, hG⟩ := match_stacks_inside_globalenvs MS
        have hsp : Val.Inject F (.Vptr sp0 Ptrofs.zero) (.Vptr sp' (Ptrofs.repr ctx.dstk)) :=
          .ptr _ SP (Ptrofs.add_zero_l _).symm
        obtain ⟨a', P, Q⟩ := evalAddressing_inject _ hG.symbolAddress_inject hsp
          (agree_val_regs AG args) hev
        obtain ⟨v', U, V⟩ := Mem.loadv_inject MINJ hl Q
        refine .inl ⟨_, plus_one (.Iload _ _ _ _ _ _ _ _ _ _ _ _ _ h ?_ U),
          .regular _ _ _ _ _ _ _ _ _ _ _ _ _ _ (match_stacks_inside_set_reg _ _ MS) COMPAT FB
            (agree_set_reg AG V hres) SP MINJ VB PRIV S1 S2 S3⟩
        rw [saddr, evalAddressing_shiftStack, Op.evalAddressing_preserved _ _ hsymb]; exact P
  | Istore s f sp pc rs m chunk addr args src pc' a m1 hc hev hs =>
    cases hm with
    | regular _ _ sp0 _ _ _ stk' f' sp' rs' m' F fenv ctx MS COMPAT FB AG SP MINJ VB PRIV S1 S2 S3 =>
      have TR := tr_funbody_inv FB hc
      cases TR with
      | store _ _ _ _ _ _ _ _ h =>
        obtain ⟨G, hG⟩ := match_stacks_inside_globalenvs MS
        have hsp : Val.Inject F (.Vptr sp0 Ptrofs.zero) (.Vptr sp' (Ptrofs.repr ctx.dstk)) :=
          .ptr _ SP (Ptrofs.add_zero_l _).symm
        obtain ⟨a', P, Q⟩ := evalAddressing_inject _ hG.symbolAddress_inject hsp
          (agree_val_regs AG args) hev
        obtain ⟨m1', U, V⟩ := Mem.storev_mapped_inject MINJ hs Q (agree_val_reg src AG)
        refine .inl ⟨_, plus_one (.Istore _ _ _ _ _ _ _ _ _ _ _ _ _ h ?_ U),
          .regular _ _ _ _ _ _ _ _ _ _ _ _ _ _ (match_stacks_inside_store MS hs U) COMPAT FB
            AG SP V ?_ ?_ S1 S2 ?_⟩
        · rw [saddr, evalAddressing_shiftStack, Op.evalAddressing_preserved _ _ hsymb]; exact P
        · simp only [Mem.validBlock] at VB ⊢; rw [Mem.storev_nextblock U]; exact VB
        · exact range_private_invariant PRIV
            (fun _ _ _ hf hp _ _ => ⟨hf, by rwa [perm_storev hs] at hp⟩)
            (fun _ h => by rwa [perm_storev U])
        · exact fun o h => S3 o (by rwa [perm_storev U] at h)
  | Icall s f sp pc rs m sig ros args res pc' fd hc hfind hsig =>
    cases hm with
    | regular _ _ sp0 _ _ _ stk' f' sp' rs' m' F fenv ctx MS COMPAT FB AG SP MINJ VB PRIV S1 S2 S3 =>
      obtain ⟨G, hG⟩ := match_stacks_inside_globalenvs MS
      obtain ⟨fd', A, B⟩ := find_function_agree TRANSF hfind AG hG
      have TR := tr_funbody_inv FB hc
      cases TR with
      | call _ _ _ _ _ _ _ _ hres h =>
        exact .inl ⟨_, plus_one (.Icall _ _ _ _ _ _ _ _ _ _ _ _ h A
            (by rw [sig_function_translated B]; exact hsig)),
          .call _ _ _ _ _ _ _ _ _ (.cons _ _ _ _ _ _ _ _ _ _ _ _ _ MS COMPAT FB AG SP PRIV S1 S2 S3
            hres (lt_of_validBlock VB)) B (agree_val_regs AG args) MINJ⟩
      | call_inlined _ _ _ id _ _ _ _ f0 pc1 ctx' hres hfenv hnop hmoves hfb' hret hbelow hstk =>
        have EQ := find_inlined_function COMPAT hfind hfenv
        subst EQ
        have hd' := tr_funbody_dstk hfb'
        have hm' := max_stacksize_ge f0.fn_stacksize
        rw [tr_funbody_mstk hfb'] at hd'
        have hs := hstk
        unfold ContextStackCall at hs
        refine .inr ⟨by simp only [measure]; omega, rfl, ?_⟩
        exact .call_regular _ _ _ _ _ _ _ _ _ _ _ ctx' ctx _ pc1 args
          (.inlined _ _ _ _ _ _ _ _ _ _ _ _ ctx MS COMPAT FB AG SP
            (range_private_mono PRIV (Int.le_refl _) (by zomega)) hres hret hbelow hstk)
          COMPAT hfb' hbelow hnop hmoves (agree_val_regs_gen AG args) MINJ VB
          (range_private_mono PRIV hs.2 (Int.le_refl _)) S1 S2 S3
  | Itailcall s f stk pc rs m sig ros args fd m1 hc hfind hsig hfree =>
    cases hm with
    | regular _ _ _ _ _ _ stk' f' sp' rs' m' F fenv ctx MS COMPAT FB AG SP MINJ VB PRIV S1 S2 S3 =>
      obtain ⟨G, hG⟩ := match_stacks_inside_globalenvs MS
      obtain ⟨fd', A, B⟩ := find_function_agree TRANSF hfind AG hG
      have hmstk := tr_funbody_mstk FB
      have PRIV' : RangePrivate F m1 m' sp' ctx.dstk f'.fn_stacksize :=
        range_private_free_left (by rw [← hmstk]; exact PRIV) hfree SP MINJ
      have MS1 : MatchStacksInside prog F m1 m' s stk' f' ctx sp' rs' :=
        match_stacks_inside_invariant (Val.inject_incr_refl F) MS rs' (fun _ _ => rfl)
          (fun _ _ _ hf _ => hf) (fun _ _ _ _ _ _ hp => perm_free_inv hfree hp)
          (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)
      have TR := tr_funbody_inv FB hc
      cases TR with
      | tailcall _ _ _ _ _ _ h hretn =>
        cases MS with
        | inlined _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hret0 _ _ =>
          rw [hretn] at hret0; cases hret0
        | base _ _ _ _ _ _ hms _ hdstk =>
          obtain ⟨m1', FREE⟩ := free_target_exists (f := f) (f' := f') SP hdstk MINJ hfree PRIV hmstk
          rw [hdstk] at PRIV'
          refine .inl ⟨_, plus_one (.Itailcall _ _ _ _ _ _ _ _ _ _ _ h A
            (by rw [sig_function_translated B]; exact hsig) FREE), ?_⟩
          refine .call _ _ _ _ _ _ _ _ _ ?_ B (agree_val_regs AG args)
            (free_inject_both MINJ hfree FREE PRIV')
          refine match_stacks_bound (match_stacks_free_right (match_stacks_free_left hms hfree) FREE)
            ?_
          rw [Mem.nextblock_free FREE]; exact Nat.le_of_lt (lt_of_validBlock VB)
      | tailcall_call _ _ _ _ _ _ res pc' h hret =>
        exact .inl ⟨_, plus_one (.Icall _ _ _ _ _ _ _ _ _ _ _ _ h A
            (by rw [sig_function_translated B]; exact hsig)),
          .call _ _ _ _ _ _ _ _ _ (.untailcall _ _ _ _ _ _ _ _ _ MS1 PRIV' S1 S2 S3 hret
            (lt_of_validBlock VB)) B (agree_val_regs AG args) (Mem.free_left_inject MINJ hfree)⟩
      | tailcall_inlined _ _ _ id _ _ f0 pc1 ctx' hfenv hnop hmoves hfb' hret hbelow hstk =>
        have EQ := find_inlined_function COMPAT hfind hfenv
        subst EQ
        have hle : ctx.dstk ≤ ctx'.dstk := by
          rw [hstk]; exact align_le _ _ (minSafeAlignment_pos _)
        refine .inr ⟨by simp only [measure]; omega, rfl, ?_⟩
        exact .call_regular _ _ _ _ _ _ _ _ _ _ _ ctx' ctx _ pc1 args
          (match_stacks_inside_inlined_tailcall MS1 hbelow hstk hret PRIV' hfb')
          COMPAT hfb' hbelow hnop hmoves (agree_val_regs_gen AG args)
          (Mem.free_left_inject MINJ hfree) VB (range_private_mono PRIV' hle (Int.le_refl _))
          S1 S2 S3
  | Ibuiltin s f sp pc rs m ef args res pc' vargs t vres m1 hc hargs hec =>
    cases hm with
    | regular _ _ sp0 _ _ _ stk' f' sp' rs' m' F fenv ctx MS COMPAT FB AG SP MINJ VB PRIV S1 S2 S3 =>
      have TR := tr_funbody_inv FB hc
      cases TR with
      | builtin _ _ _ _ _ _ _ hres h =>
        obtain ⟨G, hG⟩ := match_stacks_inside_globalenvs MS
        obtain ⟨vargs', P, Q⟩ := tr_builtin_args TRANSF hG AG SP MINJ hargs
        obtain ⟨F1, v1, m1', A, B, C, D, E, J, K⟩ := externalCall_memInject ef hext hasm _ _ _ _ _ _ _
          _ _ _ hG.symbolsInject hec MINJ Q
        have MP := externalCall_memProps ef (Genv.toSenv prog.globalenv)
          (fun n sg => hextp n sg _) (fun n sg => hasmp n sg _)
        have MP1 : ∀ b ofs p, Mem.validBlock m b = true → Mem.perm m1 b ofs .Max p = true →
            Mem.perm m b ofs .Max p = true := fun b ofs p hv hp => MP.maxPerm _ _ _ _ _ b ofs p hec hv hp
        have MP2 : ∀ b ofs p, Mem.validBlock m' b = true → Mem.perm m1' b ofs .Max p = true →
            Mem.perm m' b ofs .Max p = true := fun b ofs p hv hp => MP.maxPerm _ _ _ _ _ b ofs p A hv hp
        have VB' : Mem.validBlock m1' sp' = true :=
          validBlock_of_lt (Nat.lt_of_lt_of_le (lt_of_validBlock VB) E.nextblock_le)
        have AG' : AgreeRegs F1 ctx (regmapSetres res vres rs)
            (regmapSetres (sbuiltinres ctx res) v1 rs') := by
          cases res with
          | BR r => exact agree_set_reg (agree_regs_incr AG J) B hres
          | _ => exact agree_regs_incr AG J
        refine .inl ⟨_, plus_one (.Ibuiltin _ _ _ _ _ _ _ _ _ _ _ _ _ _ h P
          (by rw [senv_preserved TRANSF]; exact A)), ?_⟩
        exact .regular _ _ _ _ _ _ _ _ _ _ _ _ _ _
          (match_stacks_inside_set_res _ _ (match_stacks_inside_extcall MP1 MP2 E MINJ J K MS
            (lt_of_validBlock VB)))
          COMPAT FB AG' (J _ _ _ SP) C VB' (range_private_extcall PRIV MP1 E MINJ J K VB) S1 S2
          (fun o h => S3 o (MP2 sp' o _ VB h))
  | Icond s f sp pc rs m cond args ifso ifnot b pc' hc hev hpc =>
    cases hm with
    | regular _ _ sp0 _ _ _ stk' f' sp' rs' m' F fenv ctx MS COMPAT FB AG SP MINJ VB PRIV S1 S2 S3 =>
      have TR := tr_funbody_inv FB hc
      cases TR with
      | cond _ _ _ _ _ _ _ h =>
        have A := evalCondition_inject (agree_val_regs AG args) MINJ hev
        subst hpc
        refine .inl ⟨_, plus_one (.Icond _ _ _ _ _ _ _ _ _ _ b _ h A rfl), ?_⟩
        cases b
        · exact .regular _ _ _ _ _ _ _ _ _ _ _ _ _ _ MS COMPAT FB AG SP MINJ VB PRIV S1 S2 S3
        · exact .regular _ _ _ _ _ _ _ _ _ _ _ _ _ _ MS COMPAT FB AG SP MINJ VB PRIV S1 S2 S3
  | Ijumptable s f sp pc rs m arg tbl n pc' hc harg hnth =>
    cases hm with
    | regular _ _ sp0 _ _ _ stk' f' sp' rs' m' F fenv ctx MS COMPAT FB AG SP MINJ VB PRIV S1 S2 S3 =>
      have TR := tr_funbody_inv FB hc
      cases TR with
      | jumptable _ _ _ _ _ h =>
        have A := agree_val_reg arg AG
        rw [harg] at A
        generalize hv' : rs'.get (sreg ctx arg) = v' at A
        cases A
        exact .inl ⟨_, plus_one (.Ijumptable _ _ _ _ _ _ _ _ n _ h hv'
          (Renumberproof.listNthZ_map _ hnth)),
          .regular _ _ _ _ _ _ _ _ _ _ _ _ _ _ MS COMPAT FB AG SP MINJ VB PRIV S1 S2 S3⟩
  | Ireturn s f stk pc rs m or m1 hc hfree =>
    cases hm with
    | regular _ _ _ _ _ _ stk' f' sp' rs' m' F fenv ctx MS COMPAT FB AG SP MINJ VB PRIV S1 S2 S3 =>
      have hmstk := tr_funbody_mstk FB
      have PRIV' : RangePrivate F m1 m' sp' ctx.dstk f'.fn_stacksize :=
        range_private_free_left (by rw [← hmstk]; exact PRIV) hfree SP MINJ
      have TR := tr_funbody_inv FB hc
      cases TR with
      | ret _ _ _ _ h hretn =>
        cases MS with
        | inlined _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hret0 _ _ =>
          rw [hretn] at hret0; cases hret0
        | base _ _ _ _ _ _ hms _ hdstk =>
          obtain ⟨m1', FREE⟩ := free_target_exists (f := f) (f' := f') SP hdstk MINJ hfree PRIV hmstk
          rw [hdstk] at PRIV'
          refine .inl ⟨_, plus_one (.Ireturn _ _ _ _ _ _ _ _ h FREE), ?_⟩
          refine .ret _ _ _ _ _ _ _ ?_ ?_ (free_inject_both MINJ hfree FREE PRIV')
          · refine match_stacks_bound
              (match_stacks_free_right (match_stacks_free_left hms hfree) FREE) ?_
            rw [Mem.nextblock_free FREE]; exact Nat.le_of_lt (lt_of_validBlock VB)
          · cases or with
            | none => exact .undef _
            | some r => exact agree_val_reg r AG
      | return_inlined _ _ _ _ rinfo h hret =>
        refine .inr ⟨by simp only [measure]; omega, rfl, ?_⟩
        refine .return_regular _ _ _ _ _ _ _ _ _ _ _ or rinfo
          (match_stacks_inside_invariant (Val.inject_incr_refl F) MS rs' (fun _ _ => rfl)
            (fun _ _ _ hf _ => hf) (fun _ _ _ _ _ _ hp => perm_free_inv hfree hp)
            (fun _ _ _ h => h) (fun _ _ _ _ _ h => h))
          hret h ?_ (Mem.free_left_inject MINJ hfree) VB PRIV' S1 S2 S3
        cases or with
        | none => rfl
        | some r => exact agree_val_reg r AG
  | function_internal s f args m m1 stk htyp halloc =>
    obtain ⟨hstk_eq, hm1⟩ := alloc_eq_nextblock halloc
    have hmx := max_stacksize_ge f.fn_stacksize
    cases hm with
    | call _ _ _ _ stk' fd' args' m' F MS FD VINJ MINJ =>
      simp only [transfFundef, ASTFundef.transfPartial] at FD
      split at FD
      · next f' hf =>
        cases FD
        cases transf_function_spec_compat COMPAT0 hf with
        | intro fenv _ _ ctx COMPAT FB hdstk hretn hsig hparams hentry hs1 hs2 =>
          have hd := tr_funbody_dstk FB
          have hmstk := tr_funbody_mstk FB
          have hle : f.fn_stacksize ≤ f'.fn_stacksize := by zomega
          obtain ⟨F', m1', sp', A, B, C, D, E⟩ := Mem.alloc_parallel_inject MINJ halloc (Int.le_refl 0) hle
          obtain ⟨hsp_eq, hm1'⟩ := alloc_eq_nextblock A
          have hstep := RTL.Step.function_internal (ge := tprog.globalenv) stk' f' args' m' m1' sp'
            (by rw [hsig]; exact Val.has_argtype_list_inject htyp VINJ) A
          rw [hentry, hparams] at hstep
          refine .inl ⟨_, plus_one hstep, ?_⟩
          have MS' : MatchStacks prog F' m1 m1' s stk' sp' := by
            rw [hsp_eq]
            refine match_stacks_invariant C MS ?_ ?_ ?_ ?_
            · intro b1 b2 d hf hlt
              by_cases e : b1 = stk
              · rw [e, D] at hf; cases hf; rw [hsp_eq] at hlt; exact absurd hlt (Nat.lt_irrefl _)
              · rwa [E b1 e] at hf
            · intro b1 b2 d o hf hlt hp
              rw [hm1] at hp
              have hi := Mem.perm_alloc_inv hp
              by_cases e : b1 = stk
              · rw [e, D] at hf; cases hf; rw [hsp_eq] at hlt; exact absurd hlt (Nat.lt_irrefl _)
              · rwa [if_neg (fun e' => e (e'.trans hstk_eq.symm))] at hi
            · intro b o _ hp
              rw [hm1']; exact Mem.perm_alloc_1 hp
            · intro b o k p hlt hp
              rw [hm1'] at hp
              have hi := Mem.perm_alloc_inv hp
              rwa [if_neg (fun e => by rw [e] at hlt; exact Nat.lt_irrefl _ hlt)] at hi
          refine .regular _ _ _ _ _ _ _ _ _ _ _ _ fenv ctx (.base _ _ _ _ _ _ MS' hretn hdstk) COMPAT
            FB (agree_regs_init_regs f.fn_params args args' (Val.inject_incr_inject_list C VINJ)
              (tr_funbody_params FB)) (by rw [hdstk]; exact D) B
            (by rw [hm1', hsp_eq]; exact Mem.valid_new_block m' 0 _) ?_ hs1 hs2 ?_
          · intro ofs h1 h2
            refine ⟨?_, ?_⟩
            · rw [hm1', hsp_eq]; exact Mem.perm_alloc_same m' 0 _ ofs .Cur (by zomega) h2
            · intro b δ hf hp
              rw [hm1] at hp
              have hi := Mem.perm_alloc_inv hp
              by_cases e : b = stk
              · rw [e, D] at hf; cases hf
                rw [if_pos (e.trans hstk_eq)] at hi
                zomega
              · rw [E b e] at hf
                have := lt_of_validBlock (MINJ.mappedblocks _ _ _ hf)
                rw [hsp_eq] at this; exact Nat.lt_irrefl _ this
          · intro o h
            rw [hm1', hsp_eq] at h
            have hi := Mem.perm_alloc_inv h
            rw [if_pos rfl] at hi
            zomega
      · cases FD
    | call_regular _ _ _ _ stk' f' sp' rs' m' F fenv ctx ctx' pc' pc1' rargs MS COMPAT FB BELOW NOP
        MOVES VINJ MINJ VB PRIV S1 S2 S3 =>
      have hd := tr_funbody_dstk FB
      have hmstk := tr_funbody_mstk FB
      obtain ⟨F', A, B, C, D⟩ := Mem.alloc_left_mapped_inject (delta := ctx.dstk) MINJ halloc VB
        ⟨hd.1, by zomega⟩ (.inr (Int.le_refl _))
        (fun ofs k p hp => .inr (by have := S3 ofs (perm_max_nonempty hp); zomega))
        (fun ofs k p h1 h2 => by
          have := range_private_perms PRIV (ofs + ctx.dstk) (by zomega) (by zomega)
          exact Mem.perm_implies (Mem.perm_cur this) (by cases p <;> rfl))
        (by rw [Int.sub_zero]; exact tr_funbody_align FB)
        (fun b δ' ofs k p hf hp h1 h2 => (PRIV (ofs + δ') (by zomega) (by zomega)).2 b δ' hf
          (by rw [Int.add_sub_cancel]; exact perm_max_nonempty hp))
      obtain ⟨rs2, P, Q, R⟩ := tr_moves_init_regs tprog.globalenv (stk := stk') (f := f')
        (sp := .Vptr sp' Ptrofs.zero) (m := m') BELOW f.fn_params rargs args pc1'
        (spc ctx f.fn_entrypoint) rs' MOVES (tr_funbody_params FB) VINJ
      refine .inl ⟨_, plus_left (.Inop _ _ _ _ _ _ _ NOP) P rfl, ?_⟩
      exact .regular _ _ _ _ _ _ _ _ _ _ _ _ fenv ctx
        (match_stacks_inside_alloc_left halloc B D
          (match_stacks_inside_invariant (Val.inject_incr_refl F) MS rs2 R (fun _ _ _ hf _ => hf)
            (fun _ _ _ _ _ _ hp => hp) (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)) C (Int.le_refl _))
        COMPAT FB (agree_regs_incr Q B) C A VB
        (by rw [hmstk]; exact range_private_alloc_left PRIV halloc C D) S1 S2 S3
  | function_external s ef args res t m m1 hec =>
    cases hm with
    | call _ _ _ _ stk' fd' args' m' F MS FD VINJ MINJ =>
      obtain ⟨G, hG⟩ := match_stacks_globalenvs MS
      obtain ⟨F1, v1, m1', A, B, C, D, E, J, K⟩ := externalCall_memInject ef hext hasm _ _ _ _ _ _ _
        _ _ _ hG.symbolsInject hec MINJ VINJ
      have MP := externalCall_memProps ef (Genv.toSenv prog.globalenv)
        (fun n sg => hextp n sg _) (fun n sg => hasmp n sg _)
      have MP1 : ∀ b ofs p, Mem.validBlock m b = true → Mem.perm m1 b ofs .Max p = true →
          Mem.perm m b ofs .Max p = true := fun b ofs p hv hp => MP.maxPerm _ _ _ _ _ b ofs p hec hv hp
      have MP2 : ∀ b ofs p, Mem.validBlock m' b = true → Mem.perm m1' b ofs .Max p = true →
          Mem.perm m' b ofs .Max p = true := fun b ofs p hv hp => MP.maxPerm _ _ _ _ _ b ofs p A hv hp
      cases FD
      exact .inl ⟨_, plus_one (.function_external _ _ _ _ _ _ _
          (by rw [senv_preserved TRANSF]; exact A)),
        .ret _ _ _ _ _ _ _ (match_stacks_bound (match_stacks_extcall MP1 MP2 E MINJ J K MS
          (Nat.le_refl _)) E.nextblock_le) B C⟩
  | «return» res f sp pc rs s vres m =>
    cases hm with
    | ret _ _ _ stk' v' m' F MS VINJ MINJ =>
      cases MS with
      | cons _ _ sp0 _ _ _ f' sp' rs' stk'' _ fenv ctx hms hc hfb hag hsp hpriv hs1 hs2 hssz hres
          hb =>
        exact .inl ⟨_, plus_one (.return _ _ _ _ _ _ _ _),
          .regular _ _ _ _ _ _ _ _ _ _ _ _ _ _ (match_stacks_inside_set_reg _ _ hms) hc hfb
            (agree_set_reg hag VINJ hres) hsp MINJ (validBlock_of_lt hb) hpriv hs1 hs2 hssz⟩
      | untailcall _ res' f' sp' rpc rs' stk'' _ ctx hms hpriv hs1 hs2 hssz hret hb =>
        cases hms with
        | base _ _ _ _ _ _ _ hret0 _ => rw [hret] at hret0; cases hret0
        | inlined _ _ sp0 _ _ _ _ _ fenv _ _ _ ctx' hms' hc hfb hag hsp hpad hres hret0 hbelow
            hsbelow =>
          rw [hret] at hret0
          cases hret0
          exact .inl ⟨_, plus_one (.return _ _ _ _ _ _ _ _),
            .regular _ _ _ _ _ _ _ _ _ _ _ _ _ _ (match_stacks_inside_set_reg _ _ hms') hc hfb
              (agree_set_reg hag VINJ hres) hsp MINJ (validBlock_of_lt hb)
              (range_private_concat hpad hpriv) hs1 hs2 hssz⟩
    | return_regular _ _ _ stk' f' sp' rs' m' F ctx pc' or rinfo MS RET AT VINJ MINJ VB PRIV S1 S2
        S3 =>
      cases MS with
      | base _ _ _ _ _ _ _ hret0 _ => rw [hret0] at RET; cases RET
      | inlined _ _ sp0 _ _ _ _ _ fenv _ _ _ ctx' hms' hc hfb hag hsp hpad hres hret0 hbelow
          hsbelow =>
        rw [hret0] at RET
        cases RET
        have PRIV' := range_private_concat hpad PRIV
        cases or with
        | some r =>
          exact .inl ⟨_, plus_one (.Iop _ _ _ _ _ _ .Omove [sreg ctx r] _ _ _ AT rfl),
            .regular _ _ _ _ _ _ _ _ _ _ _ _ _ _ (match_stacks_inside_set_reg _ _ hms') hc hfb
              (agree_set_reg hag VINJ hres) hsp MINJ VB PRIV' S1 S2 S3⟩
        | none =>
          simp only at VINJ
          subst VINJ
          exact .inl ⟨_, plus_one (.Inop _ _ _ _ _ _ _ AT),
            .regular _ _ _ _ _ _ _ _ _ _ _ _ _ _ hms' hc hfb
              (agree_set_reg_undef' hag) hsp MINJ VB PRIV' S1 S2 S3⟩

end SIMULATION

end Inlining
end RiscV
end CC
