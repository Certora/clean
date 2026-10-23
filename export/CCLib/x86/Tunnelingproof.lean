/-
  [x86-64 instance of `CCLib/backend/Tunnelingproof.lean`: the same development, in
  namespace `CC.X86`, over the x86-64 operators, registers and conventions.]

  Correctness proof for the branch tunneling optimization — port of the
  `PRESERVATION` section of `backend/Tunnelingproof.v` (the branch-map part
  is in `TunnelingBranch.lean`).

  Main result: `Tunnelingproof.transf_program_correct`, a forward simulation
  from the LTL semantics of a program to the LTL semantics of
  `Tunneling.tunnelProgram` of it.

  Differences from Rocq: `Senv.equiv` is the equality of symbol
  environments `senv_transf`.  Rocq's `external_call_mem_extends` comes
  from the axiom `external_functions_properties` (and
  `inline_assembly_properties`); in the port the semantics of external
  functions and inline assembly are uninterpreted, so the corresponding
  property `ExtcallMemExtends` is an explicit hypothesis (`hext`, `hasm`)
  of the theorem.
-/
import CCLib.x86.TunnelingBranch
import CCLib.x86.OpInject
import CCLib.common.EventsExtends
import CCLib.x86.CleanupLabelsproof
import CCLib.x86.Renumberproof

namespace CC
namespace X86

/- `Archi.win64` (a Rocq `Parameter`): whether the Windows x86-64 ABI is used. -/
variable (win64 : Bool)
namespace Tunnelingproof

open LTL Tunneling UnionFind UnionFind.UF Smallstep

/-- `tunneled_block` -/
def tunneledBlock (f : LTL.Function) (b : Bblock) : Bblock := tunnelBlock (recordGotos f) b

/-- `locmap_lessdef` -/
def LocmapLessdef (ls1 ls2 : LTL.Locset) : Prop := ∀ l, Val.Lessdef (ls1 l) (ls2 l)

/-! ### Properties of `locmap_lessdef` -/

/-- `reglist_lessdef` -/
theorem reglist_lessdef {ls1 ls2 : LTL.Locset} (h : LocmapLessdef ls1 ls2) :
    ∀ rl, Val.LessdefList (reglist ls1 rl) (reglist ls2 rl)
  | [] => .nil
  | r :: rl => .cons (h (.R r)) (reglist_lessdef h rl)

theorem loadResult_undef (chunk : Chunk) : Val.loadResult chunk .Vundef = .Vundef := by
  cases chunk <;> rfl

/-- `locmap_set_lessdef` -/
theorem locmap_set_lessdef {ls1 ls2 : LTL.Locset} {v1 v2 : Val} (l : Loc)
    (h : LocmapLessdef ls1 ls2) (hv : Val.Lessdef v1 v2) :
    LocmapLessdef (Locmap.set l v1 ls1) (Locmap.set l v2 ls2) := by
  intro l'
  simp only [Locmap.set]
  split
  · cases l with
    | R _ => exact hv
    | S _ _ ty => exact Val.load_result_lessdef _ hv
  · split
    · exact h l'
    · exact .refl _

/-- `locmap_set_undef_lessdef` -/
theorem locmap_set_undef_lessdef {ls1 ls2 : LTL.Locset} (l : Loc) (h : LocmapLessdef ls1 ls2) :
    LocmapLessdef (Locmap.set l .Vundef ls1) ls2 := by
  intro l'
  simp only [Locmap.set]
  split
  · cases l with
    | R _ => exact .undef _
    | S _ _ ty =>
        show Val.Lessdef (Val.loadResult (Chunk.ofTyp ty) .Vundef) _
        rw [loadResult_undef]; exact .undef _
  · split
    · exact h l'
    · exact .undef _

/-- `locmap_undef_regs_lessdef` -/
theorem locmap_undef_regs_lessdef {ls1 ls2 : LTL.Locset} (h : LocmapLessdef ls1 ls2) :
    ∀ rl, LocmapLessdef (undefRegs rl ls1) (undefRegs rl ls2)
  | [] => h
  | _ :: rl => locmap_set_lessdef _ (locmap_undef_regs_lessdef h rl) (.refl _)

/-- `locmap_undef_regs_lessdef_1` -/
theorem locmap_undef_regs_lessdef_1 {ls1 ls2 : LTL.Locset} (h : LocmapLessdef ls1 ls2) :
    ∀ rl, LocmapLessdef (undefRegs rl ls1) ls2
  | [] => h
  | _ :: rl => locmap_set_undef_lessdef _ (locmap_undef_regs_lessdef_1 h rl)

/-- `locmap_getpair_lessdef` -/
theorem locmap_getpair_lessdef {ls1 ls2 : LTL.Locset} (h : LocmapLessdef ls1 ls2) :
    ∀ p : RPair Loc, Val.Lessdef (Locmap.getpair p ls1) (Locmap.getpair p ls2)
  | .One l => h l
  | .Twolong l1 l2 => Val.longofwords_lessdef (h l1) (h l2)

/-- `locmap_getpairs_lessdef` -/
theorem locmap_getpairs_lessdef {ls1 ls2 : LTL.Locset} (h : LocmapLessdef ls1 ls2) :
    ∀ pl : List (RPair Loc), Val.LessdefList (pl.map (fun p => Locmap.getpair p ls1))
      (pl.map (fun p => Locmap.getpair p ls2))
  | [] => .nil
  | p :: pl => .cons (locmap_getpair_lessdef h p) (locmap_getpairs_lessdef h pl)

/-- `locmap_setpair_lessdef` -/
theorem locmap_setpair_lessdef {ls1 ls2 : LTL.Locset} {v1 v2 : Val} (h : LocmapLessdef ls1 ls2)
    (hv : Val.Lessdef v1 v2) :
    ∀ p : RPair Mreg, LocmapLessdef (Locmap.setpair p v1 ls1) (Locmap.setpair p v2 ls2)
  | .One _ => locmap_set_lessdef _ h hv
  | .Twolong _ _ => locmap_set_lessdef _ (locmap_set_lessdef _ h (Val.hiword_lessdef hv))
      (Val.loword_lessdef hv)

/-- `locmap_setres_lessdef` -/
theorem locmap_setres_lessdef :
    ∀ (res : BuiltinRes Mreg) {ls1 ls2 : LTL.Locset} {v1 v2 : Val}, LocmapLessdef ls1 ls2 →
      Val.Lessdef v1 v2 → LocmapLessdef (Locmap.setres res v1 ls1) (Locmap.setres res v2 ls2)
  | .BR _, _, _, _, _, h, hv => locmap_set_lessdef _ h hv
  | .BR_none, _, _, _, _, h, _ => h
  | .BR_splitlong hi lo, _, _, _, _, h, hv =>
      locmap_setres_lessdef lo (locmap_setres_lessdef hi h (Val.hiword_lessdef hv))
        (Val.loword_lessdef hv)

/-- `locmap_undef_caller_save_regs_lessdef` -/
theorem locmap_undef_caller_save_regs_lessdef {ls1 ls2 : LTL.Locset} (h : LocmapLessdef ls1 ls2) :
    LocmapLessdef (undefCallerSaveRegs win64 ls1) (undefCallerSaveRegs win64 ls2) := by
  intro l
  cases l with
  | R r =>
      simp only [undefCallerSaveRegs]
      split
      · exact h _
      · exact .refl _
  | S sl ofs ty => cases sl <;> first | exact .refl _ | exact h _

/-- `call_regs_lessdef` -/
theorem call_regs_lessdef {ls1 ls2 : LTL.Locset} (h : LocmapLessdef ls1 ls2) :
    LocmapLessdef (callRegs ls1) (callRegs ls2) := by
  intro l
  cases l with
  | R r => exact h _
  | S sl ofs ty => cases sl <;> first | exact .refl _ | exact h _

/-- `return_regs_lessdef` -/
theorem return_regs_lessdef {caller1 callee1 caller2 callee2 : LTL.Locset}
    (h1 : LocmapLessdef caller1 caller2) (h2 : LocmapLessdef callee1 callee2) :
    LocmapLessdef (returnRegs win64 caller1 callee1) (returnRegs win64 caller2 callee2) := by
  intro l
  cases l with
  | R r =>
      simp only [returnRegs]
      split
      · exact h1 _
      · exact h2 _
  | S sl ofs ty => cases sl <;> first | exact .refl _ | exact h1 _

/-! ### The simulation -/

section PRESERVATION
variable (win64 : Bool) (prog : LTL.Program)

local notation "tprog" => Tunneling.tunnelProgram prog

theorem symbols_preserved (id : Ident) :
    Genv.findSymbol (tprog).globalenv id = Genv.findSymbol prog.globalenv id :=
  find_symbol_transf tunnelFundef prog id

theorem senv_preserved : Genv.toSenv (tprog).globalenv = Genv.toSenv prog.globalenv :=
  senv_transf tunnelFundef prog

theorem functions_translated {v : Val} {f : LTL.Fundef}
    (h : Genv.findFunct prog.globalenv v = some f) :
    Genv.findFunct (tprog).globalenv v = some (tunnelFundef f) :=
  find_funct_transf tunnelFundef h

theorem function_ptr_translated {b : Block} {f : LTL.Fundef}
    (h : Genv.findFunctPtr prog.globalenv b = some f) :
    Genv.findFunctPtr (tprog).globalenv b = some (tunnelFundef f) :=
  find_funct_ptr_transf tunnelFundef h

/-- `sig_preserved` -/
theorem sig_preserved (f : LTL.Fundef) : LTL.funsig (tunnelFundef f) = LTL.funsig f := by
  cases f <;> rfl

/-- `find_function_translated` -/
theorem find_function_translated {ros : Sum Mreg Ident} {ls tls : LTL.Locset} {fd : LTL.Fundef}
    (hls : LocmapLessdef ls tls) (h : LTL.findFunction prog.globalenv ros ls = some fd) :
    LTL.findFunction (tprog).globalenv ros tls = some (tunnelFundef fd) := by
  cases ros with
  | inl r =>
      simp only [LTL.findFunction] at h ⊢
      have hl := hls (.R r)
      generalize ls (.R r) = v at hl h
      generalize tls (.R r) = v' at hl ⊢
      cases hl with
      | refl => exact functions_translated prog h
      | undef => cases h
  | inr id =>
      simp only [LTL.findFunction, symbols_preserved] at h ⊢
      cases e : Genv.findSymbol prog.globalenv id with
      | none => rw [e] at h; cases h
      | some b => rw [e] at h; exact function_ptr_translated prog h

/-- `match_stackframes` -/
inductive MatchStackframes : LTL.Stackframe → LTL.Stackframe → Prop where
  | intro (f sp ls0 bb tls0) : LocmapLessdef ls0 tls0 →
      MatchStackframes (.Stackframe f sp ls0 bb)
        (.Stackframe (tunnelFunction f) sp tls0 (tunneledBlock f bb))

/-- `match_states` -/
inductive MatchStates : LTL.State → LTL.State → Prop where
  | intro (s f sp pc ls m ts tls tm) : ListForall2 MatchStackframes s ts →
      LocmapLessdef ls tls → Mem.Extends m tm →
      MatchStates (.State s f sp pc ls m)
        (.State ts (tunnelFunction f) sp (branchTarget f pc) tls tm)
  | block (s f sp bb ls m ts tls tm) : ListForall2 MatchStackframes s ts →
      LocmapLessdef ls tls → Mem.Extends m tm →
      MatchStates (.Block s f sp bb ls m)
        (.Block ts (tunnelFunction f) sp (tunneledBlock f bb) tls tm)
  | interm_branch (s f sp pc bb ls m ts tls tm) : ListForall2 MatchStackframes s ts →
      LocmapLessdef ls tls → Mem.Extends m tm →
      MatchStates (.Block s f sp (.Lbranch pc :: bb) ls m)
        (.State ts (tunnelFunction f) sp (branchTarget f pc) tls tm)
  | interm_cond (s f sp cond args pc1 pc2 bb ls m ts tls tm) :
      ListForall2 MatchStackframes s ts → LocmapLessdef ls tls → Mem.Extends m tm →
      branchTarget f pc1 = branchTarget f pc2 →
      MatchStates (.Block s f sp (.Lcond cond args pc1 pc2 :: bb) ls m)
        (.State ts (tunnelFunction f) sp (branchTarget f pc1) tls tm)
  | call (s f ls m ts tls tm) : ListForall2 MatchStackframes s ts →
      LocmapLessdef ls tls → Mem.Extends m tm →
      MatchStates (.Callstate s f ls m) (.Callstate ts (tunnelFundef f) tls tm)
  | ret (s ls m ts tls tm) : ListForall2 MatchStackframes s ts →
      LocmapLessdef ls tls → Mem.Extends m tm →
      MatchStates (.Returnstate s ls m) (.Returnstate ts tls tm)

/-- `measure` -/
noncomputable def measure : LTL.State → Nat
  | .State _ f _ pc _ _ => countGotos f pc * 2
  | .Block _ f _ (.Lbranch pc :: _) _ _ => countGotos f pc * 2 + 1
  | .Block _ f _ (.Lcond _ _ pc1 pc2 :: _) _ _ => max (countGotos f pc1) (countGotos f pc2) * 2 + 1
  | _ => 0

/-- `match_parent_locset` -/
theorem match_parent_locset {s ts : List LTL.Stackframe} (h : ListForall2 MatchStackframes s ts) :
    LocmapLessdef (LTL.parentLocset s) (LTL.parentLocset ts) := by
  cases h with
  | nil => intro _; exact .refl _
  | cons hm _ => cases hm with
    | intro _ _ _ _ _ hl => exact hl

theorem tunnelFunction_code (f : LTL.Function) (pc : Node) :
    (tunnelFunction f).fn_code.get pc = (f.fn_code.get pc).map (tunneledBlock f) := by
  simp [tunnelFunction]; rfl

theorem tunneledBlock_cons (f : LTL.Function) (i : LTL.Instruction) (bb : Bblock) :
    tunneledBlock f (i :: bb) = tunnelInstr (recordGotos f) i :: tunneledBlock f bb := rfl

/-- `tunnel_step_correct` -/
theorem tunnel_step_correct
    (hext : ∀ name sg ge, ExtcallMemExtends (externalFunctionsSem name sg) ge)
    (hasm : ∀ name sg ge, ExtcallMemExtends (inlineAssemblySem name sg) ge)
    {st1 t st2} (hst : LTL.Step win64 prog.globalenv st1 t st2) {st1'}
    (hm : MatchStates st1 st1') :
    (∃ st2', LTL.Step win64 (tprog).globalenv st1' t st2' ∧ MatchStates st2 st2') ∨
    (measure st2 < measure st1 ∧ t = E0 ∧ MatchStates st2 st1') := by
  have hsym := symbols_preserved prog
  have hsenv := senv_preserved prog
  have hec : ∀ ef, ExtcallMemExtends (externalCall ef) (Genv.toSenv prog.globalenv) :=
    fun ef => externalCall_memExtends ef _ (fun n sg => hext n sg _) (fun n sg => hasm n sg _)
  cases hst with
  | start_block s f sp pc rs m bb hget =>
    cases hm with
    | intro _ _ _ _ _ _ ts tls tm STK LS MEM =>
      have DEFAULT : branchTarget f pc = pc →
          ∃ st2', LTL.Step win64 (tprog).globalenv
            (.State ts (tunnelFunction f) sp (branchTarget f pc) tls tm) E0 st2' ∧
            MatchStates (.Block s f sp bb rs m) st2' := fun h => by
        rw [h]
        exact ⟨_, .start_block _ _ _ _ _ _ _ (by rw [tunnelFunction_code, hget]; rfl),
          .block _ _ _ _ _ _ _ _ _ STK LS MEM⟩
      have hb := record_gotos_correct f pc
      rw [hget] at hb
      match bb, hb, DEFAULT with
      | [], hb, DEFAULT => exact .inl (DEFAULT hb)
      | i :: bb', hb, DEFAULT =>
        cases i
        case Lbranch s0 =>
          rcases hb with hb | ⟨B, C⟩
          · exact .inl (DEFAULT hb)
          · refine .inr ⟨by simp only [measure]; omega, rfl, ?_⟩
            show MatchStates _ (.State ts (tunnelFunction f) sp ((recordGotos f).repr pc) tls tm)
            rw [B]
            exact .interm_branch _ _ _ _ _ _ _ _ _ _ STK LS MEM
        case Lcond cond args s1 s2 =>
          rcases hb with hb | ⟨B, C, D, E⟩
          · exact .inl (DEFAULT hb)
          · refine .inr ⟨by simp only [measure]; omega, rfl, ?_⟩
            show MatchStates _ (.State ts (tunnelFunction f) sp ((recordGotos f).repr pc) tls tm)
            rw [B]
            exact .interm_cond _ _ _ _ _ _ _ _ _ _ _ _ _ STK LS MEM (B.symm.trans C)
        all_goals exact .inl (DEFAULT hb)
  | Lop s f sp op args res bb rs m v rs' hv hrs =>
    cases hm with
    | block _ _ _ _ _ _ ts tls tm STK LS MEM =>
      subst hrs
      obtain ⟨tv, EV, LD⟩ := Op.evalOperation_lessdef _ _ _ (reglist_lessdef LS args) MEM hv
      refine .inl ⟨_, .Lop _ _ _ _ _ _ _ _ _ tv _ ?_ rfl,
        .block _ _ _ _ _ _ _ _ _ STK
          (locmap_set_lessdef _ (locmap_undef_regs_lessdef LS _) LD) MEM⟩
      rw [Op.evalOperation_preserved prog.globalenv (tprog).globalenv hsym]; exact EV
  | Lload s f sp chunk addr args dst bb rs m a v rs' ha hv hrs =>
    cases hm with
    | block _ _ _ _ _ _ ts tls tm STK LS MEM =>
      subst hrs
      obtain ⟨ta, EV, LD⟩ := Op.evalAddressing_lessdef _ _ _ (reglist_lessdef LS args) ha
      obtain ⟨tv, LOAD, LD'⟩ := Mem.loadv_extends MEM hv LD
      refine .inl ⟨_, .Lload _ _ _ _ _ _ _ _ _ _ ta tv _ ?_ LOAD rfl,
        .block _ _ _ _ _ _ _ _ _ STK
          (locmap_set_lessdef _ (locmap_undef_regs_lessdef LS _) LD') MEM⟩
      rw [Op.evalAddressing_preserved prog.globalenv (tprog).globalenv hsym]; exact EV
  | Lgetstack s f sp sl ofs ty dst bb rs m rs' hrs =>
    cases hm with
    | block _ _ _ _ _ _ ts tls tm STK LS MEM =>
      subst hrs
      exact .inl ⟨_, .Lgetstack _ _ _ _ _ _ _ _ _ _ _ rfl,
        .block _ _ _ _ _ _ _ _ _ STK
          (locmap_set_lessdef _ (locmap_undef_regs_lessdef LS _) (LS _)) MEM⟩
  | Lsetstack s f sp src sl ofs ty bb rs m rs' hrs =>
    cases hm with
    | block _ _ _ _ _ _ ts tls tm STK LS MEM =>
      subst hrs
      exact .inl ⟨_, .Lsetstack _ _ _ _ _ _ _ _ _ _ _ rfl,
        .block _ _ _ _ _ _ _ _ _ STK
          (locmap_set_lessdef _ (locmap_undef_regs_lessdef LS _) (LS _)) MEM⟩
  | Lstore s f sp chunk addr args src bb rs m a rs' m' ha hs hrs =>
    subst rs'
    cases hm with
    | block _ _ _ _ _ _ ts tls tm STK LS MEM =>
      obtain ⟨ta, EV, LD⟩ := Op.evalAddressing_lessdef _ _ _ (reglist_lessdef LS args) ha
      obtain ⟨tm', STORE, MEM'⟩ := Mem.storev_extends MEM hs LD (LS _)
      refine .inl ⟨_, .Lstore _ _ _ _ _ _ _ _ _ _ ta _ tm' ?_ STORE rfl,
        .block _ _ _ _ _ _ _ _ _ STK (locmap_undef_regs_lessdef LS _) MEM'⟩
      rw [Op.evalAddressing_preserved prog.globalenv (tprog).globalenv hsym]; exact EV
  | Lcall s f sp sig ros bb rs m fd hf hsig =>
    cases hm with
    | block _ _ _ _ _ _ ts tls tm STK LS MEM =>
      exact .inl ⟨_, .Lcall _ _ _ _ _ _ _ _ _ (find_function_translated prog LS hf)
        (by rw [sig_preserved]; exact hsig),
        .call _ _ _ _ _ _ _ (.cons (.intro _ _ _ _ _ LS) STK) LS MEM⟩
  | Ltailcall s f sp sig ros bb rs m fd rs' m' hrs hf hsig hfree =>
    cases hm with
    | block _ _ _ _ _ _ ts tls tm STK LS MEM =>
      subst hrs
      obtain ⟨tm', FREE, MEM'⟩ := Mem.free_parallel_extends MEM hfree
      have LS' := return_regs_lessdef win64 (match_parent_locset STK) LS
      exact .inl ⟨_, .Ltailcall _ _ _ _ _ _ _ _ _ _ tm' rfl
        (find_function_translated prog LS' hf) (by rw [sig_preserved]; exact hsig) FREE,
        .call _ _ _ _ _ _ _ STK LS' MEM'⟩
  | Lbuiltin s f sp ef args res bb rs m vargs t vres rs' m' hargs hcall hrs =>
    cases hm with
    | block _ _ _ _ _ _ ts tls tm STK LS MEM =>
      subst hrs
      obtain ⟨tvargs, EVA, LDA⟩ := evalBuiltinArgs_lessdef LS MEM hargs
      obtain ⟨tvres, tm', A, B, C, _⟩ := hec ef _ _ _ _ _ _ _ hcall MEM LDA
      refine .inl ⟨_, .Lbuiltin _ _ _ _ _ _ _ _ _ tvargs t tvres _ tm' ?_ ?_ rfl,
        .block _ _ _ _ _ _ _ _ _ STK
          (locmap_setres_lessdef _ (locmap_undef_regs_lessdef LS _) B) C⟩
      · rw [hsenv]; exact EVA
      · rw [hsenv]; exact A
  | Lbranch s f sp pc bb rs m =>
    cases hm with
    | block _ _ _ _ _ _ ts tls tm STK LS MEM =>
      exact .inl ⟨_, .Lbranch _ _ _ _ _ _ _, .intro _ _ _ _ _ _ _ _ _ STK LS MEM⟩
    | interm_branch _ _ _ _ _ _ _ ts tls tm STK LS MEM =>
      exact .inr ⟨by simp only [measure]; omega, rfl, .intro _ _ _ _ _ _ _ _ _ STK LS MEM⟩
  | Lcond s f sp cond args pc1 pc2 bb rs b pc rs' m hc hpc hrs =>
    subst pc rs'
    cases hm with
    | block _ _ _ _ _ _ ts tls tm STK LS MEM =>
      rw [tunneledBlock_cons]
      simp only [tunnelInstr]
      split
      · rename_i e
        refine .inl ⟨_, .Lbranch _ _ _ _ _ _ _, ?_⟩
        have : (recordGotos f).repr pc1 = branchTarget f (if b then pc1 else pc2) := by
          cases b
          · exact e
          · rfl
        rw [this]
        exact .intro _ _ _ _ _ _ _ _ _ STK (locmap_undef_regs_lessdef_1 LS _) MEM
      · refine .inl ⟨_, .Lcond _ _ _ _ _ _ _ _ _ b _ _ _
          (Op.evalCondition_lessdef (reglist_lessdef LS args) MEM hc) rfl rfl, ?_⟩
        have : (if b then (recordGotos f).repr pc1 else (recordGotos f).repr pc2) =
            branchTarget f (if b then pc1 else pc2) := by cases b <;> rfl
        rw [this]
        exact .intro _ _ _ _ _ _ _ _ _ STK (locmap_undef_regs_lessdef LS _) MEM
    | interm_cond _ _ _ _ _ _ _ _ _ _ ts tls tm STK LS MEM SAME =>
      refine .inr ⟨by cases b <;> simp only [measure, if_true, Bool.false_eq_true, if_false] <;> omega, rfl, ?_⟩
      have : branchTarget f pc1 = branchTarget f (if b then pc1 else pc2) := by
        cases b
        · exact SAME
        · rfl
      rw [this]
      exact .intro _ _ _ _ _ _ _ _ _ STK (locmap_undef_regs_lessdef_1 LS _) MEM
  | Ljumptable s f sp arg tbl bb rs m n pc rs' hn hl hrs =>
    cases hm with
    | block _ _ _ _ _ _ ts tls tm STK LS MEM =>
      subst hrs
      have htls : tls (.R arg) = .Vint n := by
        have := LS (.R arg)
        rw [hn] at this
        generalize tls (.R arg) = v at this ⊢
        cases this
        rfl
      exact .inl ⟨_, .Ljumptable _ _ _ _ _ _ _ _ n _ _ htls (Renumberproof.listNthZ_map _ hl) rfl,
        .intro _ _ _ _ _ _ _ _ _ STK (locmap_undef_regs_lessdef LS _) MEM⟩
  | Lreturn s f sp bb rs m m' hfree =>
    cases hm with
    | block _ _ _ _ _ _ ts tls tm STK LS MEM =>
      obtain ⟨tm', FREE, MEM'⟩ := Mem.free_parallel_extends MEM hfree
      exact .inl ⟨_, .Lreturn _ _ _ _ _ _ _ FREE,
        .ret _ _ _ _ _ _ STK (return_regs_lessdef win64 (match_parent_locset STK) LS) MEM'⟩
  | function_internal s f rs m m' sp rs' halloc hrs =>
    cases hm with
    | call _ _ _ _ ts tls tm STK LS MEM =>
      subst hrs
      obtain ⟨tm', ALLOC, MEM'⟩ := Mem.alloc_extends MEM halloc (Int.le_refl _) (Int.le_refl _)
      exact .inl ⟨_, .function_internal _ _ _ _ _ _ _ ALLOC rfl,
        .intro _ _ _ _ _ _ _ _ _ STK
          (locmap_undef_regs_lessdef (call_regs_lessdef LS) _) MEM'⟩
  | function_external s ef t args res rs m rs' m' hargs hcall hrs =>
    cases hm with
    | call _ _ _ _ ts tls tm STK LS MEM =>
      subst hargs hrs
      obtain ⟨tvres, tm', A, B, C, _⟩ :=
        hec ef _ _ _ _ _ _ _ hcall MEM (locmap_getpairs_lessdef LS _)
      refine .inl ⟨_, .function_external _ _ _ _ _ _ _ _ _ rfl ?_ rfl,
        .ret _ _ _ _ _ _ STK
          (locmap_setpair_lessdef (locmap_undef_caller_save_regs_lessdef win64 LS) B _) C⟩
      rw [hsenv]; exact A
  | «return» f sp rs1 bb s rs m =>
    cases hm with
    | ret _ _ _ ts tls tm STK LS MEM =>
      cases STK with
      | cons hf STK =>
        cases hf with
        | intro _ _ _ _ tls0 _ =>
          exact .inl ⟨_, .return _ _ _ _ _ _ _, .block _ _ _ _ _ _ _ _ _ STK LS MEM⟩

/-- `transf_initial_states` -/
theorem transf_initial_states {st1 : LTL.State} (h : LTL.InitialState prog st1) :
    ∃ st2, LTL.InitialState (tprog) st2 ∧ MatchStates st1 st2 := by
  cases h with
  | intro b f m0 hm hs hf hsig =>
      refine ⟨_, .intro b (tunnelFundef f) m0 ?_ ?_ (function_ptr_translated prog hf) ?_,
        .call _ _ _ _ _ _ _ .nil (fun _ => .refl _) (Mem.extends_refl _)⟩
      · exact (init_mem_transf tunnelFundef prog).trans hm
      · rw [symbols_preserved]; exact hs
      · rw [sig_preserved]; exact hsig

/-- `transf_final_states` -/
theorem transf_final_states {st1 st2 : LTL.State} {r : Integers.Int} (hm : MatchStates st1 st2)
    (h : LTL.FinalState st1 r) : LTL.FinalState st2 r := by
  cases h with
  | intro rs m retcode hr =>
      cases hm with
      | ret _ _ _ ts tls tm STK LS MEM =>
          cases STK
          have := locmap_getpair_lessdef LS ((Conventions1.locResult signature_main).map Loc.R)
          rw [hr] at this
          generalize hv : Locmap.getpair _ tls = v at this
          cases this
          exact .intro _ _ _ hv

/-- `transf_program_correct`: branch tunneling preserves the semantics of LTL
    programs (forward simulation).  The hypotheses `hext` and `hasm` state
    that external functions and inline assembly are compatible with memory
    extensions (`ec_mem_extends`), which CompCert assumes by axiom. -/
theorem transf_program_correct
    (hext : ∀ name sg ge, ExtcallMemExtends (externalFunctionsSem name sg) ge)
    (hasm : ∀ name sg ge, ExtcallMemExtends (inlineAssemblySem name sg) ge) :
    Smallstep.ForwardSimulation (LTL.semantics win64 prog) (LTL.semantics win64 (tprog)) :=
  Smallstep.forward_simulation_opt (L1 := LTL.semantics win64 prog)
    (L2 := LTL.semantics win64 (tprog)) MatchStates
    (fun id => by
      show (Genv.toSenv (tprog).globalenv).public_symbol id =
        (Genv.toSenv prog.globalenv).public_symbol id
      rw [senv_preserved])
    (fun _ h => transf_initial_states prog h)
    (fun _ _ _ hm h => transf_final_states hm h)
    measure
    (fun _ _ _ hst _ hm => tunnel_step_correct win64 prog hext hasm hst hm)

end PRESERVATION

end Tunnelingproof
end X86
end CC
