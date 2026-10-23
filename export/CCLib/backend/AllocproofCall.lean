/-
  Correctness of register allocation, part 3 — port of the middle part of
  `backend/Allocproof.v`: function returns and entry points
  (`function_return_satisf`, `compat_left_sound`, `compat_entry_satisf`,
  `call_regs_param_values`, `return_regs_arg_values`,
  `find_function_tailcall`), builtin arguments and results
  (`add_equations_builtin_arg(s)_satisf/lessdef`,
  `add_equations_debug_args_satisf/eval`, `add_equations_builtin_eval`,
  `parallel_set_builtin_res_satisf`), the dataflow analysis
  (`analyze_successors`, `satisf_successors`) and the inversion lemmas
  `transf_function_inv` and `invert_code`.

  Differences from Rocq: on this (64-bit) configuration results and
  arguments always live in one location (`locResult_one`,
  `locArguments_one`), so the lemmas on 32-bit register pairs
  (`val_hiword_longofwords`, `val_loword_longofwords`, the `Twolong` cases)
  are not needed.  The well-typedness of external calls is not needed by
  `add_equations_builtin_arg_lessdef` either (its only use is the split
  64-bit case, rejected here because `Archi.splitlong = false`).
-/
import CCLib.backend.AllocproofEqs
import CCLib.aarch64.OpLessdef
import CCLib.common.EventsExtends

namespace CC
namespace Allocproof

open Op Allocation LTL RTLtyping Conventions1 Conventions
open Allocation.Eqs (add remove)

/-! ### Function results and parameters -/

/-- On AArch64, a function result is returned in a single register. -/
theorem locResult_one (sg : Signature) : ∃ mr, locResult sg = .One mr := by
  unfold locResult; split <;> exact ⟨_, rfl⟩

/-- A list of argument locations that are all single locations. -/
def AllOne (ll : List (RPair Loc)) : Prop := ∀ p ∈ ll, ∃ l, p = .One l

private theorem allOne_cons {p : RPair Loc} {ll : List (RPair Loc)} (hp : ∃ l, p = .One l)
    (h : AllOne ll) : AllOne (p :: ll) := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact hp
  · exact h q hq

private theorem allOne_stack : ∀ (tys : List ATyp) (ofs : Z), AllOne (locArgumentsStack tys ofs)
  | [], _ => fun _ h => by cases h
  | _ :: tys, ofs => allOne_cons ⟨_, rfl⟩ (allOne_stack tys _)

/-- On AArch64, every argument is passed in a single location. -/
theorem locArgumentsRec_one (abi : AbiKind) :
    ∀ (tyl : List ATyp) (fixed ir fr ofs : Z), AllOne (locArgumentsRec abi tyl fixed ir fr ofs)
  | [], _, _, _, _ => fun _ h => by cases h
  | ty :: tys, fixed, ir, fr, ofs => by
    have IH := fun ir fr ofs => locArgumentsRec_one abi tys (fixed - 1) ir fr ofs
    have hs : ∀ ir fr ofs, AllOne (stackArg abi ty ir fr ofs (locArgumentsRec abi tys (fixed - 1))) := by
      intro ir fr ofs
      unfold stackArg; split <;> exact allOne_cons ⟨_, rfl⟩ (IH _ _ _)
    simp only [locArgumentsRec]
    split
    · exact allOne_stack _ _
    · split
      all_goals first
        | (unfold intArg; split; · exact hs _ _ _
           · exact allOne_cons ⟨_, rfl⟩ (IH _ _ _))
        | (unfold floatArg; split; · exact hs _ _ _
           · exact allOne_cons ⟨_, rfl⟩ (IH _ _ _))

theorem locArguments_one (abi : AbiKind) (sg : Signature) : AllOne (locArguments abi sg) :=
  locArgumentsRec_one abi _ _ _ _ _

theorem locParameters_one (abi : AbiKind) (sg : Signature) : AllOne (locParameters abi sg) := by
  intro p hp
  simp only [locParameters, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  obtain ⟨l, rfl⟩ := locArguments_one abi sg q hq
  exact ⟨_, rfl⟩

/-- `Allocproof.function_return_satisf` (64-bit version). -/
theorem function_return_satisf {rs : RTL.Regset} {ls_before ls_after : Locset} {res : Reg}
    {sg : Signature} {e e' : Eqs} {v : Val}
    (h : removeEquationsRes res (locResult sg) e = some e') (hs : Satisf rs ls_before e')
    (hu : (RPair.regs (locResult sg)).all (fun r => regLocUnconstrained res (.R r) e') = true)
    (hn : noCallerSaves e' = true)
    (hv : Val.Lessdef v (Locmap.getpair ((locResult sg).map Loc.R) ls_after))
    (ha : AgreeCalleeSave ls_before ls_after) :
    Satisf (rs.set res v) ls_after e := by
  obtain ⟨mr, hmr⟩ := locResult_one sg
  rw [hmr] at h hu hv
  simp only [removeEquationsRes, Option.some.injEq] at h
  subst h
  simp only [RPair.regs, List.all_cons, List.all_nil, Bool.and_true] at hu
  simp only [RPair.map, Locmap.getpair] at hv
  intro q hq
  by_cases hqe : q = ⟨.Full, res, .R mr⟩
  · subst hqe; simp only [selVal, PMap.gss]; exact hv
  · have hq' : q ∈ remove ⟨.Full, res, .R mr⟩ e := Eqs.mem_remove.mpr ⟨hqe, hq⟩
    obtain ⟨A, _⟩ := reg_loc_unconstrained_sound hu hq'
    rw [PMap.gso _ _ _ _ (Ne.symm A), ← ha _ (no_caller_saves_sound hn hq')]
    exact hs q hq'

/-- `Allocproof.compat_left_sound` -/
theorem compat_left_sound {r : Reg} {l : Loc} {e : Eqs} {q : Equation}
    (h : compatLeft r l e = true) (hq : q ∈ e) (hr : q.ereg = r) :
    q.ekind = .Full ∧ q.eloc = l := by
  simp only [compatLeft, List.all_eq_true] at h
  have := h q (List.mem_filter.mpr ⟨hq, by simp [selectReg, hr]⟩)
  revert this
  cases q.ekind <;> simp [eq_comm]

/-- `Allocproof.compat_entry_satisf` (for parameters passed in single
    locations, which is always the case on AArch64). -/
theorem compat_entry_satisf :
    ∀ {rl : List Reg} {ll : List (RPair Loc)} {e : Eqs},
    compatEntry rl ll e = true → AllOne ll → ∀ {vl : List Val} {ls : Locset},
    Val.LessdefList vl (ll.map (fun p => Locmap.getpair p ls)) →
    Satisf (RTL.initRegs vl rl) ls e
  | [], [], _, _, _, vl, _, _ => by
    intro q _
    have : RTL.initRegs vl [] = PMap.init .Vundef := by cases vl <;> rfl
    rw [this, PMap.gi]
    cases q.ekind <;> exact .undef _
  | r1 :: rl, .One l1 :: ll, e, h, ho, vl, ls, hl => by
    simp only [compatEntry, Bool.and_eq_true] at h
    match vl, hl with
    | v1 :: vs, .cons hv hvs =>
      have IH := compat_entry_satisf h.2 (fun p hp => ho p (List.mem_cons_of_mem _ hp)) hvs
      intro q hq
      show Val.Lessdef (selVal q.ekind (((RTL.initRegs vs rl).set r1 v1).get q.ereg)) _
      rw [PMap.gsspec]
      split
      · next hr =>
        obtain ⟨A, B⟩ := compat_left_sound h.1 hq hr
        rw [A, B]; exact hv
      · exact IH q hq
  | _ :: _, .Twolong _ _ :: _, _, _, ho, _, _, _ => by
    obtain ⟨_, h⟩ := ho _ List.mem_cons_self; cases h
  | [], _ :: _, _, h, _, _, _, _ => by cases h
  | _ :: _, [], _, h, _, _, _, _ => by cases h

/-- `Allocproof.call_regs_param_values` -/
theorem call_regs_param_values (abi : AbiKind) (sg : Signature) (ls : Locset) :
    (locParameters abi sg).map (fun p => Locmap.getpair p (callRegs ls)) =
      (locArguments abi sg).map (fun p => Locmap.getpair p ls) := by
  unfold locParameters
  rw [List.map_map]
  apply List.map_congr_left
  intro p hp
  have A := locArguments_acceptable abi sg p hp
  have K : ∀ l, LocArgumentAcceptable l → callRegs ls (parameterOfArgument l) = ls l := by
    intro l hl
    cases l with
    | R r => rfl
    | S sl ofs ty => cases sl <;> first | rfl | exact hl.elim
  cases p with
  | One l => exact K l A
  | Twolong l1 l2 =>
    show Val.longofwords _ _ = Val.longofwords _ _
    rw [K l1 A.1, K l2 A.2]

/-- `Allocproof.return_regs_arg_values` -/
theorem return_regs_arg_values {abi : AbiKind} {sg : Signature} (ls1 ls2 : Locset)
    (h : tailcallIsPossible abi sg = true) :
    (locArguments abi sg).map (fun p => Locmap.getpair p (returnRegs ls1 ls2)) =
      (locArguments abi sg).map (fun p => Locmap.getpair p ls2) := by
  apply List.map_congr_left
  intro p hp
  apply Locmap.getpair_exten
  intro l hl
  have hin := RPair.in_regsList hl hp
  have A := locArguments_acceptable_2 abi sg l hin
  have B := tailcallIsPossible_correct h l hin
  cases l with
  | R r =>
    simp only [LocArgumentAcceptable] at A
    simp [returnRegs, A]
  | S _ _ _ => exact B.elim

/-- `Allocproof.find_function_tailcall` -/
theorem find_function_tailcall (tge : LTL.CGenv) {ros : Sum Mreg Ident} (ls1 ls2 : Locset)
    (h : rosCompatibleTailcall ros = true) :
    LTL.findFunction tge ros (returnRegs ls1 ls2) = LTL.findFunction tge ros ls2 := by
  cases ros with
  | inl r =>
    simp only [rosCompatibleTailcall, Bool.not_eq_true'] at h
    simp [LTL.findFunction, returnRegs, h]
  | inr _ => rfl

/-! ### Builtin arguments and results -/

/-- `Allocproof.add_equations_builtin_arg_satisf` -/
theorem add_equations_builtin_arg_satisf {env : Regenv} {rs : RTL.Regset} {ls : Locset} :
    ∀ {arg : BuiltinArg Reg} {arg' : BuiltinArg Loc} {e e' : Eqs},
    addEquationsBuiltinArg env arg arg' e = some e' → Satisf rs ls e' → Satisf rs ls e := by
  intro arg
  induction arg with
  | BA r =>
    intro arg' e e' h hs
    cases arg' with
    | BA l =>
      simp only [addEquationsBuiltinArg, Option.some.injEq] at h; subst h
      exact add_equation_satisf hs
    | BA_splitlong hi lo =>
      cases hi <;> cases lo <;> simp [addEquationsBuiltinArg, Archi.splitlong] at h
    | _ => simp [addEquationsBuiltinArg] at h
  | BA_splitlong hi lo ih1 ih2 =>
    intro arg' e e' h hs
    cases arg' with
    | BA_splitlong hi' lo' =>
      simp only [addEquationsBuiltinArg] at h
      split at h
      · cases h
      · next e1 h1 => exact ih1 h1 (ih2 h hs)
    | _ => simp [addEquationsBuiltinArg] at h
  | BA_addptr a1 a2 ih1 ih2 =>
    intro arg' e e' h hs
    cases arg' with
    | BA_addptr a1' a2' =>
      simp only [addEquationsBuiltinArg] at h
      split at h
      · cases h
      · next e1 h1 => exact ih1 h1 (ih2 h hs)
    | _ => simp [addEquationsBuiltinArg] at h
  | _ =>
    intro arg' e e' h hs
    cases arg' <;> simp [addEquationsBuiltinArg] at h
    all_goals (rw [h.2]; exact hs)

/-- `Allocproof.add_equations_builtin_arg_lessdef` -/
theorem add_equations_builtin_arg_lessdef {env : Regenv} {ge : Senv} {sp : Val}
    {rs : RTL.Regset} {ls : Locset} {m : Mem} {arg : BuiltinArg Reg} {v : Val}
    (hev : EvalBuiltinArg ge (fun r => rs.get r) sp m arg v) :
    ∀ {e e' : Eqs} {arg' : BuiltinArg Loc}, addEquationsBuiltinArg env arg arg' e = some e' →
    Satisf rs ls e' → ∃ v', EvalBuiltinArg ge ls sp m arg' v' ∧ Val.Lessdef v v' := by
  induction hev with
  | BA x =>
    intro e e' arg' h hs
    cases arg' with
    | BA l =>
      simp only [addEquationsBuiltinArg, Option.some.injEq] at h; subst h
      exact ⟨_, .BA l, add_equation_lessdef (q := ⟨.Full, x, l⟩) hs⟩
    | BA_splitlong hi lo =>
      cases hi <;> cases lo <;> simp [addEquationsBuiltinArg, Archi.splitlong] at h
    | _ => simp [addEquationsBuiltinArg] at h
  | BA_splitlong hi lo vhi vlo _ _ ih1 ih2 =>
    intro e e' arg' h hs
    cases arg' with
    | BA_splitlong hi' lo' =>
      simp only [addEquationsBuiltinArg] at h
      split at h
      · cases h
      · next e1 h1 =>
        obtain ⟨v1, A, B⟩ := ih1 h1 (add_equations_builtin_arg_satisf h hs)
        obtain ⟨v2, C, D⟩ := ih2 h hs
        exact ⟨_, .BA_splitlong _ _ _ _ A C,
          Op.lessdef_binop Op.longofwords_undef_l Op.longofwords_undef_r B D⟩
    | _ => simp [addEquationsBuiltinArg] at h
  | BA_addptr a1 a2 v1 v2 _ _ ih1 ih2 =>
    intro e e' arg' h hs
    cases arg' with
    | BA_addptr a1' a2' =>
      simp only [addEquationsBuiltinArg] at h
      split at h
      · cases h
      · next e1 h1 =>
        obtain ⟨v1', A, B⟩ := ih1 h1 (add_equations_builtin_arg_satisf h hs)
        obtain ⟨v2', C, D⟩ := ih2 h hs
        refine ⟨_, .BA_addptr _ _ _ _ A C, ?_⟩
        cases hp : Archi.ptr64
        · simp only [Bool.false_eq_true, if_false]
          exact Op.lessdef_binop Op.add_undef_l Op.add_undef_r B D
        · simp only [if_true]
          exact Op.lessdef_binop Op.addl_undef_l Op.addl_undef_r B D
    | _ => simp [addEquationsBuiltinArg] at h
  | _ =>
    intro e e' arg' h hs
    cases arg' <;> simp [addEquationsBuiltinArg] at h
    all_goals
      obtain ⟨h1, -⟩ := h
      first
        | subst h1
        | obtain ⟨rfl, rfl⟩ := h1
        | obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h1
      first
        | exact ⟨_, .BA_int _, .refl _⟩
        | exact ⟨_, .BA_long _, .refl _⟩
        | exact ⟨_, .BA_float _, .refl _⟩
        | exact ⟨_, .BA_single _, .refl _⟩
        | exact ⟨_, .BA_loadstack _ _ _ ‹_›, .refl _⟩
        | exact ⟨_, .BA_addrstack _, .refl _⟩
        | exact ⟨_, .BA_loadglobal _ _ _ _ ‹_›, .refl _⟩
        | exact ⟨_, .BA_addrglobal _ _, .refl _⟩

/-- `Allocproof.add_equations_builtin_args_satisf` -/
theorem add_equations_builtin_args_satisf {env : Regenv} {rs : RTL.Regset} {ls : Locset} :
    ∀ {args : List (BuiltinArg Reg)} {args' : List (BuiltinArg Loc)} {e e' : Eqs},
    addEquationsBuiltinArgs env args args' e = some e' → Satisf rs ls e' → Satisf rs ls e
  | [], [], _, _, h, hs => by cases h; exact hs
  | a :: al, a' :: al', e, e', h, hs => by
    simp only [addEquationsBuiltinArgs] at h
    split at h
    · cases h
    · next e1 h1 => exact add_equations_builtin_arg_satisf h1 (add_equations_builtin_args_satisf h hs)
  | [], _ :: _, _, _, h, _ => by cases h
  | _ :: _, [], _, _, h, _ => by cases h

/-- `Allocproof.add_equations_builtin_args_lessdef` -/
theorem add_equations_builtin_args_lessdef {env : Regenv} {ge : Senv} {sp : Val}
    {rs : RTL.Regset} {ls : Locset} {m tm : Mem} (hm : Mem.Extends m tm) :
    ∀ {args : List (BuiltinArg Reg)} {vl : List Val},
    EvalBuiltinArgs ge (fun r => rs.get r) sp m args vl →
    ∀ {args' : List (BuiltinArg Loc)} {e e' : Eqs},
    addEquationsBuiltinArgs env args args' e = some e' → Satisf rs ls e' →
    ∃ vl', EvalBuiltinArgs ge ls sp tm args' vl' ∧ Val.LessdefList vl vl'
  | [], [], .nil, args', e, e', h, _ => by
    cases args' with
    | nil => exact ⟨[], .nil, .nil⟩
    | cons _ _ => cases h
  | a :: al, v :: vl, .cons ha hl, args', e, e', h, hs => by
    cases args' with
    | nil => cases h
    | cons a' al' =>
      simp only [addEquationsBuiltinArgs] at h
      split at h
      · cases h
      · next e1 h1 =>
        obtain ⟨vl', A, B⟩ := add_equations_builtin_args_lessdef hm hl h hs
        obtain ⟨v1, C, D⟩ := add_equations_builtin_arg_lessdef ha h1
          (add_equations_builtin_args_satisf h hs)
        obtain ⟨v2, E, F⟩ := evalBuiltinArg_lessdef (fun _ => .refl _) hm C
        exact ⟨v2 :: vl', .cons E A, .cons (Val.lessdef_trans D F) B⟩

/-- `Allocproof.add_equations_debug_args_satisf` -/
theorem add_equations_debug_args_satisf {env : Regenv} {rs : RTL.Regset} {ls : Locset} :
    ∀ {args : List (BuiltinArg Reg)} {args' : List (BuiltinArg Loc)} {e e' : Eqs},
    addEquationsDebugArgs env args args' e = some e' → Satisf rs ls e' → Satisf rs ls e
  | [], [], _, _, h, hs => by cases h; exact hs
  | _ :: _, [], _, _, h, hs => by cases h; exact hs
  | a :: al, a' :: al', e, e', h, hs => by
    simp only [addEquationsDebugArgs] at h
    split at h
    · exact add_equations_debug_args_satisf h hs
    · next e1 h1 =>
      exact add_equations_builtin_arg_satisf h1 (add_equations_debug_args_satisf h hs)
  | [], _ :: _, _, _, h, _ => by cases h

/-- `Allocproof.add_equations_debug_args_eval` -/
theorem add_equations_debug_args_eval {env : Regenv} {ge : Senv} {sp : Val}
    {rs : RTL.Regset} {ls : Locset} {m tm : Mem} (hm : Mem.Extends m tm) :
    ∀ {args : List (BuiltinArg Reg)} {vl : List Val},
    EvalBuiltinArgs ge (fun r => rs.get r) sp m args vl →
    ∀ {args' : List (BuiltinArg Loc)} {e e' : Eqs},
    addEquationsDebugArgs env args args' e = some e' → Satisf rs ls e' →
    ∃ vl', EvalBuiltinArgs ge ls sp tm args' vl'
  | [], [], .nil, args', e, e', h, _ => by
    cases args' with
    | nil => exact ⟨[], .nil⟩
    | cons _ _ => cases h
  | a :: al, v :: vl, .cons ha hl, args', e, e', h, hs => by
    cases args' with
    | nil => exact ⟨[], .nil⟩
    | cons a' al' =>
      simp only [addEquationsDebugArgs] at h
      split at h
      · exact add_equations_debug_args_eval hm hl h hs
      · next e1 h1 =>
        obtain ⟨vl', A⟩ := add_equations_debug_args_eval hm hl h hs
        obtain ⟨v1, C, _⟩ := add_equations_builtin_arg_lessdef ha h1
          (add_equations_debug_args_satisf h hs)
        obtain ⟨v2, E, _⟩ := evalBuiltinArg_lessdef (fun _ => .refl _) hm C
        exact ⟨v2 :: vl', .cons E A⟩

/-- `Allocproof.add_equations_builtin_eval` -/
theorem add_equations_builtin_eval {ef : ExtFun} {env : Regenv}
    {args : List (BuiltinArg Reg)} {args' : List (BuiltinArg Loc)} {e1 e2 : Eqs}
    {m1 m1' : Mem} {rs : RTL.Regset} {ls : Locset} {ge : Senv} {sp : Val}
    {vargs : List Val} {t : Trace} {vres : Val} {m2 : Mem}
    (hx : ExtcallMemExtends (externalCall ef) ge)
    (h : (match ef with
      | .EF_debug _ _ _ => addEquationsDebugArgs env args args' e1
      | _ => addEquationsBuiltinArgs env args args' e1) = some e2)
    (hm : Mem.Extends m1 m1') (hs : Satisf rs ls e2)
    (hev : EvalBuiltinArgs ge (fun r => rs.get r) sp m1 args vargs)
    (hc : externalCall ef ge vargs m1 t vres m2) :
    Satisf rs ls e1 ∧ ∃ vargs' vres' m2', EvalBuiltinArgs ge ls sp m1' args' vargs' ∧
      externalCall ef ge vargs' m1' t vres' m2' ∧ Val.Lessdef vres vres' ∧
      Mem.Extends m2 m2' := by
  have DEFAULT : addEquationsBuiltinArgs env args args' e1 = some e2 →
      Satisf rs ls e1 ∧ ∃ vargs' vres' m2', EvalBuiltinArgs ge ls sp m1' args' vargs' ∧
        externalCall ef ge vargs' m1' t vres' m2' ∧ Val.Lessdef vres vres' ∧
        Mem.Extends m2 m2' := by
    intro h'
    refine ⟨add_equations_builtin_args_satisf h' hs, ?_⟩
    obtain ⟨vargs', A, B⟩ := add_equations_builtin_args_lessdef hm hev h' hs
    obtain ⟨vres', m2', C, D, E, _⟩ := hx _ _ _ _ _ _ _ hc hm B
    exact ⟨vargs', vres', m2', A, C, D, E⟩
  cases ef with
  | EF_debug k txt targs =>
    refine ⟨add_equations_debug_args_satisf h hs, ?_⟩
    obtain ⟨vargs', A⟩ := add_equations_debug_args_eval hm hev h hs
    cases hc
    exact ⟨vargs', .Vundef, m1', A, .intro _ _ _, .refl _, hm⟩
  | _ => exact DEFAULT h

/-- `Allocproof.parallel_set_builtin_res_satisf` -/
theorem parallel_set_builtin_res_satisf {env : Regenv} {res : BuiltinRes Reg}
    {res' : BuiltinRes Mreg} {e0 e1 : Eqs} {rs : RTL.Regset} {ls : Locset} {v v' : Val}
    (h : removeEquationsBuiltinRes env res res' e0 = some e1)
    (h1 : (BuiltinRes.params res).all (fun r => regUnconstrained r e1) = true)
    (h2 : (BuiltinRes.params res').all (fun mr => locUnconstrained (.R mr) e1) = true)
    (hs : Satisf rs ls e1) (hv : Val.Lessdef v v') :
    Satisf (regmapSetres res v rs) (Locmap.setres res' v' ls) e0 := by
  unfold removeEquationsBuiltinRes at h
  split at h
  · next x r' =>
    cases h
    simp only [BuiltinRes.params, List.all_cons, List.all_nil, Bool.and_true] at h1 h2
    exact parallel_assignment_satisf (k := .Full) hv (by simp [regLocUnconstrained, h1, h2]) hs
  · next x hi lo =>
    split at h
    · split at h
      · cases h
      · next hne =>
        cases h
        simp only [BuiltinRes.params, List.all_cons, List.all_nil, Bool.and_true,
          List.cons_append, List.nil_append, Bool.and_eq_true] at h1 h2
        intro q hq
        show Val.Lessdef _ (Locmap.set (.R lo) (Val.loword v') (Locmap.set (.R hi) (Val.hiword v') ls) q.eloc)
        by_cases hql : q = ⟨.Low, x, .R lo⟩
        · subst hql
          simp only [selVal, Locmap.gss_reg, regmapSetres, PMap.gss]
          exact Val.loword_lessdef hv
        by_cases hqh : q = ⟨.High, x, .R hi⟩
        · subst hqh
          have hd : Loc.diff (.R lo) (.R hi) := fun e => hne e.symm
          simp only [selVal, regmapSetres, PMap.gss]
          rw [Locmap.gso hd, Locmap.gss_reg]
          exact Val.hiword_lessdef hv
        have hq' : q ∈ remove ⟨.Low, x, .R lo⟩ (remove ⟨.High, x, .R hi⟩ e0) :=
          Eqs.mem_remove.mpr ⟨hql, Eqs.mem_remove.mpr ⟨hqh, hq⟩⟩
        show Val.Lessdef (selVal q.ekind ((rs.set x v).get q.ereg)) _
        rw [PMap.gso _ _ _ _ (Ne.symm (reg_unconstrained_sound h1 hq')),
          Locmap.gso (loc_unconstrained_sound h2.2 hq'),
          Locmap.gso (loc_unconstrained_sound h2.1 hq')]
        exact hs q hq'
    · cases h
  · cases h; exact hs
  · cases h

/-! ### Properties of the dataflow analysis -/

/-- `Allocproof.analyze_successors` -/
theorem analyze_successors {abi : AbiKind} {f : RTL.Function} {env : Regenv}
    {bsh : PTree BlockShape} {an : PMap (Res Eqs)} {pc : RTL.Node} {bs : BlockShape}
    {s : RTL.Node} {e : Eqs} (ha : analyze abi f env bsh = some an) (hb : bsh.get pc = some bs)
    (hs : s ∈ successorsBlockShape bs) (he : an.get pc = .OK e) :
    ∃ e', transfer abi f env bsh s (an.get s) = .OK e' ∧ Eqs.Subset e' e := by
  have := analyze_solution abi f env bsh an pc bs s ha hb hs
  rw [he] at this
  revert this
  cases transfer abi f env bsh s (an.get s) with
  | OK e' => intro h; exact ⟨e', rfl, h⟩
  | Error _ => intro h; exact (h : False).elim

/-- `Allocproof.satisf_successors` -/
theorem satisf_successors {abi : AbiKind} {f : RTL.Function} {env : Regenv}
    {bsh : PTree BlockShape} {an : PMap (Res Eqs)} {pc : RTL.Node} {bs : BlockShape}
    {s : RTL.Node} {e : Eqs} {rs : RTL.Regset} {ls : Locset}
    (ha : analyze abi f env bsh = some an) (hb : bsh.get pc = some bs)
    (hs : s ∈ successorsBlockShape bs) (he : an.get pc = .OK e) (hsat : Satisf rs ls e) :
    ∃ e', transfer abi f env bsh s (an.get s) = .OK e' ∧ Satisf rs ls e' := by
  obtain ⟨e', A, B⟩ := analyze_successors ha hb hs he
  exact ⟨e', A, satisf_incr hsat B⟩

/-! ### Inversion lemmas -/

private theorem rbind_OK {A B : Type} {x : Res A} {f : A → Res B} {b : B} :
    (bind x f = Res.OK b) ↔ ∃ a, x = .OK a ∧ f a = .OK b := by
  cases x <;> simp [bind, Res.bind]

/-- `Allocproof.transf_function_spec` -/
inductive TransfFunctionSpec (abi : AbiKind) (f : RTL.Function) (tf : LTL.Function) : Prop where
  | intro (env : Regenv) (an : PMap (Res Eqs)) (mv : Moves) (k : Bblock) (e1 e2 : Eqs) :
      WtFunction abi f env →
      analyze abi f env (pairCodes f tf) = some an →
      tf.fn_code.get tf.fn_entrypoint = some (expandMoves mv (.Lbranch f.fn_entrypoint :: k)) →
      WfMoves mv →
      transfer abi f env (pairCodes f tf) f.fn_entrypoint (an.get f.fn_entrypoint) = .OK e1 →
      trackMoves env mv e1 = some e2 →
      compatEntry f.fn_params (locParameters abi f.fn_sig) e2 = true →
      canUndef destroyedAtFunctionEntry e2 = true →
      f.fn_stacksize = tf.fn_stacksize →
      f.fn_sig = tf.fn_sig →
      TransfFunctionSpec abi f tf

/-- `Allocproof.transf_function_inv` -/
theorem transf_function_inv {abi : AbiKind} {regalloc : RTL.Function → Res LTL.Function}
    {f : RTL.Function} {tf : LTL.Function} (h : transfFunction abi regalloc f = .OK tf) :
    TransfFunctionSpec abi f tf := by
  unfold transfFunction at h
  split at h
  · cases h
  next env TY =>
  split at h
  · cases h
  next tf0 _ =>
  obtain ⟨u, hc, h⟩ := rbind_OK.mp h
  cases h
  unfold checkFunction at hc
  dsimp only at hc
  split at hc
  · cases hc
  next an ANL =>
  unfold checkEntrypoints at hc
  obtain ⟨e1, TR, hc⟩ := rbind_OK.mp hc
  split at hc
  · cases hc
  next x CE =>
  unfold checkEntrypointsAux at CE
  cases hp : pairEntrypoints f tf with
  | none => rw [hp] at CE; cases CE
  | some mv =>
    rw [hp] at CE
    dsimp only [bind, Option.bind] at CE
    cases ht : trackMoves env mv e1 with
    | none => rw [ht] at CE; cases CE
    | some e2 =>
      rw [ht] at CE
      dsimp only at CE
      split at CE
      · next hcond =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        obtain ⟨⟨⟨C1, C2⟩, C3⟩, C4⟩ := hcond
        rw [pairEntrypoints] at hp
        split at hp
        · cases hp
        next b HB =>
        split at hp
        next mv' b1 heq =>
        split at hp
        · next hcs =>
          cases hp
          obtain ⟨W, E⟩ := extract_moves_ext_sound heq
          obtain ⟨k, rfl⟩ := check_succ_sound hcs
          exact .intro env an mv k e1 e2 (type_function_correct TY) ANL (E ▸ HB) W TR ht
            C1 C2 C3 C4
        · cases hp
      · cases CE

/-- `Allocproof.invert_code` -/
theorem invert_code {abi : AbiKind} {f : RTL.Function} {env : Regenv} {tf : LTL.Function}
    {pc : RTL.Node} {i : RTL.Instruction} {opte : Res Eqs} {e : Eqs}
    (hwt : WtFunction abi f env) (hc : f.fn_code.get pc = some i)
    (ht : transfer abi f env (pairCodes f tf) pc opte = .OK e) :
    ∃ eafter bsh bb, opte = .OK eafter ∧ (pairCodes f tf).get pc = some bsh ∧
      tf.fn_code.get pc = some bb ∧ ExpandBlockShape bsh i bb ∧
      transferAux abi f env bsh eafter = some e ∧ WtInstr abi f env i := by
  unfold transfer at ht
  split at ht
  · cases ht
  next eafter =>
  split at ht
  · cases ht
  next bsh BSH =>
  split at ht
  · cases ht
  next e' TR =>
  cases ht
  obtain ⟨bb, A, B⟩ := matching_instr_block BSH hc
  exact ⟨eafter, bsh, bb, rfl, BSH, A, B, TR, wt_instr_at hwt hc⟩

end Allocproof
end CC
