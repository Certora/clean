/-
  [x86-64 instance of `CCLib/backend/UnusedglobproofStep.lean`: the same development, in
  namespace `CC.X86`, over the x86-64 operators, registers and conventions.]

  Elimination of unreferenced static definitions: semantic preservation —
  port of `backend/Unusedglobproof.v`, part 3 (lines 756–1052):
  `match_states`, `external_call_inject`, `find_function_inject`,
  `eval_builtin_arg(s)_inject` and `step_simulation`.
-/
import CCLib.x86.UnusedglobproofGlobals
import CCLib.x86.OpTheory
import CCLib.x86.Conventions
import CCLib.x86.Renumberproof

namespace CC
namespace X86
namespace Unusedglob

open Op RTL Smallstep
open Integers (Ptrofs)

private theorem lt_of_validBlock {m : Mem} {b : Block} (h : Mem.validBlock m b = true) :
    b < m.nextblock := by
  simpa [Mem.validBlock] using h

private theorem alloc_eq_nextblock {m : Mem} {lo hi : Z} {m1 : Mem} {b : Block}
    (h : Mem.alloc m lo hi = (m1, b)) : b = m.nextblock ∧ m1 = (Mem.alloc m lo hi).1 := by
  refine ⟨?_, by rw [h]⟩
  have := congrArg Prod.snd h; simp at this; exact this.symm

/-! ## Evaluation of operators in two global environments -/

theorem evalAddressing_ge_irrel {F1 V1 F2 V2 : Type} (ge1 : Genv F1 V1) (ge2 : Genv F2 V2)
    (sp : Val) (addr : Addressing) (ha : globalsAddressing addr = []) (vl : List Val) :
    evalAddressing ge1 sp addr vl = evalAddressing ge2 sp addr vl := by
  cases addr <;> simp only [globalsAddressing, reduceCtorEq] at ha
  all_goals rcases vl with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl

theorem evalOperation_ge_irrel {F1 V1 F2 V2 : Type} (ge1 : Genv F1 V1) (ge2 : Genv F2 V2)
    (sp : Val) (op : Operation) (hop : globalsOperation op = []) (vl : List Val) (m : Mem) :
    evalOperation ge1 sp op vl m = evalOperation ge2 sp op vl m := by
  cases op
  case Oindirectsymbol s => simp [globalsOperation] at hop
  case Olea a =>
    cases a <;> simp only [globalsOperation, globalsAddressing, reduceCtorEq] at hop
    all_goals rcases vl with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
  case Oleal a =>
    cases a <;> simp only [globalsOperation, globalsAddressing, reduceCtorEq] at hop
    all_goals rcases vl with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
  all_goals rcases vl with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ <;> rfl

/-- A global environment without symbols. -/
def noSymbols {F V : Type} (ge : Genv F V) : Genv F V := { ge with genv_symb := PTree.empty }

theorem noSymbols_inject {F V : Type} (ge : Genv F V) (f : Val.Meminj) (id : Ident) (ofs : Ptrofs) :
    Val.Inject f (Genv.symbolAddress (noSymbols ge) id ofs)
      (Genv.symbolAddress (noSymbols ge) id ofs) := by
  simp only [Genv.symbolAddress, Genv.findSymbol, noSymbols, PTree.gempty]; exact .undef _

/-- `Op.eval_operation_inj`, for two global environments that agree on the
    symbols referenced by the operation. -/
theorem evalOperation_inject2 {F1 V1 F2 V2 : Type} (ge1 : Genv F1 V1) (ge2 : Genv F2 V2)
    {f : Val.Meminj} {op : Operation}
    (hsym : ∀ id ofs, id ∈ globalsOperation op →
      Val.Inject f (Genv.symbolAddress ge1 id ofs) (Genv.symbolAddress ge2 id ofs))
    {sp1 sp2 : Val} (hsp : Val.Inject f sp1 sp2) {vl1 vl2 : List Val} {v1 : Val} {m1 m2 : Mem}
    (hl : Val.InjectList f vl1 vl2) (hm : Mem.Inject f m1 m2)
    (h : evalOperation ge1 sp1 op vl1 m1 = some v1) :
    ∃ v2, evalOperation ge2 sp2 op vl2 m2 = some v2 ∧ Val.Inject f v1 v2 := by
  by_cases hop : globalsOperation op = []
  · rw [evalOperation_ge_irrel ge1 (noSymbols ge1) sp1 op hop] at h
    obtain ⟨v2, A, B⟩ := Op.evalOperation_inject (noSymbols ge1) (noSymbols_inject ge1 f) hsp hl hm h
    exact ⟨v2, by rw [evalOperation_ge_irrel ge2 (noSymbols ge1) sp2 op hop]; exact A, B⟩
  · cases op <;> simp only [globalsOperation, not_true_eq_false] at hop
    case Oindirectsymbol s =>
      cases hl with
      | nil => cases h; exact ⟨_, rfl, hsym s _ (by simp [globalsOperation])⟩
      | cons _ _ => cases h
    case Olea a =>
      cases a <;> simp only [globalsAddressing, not_true_eq_false] at hop <;>
        rcases hl with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> cases h
    case Oleal a =>
      cases a <;> simp only [globalsAddressing, not_true_eq_false] at hop <;>
        rcases hl with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> cases h
      exact ⟨_, rfl, hsym _ _ (by simp [globalsOperation, globalsAddressing])⟩

/-- `Op.eval_addressing_inj`, for two global environments. -/
theorem evalAddressing_inject2 {F1 V1 F2 V2 : Type} (ge1 : Genv F1 V1) (ge2 : Genv F2 V2)
    {f : Val.Meminj} {addr : Addressing}
    (hsym : ∀ id ofs, id ∈ globalsAddressing addr →
      Val.Inject f (Genv.symbolAddress ge1 id ofs) (Genv.symbolAddress ge2 id ofs))
    {sp1 sp2 : Val} (hsp : Val.Inject f sp1 sp2) {vl1 vl2 : List Val} {v1 : Val}
    (hl : Val.InjectList f vl1 vl2) (h : evalAddressing ge1 sp1 addr vl1 = some v1) :
    ∃ v2, evalAddressing ge2 sp2 addr vl2 = some v2 ∧ Val.Inject f v1 v2 := by
  by_cases ha : globalsAddressing addr = []
  · rw [evalAddressing_ge_irrel ge1 (noSymbols ge1) sp1 addr ha] at h
    obtain ⟨v2, A, B⟩ := Op.evalAddressing_inject (noSymbols ge1) (noSymbols_inject ge1 f) hsp hl h
    exact ⟨v2, by rw [evalAddressing_ge_irrel ge2 (noSymbols ge1) sp2 addr ha]; exact A, B⟩
  · cases addr <;> simp only [globalsAddressing, not_true_eq_false] at ha <;>
      rcases hl with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> cases h
    exact ⟨_, rfl, hsym _ _ (by simp [globalsAddressing])⟩

/-- `Unusedglobproof.eval_builtin_arg_inject` (for two symbol environments that
    agree on the symbols referenced by the argument). -/
theorem evalBuiltinArg_inject_kept {f : Val.Meminj} {ge1 ge2 : Senv} {e1 e2 : Reg → Val}
    {sp1 sp2 : Val} {m1 m2 : Mem} (hsp : Val.Inject f sp1 sp2)
    (he : ∀ x, Val.Inject f (e1 x) (e2 x)) (hm : Mem.Inject f m1 m2) {a : BuiltinArg Reg}
    {v1 : Val} (h : EvalBuiltinArg ge1 e1 sp1 m1 a v1) :
    (∀ id ofs, id ∈ BuiltinArg.globals a →
      Val.Inject f (ge1.symbolAddress id ofs) (ge2.symbolAddress id ofs)) →
    ∃ v2, EvalBuiltinArg ge2 e2 sp2 m2 a v2 ∧ Val.Inject f v1 v2 := by
  induction h with
  | BA x => exact fun _ => ⟨_, .BA x, he x⟩
  | BA_int n => exact fun _ => ⟨_, .BA_int n, .int _⟩
  | BA_long n => exact fun _ => ⟨_, .BA_long n, .long _⟩
  | BA_float n => exact fun _ => ⟨_, .BA_float n, .float _⟩
  | BA_single n => exact fun _ => ⟨_, .BA_single n, .single _⟩
  | BA_loadstack chunk ofs v hl =>
    intro _
    obtain ⟨v2, h2, hv⟩ := Mem.loadv_inject hm hl (Val.offset_ptr_inject ofs hsp)
    exact ⟨v2, .BA_loadstack _ _ _ h2, hv⟩
  | BA_addrstack ofs => exact fun _ => ⟨_, .BA_addrstack ofs, Val.offset_ptr_inject ofs hsp⟩
  | BA_loadglobal chunk id ofs v hl =>
    intro hsym
    obtain ⟨v2, h2, hv⟩ := Mem.loadv_inject hm hl (hsym id ofs (by simp [BuiltinArg.globals]))
    exact ⟨v2, .BA_loadglobal _ _ _ _ h2, hv⟩
  | BA_addrglobal id ofs =>
    exact fun hsym => ⟨_, .BA_addrglobal id ofs, hsym id ofs (by simp [BuiltinArg.globals])⟩
  | BA_splitlong hi lo vhi vlo _ _ ih1 ih2 =>
    intro hsym
    obtain ⟨v1', e1', l1⟩ := ih1 (fun id ofs h => hsym id ofs
      (by simp only [BuiltinArg.globals]; exact List.mem_append_left _ h))
    obtain ⟨v2', e2', l2⟩ := ih2 (fun id ofs h => hsym id ofs
      (by simp only [BuiltinArg.globals]; exact List.mem_append_right _ h))
    exact ⟨_, .BA_splitlong _ _ _ _ e1' e2', Val.longofwords_inject l1 l2⟩
  | BA_addptr a1 a2 v1 v2 _ _ ih1 ih2 =>
    intro hsym
    obtain ⟨v1', e1', l1⟩ := ih1 (fun id ofs h => hsym id ofs
      (by simp only [BuiltinArg.globals]; exact List.mem_append_left _ h))
    obtain ⟨v2', e2', l2⟩ := ih2 (fun id ofs h => hsym id ofs
      (by simp only [BuiltinArg.globals]; exact List.mem_append_right _ h))
    refine ⟨_, .BA_addptr _ _ _ _ e1' e2', ?_⟩
    simp only [Archi.ptr64, if_true]
    exact Op.addl_inject l1 l2

/-- `Unusedglobproof.eval_builtin_args_inject` -/
theorem evalBuiltinArgs_inject_kept {f : Val.Meminj} {ge1 ge2 : Senv} {e1 e2 : Reg → Val}
    {sp1 sp2 : Val} {m1 m2 : Mem} (hsp : Val.Inject f sp1 sp2)
    (he : ∀ x, Val.Inject f (e1 x) (e2 x)) (hm : Mem.Inject f m1 m2) :
    ∀ {al : List (BuiltinArg Reg)} {vl1 : List Val}, EvalBuiltinArgs ge1 e1 sp1 m1 al vl1 →
    (∀ id ofs, id ∈ BuiltinArg.globalsList al →
      Val.Inject f (ge1.symbolAddress id ofs) (ge2.symbolAddress id ofs)) →
    ∃ vl2, EvalBuiltinArgs ge2 e2 sp2 m2 al vl2 ∧ Val.InjectList f vl1 vl2
  | [], [], .nil, _ => ⟨[], .nil, .nil⟩
  | a :: al, _ :: _, .cons h hl, hsym => by
    have hg : ∀ x, x ∈ BuiltinArg.globalsList (a :: al) ↔
        x ∈ BuiltinArg.globals a ∨ x ∈ BuiltinArg.globalsList al := by
      intro x; simp [BuiltinArg.globalsList]
    obtain ⟨v2, h2, l2⟩ := evalBuiltinArg_inject_kept hsp he hm h
      (fun id ofs h => hsym id ofs ((hg id).2 (.inl h)))
    obtain ⟨vl2, hl2, ll2⟩ := evalBuiltinArgs_inject_kept hsp he hm hl
      (fun id ofs h => hsym id ofs ((hg id).2 (.inr h)))
    exact ⟨v2 :: vl2, .cons h2 hl2, .cons l2 ll2⟩

section SOUNDNESS
variable {p tp : RTL.Program} {used : IS}

variable (p tp used) in
/-- `Unusedglobproof.match_states` -/
inductive MatchStates : RTL.State → RTL.State → Prop where
  | regular (s : List RTL.Stackframe) (f : RTL.Function) (sp : Block) (pc : Node) (rs : RTL.Regset)
      (m : Mem) (ts : List RTL.Stackframe) (tsp : Block) (trs : RTL.Regset) (tm : Mem)
      (j : Val.Meminj) :
      MatchStacks p tp used j s ts sp tsp →
      (∀ id, RefFunction f id → id ∈ used) →
      j sp = some (tsp, 0) →
      RegsetInject j rs trs →
      Mem.Inject j m tm →
      MatchStates (.State s f (.Vptr sp Ptrofs.zero) pc rs m)
        (.State ts f (.Vptr tsp Ptrofs.zero) pc trs tm)
  | call (s : List RTL.Stackframe) (fd : RTL.Fundef) (args : List Val) (m : Mem)
      (ts : List RTL.Stackframe) (targs : List Val) (tm : Mem) (j : Val.Meminj) :
      MatchStacks p tp used j s ts m.nextblock tm.nextblock →
      (∀ id, RefFundef fd id → id ∈ used) →
      Val.InjectList j args targs →
      Mem.Inject j m tm →
      MatchStates (.Callstate s fd args m) (.Callstate ts fd targs tm)
  | ret (s : List RTL.Stackframe) (res : Val) (m : Mem) (ts : List RTL.Stackframe) (tres : Val)
      (tm : Mem) (j : Val.Meminj) :
      MatchStacks p tp used j s ts m.nextblock tm.nextblock →
      Val.Inject j res tres →
      Mem.Inject j m tm →
      MatchStates (.Returnstate s res m) (.Returnstate ts tres tm)

/-- `Unusedglobproof.find_function_inject` -/
theorem find_function_inject {j : Val.Meminj} (h : MeminjPreservesGlobals p tp used j)
    {ros : Sum Reg Ident} {rs trs : RTL.Regset} {fd : RTL.Fundef}
    (hf : findFunction p.globalenv ros rs = some fd)
    (hk : match ros with | .inl _ => RegsetInject j rs trs | .inr id => id ∈ used) :
    findFunction tp.globalenv ros trs = some fd ∧ ∀ id, RefFundef fd id → id ∈ used := by
  cases ros with
  | inl r =>
    simp only [findFunction] at hf ⊢
    obtain ⟨b, hb⟩ := Genv.findFunct_inv hf
    rw [hb, Genv.findFunct_findFunctPtr] at hf
    have A := hk r
    rw [hb] at A
    generalize trs.get r = v' at A ⊢
    cases A with
    | ptr delta hj ho =>
      have hd := (Genv.findFunctPtr_iff _ _ _).1 hf
      obtain ⟨B, C, D⟩ := h.defs_inject _ _ _ _ hj hd
      subst C
      rw [ho, Ptrofs.repr_zero, Ptrofs.add_zero, Genv.findFunct_findFunctPtr]
      exact ⟨(Genv.findFunctPtr_iff _ _ _).2 B, fun id hr => D id hr⟩
  | inr id =>
    simp only [findFunction] at hf ⊢
    split at hf
    · cases hf
    · next b hs =>
      obtain ⟨tb, P, Q⟩ := h.symbols_inject_2 id b hk hs
      rw [P]
      have hd := (Genv.findFunctPtr_iff _ _ _).1 hf
      obtain ⟨B, _, D⟩ := h.defs_inject _ _ _ _ Q hd
      exact ⟨(Genv.findFunctPtr_iff _ _ _).2 B, fun id hr => D id hr⟩

theorem ref_of_code {f : RTL.Function} {pc : Node} {i : Instruction}
    (hk : ∀ id, RefFunction f id → id ∈ used) (hc : f.fn_code.get pc = some i) :
    ∀ id, id ∈ refInstruction i → id ∈ used :=
  fun id hid => hk id ⟨pc, i, hc, hid⟩

theorem nextblock_le_of_invalid {m : Mem} {b : Block} (h : Mem.validBlock m b = false) :
    m.nextblock ≤ b := by
  simp only [Mem.validBlock, decide_eq_false_iff_not] at h
  exact Nat.not_lt.1 h

section SIM
variable (TRANSF : MatchProg1 used p tp) (USED : ValidUsedSet p used)
  (hext : ∀ name sg, ExtcallMemInject (externalFunctionsSem name sg))
  (hasm : ∀ name sg, ExtcallMemInject (inlineAssemblySem name sg))

include TRANSF USED hext hasm in
/-- `Unusedglobproof.step_simulation` -/
theorem step_simulation {S1 : RTL.State} {t : Trace} {S2 : RTL.State}
    (hstep : RTL.Step p.globalenv S1 t S2) {S1' : RTL.State}
    (hm : MatchStates p tp used S1 S1') :
    ∃ S2', RTL.Step tp.globalenv S1' t S2' ∧ MatchStates p tp used S2 S2' := by
  cases hstep with
  | Inop s f sp pc rs m pc' hc =>
    cases hm with
    | regular _ _ sp0 _ _ _ ts tsp trs tm j STACKS KEPT SPINJ REGINJ MEMINJ =>
      exact ⟨_, .Inop _ _ _ _ _ _ _ hc,
        .regular _ _ _ _ _ _ _ _ _ _ _ STACKS KEPT SPINJ REGINJ MEMINJ⟩
  | Iop s f sp pc rs m op args res pc' v hc hev =>
    cases hm with
    | regular _ _ sp0 _ _ _ ts tsp trs tm j STACKS KEPT SPINJ REGINJ MEMINJ =>
      have hg := match_stacks_preserves_globals STACKS
      obtain ⟨tv, B, C⟩ := evalOperation_inject2 p.globalenv tp.globalenv
        (fun id ofs hid => symbol_address_inject hg (ref_of_code KEPT hc id hid) ofs)
        (.ptr _ SPINJ (by rw [Ptrofs.repr_zero, Ptrofs.add_zero])) (regs_inject REGINJ args)
        MEMINJ hev
      exact ⟨_, .Iop _ _ _ _ _ _ _ _ _ _ _ hc B,
        .regular _ _ _ _ _ _ _ _ _ _ _ STACKS KEPT SPINJ (set_reg_inject REGINJ C) MEMINJ⟩
  | Iload s f sp pc rs m chunk addr args dst pc' a v hc hev hl =>
    cases hm with
    | regular _ _ sp0 _ _ _ ts tsp trs tm j STACKS KEPT SPINJ REGINJ MEMINJ =>
      have hg := match_stacks_preserves_globals STACKS
      obtain ⟨ta, B, C⟩ := evalAddressing_inject2 p.globalenv tp.globalenv
        (fun id ofs hid => symbol_address_inject hg (ref_of_code KEPT hc id hid) ofs)
        (.ptr _ SPINJ (by rw [Ptrofs.repr_zero, Ptrofs.add_zero])) (regs_inject REGINJ args) hev
      obtain ⟨tv, D, E⟩ := Mem.loadv_inject MEMINJ hl C
      exact ⟨_, .Iload _ _ _ _ _ _ _ _ _ _ _ _ _ hc B D,
        .regular _ _ _ _ _ _ _ _ _ _ _ STACKS KEPT SPINJ (set_reg_inject REGINJ E) MEMINJ⟩
  | Istore s f sp pc rs m chunk addr args src pc' a m1 hc hev hs =>
    cases hm with
    | regular _ _ sp0 _ _ _ ts tsp trs tm j STACKS KEPT SPINJ REGINJ MEMINJ =>
      have hg := match_stacks_preserves_globals STACKS
      obtain ⟨ta, B, C⟩ := evalAddressing_inject2 p.globalenv tp.globalenv
        (fun id ofs hid => symbol_address_inject hg (ref_of_code KEPT hc id hid) ofs)
        (.ptr _ SPINJ (by rw [Ptrofs.repr_zero, Ptrofs.add_zero])) (regs_inject REGINJ args) hev
      obtain ⟨tm', D, E⟩ := Mem.storev_mapped_inject MEMINJ hs C (REGINJ src)
      have STACKS' : MatchStacks p tp used j s ts sp0 tsp := STACKS
      exact ⟨_, .Istore _ _ _ _ _ _ _ _ _ _ _ _ _ hc B D,
        .regular _ _ _ _ _ _ _ _ _ _ _ STACKS' KEPT SPINJ REGINJ E⟩
  | Icall s f sp pc rs m sig ros args res pc' fd hc hfind hsig =>
    cases hm with
    | regular _ _ sp0 _ _ _ ts tsp trs tm j STACKS KEPT SPINJ REGINJ MEMINJ =>
      have hg := match_stacks_preserves_globals STACKS
      obtain ⟨A, B⟩ := find_function_inject hg hfind (trs := trs) (by
        cases ros with
        | inl r => exact REGINJ
        | inr id => exact ref_of_code KEPT hc id (by simp [refInstruction]))
      exact ⟨_, .Icall _ _ _ _ _ _ _ _ _ _ _ _ hc A hsig,
        .call _ _ _ _ _ _ _ _ (.cons _ _ _ _ _ _ _ _ _ _ _ STACKS KEPT SPINJ REGINJ
          (lt_of_validBlock (Mem.validBlock_inject_1 SPINJ MEMINJ))
          (lt_of_validBlock (Mem.validBlock_inject_2 SPINJ MEMINJ)))
          B (regs_inject REGINJ args) MEMINJ⟩
  | Itailcall s f stk pc rs m sig ros args fd m1 hc hfind hsig hfree =>
    cases hm with
    | regular _ _ _ _ _ _ ts tsp trs tm j STACKS KEPT SPINJ REGINJ MEMINJ =>
      have hg := match_stacks_preserves_globals STACKS
      obtain ⟨A, B⟩ := find_function_inject hg hfind (trs := trs) (by
        cases ros with
        | inl r => exact REGINJ
        | inr id => exact ref_of_code KEPT hc id (by simp [refInstruction]))
      obtain ⟨tm', C, D⟩ := Mem.free_parallel_inject MEMINJ hfree SPINJ
      rw [Int.add_zero, Int.add_zero] at C
      refine ⟨_, .Itailcall _ _ _ _ _ _ _ _ _ _ _ hc A hsig C,
        .call _ _ _ _ _ _ _ _ (match_stacks_bound STACKS ?_ ?_) B (regs_inject REGINJ args) D⟩
      · rw [Mem.nextblock_free hfree]
        exact Nat.le_of_lt (lt_of_validBlock (Mem.validBlock_inject_1 SPINJ MEMINJ))
      · rw [Mem.nextblock_free C]
        exact Nat.le_of_lt (lt_of_validBlock (Mem.validBlock_inject_2 SPINJ MEMINJ))
  | Ibuiltin s f sp pc rs m ef args res pc' vargs t vres m1 hc hargs hec =>
    cases hm with
    | regular _ _ sp0 _ _ _ ts tsp trs tm j STACKS KEPT SPINJ REGINJ MEMINJ =>
      have hg := match_stacks_preserves_globals STACKS
      obtain ⟨vargs', P, Q⟩ := evalBuiltinArgs_inject_kept (ge2 := Genv.toSenv tp.globalenv)
        (.ptr _ SPINJ (by rw [Ptrofs.repr_zero, Ptrofs.add_zero])) REGINJ MEMINJ hargs
        (fun id ofs hid => by
          rw [Genv.toSenv_symbolAddress, Genv.toSenv_symbolAddress]
          exact symbol_address_inject hg (ref_of_code KEPT hc id hid) ofs)
      obtain ⟨j', tv, tm', A, B, C, D, E, F, G⟩ := externalCall_memInject ef hext hasm _ _ _ _ _ _ _
        _ _ _ (globals_symbols_inject TRANSF USED hg) hec MEMINJ Q
      refine ⟨_, .Ibuiltin _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc P A,
        .regular _ _ _ _ _ _ _ _ _ _ _ (match_stacks_incr F STACKS ?_) KEPT (F _ _ _ SPINJ)
          (set_res_inject res (regset_inject_incr REGINJ F) B) C⟩
      intro b1 b2 delta h1 h2
      obtain ⟨U, V⟩ := G b1 b2 delta h1 h2
      exact ⟨Nat.le_trans (Nat.le_of_lt (lt_of_validBlock (Mem.validBlock_inject_1 SPINJ MEMINJ)))
          (nextblock_le_of_invalid U),
        Nat.le_trans (Nat.le_of_lt (lt_of_validBlock (Mem.validBlock_inject_2 SPINJ MEMINJ)))
          (nextblock_le_of_invalid V)⟩
  | Icond s f sp pc rs m cond args ifso ifnot b pc' hc hev hpc =>
    cases hm with
    | regular _ _ sp0 _ _ _ ts tsp trs tm j STACKS KEPT SPINJ REGINJ MEMINJ =>
      exact ⟨_, .Icond _ _ _ _ _ _ _ _ _ _ b _ hc
          (evalCondition_inject (regs_inject REGINJ args) MEMINJ hev) hpc,
        .regular _ _ _ _ _ _ _ _ _ _ _ STACKS KEPT SPINJ REGINJ MEMINJ⟩
  | Ijumptable s f sp pc rs m arg tbl n pc' hc harg hnth =>
    cases hm with
    | regular _ _ sp0 _ _ _ ts tsp trs tm j STACKS KEPT SPINJ REGINJ MEMINJ =>
      have A := REGINJ arg
      rw [harg] at A
      generalize hv' : trs.get arg = v' at A
      cases A
      exact ⟨_, .Ijumptable _ _ _ _ _ _ _ _ n _ hc hv' hnth,
        .regular _ _ _ _ _ _ _ _ _ _ _ STACKS KEPT SPINJ REGINJ MEMINJ⟩
  | Ireturn s f stk pc rs m or m1 hc hfree =>
    cases hm with
    | regular _ _ _ _ _ _ ts tsp trs tm j STACKS KEPT SPINJ REGINJ MEMINJ =>
      obtain ⟨tm', C, D⟩ := Mem.free_parallel_inject MEMINJ hfree SPINJ
      rw [Int.add_zero, Int.add_zero] at C
      refine ⟨_, .Ireturn _ _ _ _ _ _ _ _ hc C,
        .ret _ _ _ _ _ _ _ (match_stacks_bound STACKS ?_ ?_) ?_ D⟩
      · rw [Mem.nextblock_free hfree]
        exact Nat.le_of_lt (lt_of_validBlock (Mem.validBlock_inject_1 SPINJ MEMINJ))
      · rw [Mem.nextblock_free C]
        exact Nat.le_of_lt (lt_of_validBlock (Mem.validBlock_inject_2 SPINJ MEMINJ))
      · cases or with
        | none => exact .undef _
        | some r => exact REGINJ r
  | function_internal s f args m m1 stk htyp halloc =>
    cases hm with
    | call _ _ _ _ ts targs tm j STACKS KEPT ARGINJ MEMINJ =>
      obtain ⟨j', tm', tstk, C, D, E, F, G⟩ :=
        Mem.alloc_parallel_inject MEMINJ halloc (Int.le_refl _) (Int.le_refl _)
      obtain ⟨hstk, _⟩ := alloc_eq_nextblock halloc
      obtain ⟨htstk, _⟩ := alloc_eq_nextblock C
      have STACKS' : MatchStacks p tp used j' s ts stk tstk := by
        rw [hstk, htstk]
        refine match_stacks_incr E STACKS ?_
        intro b1 b2 delta h1 h2
        by_cases e : b1 = stk
        · rw [e, F] at h2; cases h2
          exact ⟨by rw [e, hstk]; exact Nat.le_refl _, by rw [htstk]; exact Nat.le_refl _⟩
        · rw [G b1 e] at h2; rw [h1] at h2; cases h2
      exact ⟨_, .function_internal _ _ _ _ _ _ (Val.has_argtype_list_inject htyp ARGINJ) C,
        .regular _ _ _ _ _ _ _ _ _ _ _ STACKS' KEPT F
          (init_regs_inject (Val.inject_incr_inject_list E ARGINJ) _) D⟩
  | function_external s ef args res t m m1 hec =>
    cases hm with
    | call _ _ _ _ ts targs tm j STACKS KEPT ARGINJ MEMINJ =>
      have hg := match_stacks_preserves_globals STACKS
      obtain ⟨j', tres, tm', A, B, C, D, E, F, G⟩ := externalCall_memInject ef hext hasm _ _ _ _ _ _
        _ _ _ _ (globals_symbols_inject TRANSF USED hg) hec MEMINJ ARGINJ
      refine ⟨_, .function_external _ _ _ _ _ _ _ A,
        .ret _ _ _ _ _ _ _ (match_stacks_bound (match_stacks_incr F STACKS ?_) D.nextblock_le
          E.nextblock_le) B C⟩
      intro b1 b2 delta h1 h2
      obtain ⟨U, V⟩ := G b1 b2 delta h1 h2
      exact ⟨nextblock_le_of_invalid U, nextblock_le_of_invalid V⟩
  | «return» res f sp pc rs s vres m =>
    cases hm with
    | ret _ _ _ ts tres tm j STACKS RESINJ MEMINJ =>
      cases STACKS with
      | cons _ _ sp0 _ _ _ tsp trs ts' _ _ STACKS' KEPT SPINJ REGINJ _ _ =>
        exact ⟨_, .return _ _ _ _ _ _ _ _,
          .regular _ _ _ _ _ _ _ _ _ _ _ STACKS' KEPT SPINJ (set_reg_inject REGINJ RESINJ) MEMINJ⟩

end SIM

end SOUNDNESS

end Unusedglob
end X86
end CC
