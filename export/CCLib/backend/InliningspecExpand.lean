/-
  RTL function inlining: relational specification — port of
  `backend/Inliningspec.v`, part 3: CFG expansion meets its specification
  (`expand_instr_spec`, `iter_expand_instr_spec`, `expand_cfg_rec_spec`,
  `expand_cfg_spec`).
-/
import CCLib.backend.InliningspecCfg

namespace CC
namespace Inlining

open Op RTL

/-- Rocq's hypothesis `rec_spec` on the recursor, for a given environment and stack size. -/
def RecSpec (fenv : Funenv) (stacksize : Z) (r : Funenv → Context → RTL.Function → Mon Unit) :
    Prop :=
  ∀ fe' ctx f s c, FenvAgree fenv fe' →
    Positive.add ctx.dpc (maxPcFunction f) ≤ s.st_nextnode →
    ctx.mreg = maxRegFunction f →
    Positive.add ctx.dreg ctx.mreg ≤ s.st_nextreg →
    ctx.mstk ≥ 0 →
    ctx.mstk = Max.max f.fn_stacksize 0 →
    minSafeAlignment f.fn_stacksize ∣ ctx.dstk →
    ctx.dstk ≥ 0 →
    (r fe' ctx f s).2.st_stksize ≤ stacksize →
    (∀ pc, ctx.dpc ≤ pc → pc < (r fe' ctx f s).2.st_nextnode →
      c.get pc = (r fe' ctx f s).2.st_code.get pc) →
    TrFunbody fenv stacksize ctx f c

theorem fenvAgree_remove {fenv fe : Funenv} (h : FenvAgree fenv fe) (id : Ident) :
    FenvAgree fenv (fe.remove id) := by
  intro id' f hf
  by_cases e : id = id'
  · subst e; simp at hf
  · rw [PTree.gro _ _ _ e] at hf; exact h _ _ hf

section EXPAND
variable (fenv : Funenv) (stacksize : Z)

/-- The common part of the two inlining cases of `expand_instr_spec`. -/
theorem inlined_spec (fe : Funenv) (FE : FenvAgree fenv fe)
    (r : Funenv → Context → RTL.Function → Mon Unit) (RI : RecIncr r)
    (RS : RecSpec fenv stacksize r) (ctx ctx' : Context) (pc : Node) (id : Ident)
    (f : RTL.Function) (srcs : List Reg) (s : State) (c : Code)
    (hdpc : ctx'.dpc = s.st_nextnode) (hdreg : ctx'.dreg = s.st_nextreg)
    (hmreg : ctx'.mreg = maxRegFunction f) (hmstk : ctx'.mstk = Max.max f.fn_stacksize 0)
    (halign : minSafeAlignment f.fn_stacksize ∣ ctx'.dstk) (hdstk : ctx'.dstk ≥ 0)
    (OPC : spc ctx pc < s.st_nextnode) :
    let s3 := (r (fe.remove id) ctx' f (reserved s f)).2
    let p4 := addMoves srcs (sregs ctx' f.fn_params) (spc ctx' f.fn_entrypoint) s3
    let s5 := (setInstr (spc ctx pc) (.Inop p4.1) p4.2).2
    s5.st_stksize ≤ stacksize →
    (∀ pc', s.st_nextnode ≤ pc' → pc' < s5.st_nextnode → c.get pc' = s5.st_code.get pc') →
    c.get (spc ctx pc) = s5.st_code.get (spc ctx pc) →
    c.get (spc ctx pc) = some (.Inop p4.1) ∧
    TrMoves c p4.1 srcs (sregs ctx' f.fn_params) (spc ctx' f.fn_entrypoint) ∧
    TrFunbody fenv stacksize ctx' f c := by
  intro s3 p4 s5 STK3 S1 S2
  have I2 := reserved_incr s f
  have I3 : Sincr (reserved s f) s3 := RI.incr (fe.remove id) ctx' f (reserved s f)
  have I4 : Sincr s3 p4.2 := addMoves_incr srcs (sregs ctx' f.fn_params) (spc ctx' f.fn_entrypoint) s3
  have I2n := I2.nextnode
  have N2 : (reserved s f).st_nextnode = Positive.add s.st_nextnode (maxPcFunction f) := rfl
  have R2 : (reserved s f).st_nextreg = Positive.add s.st_nextreg (maxRegFunction f) := rfl
  have N5 : s5.st_nextnode = p4.2.st_nextnode := rfl
  have K5 : s5.st_stksize = p4.2.st_stksize := rfl
  have I3n := I3.nextnode
  have I4n := I4.nextnode
  have I3k := I3.stksize
  have I4k := I4.stksize
  refine ⟨by rw [S2]; exact setInstr_get_same _ _ _, ?_, ?_⟩
  · refine add_moves_spec _ _ _ (rfl : _ = (p4.1, p4.2)) (fun pc0 h1 h2 => ?_)
    rw [S1 pc0 (by pos_omega) (by rw [N5]; exact h2)]
    exact setInstr_get _ _ _ (fun he => by subst he; pos_omega)
  · refine RS (fe.remove id) ctx' f (reserved s f) c (fenvAgree_remove FE id)
      (by rw [hdpc, N2]; exact Nat.le_refl _) hmreg
      (by rw [hdreg, hmreg, R2]; exact Nat.le_refl _)
      (by rw [hmstk]; exact Int.le_max_right _ _) hmstk halign hdstk
      (by rw [K5] at STK3; exact Int.le_trans I4k STK3) (fun pc0 h1 h2 => ?_)
    rw [hdpc] at h1
    have h2' : pc0 < s3.st_nextnode := h2
    clear h2
    rw [S1 pc0 h1 (by rw [N5]; pos_omega)]
    rw [setInstr_get _ _ _ (fun he => by subst he; pos_omega)]
    exact add_moves_unchanged _ _ _ (rfl : _ = (p4.1, p4.2)) (.inl h2')

theorem base_spec {E : State} {c : Code} {p : Node} {i : Instruction} {s : State}
    (S2 : c.get p = E.st_code.get p) (hE : E = (setInstr p i s).2) : c.get p = some i := by
  rw [S2, hE]; exact setInstr_get_same _ _ _

/-- `Inliningspec.expand_instr_spec` -/
theorem expand_instr_spec (fe : Funenv) (FE : FenvAgree fenv fe) (rec : Recursor)
    (hrec : ∀ r, rec = some r → RecIncr r ∧ RecSpec fenv stacksize r)
    (ctx : Context) (pc : Node) (instr : Instruction) (s : State) (c : Code)
    (DEFS : ∀ r, instrDefs instr = some r → r ≤ ctx.mreg)
    (OPC : spc ctx pc < s.st_nextnode)
    (OREG : Positive.add ctx.dreg ctx.mreg ≤ s.st_nextreg)
    (STK1 : ctx.mstk ≥ 0) (STK2 : ctx.dstk ≥ 0)
    (STK3 : (expandInstr fe rec ctx pc instr s).2.st_stksize ≤ stacksize)
    (S1 : ∀ pc', s.st_nextnode ≤ pc' → pc' < (expandInstr fe rec ctx pc instr s).2.st_nextnode →
      c.get pc' = (expandInstr fe rec ctx pc instr s).2.st_code.get pc')
    (S2 : c.get (spc ctx pc) = (expandInstr fe rec ctx pc instr s).2.st_code.get (spc ctx pc)) :
    TrInstr fenv stacksize ctx pc instr c := by
  cases instr with
  | Inop s0 => exact .nop _ _ _ _ (base_spec (i := .Inop (spc ctx s0)) S2 rfl)
  | Iop op args res s0 =>
    exact .op _ _ _ _ _ _ _ (DEFS _ rfl)
      (base_spec (i := .Iop (sop ctx op) (sregs ctx args) (sreg ctx res) (spc ctx s0)) S2 rfl)
  | Iload chunk addr args dst s0 =>
    exact .load _ _ _ _ _ _ _ _ (DEFS _ rfl)
      (base_spec (i := .Iload chunk (saddr ctx addr) (sregs ctx args) (sreg ctx dst) (spc ctx s0))
        S2 rfl)
  | Istore chunk addr args src s0 =>
    exact .store _ _ _ _ _ _ _ _
      (base_spec (i := .Istore chunk (saddr ctx addr) (sregs ctx args) (sreg ctx src) (spc ctx s0))
        S2 rfl)
  | Icall sg ros args res s0 =>
    rcases hci : canInline fe rec ros with _ | ⟨id, f, r⟩
    · rw [expandInstr_call_none hci] at S2
      exact .call _ _ _ _ _ _ _ _ (DEFS _ rfl) (S2.trans (setInstr_get_same _ _ _))
    · obtain ⟨rfl, hr, hfe⟩ := canInline_some hci
      obtain ⟨RI, RS⟩ := hrec r hr
      rw [expandInstr_call_some hci] at STK3 S1 S2
      have hdstk : (ictx ctx s f s0 res).dstk ≥ ctx.dstk + ctx.mstk :=
        align_le _ _ (minSafeAlignment_pos _)
      obtain ⟨A, B, C⟩ := inlined_spec fenv stacksize fe FE r RI RS ctx (ictx ctx s f s0 res) pc id f
        (sregs ctx args) s c rfl rfl rfl rfl (align_divides _ _)
        (Int.le_trans (Int.add_nonneg STK2 STK1) hdstk) OPC STK3 S1 S2
      exact .call_inlined ctx pc sg id args res s0 c f _ (ictx ctx s f s0 res) (DEFS _ rfl)
        (FE _ _ hfe) A B C rfl OREG ⟨STK1, hdstk⟩
  | Itailcall sg ros args =>
    rcases hci : canInline fe rec ros with _ | ⟨id, f, r⟩
    · rcases hri : ctx.retinfo with _ | ⟨rpc, rreg⟩
      · rw [expandInstr_tailcall_none_none hci hri] at S2
        exact .tailcall _ _ _ _ _ _ (S2.trans (setInstr_get_same _ _ _)) hri
      · rw [expandInstr_tailcall_none_some hci hri] at S2
        exact .tailcall_call _ _ _ _ _ _ _ _ (S2.trans (setInstr_get_same _ _ _)) hri
    · obtain ⟨rfl, hr, hfe⟩ := canInline_some hci
      obtain ⟨RI, RS⟩ := hrec r hr
      rw [expandInstr_tailcall_some hci] at STK3 S1 S2
      have hdstk : (tctx ctx s f).dstk ≥ ctx.dstk := align_le _ _ (minSafeAlignment_pos _)
      obtain ⟨A, B, C⟩ := inlined_spec fenv stacksize fe FE r RI RS ctx (tctx ctx s f) pc id f
        (sregs ctx args) s c rfl rfl rfl rfl (align_divides _ _) (Int.le_trans STK2 hdstk) OPC
        STK3 S1 S2
      exact .tailcall_inlined ctx pc sg id args c f _ (tctx ctx s f) (FE _ _ hfe) A B C rfl OREG rfl
  | Ibuiltin ef args res s0 =>
    refine .builtin _ _ _ _ _ _ _ ?_
      (base_spec (i := .Ibuiltin ef (args.map (sbuiltinarg ctx)) (sbuiltinres ctx res) (spc ctx s0))
        S2 rfl)
    cases res with
    | BR r => exact DEFS _ rfl
    | _ => trivial
  | Icond cond args s1 s2 =>
    exact .cond _ _ _ _ _ _ _
      (base_spec (i := .Icond cond (sregs ctx args) (spc ctx s1) (spc ctx s2)) S2 rfl)
  | Ijumptable r tbl =>
    exact .jumptable _ _ _ _ _
      (base_spec (i := .Ijumptable (sreg ctx r) (tbl.map (spc ctx))) S2 rfl)
  | Ireturn or =>
    rcases hri : ctx.retinfo with _ | rinfo
    · rw [expandInstr_return_none hri] at S2
      exact .ret _ _ _ _ (S2.trans (setInstr_get_same _ _ _)) hri
    · rw [expandInstr_return_some hri] at S2
      exact .return_inlined _ _ _ _ _ (S2.trans (setInstr_get_same _ _ _)) hri

/-- `Inliningspec.iter_expand_instr_spec` -/
theorem iter_expand_instr_spec (fe : Funenv) (FE : FenvAgree fenv fe) (rec : Recursor)
    (hrec : ∀ r, rec = some r → RecIncr r ∧ RecSpec fenv stacksize r) (ctx : Context) (c : Code) :
    ∀ (l : List (Positive × Instruction)) (s : State),
    (l.map Prod.fst).Nodup →
    (∀ pc i r, (pc, i) ∈ l → instrDefs i = some r → r ≤ ctx.mreg) →
    (∀ pc i, (pc, i) ∈ l → spc ctx pc < s.st_nextnode) →
    Positive.add ctx.dreg ctx.mreg ≤ s.st_nextreg →
    ctx.mstk ≥ 0 → ctx.dstk ≥ 0 →
    (iterState (expandInstr fe rec ctx) l s).st_stksize ≤ stacksize →
    (∀ pc', s.st_nextnode ≤ pc' → pc' < (iterState (expandInstr fe rec ctx) l s).st_nextnode →
      c.get pc' = (iterState (expandInstr fe rec ctx) l s).st_code.get pc') →
    (∀ pc i, (pc, i) ∈ l →
      c.get (spc ctx pc) = (iterState (expandInstr fe rec ctx) l s).st_code.get (spc ctx pc)) →
    ∀ pc i, (pc, i) ∈ l → TrInstr fenv stacksize ctx pc i c
  | [], _, _, _, _, _, _, _, _, _, _, _, _, h => by cases h
  | (pc1, i1) :: l, s, ND, H1, H2, OREG, STK1, STK2, STK3, H7, H8, pc, i, hmem => by
    have hri : ∀ r, rec = some r → RecIncr r := fun r h => (hrec r h).1
    rw [List.map_cons, List.nodup_cons] at ND
    obtain ⟨ND1, ND2⟩ := ND
    simp only [iterState_cons] at STK3 H7 H8
    have I0 := expandInstr_incr fe rec hri ctx pc1 i1 s
    have I1 := iterState_incr (fun k v => expandInstr_incr fe rec hri ctx k v) l
      (expandInstr fe rec ctx pc1 i1 s).2
    have I0n := I0.nextnode
    have I0r := I0.nextreg
    have I1n := I1.nextnode
    have I1k := I1.stksize
    have notin : ∀ pc', s.st_nextnode ≤ pc' → pc' ∉ (l.map Prod.fst).map (spc ctx) := by
      intro pc' h1 h2
      rw [List.map_map] at h2
      obtain ⟨⟨pc0, i0⟩, hm, he⟩ := List.mem_map.mp h2
      have := H2 pc0 i0 (List.mem_cons_of_mem _ hm)
      simp only [Function.comp] at he
      rw [he] at this
      pos_omega
    rcases List.mem_cons.mp hmem with he | hm
    · cases he
      refine expand_instr_spec fenv stacksize fe FE rec hrec ctx _ _ s c
        (fun r h => H1 _ _ r (List.mem_cons_self) h) (H2 _ _ List.mem_cons_self) OREG STK1 STK2
        (Int.le_trans I1k STK3) (fun pc' h1 h2 => ?_) ?_
      · rw [H7 pc' h1 (by pos_omega)]
        exact iter_expand_instr_unchanged fe rec hri ctx l _ h2 (notin pc' h1)
      · rw [H8 _ _ List.mem_cons_self]
        refine iter_expand_instr_unchanged fe rec hri ctx l _
          (by have := H2 _ _ List.mem_cons_self; pos_omega) ?_
        intro h2
        rw [List.map_map] at h2
        obtain ⟨⟨pc0, i0⟩, hm, he⟩ := List.mem_map.mp h2
        simp only [Function.comp] at he
        have := shiftpos_inj he
        subst this
        exact ND1 (List.mem_map.mpr ⟨_, hm, rfl⟩)
    · exact iter_expand_instr_spec fe FE rec hrec ctx c l _ ND2
        (fun pc i r h => H1 pc i r (List.mem_cons_of_mem _ h))
        (fun pc i h => by have := H2 pc i (List.mem_cons_of_mem _ h); pos_omega)
        (by pos_omega) STK1 STK2 STK3
        (fun pc' h1 h2 => H7 pc' (by pos_omega) h2)
        (fun pc i h => H8 pc i (List.mem_cons_of_mem _ h)) pc i hm

/-- `Inliningspec.expand_cfg_rec_spec` -/
theorem expand_cfg_rec_spec (fe : Funenv) (FE : FenvAgree fenv fe) (rec : Recursor)
    (hrec : ∀ r, rec = some r → RecIncr r ∧ RecSpec fenv stacksize r)
    (ctx : Context) (f : RTL.Function) (s : State) (c : Code)
    (H1 : Positive.add ctx.dpc (maxPcFunction f) ≤ s.st_nextnode)
    (H2 : ctx.mreg = maxRegFunction f)
    (H3 : Positive.add ctx.dreg ctx.mreg ≤ s.st_nextreg)
    (H4 : ctx.mstk ≥ 0) (H5 : ctx.mstk = Max.max f.fn_stacksize 0)
    (H6 : minSafeAlignment f.fn_stacksize ∣ ctx.dstk) (H7 : ctx.dstk ≥ 0)
    (H8 : (expandCfgRec fe rec ctx f s).2.st_stksize ≤ stacksize)
    (H9 : ∀ pc', ctx.dpc ≤ pc' → pc' < (expandCfgRec fe rec ctx f s).2.st_nextnode →
      c.get pc' = (expandCfgRec fe rec ctx f s).2.st_code.get pc') :
    TrFunbody fenv stacksize ctx f c := by
  have hri : ∀ r, rec = some r → RecIncr r := fun r h => (hrec r h).1
  let s0 := (requestStack (ctx.dstk + ctx.mstk) s).2
  have E : (expandCfgRec fe rec ctx f s).2 =
      iterState (expandInstr fe rec ctx) (PTree.elements f.fn_code) s0 := rfl
  rw [E] at H8 H9
  have N0 : s0.st_nextnode = s.st_nextnode := rfl
  have N0' : s0.st_nextnode.toNat = s.st_nextnode.toNat := rfl
  have R0 : s0.st_nextreg = s.st_nextreg := rfl
  have K0 : ctx.dstk + ctx.mstk ≤ s0.st_stksize := Int.le_max_right _ _
  have I1 := iterState_incr (fun k v => expandInstr_incr fe rec hri ctx k v)
    (PTree.elements f.fn_code) s0
  have I1n := I1.nextnode
  have I1k := I1.stksize
  have below : ∀ pc i, (pc, i) ∈ PTree.elements f.fn_code → spc ctx pc < s.st_nextnode := by
    intro pc i h
    have := max_pc_function_sound (PTree.elements_complete _ _ _ h)
    have := Positive.toNat_pos ctx.dpc
    have := Positive.toNat_pos pc
    unfold spc
    pos_omega
  refine .intro _ _ _ (fun r hr => by rw [H2]; exact max_reg_function_params hr) ?_ H5 H6 H7
    (Int.le_trans K0 (Int.le_trans I1k H8))
  intro pc i hpc
  refine iter_expand_instr_spec fenv stacksize fe FE rec hrec ctx c _ s0
    (PTree.elements_keys_norepet _)
    (fun pc i r h hd => by rw [H2]; exact max_reg_function_def (PTree.elements_complete _ _ _ h) hd)
    (fun pc i h => by rw [N0]; exact below pc i h) (by rw [R0]; exact H3) H4 H7 H8
    (fun pc' h1 h2 => H9 pc' (by have := Positive.toNat_pos (maxPcFunction f); pos_omega) h2)
    (fun pc i h => H9 _ (shiftpos_above _ _) (by have := below pc i h; pos_omega))
    pc i (PTree.elements_correct _ _ _ hpc)

/-- The recursor `expand_cfg_rec` meets its specification (the induction of `expand_cfg_spec`). -/
theorem expandCfgFuel_spec : ∀ n, RecSpec fenv stacksize (expandCfgFuel n)
  | 0 => fun fe' ctx f s c FE' => expand_cfg_rec_spec fenv stacksize fe' FE' none
      (fun _ h => by cases h) ctx f s c
  | n + 1 => fun fe' ctx f s c FE' => expand_cfg_rec_spec fenv stacksize fe' FE'
      (some (expandCfgFuel n)) (fun r h => by
        cases h; exact ⟨expandCfgFuel_recIncr n, expandCfgFuel_spec n⟩) ctx f s c

/-- `Inliningspec.expand_cfg_spec` -/
theorem expand_cfg_spec (fe : Funenv) : RecSpec fenv stacksize (fun fe' => expandCfg fe') :=
  fun fe' => expandCfgFuel_spec fenv stacksize (sizeFenv fe') fe'

end EXPAND

end Inlining
end CC
