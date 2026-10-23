/-
  Correctness proof for x86-64 code generation, part 1 — port of the
  `TRANSL_LABEL` section of `x86/Asmgenproof.v`: the Asm constructor
  functions do not introduce labels, so that the translation commutes with
  label lookup (`transl_code_label`, `transl_find_label`).
-/
import CCLib.x86.Asmgenproof1Op

namespace CC
namespace X86
namespace Asmgenproof

open Asm Asmgen Asmgenproof0 Asmgenproof1 Op

/-- Peel off non-label instructions until the continuation is reached. -/
macro "tnl" : tactic =>
  `(tactic| repeat' (first | exact tail_nolabel_refl _ | refine tail_nolabel_cons (by trivial) ?_))

/-- `Asmgenproof.mk_mov_label` -/
theorem mk_mov_label {rd rs : Preg} {k c : Code} (h : mkMov rd rs k = .OK c) :
    TailNolabel k c := by
  unfold mkMov at h; split at h <;> cases h <;> tnl

/-- `Asmgenproof.mk_shrximm_label` -/
theorem mk_shrximm_label {n : Integers.Int} {k c : Code} (h : mkShrximm n k = .OK c) :
    TailNolabel k c := by
  unfold mkShrximm at h; cases h; tnl

/-- `Asmgenproof.mk_shrxlimm_label` -/
theorem mk_shrxlimm_label {n : Integers.Int} {k c : Code} (h : mkShrxlimm n k = .OK c) :
    TailNolabel k c := by
  unfold mkShrxlimm at h; cases h; split <;> tnl

/-- `Asmgenproof.mk_intconv_label` -/
theorem mk_intconv_label {mk : Ireg → Ireg → Instruction} {r1 r2 : Ireg} {k c : Code}
    (h : mkIntconv mk r1 r2 k = .OK c) (hmk : ∀ r r', Nolabel (mk r r')) : TailNolabel k c := by
  unfold mkIntconv at h; split at h <;> cases h
  · exact tail_nolabel_cons (hmk _ _) (tail_nolabel_refl _)
  · exact tail_nolabel_cons (by trivial) (tail_nolabel_cons (hmk _ _) (tail_nolabel_refl _))

/-- `Asmgenproof.mk_storebyte_label` -/
theorem mk_storebyte_label {addr : Addrmode} {r : Ireg} {k c : Code}
    (h : mkStorebyte addr r k = .OK c) : TailNolabel k c := by
  unfold mkStorebyte at h; split at h <;> (try split at h) <;> cases h <;> tnl

/-- `Asmgenproof.loadind_label` -/
theorem loadind_label {base : Ireg} {ofs : Integers.Ptrofs} {ty : ATyp} {dst : Mreg}
    {k c : Code} (h : loadind base ofs ty dst k = .OK c) : TailNolabel k c := by
  unfold loadind at h; split at h <;> (try split at h) <;> cases h <;> tnl

/-- `Asmgenproof.storeind_label` -/
theorem storeind_label {src : Mreg} {base : Ireg} {ofs : Integers.Ptrofs} {ty : ATyp}
    {k c : Code} (h : storeind src base ofs ty k = .OK c) : TailNolabel k c := by
  unfold storeind at h; split at h <;> (try split at h) <;> cases h <;> tnl

/-- `Asmgenproof.mk_setcc_base_label` -/
theorem mk_setcc_base_label (xc : Extcond) (rd : Ireg) (k : Code) :
    TailNolabel k (mkSetccBase xc rd k) := by
  cases xc <;> simp only [mkSetccBase] <;> (try split) <;> tnl

/-- `Asmgenproof.mk_setcc_label` -/
theorem mk_setcc_label (xc : Extcond) (rd : Ireg) (k : Code) :
    TailNolabel k (mkSetcc xc rd k) := by
  unfold mkSetcc; split
  · exact mk_setcc_base_label _ _ _
  · exact tail_nolabel_trans (mk_setcc_base_label _ _ _)
      (tail_nolabel_cons (by trivial) (tail_nolabel_refl _))

/-- `Asmgenproof.mk_jcc_label` -/
theorem mk_jcc_label (xc : Extcond) (lbl : Label) (k : Code) :
    TailNolabel k (mkJcc xc lbl k) := by
  cases xc <;> simp only [mkJcc] <;> tnl

/-- `Asmgenproof.mk_sel_label` -/
theorem mk_sel_label {xc : Extcond} {rd r2 : Ireg} {k c : Code} (h : mkSel xc rd r2 k = .OK c) :
    TailNolabel k c := by
  cases xc <;> simp only [mkSel] at h <;> cases h <;> tnl

/-- `Asmgenproof.transl_cond_label` -/
theorem transl_cond_label {cond : Condition} {args : List Mreg} {k c : Code}
    (h : translCond cond args k = .OK c) : TailNolabel k c := by
  cases cond <;> rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, args⟩⟩⟩ <;>
    simp only [translCond, res_bind_OK, res_pure_OK] at h <;> (try (cases h; done))
  all_goals first
    | (obtain ⟨_, _, rfl⟩ := h; split <;> tnl; done)
    | (obtain ⟨_, _, _, _, rfl⟩ := h
       (try (unfold floatcomp; split)) <;> (try (unfold floatcomp32; split)) <;> tnl; done)
    | (obtain ⟨_, _, rfl⟩ := h; tnl; done)

/-- `Asmgenproof.transl_sel_label` (part of `transl_op_label` in Rocq). -/
theorem transl_sel_label {cond : Condition} {args : List Mreg} {rd r2 : Ireg} {k c : Code}
    (h : translSel cond args rd r2 k = .OK c) : TailNolabel k c := by
  unfold translSel at h; split at h
  · cases h; tnl
  · simp only [res_bind_OK] at h
    obtain ⟨k1, h1, h2⟩ := h
    exact tail_nolabel_trans (transl_cond_label h2) (mk_sel_label h1)

set_option maxHeartbeats 1000000 in
/-- `Asmgenproof.transl_op_label` -/
theorem transl_op_label {op : Op.Operation} {args : List Mreg} {r : Mreg} {k c : Code}
    (h : translOp op args r k = .OK c) : TailNolabel k c := by
  cases op
  case Ocmp cond =>
    unfold translOp at h
    simp only [res_bind_OK] at h; obtain ⟨_, _, h⟩ := h
    exact tail_nolabel_trans (transl_cond_label h) (mk_setcc_label _ _ _)
  case Osel cond ty =>
    rcases args with _ | ⟨a1, _ | ⟨a2, args⟩⟩ <;> unfold translOp at h <;> try cases h
    obtain ⟨_, hb⟩ := assert_OK h
    simp only [res_bind_OK] at hb; obtain ⟨_, _, _, _, h⟩ := hb
    exact transl_sel_label h
  case Olea addr =>
    unfold translOp at h
    simp only [res_bind_OK, res_pure_OK] at h; obtain ⟨_, _, _, _, rfl⟩ := h; tnl
  case Oleal addr =>
    unfold translOp at h
    simp only [res_bind_OK, res_pure_OK] at h; obtain ⟨_, _, _, _, rfl⟩ := h
    split <;> tnl
  all_goals (rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, args⟩⟩⟩ <;>
              unfold translOp at h <;> dsimp only at h <;> (try (cases h; done)))
  all_goals first
    | (guard_hyp h : iop1 _ _ _ _ = _; obtain ⟨_, _, _, rfl⟩ := iop1_inv h; tnl)
    | (guard_hyp h : iop2 _ _ _ _ _ = _; obtain ⟨_, _, _, _, _, rfl⟩ := iop2_inv h; tnl)
    | (guard_hyp h : ishift _ _ _ _ _ = _; obtain ⟨_, _, _, _, rfl⟩ := ishift_inv h; tnl)
    | (guard_hyp h : fop1 _ _ _ _ = _; obtain ⟨_, _, _, rfl⟩ := fop1_inv h; tnl)
    | (guard_hyp h : fop2 _ _ _ _ _ = _; obtain ⟨_, _, _, _, _, rfl⟩ := fop2_inv h; tnl)
    | (guard_hyp h : mulh _ _ _ _ _ = _; obtain ⟨_, _, _, _, rfl⟩ := mulh_inv h; tnl)
    | (guard_hyp h : divop _ _ _ _ _ = _; obtain ⟨_, _, _, rfl⟩ := divop_inv h; tnl)
    | (guard_hyp h : mkMov _ _ _ = _; exact mk_mov_label h)
    | (guard_hyp h : Asmgen.assert _ (Asmgen.assert _ (mkShrximm _ _)) = _
       obtain ⟨_, h⟩ := assert_OK h; obtain ⟨_, h⟩ := assert_OK h
       exact mk_shrximm_label h)
    | (guard_hyp h : Asmgen.assert _ (Asmgen.assert _ (mkShrxlimm _ _)) = _
       obtain ⟨_, h⟩ := assert_OK h; obtain ⟨_, h⟩ := assert_OK h
       exact mk_shrxlimm_label h)
    | (simp only [res_bind_OK, res_pure_OK] at h
       first
         | (obtain ⟨_, _, _, _, h⟩ := h
            first
              | (subst h; tnl)
              | exact mk_intconv_label h (fun _ _ => trivial))
         | (obtain ⟨_, _, rfl⟩ := h; (try split) <;> tnl))

/-- `Asmgenproof.transl_load_label` -/
theorem transl_load_label {chunk : Chunk} {addr : Op.Addressing} {args : List Mreg} {dst : Mreg}
    {k c : Code} (h : translLoad chunk addr args dst k = .OK c) : TailNolabel k c := by
  unfold translLoad at h
  simp only [res_bind_OK] at h; obtain ⟨_, _, h⟩ := h
  cases chunk <;> (try cases h) <;>
    (simp only [res_bind_OK, res_pure_OK] at h; obtain ⟨_, _, rfl⟩ := h; tnl)

/-- `Asmgenproof.transl_store_label` -/
theorem transl_store_label {chunk : Chunk} {addr : Op.Addressing} {args : List Mreg} {src : Mreg}
    {k c : Code} (h : translStore chunk addr args src k = .OK c) : TailNolabel k c := by
  unfold translStore at h
  simp only [res_bind_OK] at h; obtain ⟨_, _, h⟩ := h
  cases chunk <;> (try cases h) <;>
    (simp only [res_bind_OK, res_pure_OK] at h; obtain ⟨_, _, h⟩ := h
     first | exact mk_storebyte_label h | (subst h; tnl))

/-- The conclusion of `Asmgenproof.transl_instr_label`. -/
def InstrLabelSpec (i : Mach.Instruction) (k c : Code) : Prop :=
  match i with
  | .Mlabel lbl => c = .Plabel lbl :: k
  | _ => TailNolabel k c

/-- `Asmgenproof.transl_instr_label` -/
theorem transl_instr_label (f : Mach.Function) (i : Mach.Instruction) (ep : Bool)
    (k c : Code) (h : translInstr f i ep k = .OK c) : InstrLabelSpec i k c := by
  cases i <;> simp only [translInstr] at h <;> simp only [InstrLabelSpec]
  case Mgetstack => exact loadind_label h
  case Msetstack => exact storeind_label h
  case Mgetparam =>
    split at h
    · exact loadind_label h
    · simp only [res_bind_OK] at h
      obtain ⟨c1, h1, h2⟩ := h
      exact tail_nolabel_trans (loadind_label h2) (loadind_label h1)
  case Mop => exact transl_op_label h
  case Mload => exact transl_load_label h
  case Mstore => exact transl_store_label h
  case Mcall sig ros =>
    cases ros <;> simp only [res_bind_OK, res_pure_OK, Res.OK.injEq] at h
    · obtain ⟨_, _, rfl⟩ := h; tnl
    · subst h; tnl
  case Mtailcall sig ros =>
    cases ros <;> simp only [res_bind_OK, res_pure_OK, Res.OK.injEq] at h
    · obtain ⟨_, _, rfl⟩ := h; tnl
    · subst h; tnl
  case Mbuiltin => cases h; tnl
  case Mlabel => cases h; rfl
  case Mgoto => cases h; tnl
  case Mcond => exact tail_nolabel_trans (transl_cond_label h) (mk_jcc_label _ _ _)
  case Mjumptable =>
    simp only [res_bind_OK, res_pure_OK] at h
    obtain ⟨_, _, rfl⟩ := h; tnl
  case Mreturn => cases h; tnl

/-- `Asmgenproof.transl_instr_label'` -/
theorem transl_instr_label' (lbl : Label) (f : Mach.Function) (i : Mach.Instruction)
    (ep : Bool) (k c : Code) (h : translInstr f i ep k = .OK c) :
    Asmgenproof0.findLabel lbl c =
      if Mach.isLabel lbl i then some k else Asmgenproof0.findLabel lbl k := by
  have A := transl_instr_label f i ep k c h
  cases i <;> simp only [InstrLabelSpec] at A <;> try exact A.2 lbl
  subst A
  simp [Asmgenproof0.findLabel, isLabel, Mach.isLabel]

/-- `Asmgenproof.transl_code_label` -/
theorem transl_code_label (lbl : Label) (f : Mach.Function) :
    ∀ (c : Mach.Code) (ep : Bool) (tc : Code), translCode f c ep = .OK tc →
    match Mach.findLabel lbl c with
    | none => Asmgenproof0.findLabel lbl tc = none
    | some c' => ∃ tc', Asmgenproof0.findLabel lbl tc = some tc' ∧ translCode f c' false = .OK tc'
  | [], _, tc, h => by cases h; rfl
  | a :: c, ep, tc, h => by
    simp only [translCode, res_bind_OK] at h
    obtain ⟨k, hk, h⟩ := h
    simp only [Mach.findLabel]
    rw [transl_instr_label' lbl _ _ _ _ _ h]
    by_cases hl : Mach.isLabel lbl a = true
    · have C : a = .Mlabel lbl := by cases a <;> simp_all [Mach.isLabel]
      subst C
      simp only [Mach.isLabel, decide_true, if_true]
      exact ⟨k, rfl, hk⟩
    · simp only [hl, Bool.false_eq_true, if_false]
      exact transl_code_label lbl f c _ k hk

/-- `Asmgenproof.transl_find_label` -/
theorem transl_find_label (lbl : Label) (f : Mach.Function) (tf : Asm.Function)
    (h : transfFunction f = .OK tf) :
    match Mach.findLabel lbl f.fn_code with
    | none => Asmgenproof0.findLabel lbl tf.fn_code = none
    | some c => ∃ tc, Asmgenproof0.findLabel lbl tf.fn_code = some tc ∧
        translCode f c false = .OK tc := by
  simp only [transfFunction, res_bind_OK] at h
  obtain ⟨tf', h1, h2⟩ := h
  split at h2
  · cases h2
  simp only [res_pure_OK] at h2; subst h2
  simp only [translFunction, res_bind_OK, res_pure_OK] at h1
  obtain ⟨c, hc, rfl⟩ := h1
  rw [transl_code'_transl_code] at hc
  have := transl_code_label lbl f _ _ _ hc
  simp only [Asmgenproof0.findLabel, isLabel]
  exact this

end Asmgenproof
end X86
end CC
