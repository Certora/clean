/-
  Correctness proof for the layout of activation records, part 2 — port of
  the "Agreement between location sets and Mach states" part of
  `backend/Stackingproof.v`: `agree_regs`, `agree_locs` and their
  preservation lemmas, and the remarks about destroyed registers.
-/
import CCLib.backend.StackingproofFrame
import CCLib.common.ValuesInject

namespace CC
namespace Stackingproof

open Linear Mach Conventions1 Conventions Stacklayout Stacking Bounds Separation
open Lineartyping

/-! ## Agreement with Mach register states -/

/-- `Stackingproof.agree_regs` -/
def AgreeRegs (j : Val.Meminj) (ls : LTL.Locset) (rs : Regset) : Prop :=
  ∀ r, Val.Inject j (ls (.R r)) (rs r)

/-- `Stackingproof.agree_locs` -/
structure AgreeLocs (abi : AbiKind) (f : Linear.Function) (ls ls0 : LTL.Locset) : Prop where
  /-- Unused registers have the same value as in the caller. -/
  agree_unused_reg : ∀ r, ¬ MregWithinBounds (bnds abi f) r → ls (.R r) = ls0 (.R r)
  /-- Incoming stack slots have the same value as the corresponding Outgoing
      stack slots in the caller. -/
  agree_incoming : ∀ ofs ty,
    Loc.S .Incoming ofs ty ∈ RPair.regsList (locParameters abi f.fn_sig) →
    ls (.S .Incoming ofs ty) = ls0 (.S .Outgoing ofs ty)

/-! ### Properties of `agree_regs` -/

/-- `Stackingproof.agree_reg` -/
theorem agree_reg {j : Val.Meminj} {ls : LTL.Locset} {rs : Regset} (r : Mreg)
    (h : AgreeRegs j ls rs) : Val.Inject j (ls (.R r)) (rs r) := h r

/-- `Stackingproof.agree_reglist` -/
theorem agree_reglist {j : Val.Meminj} {ls : LTL.Locset} {rs : Regset} (rl : List Mreg)
    (h : AgreeRegs j ls rs) : Val.InjectList j (LTL.reglist ls rl) (rl.map rs) := by
  induction rl with
  | nil => exact .nil
  | cons r rl ih => exact .cons (h r) ih

/-- `Stackingproof.agree_regs_set_reg` -/
theorem agree_regs_set_reg {j : Val.Meminj} {ls : LTL.Locset} {rs : Regset} (r : Mreg)
    {v v' : Val} (h : AgreeRegs j ls rs) (hv : Val.Inject j v v') :
    AgreeRegs j (Locmap.set (.R r) v ls) (Regset.set r v' rs) := by
  intro r0
  by_cases e : r0 = r
  · subst e; rw [Locmap.gss_reg, Regset.gss]; exact hv
  · rw [Locmap.gso (by simp [Loc.diff]; exact Ne.symm e), Regset.gso _ _ e]; exact h r0

/-- `Stackingproof.agree_regs_set_pair` -/
theorem agree_regs_set_pair {j : Val.Meminj} (p : RPair Mreg) {v v' : Val} {ls : LTL.Locset}
    {rs : Regset} (h : AgreeRegs j ls rs) (hv : Val.Inject j v v') :
    AgreeRegs j (Locmap.setpair p v ls) (setPair p v' rs) := by
  cases p with
  | One r => exact agree_regs_set_reg r h hv
  | Twolong r1 r2 =>
    exact agree_regs_set_reg _ (agree_regs_set_reg _ h (Val.hiword_inject hv))
      (Val.loword_inject hv)

/-- `Stackingproof.agree_regs_set_res` -/
theorem agree_regs_set_res {j : Val.Meminj} (res : BuiltinRes Mreg) :
    ∀ {v v' : Val} {ls : LTL.Locset} {rs : Regset}, AgreeRegs j ls rs → Val.Inject j v v' →
      AgreeRegs j (Locmap.setres res v ls) (setRes res v' rs) := by
  induction res with
  | BR r => intro v v' ls rs h hv; exact agree_regs_set_reg r h hv
  | BR_none => intro v v' ls rs h _; exact h
  | BR_splitlong hi lo ihhi ihlo =>
    intro v v' ls rs h hv
    exact ihlo (ihhi h (Val.hiword_inject hv)) (Val.loword_inject hv)

/-- `Stackingproof.agree_regs_exten` -/
theorem agree_regs_exten {j : Val.Meminj} {ls : LTL.Locset} {rs : Regset} {ls' : LTL.Locset}
    {rs' : Regset} (h : AgreeRegs j ls rs)
    (hx : ∀ r, ls' (.R r) = .Vundef ∨ (ls' (.R r) = ls (.R r) ∧ rs' r = rs r)) :
    AgreeRegs j ls' rs' := by
  intro r
  rcases hx r with A | ⟨A, B⟩
  · rw [A]; exact .undef _
  · rw [A, B]; exact h r

/-- `Stackingproof.agree_regs_undef_regs` -/
theorem agree_regs_undef_regs {j : Val.Meminj} (rl : List Mreg) {ls : LTL.Locset} {rs : Regset}
    (h : AgreeRegs j ls rs) : AgreeRegs j (LTL.undefRegs rl ls) (Mach.undefRegs rl rs) := by
  induction rl with
  | nil => exact h
  | cons r rl ih => exact agree_regs_set_reg r ih (.undef _)

/-- `Stackingproof.agree_regs_undef_caller_save_regs` -/
theorem agree_regs_undef_caller_save_regs {j : Val.Meminj} {ls : LTL.Locset} {rs : Regset}
    (h : AgreeRegs j ls rs) :
    AgreeRegs j (LTL.undefCallerSaveRegs ls) (Mach.undefCallerSaveRegs rs) := by
  intro r
  simp only [LTL.undefCallerSaveRegs, Mach.undefCallerSaveRegs]
  split
  · exact h r
  · exact .undef _

/-- `Stackingproof.agree_regs_set_slot` -/
theorem agree_regs_set_slot {j : Val.Meminj} {ls : LTL.Locset} {rs : Regset} (sl : Slot)
    (ofs : Z) (ty : ATyp) (v : Val) (h : AgreeRegs j ls rs) :
    AgreeRegs j (Locmap.set (.S sl ofs ty) v ls) rs := by
  intro r
  rw [Locmap.gso (by simp [Loc.diff])]
  exact h r

/-- `Stackingproof.agree_regs_inject_incr` -/
theorem agree_regs_inject_incr {j : Val.Meminj} {ls : LTL.Locset} {rs : Regset}
    {j' : Val.Meminj} (h : AgreeRegs j ls rs) (hj : Val.inject_incr j j') : AgreeRegs j' ls rs :=
  fun r => Val.inject_incr_inject hj (h r)

/-- `Stackingproof.agree_regs_call_regs` -/
theorem agree_regs_call_regs {j : Val.Meminj} {ls : LTL.Locset} {rs : Regset}
    (h : AgreeRegs j ls rs) : AgreeRegs j (LTL.callRegs ls) rs := h

/-! ### Properties of `agree_locs` -/

section AGREE_LOCS
variable {abi : AbiKind} {f : Linear.Function}

/-- `Stackingproof.agree_locs_set_reg` -/
theorem agree_locs_set_reg {ls ls0 : LTL.Locset} {r : Mreg} (v : Val) (h : AgreeLocs abi f ls ls0)
    (hr : MregWithinBounds (bnds abi f) r) : AgreeLocs abi f (Locmap.set (.R r) v ls) ls0 := by
  refine ⟨fun r' hr' => ?_, fun ofs ty hin => ?_⟩
  · have hne : r ≠ r' := fun e => hr' (e ▸ hr)
    rw [Locmap.gso (by simp [Loc.diff]; exact hne)]
    exact h.agree_unused_reg r' hr'
  · rw [Locmap.gso (by simp [Loc.diff])]
    exact h.agree_incoming ofs ty hin

/-- `Stackingproof.caller_save_reg_within_bounds` -/
theorem caller_save_reg_within_bounds {r : Mreg} (h : isCalleeSave r = false) :
    MregWithinBounds (bnds abi f) r := by
  intro h'; rw [h] at h'; cases h'

/-- `Stackingproof.agree_locs_set_pair` -/
theorem agree_locs_set_pair {ls0 : LTL.Locset} (p : RPair Mreg) (v : Val) {ls : LTL.Locset}
    (h : AgreeLocs abi f ls ls0) (hp : p.Forall (fun r => isCalleeSave r = false)) :
    AgreeLocs abi f (Locmap.setpair p v ls) ls0 := by
  cases p with
  | One r => exact agree_locs_set_reg _ h (caller_save_reg_within_bounds hp)
  | Twolong r1 r2 =>
    exact agree_locs_set_reg _ (agree_locs_set_reg _ h (caller_save_reg_within_bounds hp.1))
      (caller_save_reg_within_bounds hp.2)

/-- `Stackingproof.agree_locs_set_res` -/
theorem agree_locs_set_res {ls0 : LTL.Locset} (res : BuiltinRes Mreg) :
    ∀ (v : Val) {ls : LTL.Locset}, AgreeLocs abi f ls ls0 →
      (∀ r, r ∈ BuiltinRes.params res → MregWithinBounds (bnds abi f) r) →
      AgreeLocs abi f (Locmap.setres res v ls) ls0 := by
  induction res with
  | BR r => intro v ls h hr; exact agree_locs_set_reg _ h (hr r (by simp [BuiltinRes.params]))
  | BR_none => intro v ls h _; exact h
  | BR_splitlong hi lo ihhi ihlo =>
    intro v ls h hr
    exact ihlo _ (ihhi _ h fun r hr' => hr r (by simp [BuiltinRes.params, hr']))
      fun r hr' => hr r (by simp [BuiltinRes.params, hr'])

/-- `Stackingproof.agree_locs_undef_regs` -/
theorem agree_locs_undef_regs {ls0 : LTL.Locset} (regs : List Mreg) {ls : LTL.Locset}
    (h : AgreeLocs abi f ls ls0) (hr : ∀ r, r ∈ regs → MregWithinBounds (bnds abi f) r) :
    AgreeLocs abi f (LTL.undefRegs regs ls) ls0 := by
  induction regs with
  | nil => exact h
  | cons r rl ih =>
    exact agree_locs_set_reg _ (ih fun r' h' => hr r' (List.mem_cons_of_mem _ h'))
      (hr r List.mem_cons_self)

/-- `Stackingproof.agree_locs_undef_locs_1` -/
theorem agree_locs_undef_locs_1 {ls0 : LTL.Locset} (regs : List Mreg) {ls : LTL.Locset}
    (h : AgreeLocs abi f ls ls0) (hr : ∀ r, r ∈ regs → isCalleeSave r = false) :
    AgreeLocs abi f (LTL.undefRegs regs ls) ls0 :=
  agree_locs_undef_regs regs h fun r h' => caller_save_reg_within_bounds (hr r h')

/-- `Stackingproof.agree_locs_undef_locs` -/
theorem agree_locs_undef_locs {ls0 : LTL.Locset} (regs : List Mreg) {ls : LTL.Locset}
    (h : AgreeLocs abi f ls ls0) (hr : regs.any isCalleeSave = false) :
    AgreeLocs abi f (LTL.undefRegs regs ls) ls0 :=
  agree_locs_undef_locs_1 regs h fun r h' => by
    cases e : isCalleeSave r
    · rfl
    · have : regs.any isCalleeSave = true := List.any_eq_true.mpr ⟨r, h', e⟩
      rw [this] at hr; cases hr

/-- `Stackingproof.agree_locs_set_slot` -/
theorem agree_locs_set_slot {ls ls0 : LTL.Locset} {sl : Slot} (ofs : Z) (ty : ATyp) (v : Val)
    (h : AgreeLocs abi f ls ls0) (hw : slotWritable sl = true) :
    AgreeLocs abi f (Locmap.set (.S sl ofs ty) v ls) ls0 := by
  refine ⟨fun r hr => ?_, fun ofs' ty' hin => ?_⟩
  · rw [Locmap.gso (by simp [Loc.diff])]; exact h.agree_unused_reg r hr
  · rw [Locmap.gso (by cases sl <;> simp_all [Loc.diff, slotWritable])]
    exact h.agree_incoming ofs' ty' hin

/-- `Stackingproof.agree_locs_return` -/
theorem agree_locs_return {ls ls0 ls' : LTL.Locset} (h : AgreeLocs abi f ls ls0)
    (hc : AgreeCalleeSave ls' ls) : AgreeLocs abi f ls' ls0 := by
  refine ⟨fun r hr => ?_, fun ofs ty hin => ?_⟩
  · rw [hc (.R r) (by
      simp only [CalleeSaveLoc]
      cases e : isCalleeSave r
      · exact absurd (caller_save_reg_within_bounds e) hr
      · rfl)]
    exact h.agree_unused_reg r hr
  · rw [← h.agree_incoming ofs ty hin]
    exact hc _ (by simp [CalleeSaveLoc])

end AGREE_LOCS

/-! ## Properties of destroyed registers -/

/-- `Stackingproof.no_callee_saves` -/
def NoCalleeSaves (l : List Mreg) : Prop := l.any isCalleeSave = false

/-- `Stackingproof.destroyed_by_op_caller_save` -/
theorem destroyed_by_op_caller_save (op : Op.Operation) : NoCalleeSaves (destroyedByOp op) := by
  unfold NoCalleeSaves destroyedByOp; split <;> rfl

/-- `Stackingproof.destroyed_by_load_caller_save` -/
theorem destroyed_by_load_caller_save (chunk : Chunk) (addr : Op.Addressing) :
    NoCalleeSaves (destroyedByLoad chunk addr) := rfl

/-- `Stackingproof.destroyed_by_store_caller_save` -/
theorem destroyed_by_store_caller_save (chunk : Chunk) (addr : Op.Addressing) :
    NoCalleeSaves (destroyedByStore chunk addr) := rfl

/-- `Stackingproof.destroyed_by_cond_caller_save` -/
theorem destroyed_by_cond_caller_save (cond : Op.Condition) :
    NoCalleeSaves (destroyedByCond cond) := rfl

/-- `Stackingproof.destroyed_by_jumptable_caller_save` -/
theorem destroyed_by_jumptable_caller_save : NoCalleeSaves destroyedByJumptable := rfl

/-- `Stackingproof.destroyed_by_setstack_caller_save` -/
theorem destroyed_by_setstack_caller_save (ty : ATyp) :
    NoCalleeSaves (destroyedBySetstack ty) := rfl

/-- `Stackingproof.destroyed_at_function_entry_caller_save` -/
theorem destroyed_at_function_entry_caller_save : NoCalleeSaves destroyedAtFunctionEntry := rfl

/-- `Stackingproof.destroyed_by_setstack_function_entry` -/
theorem destroyed_by_setstack_function_entry (ty : ATyp) :
    ∀ r, r ∈ destroyedBySetstack ty → r ∈ destroyedAtFunctionEntry := by
  intro r h; cases h

/-- `Stackingproof.transl_destroyed_by_op` -/
theorem transl_destroyed_by_op (op : Op.Operation) (e : FrameEnv) :
    destroyedByOp (translOp e op) = destroyedByOp op := by
  cases op <;> rfl

/-- `Stackingproof.transl_destroyed_by_load` -/
theorem transl_destroyed_by_load (chunk : Chunk) (addr : Op.Addressing) (e : FrameEnv) :
    destroyedByLoad chunk (translAddr e addr) = destroyedByLoad chunk addr := rfl

/-- `Stackingproof.transl_destroyed_by_store` -/
theorem transl_destroyed_by_store (chunk : Chunk) (addr : Op.Addressing) (e : FrameEnv) :
    destroyedByStore chunk (translAddr e addr) = destroyedByStore chunk addr := rfl

end Stackingproof
end CC
