/-
  Correctness of instruction selection for x86-64 (the x86 instance of
  `CCLib/backend/SelectionproofLessdef.lean`) — port of `backend/Selectionproof.v`,
  part 3: compatibility of the Cminor evaluation functions with the
  "less defined than" relation (`eval_unop_lessdef`, `eval_binop_lessdef`)
  and the relation between local environments (`env_lessdef`,
  `set_var_lessdef`, `set_optvar_lessdef`, `set_params_lessdef`,
  `set_locals_lessdef`).
-/
import CCLib.x86.SelectionproofSwitch
import CCLib.backend.CminorSem
import CCLib.common.MemoryExtends

namespace CC
namespace X86
namespace Selectionproof

/-- `Selectionproof.eval_unop_lessdef` -/
theorem eval_unop_lessdef {op : Cminor.UnaryOperation} {v1 v1' v : Val}
    (hv : Cminor.evalUnop op v1 = some v) (h : Val.Lessdef v1 v1') :
    ∃ v', Cminor.evalUnop op v1' = some v' ∧ Val.Lessdef v v' := by
  cases h with
  | refl => exact ⟨v, hv, .refl _⟩
  | undef =>
    cases op <;>
      first
        | (cases hv; done)
        | (refine ⟨_, rfl, ?_⟩; cases hv; exact .undef _)

/-- `Selectionproof.eval_binop_lessdef` -/
theorem eval_binop_lessdef {op : Cminor.BinaryOperation} {v1 v1' v2 v2' v : Val} {m m' : Mem}
    (hv : Cminor.evalBinop op v1 v2 m = some v) (h1 : Val.Lessdef v1 v1')
    (h2 : Val.Lessdef v2 v2') (hm : Mem.Extends m m') :
    ∃ v', Cminor.evalBinop op v1' v2' m' = some v' ∧ Val.Lessdef v v' := by
  have hvp : ∀ b ofs, Mem.validPointer m b ofs = true → Mem.validPointer m' b ofs = true :=
    fun _ _ h => Mem.validPointer_extends hm h
  cases op
  case Ocmpu c =>
    cases hv
    exact ⟨_, rfl, Val.of_optbool_lessdef (fun _ hb => Val.cmpu_bool_lessdef hvp h1 h2 hb)⟩
  case Ocmplu c =>
    have hv' : (Val.cmplu_bool (Mem.validPointer m) c v1 v2).map Val.ofBool = some v := hv
    rcases hc : Val.cmplu_bool (Mem.validPointer m) c v1 v2 with _ | b
    · rw [hc] at hv'; cases hv'
    · rw [hc] at hv'; cases hv'
      refine ⟨Val.ofBool b, ?_, .refl _⟩
      show (Val.cmplu_bool (Mem.validPointer m') c v1' v2').map Val.ofBool = _
      rw [Val.cmplu_bool_lessdef hvp h1 h2 hc]; rfl
  all_goals
    cases h1 <;> cases h2 <;>
      first
        | exact ⟨v, hv, .refl _⟩
        | (cases hv; done)
        | (cases v1 <;> (cases hv; done))
        | (cases v2 <;> (cases hv; done))
        | (refine ⟨_, rfl, ?_⟩; cases hv; exact .undef _)
        | (cases v1 <;> (refine ⟨_, rfl, ?_⟩; cases hv; exact .undef _))
        | (cases v2 <;> (refine ⟨_, rfl, ?_⟩; cases hv; exact .undef _))

/-- `Selectionproof.env_lessdef` -/
def EnvLessdef (e1 e2 : Cminor.Env) : Prop :=
  ∀ id v1, e1.get id = some v1 → ∃ v2, e2.get id = some v2 ∧ Val.Lessdef v1 v2

/-- `Selectionproof.set_var_lessdef` -/
theorem set_var_lessdef {e1 e2 : Cminor.Env} {id : Ident} {v1 v2 : Val} (he : EnvLessdef e1 e2)
    (hv : Val.Lessdef v1 v2) : EnvLessdef (PTree.set id v1 e1) (PTree.set id v2 e2) := by
  intro id0 w h
  by_cases hid : id0 = id
  · subst hid
    rw [PTree.gss] at h ⊢
    cases h
    exact ⟨v2, rfl, hv⟩
  · rw [PTree.gso _ _ _ _ (Ne.symm hid)] at h ⊢
    exact he _ _ h

/-- `Selectionproof.set_optvar_lessdef` -/
theorem set_optvar_lessdef {e1 e2 : Cminor.Env} {optid : Option Ident} {v1 v2 : Val}
    (he : EnvLessdef e1 e2) (hv : Val.Lessdef v1 v2) :
    EnvLessdef (Cminor.setOptvar optid v1 e1) (Cminor.setOptvar optid v2 e2) := by
  cases optid with
  | none => exact he
  | some id => exact set_var_lessdef he hv

/-- `Selectionproof.set_params_lessdef` -/
theorem set_params_lessdef (il : List Ident) :
    ∀ {vl1 vl2 : List Val}, Val.LessdefList vl1 vl2 →
    EnvLessdef (Cminor.setParams vl1 il) (Cminor.setParams vl2 il) := by
  induction il with
  | nil =>
    intro vl1 vl2 _ id v h
    cases vl1 <;> simp [Cminor.setParams] at h
  | cons i1 il ih =>
    intro vl1 vl2 hl
    cases hl with
    | nil => exact set_var_lessdef (ih .nil) (.refl _)
    | cons hv hl => exact set_var_lessdef (ih hl) hv

/-- `Selectionproof.set_locals_lessdef` -/
theorem set_locals_lessdef {e1 e2 : Cminor.Env} (he : EnvLessdef e1 e2) (il : List Ident) :
    EnvLessdef (Cminor.setLocals il e1) (Cminor.setLocals il e2) := by
  induction il with
  | nil => exact he
  | cons i1 il ih => exact set_var_lessdef ih (.refl _)

end Selectionproof
end X86
end CC
