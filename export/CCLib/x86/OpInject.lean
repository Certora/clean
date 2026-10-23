/-
  Evaluation of x86 operators is monotone with respect to `Val.lessdef` and
  memory extensions, and commutes with memory injections — port of the
  `EVAL_LESSDEF` and `EVAL_INJECT` sections of `x86/Op.v`
  (`eval_condition_lessdef`, `eval_operation_lessdef`,
  `eval_addressing_lessdef`, `eval_condition_inject`,
  `eval_operation_inject`, `eval_addressing_inject`).

  The value-level lemmas shared with aarch64 are those of
  `CCLib/aarch64/OpLessdef.lean` and `CCLib/aarch64/OpInject.lean`; only the operators
  specific to x86 (`mulhs`, `mulhu`, `mod*`, `maxf`, `minf`, `maskzero_bool`)
  need new lemmas here.
-/
import CCLib.x86.OpTheory

namespace CC
namespace X86
namespace Op

open Val

/-! ## Strictness of the x86-specific operators -/

theorem mulhs_undef_l (v : Val) : Val.mulhs .Vundef v = .Vundef := by cases v <;> rfl
theorem mulhs_undef_r (v : Val) : Val.mulhs v .Vundef = .Vundef := by cases v <;> rfl
theorem mulhu_undef_l (v : Val) : Val.mulhu .Vundef v = .Vundef := by cases v <;> rfl
theorem mulhu_undef_r (v : Val) : Val.mulhu v .Vundef = .Vundef := by cases v <;> rfl
theorem maxf_undef_l (v : Val) : maxf .Vundef v = .Vundef := by cases v <;> rfl
theorem maxf_undef_r (v : Val) : maxf v .Vundef = .Vundef := by cases v <;> rfl
theorem minf_undef_l (v : Val) : minf .Vundef v = .Vundef := by cases v <;> rfl
theorem minf_undef_r (v : Val) : minf v .Vundef = .Vundef := by cases v <;> rfl
theorem mods_undef_l (v : Val) : Val.mods .Vundef v = none := by cases v <;> rfl
theorem mods_undef_r (v : Val) : Val.mods v .Vundef = none := by cases v <;> rfl
theorem modu_undef_l (v : Val) : Val.modu .Vundef v = none := by cases v <;> rfl
theorem modu_undef_r (v : Val) : Val.modu v .Vundef = none := by cases v <;> rfl
theorem modls_undef_l (v : Val) : Val.modls .Vundef v = none := by cases v <;> rfl
theorem modls_undef_r (v : Val) : Val.modls v .Vundef = none := by cases v <;> rfl
theorem modlu_undef_l (v : Val) : Val.modlu .Vundef v = none := by cases v <;> rfl
theorem modlu_undef_r (v : Val) : Val.modlu v .Vundef = none := by cases v <;> rfl
theorem maskzero_bool_undef (n : Integers.Int) : Val.maskzero_bool .Vundef n = none := rfl

/-- Rewrites an x86-specific operator applied to an undefined argument. -/
macro "x86_undef_simp" : tactic => `(tactic| simp only [mulhs_undef_l, mulhs_undef_r,
  mulhu_undef_l, mulhu_undef_r, maxf_undef_l, maxf_undef_r, minf_undef_l, minf_undef_r,
  mods_undef_l, mods_undef_r, modu_undef_l, modu_undef_r, modls_undef_l, modls_undef_r,
  modlu_undef_l, modlu_undef_r, maskzero_bool_undef])
macro "x86_undef_simp" "at" h:ident : tactic => `(tactic| simp only [mulhs_undef_l,
  mulhs_undef_r, mulhu_undef_l, mulhu_undef_r, maxf_undef_l, maxf_undef_r, minf_undef_l,
  minf_undef_r, mods_undef_l, mods_undef_r, modu_undef_l, modu_undef_r, modls_undef_l,
  modls_undef_r, modlu_undef_l, modlu_undef_r, maskzero_bool_undef] at $h:ident)

/-! ## `EVAL_LESSDEF` -/

/-- `Op.eval_condition_lessdef`, for any memories `m1`, `m2` such that every
    valid pointer of `m1` is valid in `m2`. -/
theorem evalCondition_lessdef_vp {cond : Condition} {vl1 vl2 : List Val} {b : Bool}
    {m1 m2 : Mem} (hl : Val.LessdefList vl1 vl2)
    (hvp : ∀ b ofs, Mem.validPointer m1 b ofs = true → Mem.validPointer m2 b ofs = true)
    (h : evalCondition cond vl1 m1 = some b) : evalCondition cond vl2 m2 = some b := by
  rcases hl with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, hl⟩⟩⟩
  all_goals cases cond
  all_goals simp only [evalCondition] at h ⊢
  all_goals first
    | exact cmpu_bool_lessdef hvp h1 h2 h
    | exact cmpu_bool_lessdef hvp h1 (.refl _) h
    | exact cmplu_bool_lessdef hvp h1 h2 h
    | exact cmplu_bool_lessdef hvp h1 (.refl _) h
    | (simp at h; done)
    | (cases h1 <;> (try cases h2) <;>
        first | exact h | (simp at h; done) | (simp [Val.maskzero_bool] at h; done))

/-- `Op.eval_condition_lessdef` -/
theorem evalCondition_lessdef {cond : Condition} {vl1 vl2 : List Val} {b : Bool} {m1 m2 : Mem}
    (hl : Val.LessdefList vl1 vl2) (hm : Mem.Extends m1 m2)
    (h : evalCondition cond vl1 m1 = some b) : evalCondition cond vl2 m2 = some b :=
  evalCondition_lessdef_vp hl (fun _ _ hv => Mem.validPointer_extends hm hv) h

/-- `Op.eval_addressing32_lessdef` -/
theorem evalAddressing32_lessdef {F V : Type} (ge : Genv F V) (sp : Val) (addr : Addressing)
    {vl1 vl2 : List Val} {v1 : Val} (hl : Val.LessdefList vl1 vl2)
    (h : evalAddressing32 ge sp addr vl1 = some v1) :
    ∃ v2, evalAddressing32 ge sp addr vl2 = some v2 ∧ Val.Lessdef v1 v2 := by
  cases addr <;> rcases hl with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, hl⟩⟩⟩
  all_goals first
    | (cases h; done)
    | (cases h; refine ⟨_, rfl, ?_⟩;
       (try cases h1) <;> (try cases h2) <;>
       first
        | with_reducible exact .refl _
        | exact .undef _
        | (val_undef_simp; exact .undef _))

/-- `Op.eval_addressing64_lessdef` -/
theorem evalAddressing64_lessdef {F V : Type} (ge : Genv F V) (sp : Val) (addr : Addressing)
    {vl1 vl2 : List Val} {v1 : Val} (hl : Val.LessdefList vl1 vl2)
    (h : evalAddressing64 ge sp addr vl1 = some v1) :
    ∃ v2, evalAddressing64 ge sp addr vl2 = some v2 ∧ Val.Lessdef v1 v2 := by
  cases addr <;> rcases hl with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, hl⟩⟩⟩
  all_goals first
    | (cases h; done)
    | (cases h; refine ⟨_, rfl, ?_⟩;
       (try cases h1) <;> (try cases h2) <;>
       first
        | with_reducible exact .refl _
        | exact .undef _
        | (val_undef_simp; exact .undef _))

/-- `Op.eval_addressing_lessdef` -/
theorem evalAddressing_lessdef {F V : Type} (ge : Genv F V) (sp : Val) (addr : Addressing)
    {vl1 vl2 : List Val} {v1 : Val} (hl : Val.LessdefList vl1 vl2)
    (h : evalAddressing ge sp addr vl1 = some v1) :
    ∃ v2, evalAddressing ge sp addr vl2 = some v2 ∧ Val.Lessdef v1 v2 :=
  evalAddressing64_lessdef ge sp addr hl h

/-- `Op.eval_operation_lessdef`, for any memories `m1`, `m2` such that every
    valid pointer of `m1` is valid in `m2`. -/
theorem evalOperation_lessdef_vp {F V : Type} (ge : Genv F V) (sp : Val) (op : Operation)
    {vl1 vl2 : List Val} {v1 : Val} {m1 m2 : Mem}
    (hl : Val.LessdefList vl1 vl2)
    (hm : ∀ b ofs, Mem.validPointer m1 b ofs = true → Mem.validPointer m2 b ofs = true)
    (h : evalOperation ge sp op vl1 m1 = some v1) :
    ∃ v2, evalOperation ge sp op vl2 m2 = some v2 ∧ Val.Lessdef v1 v2 := by
  cases op
  case Olea a => exact evalAddressing32_lessdef ge sp a hl h
  case Oleal a => exact evalAddressing64_lessdef ge sp a hl h
  case Ocmp c =>
    have e : evalOperation ge sp (.Ocmp c) vl1 m1 =
        some (Val.ofOptbool (evalCondition c vl1 m1)) := by
      rcases vl1 with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
    have e2 : evalOperation ge sp (.Ocmp c) vl2 m2 =
        some (Val.ofOptbool (evalCondition c vl2 m2)) := by
      rcases vl2 with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
    rw [e] at h; cases h
    exact ⟨_, e2, of_optbool_lessdef (fun b hb => evalCondition_lessdef_vp hl hm hb)⟩
  case Osel c ty =>
    rcases hl with _ | ⟨h1, _ | ⟨h2, hl⟩⟩
    · cases h
    · cases h
    · cases h
      refine ⟨_, rfl, select_lessdef ty ?_ h1 h2⟩
      cases e : evalCondition c _ m1 with
      | none => exact .inl rfl
      | some b => exact .inr (evalCondition_lessdef_vp hl hm e).symm
  all_goals
    rcases hl with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | ⟨h4, hl⟩⟩⟩⟩
  all_goals first
    | (cases h; done)
    | (cases h; refine ⟨_, rfl, ?_⟩;
       (try cases h1) <;> (try cases h2) <;> (try cases h3) <;>
       first
        | with_reducible exact .refl _
        | exact .undef _
        | (val_undef_simp; exact .undef _)
        | (x86_undef_simp; exact .undef _))
    | ((try cases h1) <;> (try cases h2) <;> first
        | exact ⟨_, h, .refl _⟩
        | (exfalso; unfold evalOperation at h; dsimp only at h;
           first | (val_undef_simp at h; cases h) | (x86_undef_simp at h; cases h)))

/-- `Op.eval_operation_lessdef` -/
theorem evalOperation_lessdef {F V : Type} (ge : Genv F V) (sp : Val) (op : Operation)
    {vl1 vl2 : List Val} {v1 : Val} {m1 m2 : Mem}
    (hl : Val.LessdefList vl1 vl2) (hm : Mem.Extends m1 m2)
    (h : evalOperation ge sp op vl1 m1 = some v1) :
    ∃ v2, evalOperation ge sp op vl2 m2 = some v2 ∧ Val.Lessdef v1 v2 :=
  evalOperation_lessdef_vp ge sp op hl (fun _ _ hv => Mem.validPointer_extends hm hv) h

/-! ## `EVAL_INJECT` -/

section
variable {f : Meminj}

theorem mulhs_inject {a a' b b' : Val} (ha : Inject f a a') (hb : Inject f b b') :
    Inject f (Val.mulhs a b) (Val.mulhs a' b') := by
  cases ha <;> cases hb <;> first | exact .int _ | exact .undef _
theorem mulhu_inject {a a' b b' : Val} (ha : Inject f a a') (hb : Inject f b b') :
    Inject f (Val.mulhu a b) (Val.mulhu a' b') := by
  cases ha <;> cases hb <;> first | exact .int _ | exact .undef _
theorem maxf_inject {a a' b b' : Val} (ha : Inject f a a') (hb : Inject f b b') :
    Inject f (maxf a b) (maxf a' b') := by
  cases ha <;> cases hb <;> first | exact .float _ | exact .undef _
theorem minf_inject {a a' b b' : Val} (ha : Inject f a a') (hb : Inject f b b') :
    Inject f (minf a b) (minf a' b') := by
  cases ha <;> cases hb <;> first | exact .float _ | exact .undef _

/-- Integer division-like operators: defined results are preserved. -/
theorem mods_inject {a a' b b' v : Val} (ha : Inject f a a') (hb : Inject f b b')
    (h : Val.mods a b = some v) : ∃ v', Val.mods a' b' = some v' ∧ Inject f v v' := by
  cases ha <;> cases hb <;> simp only [Val.mods] at h ⊢ <;>
    first | (cases h; done) | (refine ⟨v, h, ?_⟩; revert h; split <;> intro h <;> cases h; exact .int _)
theorem modu_inject {a a' b b' v : Val} (ha : Inject f a a') (hb : Inject f b b')
    (h : Val.modu a b = some v) : ∃ v', Val.modu a' b' = some v' ∧ Inject f v v' := by
  cases ha <;> cases hb <;> simp only [Val.modu] at h ⊢ <;>
    first | (cases h; done) | (refine ⟨v, h, ?_⟩; revert h; split <;> intro h <;> cases h; exact .int _)
theorem modls_inject {a a' b b' v : Val} (ha : Inject f a a') (hb : Inject f b b')
    (h : Val.modls a b = some v) : ∃ v', Val.modls a' b' = some v' ∧ Inject f v v' := by
  cases ha <;> cases hb <;> simp only [Val.modls] at h ⊢ <;>
    first | (cases h; done) | (refine ⟨v, h, ?_⟩; revert h; split <;> intro h <;> cases h; exact .long _)
theorem modlu_inject {a a' b b' v : Val} (ha : Inject f a a') (hb : Inject f b b')
    (h : Val.modlu a b = some v) : ∃ v', Val.modlu a' b' = some v' ∧ Inject f v v' := by
  cases ha <;> cases hb <;> simp only [Val.modlu] at h ⊢ <;>
    first | (cases h; done) | (refine ⟨v, h, ?_⟩; revert h; split <;> intro h <;> cases h; exact .long _)

theorem maskzero_bool_inject {a a' : Val} {n : Integers.Int} {b : Bool} (ha : Inject f a a')
    (h : Val.maskzero_bool a n = some b) : Val.maskzero_bool a' n = some b := by
  cases ha <;> first | exact h | cases h

/-- `Op.eval_condition_inject` -/
theorem evalCondition_inject {cond : Condition} {vl1 vl2 : List Val} {b : Bool} {m1 m2 : Mem}
    (hl : InjectList f vl1 vl2) (hm : Mem.Inject f m1 m2)
    (h : evalCondition cond vl1 m1 = some b) : evalCondition cond vl2 m2 = some b := by
  have H := Cop.copInjHyps_of_inject hm
  rcases hl with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, hl⟩⟩⟩
  all_goals cases cond
  all_goals simp only [evalCondition] at h ⊢
  all_goals first
    | (simp at h; done)
    | exact cmp_bool_inject _ h1 h2 h
    | exact cmp_bool_inject _ h1 (.int _) h
    | exact Op.cmpl_bool_inject _ h1 h2 h
    | exact Op.cmpl_bool_inject _ h1 (.long _) h
    | exact Op.cmpf_bool_inject _ h1 h2 h
    | exact Op.cmpfs_bool_inject _ h1 h2 h
    | exact Op.map_not_inject (fun _ => Op.cmpf_bool_inject _ h1 h2) h
    | exact Op.map_not_inject (fun _ => Op.cmpfs_bool_inject _ h1 h2) h
    | exact maskzero_bool_inject h1 h
    | exact Op.map_not_inject (fun _ => maskzero_bool_inject h1) h
    | exact Val.cmpu_bool_inject H h1 h2 h
    | exact Val.cmpu_bool_inject H h1 (.int _) h
    | exact Cop.cmplu_bool_inject H h1 h2 h
    | exact Cop.cmplu_bool_inject H h1 (.long _) h

/-- `Op.eval_addressing32_inject`.  With 64-bit pointers the 32-bit addressing
modes mention neither the stack pointer nor symbols, so no hypothesis on them
is needed. -/
theorem evalAddressing32_inject {F V : Type} (ge : Genv F V)
    {sp1 sp2 : Val} {addr : Addressing}
    {vl1 vl2 : List Val} {v1 : Val} (hl : InjectList f vl1 vl2)
    (h : evalAddressing32 ge sp1 addr vl1 = some v1) :
    ∃ v2, evalAddressing32 ge sp2 addr vl2 = some v2 ∧ Inject f v1 v2 := by
  cases addr <;> rcases hl with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, hl⟩⟩⟩
  all_goals first
    | (cases h; done)
    | (cases h; exact ⟨_, rfl, by inj_comp⟩)

/-- `Op.eval_addressing64_inject` -/
theorem evalAddressing64_inject {F V : Type} (ge : Genv F V)
    (hsym : ∀ id ofs, Inject f (Genv.symbolAddress ge id ofs) (Genv.symbolAddress ge id ofs))
    {sp1 sp2 : Val} (hsp : Inject f sp1 sp2) {addr : Addressing}
    {vl1 vl2 : List Val} {v1 : Val} (hl : InjectList f vl1 vl2)
    (h : evalAddressing64 ge sp1 addr vl1 = some v1) :
    ∃ v2, evalAddressing64 ge sp2 addr vl2 = some v2 ∧ Inject f v1 v2 := by
  cases addr <;> rcases hl with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, hl⟩⟩⟩
  all_goals first
    | (cases h; done)
    | (cases h; exact ⟨_, rfl, by inj_comp⟩)
    | (cases h; exact ⟨_, rfl, hsym _ _⟩)

/-- `Op.eval_addressing_inject` -/
theorem evalAddressing_inject {F V : Type} (ge : Genv F V)
    (hsym : ∀ id ofs, Inject f (Genv.symbolAddress ge id ofs) (Genv.symbolAddress ge id ofs))
    {sp1 sp2 : Val} (hsp : Inject f sp1 sp2) {addr : Addressing}
    {vl1 vl2 : List Val} {v1 : Val} (hl : InjectList f vl1 vl2)
    (h : evalAddressing ge sp1 addr vl1 = some v1) :
    ∃ v2, evalAddressing ge sp2 addr vl2 = some v2 ∧ Inject f v1 v2 :=
  evalAddressing64_inject ge hsym hsp hl h

set_option maxHeartbeats 4000000 in
/-- `Op.eval_operation_inject` (for a memory injection; the stack pointers
are arbitrary injected values). -/
theorem evalOperation_inject {F V : Type} (ge : Genv F V)
    (hsym : ∀ id ofs, Inject f (Genv.symbolAddress ge id ofs) (Genv.symbolAddress ge id ofs))
    {sp1 sp2 : Val} (hsp : Inject f sp1 sp2) {op : Operation}
    {vl1 vl2 : List Val} {v1 : Val} {m1 m2 : Mem}
    (hl : InjectList f vl1 vl2) (hm : Mem.Inject f m1 m2)
    (h : evalOperation ge sp1 op vl1 m1 = some v1) :
    ∃ v2, evalOperation ge sp2 op vl2 m2 = some v2 ∧ Inject f v1 v2 := by
  cases op
  case Olea a => exact evalAddressing32_inject ge (sp2 := sp2) hl h
  case Oleal a => exact evalAddressing64_inject ge hsym hsp hl h
  case Ocmp c =>
    have e : evalOperation ge sp1 (.Ocmp c) vl1 m1 =
        some (Val.ofOptbool (evalCondition c vl1 m1)) := by
      rcases vl1 with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
    have e2 : evalOperation ge sp2 (.Ocmp c) vl2 m2 =
        some (Val.ofOptbool (evalCondition c vl2 m2)) := by
      rcases vl2 with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
    rw [e] at h; cases h
    exact ⟨_, e2, Op.ofOptbool_inject (fun b hb => evalCondition_inject hl hm hb)⟩
  case Osel c ty =>
    rcases hl with _ | ⟨h1, _ | ⟨h2, hl⟩⟩
    · cases h
    · cases h
    · cases h
      refine ⟨_, rfl, Val.select_inject ty ?_ h1 h2⟩
      cases e : evalCondition c _ m1 with
      | none => exact .inl rfl
      | some b => exact .inr (evalCondition_inject hl hm e).symm
  all_goals
    rcases hl with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | ⟨h4, hl⟩⟩⟩⟩
  all_goals first
    | (cases h; done)
    | (cases h; exact ⟨_, rfl, by inj_comp⟩)
    | (cases h; exact ⟨_, rfl, mulhs_inject h1 h2⟩)
    | (cases h; exact ⟨_, rfl, mulhu_inject h1 h2⟩)
    | (cases h; exact ⟨_, rfl, maxf_inject h1 h2⟩)
    | (cases h; exact ⟨_, rfl, minf_inject h1 h2⟩)
    | (cases h; exact ⟨_, rfl, hsym _ _⟩)
    | exact mods_inject h1 h2 h
    | exact modu_inject h1 h2 h
    | exact modls_inject h1 h2 h
    | exact modlu_inject h1 h2 h
    | inj_optop

end

end Op
end X86
end CC
