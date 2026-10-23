/-
  Properties of the RISC-V operators — the lemmas of `riscV/Op.v`:
  `type_of_operation_sound`, `is_move_operation_correct`,
  `eval_negate_condition`, the stack-shifting lemmas,
  `cond_depends_on_memory_correct` / `op_depends_on_memory_correct`, and
  invariance under a change of global environment (`GENV_TRANSF`).

  `eval_offset_addressing` is not ported: in Rocq it carries the hypothesis
  `Archi.ptr64 = false`, which is false in this (RV64) configuration.
-/
import CCLib.riscV.Op
import CCLib.aarch64.OpInject
import CCLib.backend.CleanupLabelsproof
import CCLib.backend.CminortypingSubject

namespace CC
namespace RiscV
namespace Op

/-! ## Weak type soundness (`SOUNDNESS`) -/

private theorem hasType_select (c : Option Bool) (v1 v2 : Val) (ty : ATyp) :
    Val.HasType (Val.select c v1 v2 ty) ty := by
  cases c with
  | none => exact Cminortyping.hasType_undef ty
  | some b => exact Val.normalize_type _ _

private theorem hasType_symbolAddress {F V : Type} (ge : Genv F V) (id : Ident)
    (ofs : Integers.Ptrofs) : Val.HasType (Genv.symbolAddress ge id ofs) Tptr := by
  unfold Genv.symbolAddress
  split
  · exact Val.Vptr_has_type _ _
  · exact Cminortyping.hasType_undef _

private theorem hasType_offsetPtr (sp : Val) (ofs : Integers.Ptrofs) :
    Val.HasType (Val.offsetPtr sp ofs) Tptr := by
  unfold Val.offsetPtr
  split
  · exact Val.Vptr_has_type _ _
  · exact Cminortyping.hasType_undef _

private theorem ty_divs {a b v : Val} (h : Val.divs a b = some v) : Val.HasType v .Tint := by
  cases a <;> (try cases b) <;> simp only [Val.divs, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_divu {a b v : Val} (h : Val.divu a b = some v) : Val.HasType v .Tint := by
  cases a <;> (try cases b) <;> simp only [Val.divu, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_mods {a b v : Val} (h : Val.mods a b = some v) : Val.HasType v .Tint := by
  cases a <;> (try cases b) <;> simp only [Val.mods, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_modu {a b v : Val} (h : Val.modu a b = some v) : Val.HasType v .Tint := by
  cases a <;> (try cases b) <;> simp only [Val.modu, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_divls {a b v : Val} (h : Val.divls a b = some v) : Val.HasType v .Tlong := by
  cases a <;> (try cases b) <;> simp only [Val.divls, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_divlu {a b v : Val} (h : Val.divlu a b = some v) : Val.HasType v .Tlong := by
  cases a <;> (try cases b) <;> simp only [Val.divlu, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_modls {a b v : Val} (h : Val.modls a b = some v) : Val.HasType v .Tlong := by
  cases a <;> (try cases b) <;> simp only [Val.modls, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_modlu {a b v : Val} (h : Val.modlu a b = some v) : Val.HasType v .Tlong := by
  cases a <;> (try cases b) <;> simp only [Val.modlu, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_shrx {a b v : Val} (h : Val.shrx a b = some v) : Val.HasType v .Tint := by
  cases a <;> (try cases b) <;> simp only [Val.shrx, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_shrxl {a b v : Val} (h : Val.shrxl a b = some v) : Val.HasType v .Tlong := by
  cases a <;> (try cases b) <;> simp only [Val.shrxl, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_intoffloat {a v : Val} (h : Val.intoffloat a = some v) : Val.HasType v .Tint := by
  cases a <;> simp only [Val.intoffloat, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_intofsingle {a v : Val} (h : Val.intofsingle a = some v) : Val.HasType v .Tint := by
  cases a <;> simp only [Val.intofsingle, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_floatofint {a v : Val} (h : Val.floatofint a = some v) : Val.HasType v .Tfloat := by
  cases a <;> simp only [Val.floatofint, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_floatoflong {a v : Val} (h : Val.floatoflong a = some v) : Val.HasType v .Tfloat := by
  cases a <;> simp only [Val.floatoflong, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_singleofint {a v : Val} (h : Val.singleofint a = some v) : Val.HasType v .Tsingle := by
  cases a <;> simp only [Val.singleofint, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_singleoflong {a v : Val} (h : Val.singleoflong a = some v) : Val.HasType v .Tsingle := by
  cases a <;> simp only [Val.singleoflong, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_longoffloat {a v : Val} (h : Val.longoffloat a = some v) : Val.HasType v .Tlong := by
  cases a <;> simp only [Val.longoffloat, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_longofsingle {a v : Val} (h : Val.longofsingle a = some v) : Val.HasType v .Tlong := by
  cases a <;> simp only [Val.longofsingle, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl

private theorem ty_intuoffloat {a v : Val} (h : Val.intuoffloat a = some v) : Val.HasType v .Tint := by
  cases a <;> simp only [Val.intuoffloat, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_intuofsingle {a v : Val} (h : Val.intuofsingle a = some v) : Val.HasType v .Tint := by
  cases a <;> simp only [Val.intuofsingle, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_floatofintu {a v : Val} (h : Val.floatofintu a = some v) : Val.HasType v .Tfloat := by
  cases a <;> simp only [Val.floatofintu, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_floatoflongu {a v : Val} (h : Val.floatoflongu a = some v) : Val.HasType v .Tfloat := by
  cases a <;> simp only [Val.floatoflongu, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_singleofintu {a v : Val} (h : Val.singleofintu a = some v) : Val.HasType v .Tsingle := by
  cases a <;> simp only [Val.singleofintu, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_singleoflongu {a v : Val} (h : Val.singleoflongu a = some v) : Val.HasType v .Tsingle := by
  cases a <;> simp only [Val.singleoflongu, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_longuoffloat {a v : Val} (h : Val.longuoffloat a = some v) : Val.HasType v .Tlong := by
  cases a <;> simp only [Val.longuoffloat, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_longuofsingle {a v : Val} (h : Val.longuofsingle a = some v) : Val.HasType v .Tlong := by
  cases a <;> simp only [Val.longuofsingle, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl

set_option maxHeartbeats 1000000 in
/-- `Op.type_of_operation_sound` -/
theorem type_of_operation_sound {F V : Type} (ge : Genv F V) (sp : Val) (op : Operation)
    (vl : List Val) (m : Mem) (v : Val) (hop : op ≠ .Omove)
    (h : evalOperation ge sp op vl m = some v) :
    Val.HasType v (typeOfOperation op).2 := by
  cases op
  case Omove => exact absurd rfl hop
  case Ocmp c =>
    have e : evalOperation ge sp (.Ocmp c) vl m =
        some (Val.ofOptbool (evalCondition c vl m)) := by
      rcases vl with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
    rw [e] at h; cases h; exact Cminortyping.hasType_ofOptbool _
  case Osel c ty =>
    rcases vl with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> try cases h
    exact hasType_select _ _ _ _
  case Oaddrsymbol id ofs =>
    rcases vl with _ | ⟨_, _⟩ <;> cases h; exact hasType_symbolAddress ge _ _
  case Oaddrstack ofs =>
    rcases vl with _ | ⟨_, _⟩ <;> cases h; exact hasType_offsetPtr sp _
  all_goals
    rcases vl with _ | ⟨a, _ | ⟨b, _ | ⟨c, _⟩⟩⟩ <;> (try cases h) <;>
    first
      | exact ty_divs h
      | exact ty_divu h
      | exact ty_mods h
      | exact ty_modu h
      | exact ty_divls h
      | exact ty_divlu h
      | exact ty_modls h
      | exact ty_modlu h
      | exact ty_shrx h
      | exact ty_shrxl h
      | exact ty_intoffloat h
      | exact ty_intofsingle h
      | exact ty_floatofint h
      | exact ty_floatoflong h
      | exact ty_singleofint h
      | exact ty_singleoflong h
      | exact ty_longoffloat h
      | exact ty_longofsingle h
      | exact ty_intuoffloat h
      | exact ty_intuofsingle h
      | exact ty_floatofintu h
      | exact ty_floatoflongu h
      | exact ty_singleofintu h
      | exact ty_singleoflongu h
      | exact ty_longuoffloat h
      | exact ty_longuofsingle h
      | ((try cases a) <;> (try cases b) <;>
         simp [typeOfOperation, Val.HasType, Val.hasType, Val.signExt, Val.neg, Val.add,
          Val.sub, Val.mul, Val.mulhs, Val.mulhu, Val.and, Val.or, Val.xor, Val.shl,
          Val.shr, Val.shru, Val.longofwords, Val.loword, Val.hiword, Val.longofint,
          Val.longofintu, Val.negl, Val.addl, Val.subl, Val.mull, Val.mullhs, Val.mullhu,
          Val.andl, Val.orl, Val.xorl, Val.shll, Val.shrl, Val.shrlu,
          Val.negf, Val.absf, Val.addf, Val.subf, Val.mulf, Val.divf, Val.negfs,
          Val.absfs, Val.addfs, Val.subfs, Val.mulfs, Val.divfs, Val.singleoffloat,
          Val.floatofsingle, Archi.ptr64] <;>
         first | rfl | (apply Cminortyping.hasType_ite <;> rfl))

/-! ## Conditions and moves -/

/-- `Op.is_move_operation_correct` -/
theorem isMoveOperation_correct {A : Type} {op : Operation} {args : List A} {a : A}
    (h : isMoveOperation op args = some a) : op = .Omove ∧ args = [a] := by
  cases op <;> rcases args with _ | ⟨x, _ | ⟨y, l⟩⟩ <;> simp [isMoveOperation] at h ⊢
  exact h

/-- `Op.eval_negate_condition` -/
theorem eval_negateCondition (cond : Condition) (vl : List Val) (m : Mem) :
    evalCondition (negateCondition cond) vl m = (evalCondition cond vl m).map (!·) := by
  cases cond <;> rcases vl with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
    simp only [negateCondition, evalCondition, Option.map_none, Option.map_map] <;>
    first
    | rfl
    | exact Val.negate_cmp_bool _ _ _
    | exact Val.negate_cmpu_bool _ _ _ _
    | exact Val.negate_cmpl_bool _ _ _
    | exact Val.negate_cmplu_bool _ _ _ _
    | (cases Val.cmpf_bool _ a b <;> simp)
    | (cases Val.cmpfs_bool _ a b <;> simp)

/-! ## Shifting stack-relative references -/

/-- `Op.type_shift_stack_addressing` -/
theorem type_shiftStackAddressing (delta : Z) (addr : Addressing) :
    typeOfAddressing (shiftStackAddressing delta addr) = typeOfAddressing addr := by
  cases addr <;> rfl

/-- `Op.type_shift_stack_operation` -/
theorem type_shiftStackOperation (delta : Z) (op : Operation) :
    typeOfOperation (shiftStackOperation delta op) = typeOfOperation op := by
  cases op <;> rfl

private theorem ptrofs_shift (i delta : Integers.Ptrofs) :
    Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.add i delta) =
      Integers.Ptrofs.add delta i := by
  rw [Integers.Ptrofs.add_commut Integers.Ptrofs.zero, Integers.Ptrofs.add_zero,
    Integers.Ptrofs.add_commut]

/-- `Op.eval_shift_stack_addressing` -/
theorem evalAddressing_shiftStack {F V : Type} (ge : Genv F V) (sp : Block) (addr : Addressing)
    (vl : List Val) (delta : Z) :
    evalAddressing ge (.Vptr sp Integers.Ptrofs.zero) (shiftStackAddressing delta addr) vl =
      evalAddressing ge (.Vptr sp (Integers.Ptrofs.repr delta)) addr vl := by
  cases addr <;> rcases vl with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> try rfl
  show some (Val.offsetPtr _ _) = some (Val.offsetPtr _ _)
  simp only [Val.offsetPtr, ptrofs_shift]

/-- `Op.eval_shift_stack_operation` -/
theorem evalOperation_shiftStack {F V : Type} (ge : Genv F V) (sp : Block) (op : Operation)
    (vl : List Val) (m : Mem) (delta : Z) :
    evalOperation ge (.Vptr sp Integers.Ptrofs.zero) (shiftStackOperation delta op) vl m =
      evalOperation ge (.Vptr sp (Integers.Ptrofs.repr delta)) op vl m := by
  cases op
  case Oaddrstack ofs =>
    rcases vl with _ | ⟨_, _⟩ <;> try rfl
    show some (Val.offsetPtr _ _) = some (Val.offsetPtr _ _)
    simp only [Val.offsetPtr, ptrofs_shift]
  all_goals rcases vl with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl

/-! ## Memory dependence -/

/-- `Op.cond_depends_on_memory_correct` -/
theorem condDependsOnMemory_correct (c : Condition) (args : List Val) (m1 m2 : Mem)
    (h : condDependsOnMemory c = false) :
    evalCondition c args m1 = evalCondition c args m2 := by
  cases c <;> simp [condDependsOnMemory, Archi.ptr64] at h <;>
    rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> try rfl
  all_goals simp only [evalCondition, Val.cmpu_bool, Archi.ptr64]

/-- `Op.op_depends_on_memory_correct` -/
theorem opDependsOnMemory_correct {F V : Type} (ge : Genv F V) (sp : Val) (op : Operation)
    (args : List Val) (m1 m2 : Mem) (h : opDependsOnMemory op = false) :
    evalOperation ge sp op args m1 = evalOperation ge sp op args m2 := by
  cases op
  case Ocmp c =>
    have e : ∀ m, evalOperation ge sp (.Ocmp c) args m =
        some (Val.ofOptbool (evalCondition c args m)) := by
      intro m; rcases args with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
    rw [e, e, condDependsOnMemory_correct c args m1 m2 h]
  case Osel c ty =>
    rcases args with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> try rfl
    show some (Val.select _ a b ty) = some (Val.select _ a b ty)
    rw [condDependsOnMemory_correct c l m1 m2 h]
  all_goals rcases args with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl

/-! ## Invariance under a change of global environment (`GENV_TRANSF`) -/

section GenvTransf
variable {F1 V1 F2 V2 : Type} (ge1 : Genv F1 V1) (ge2 : Genv F2 V2)

/-- `Op.eval_addressing_preserved` -/
theorem evalAddressing_preserved (h : ∀ id, Genv.findSymbol ge2 id = Genv.findSymbol ge1 id)
    (sp : Val) (addr : Addressing) (vl : List Val) :
    evalAddressing ge2 sp addr vl = evalAddressing ge1 sp addr vl := by
  cases addr <;> rcases vl with _ | ⟨_, _ | ⟨_, _⟩⟩ <;>
    first | rfl | exact congrArg some (symbolAddress_preserved ge1 ge2 h _ _)

/-- `Op.eval_operation_preserved` -/
theorem evalOperation_preserved (h : ∀ id, Genv.findSymbol ge2 id = Genv.findSymbol ge1 id)
    (sp : Val) (op : Operation) (vl : List Val) (m : Mem) :
    evalOperation ge2 sp op vl m = evalOperation ge1 sp op vl m := by
  cases op
  all_goals rcases vl with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;>
    first | rfl | exact congrArg some (symbolAddress_preserved ge1 ge2 h _ _)

end GenvTransf

end Op
end RiscV
end CC
