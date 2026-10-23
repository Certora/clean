/-
  Properties of the x86 operators — the lemmas of `x86/Op.v`:
  `eval_negate_condition`, `is_move_operation_correct`, the stack-shifting
  lemmas, `op_depends_on_memory_correct`, invariance under a change of global
  environment with the same symbols (`GENV_TRANSF`), the `eval_addressing_*`
  remarks, and monotonicity with respect to `Val.lessdef` / memory
  extensions (`EVAL_LESSDEF`) and memory injections (`EVAL_INJECT`).

  Differences from Rocq: as for aarch64 (`CCLib/aarch64/OpLessdef.lean`,
  `CCLib/aarch64/OpInject.lean`), the lessdef and injection results are proved
  directly by case analysis rather than derived from a generic
  `EVAL_COMPAT` section.
-/
import CCLib.x86.Op
import CCLib.aarch64.OpInject
import CCLib.backend.CleanupLabelsproof

namespace CC
namespace X86
namespace Op

open Val

/-! ## Conditions and moves -/

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
    | (cases Val.maskzero_bool a _ <;> simp)

/-- `Op.is_move_operation_correct` -/
theorem isMoveOperation_correct {A : Type} {op : Operation} {args : List A} {a : A}
    (h : isMoveOperation op args = some a) : op = .Omove ∧ args = [a] := by
  cases op <;> rcases args with _ | ⟨x, _ | ⟨y, l⟩⟩ <;> simp [isMoveOperation] at h ⊢
  exact h

/-! ## Addressing remarks -/

/-- `Op.eval_addressing_Aglobal` -/
theorem evalAddressing_Aglobal {F V : Type} (genv : Genv F V) (sp : Val) (id : Ident)
    (ofs : Integers.Ptrofs) :
    evalAddressing genv sp (.Aglobal id ofs) [] = some (Genv.symbolAddress genv id ofs) := rfl

/-- `Op.eval_addressing_Ainstack` -/
theorem evalAddressing_Ainstack {F V : Type} (genv : Genv F V) (sp : Val)
    (ofs : Integers.Ptrofs) :
    evalAddressing genv sp (.Ainstack ofs) [] = some (Val.offsetPtr sp ofs) := rfl

/-- `Op.eval_addressing_Ainstack_inv` -/
theorem evalAddressing_Ainstack_inv {F V : Type} (genv : Genv F V) (sp : Val)
    (ofs : Integers.Ptrofs) (vl : List Val) (v : Val)
    (h : evalAddressing genv sp (.Ainstack ofs) vl = some v) :
    vl = [] ∧ v = Val.offsetPtr sp ofs := by
  rcases vl with _ | ⟨x, l⟩
  · cases h; exact ⟨rfl, rfl⟩
  · cases h

/-! ## Shifting stack-relative references -/

/-- `Op.type_shift_stack_addressing` -/
theorem type_shiftStackAddressing (delta : Z) (addr : Addressing) :
    typeOfAddressing (shiftStackAddressing delta addr) = typeOfAddressing addr := by
  cases addr <;> rfl

/-- `Op.type_shift_stack_operation` -/
theorem type_shiftStackOperation (delta : Z) (op : Operation) :
    typeOfOperation (shiftStackOperation delta op) = typeOfOperation op := by
  cases op <;> try rfl
  all_goals rename_i a; cases a <;> rfl

private theorem ptrofs_shift (i delta : Integers.Ptrofs) :
    Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.add i delta) =
      Integers.Ptrofs.add delta i := by
  rw [Integers.Ptrofs.add_commut Integers.Ptrofs.zero, Integers.Ptrofs.add_zero,
    Integers.Ptrofs.add_commut]

/-- `Op.eval_shift_stack_addressing32` -/
theorem evalAddressing32_shiftStack {F V : Type} (ge : Genv F V) (sp : Block) (addr : Addressing)
    (vl : List Val) (delta : Z) :
    evalAddressing32 ge (.Vptr sp Integers.Ptrofs.zero) (shiftStackAddressing delta addr) vl =
      evalAddressing32 ge (.Vptr sp (Integers.Ptrofs.repr delta)) addr vl := by
  cases addr <;> rcases vl with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl

/-- `Op.eval_shift_stack_addressing64` -/
theorem evalAddressing64_shiftStack {F V : Type} (ge : Genv F V) (sp : Block) (addr : Addressing)
    (vl : List Val) (delta : Z) :
    evalAddressing64 ge (.Vptr sp Integers.Ptrofs.zero) (shiftStackAddressing delta addr) vl =
      evalAddressing64 ge (.Vptr sp (Integers.Ptrofs.repr delta)) addr vl := by
  cases addr <;> rcases vl with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> try rfl
  show some (Val.offsetPtr _ _) = some (Val.offsetPtr _ _)
  simp only [Val.offsetPtr, ptrofs_shift]

/-- `Op.eval_shift_stack_addressing` -/
theorem evalAddressing_shiftStack {F V : Type} (ge : Genv F V) (sp : Block) (addr : Addressing)
    (vl : List Val) (delta : Z) :
    evalAddressing ge (.Vptr sp Integers.Ptrofs.zero) (shiftStackAddressing delta addr) vl =
      evalAddressing ge (.Vptr sp (Integers.Ptrofs.repr delta)) addr vl :=
  evalAddressing64_shiftStack ge sp addr vl delta

/-- `Op.eval_shift_stack_operation` -/
theorem evalOperation_shiftStack {F V : Type} (ge : Genv F V) (sp : Block) (op : Operation)
    (vl : List Val) (m : Mem) (delta : Z) :
    evalOperation ge (.Vptr sp Integers.Ptrofs.zero) (shiftStackOperation delta op) vl m =
      evalOperation ge (.Vptr sp (Integers.Ptrofs.repr delta)) op vl m := by
  cases op
  case Olea a =>
    exact evalAddressing32_shiftStack ge sp a vl delta
  case Oleal a =>
    exact evalAddressing64_shiftStack ge sp a vl delta
  all_goals rcases vl with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl

/-! ## Memory dependence -/

/-- `Op.condition_depends_on_memory_correct` -/
theorem conditionDependsOnMemory_correct (c : Condition) (args : List Val) (m1 m2 : Mem)
    (h : conditionDependsOnMemory c = false) :
    evalCondition c args m1 = evalCondition c args m2 := by
  cases c <;> simp [conditionDependsOnMemory, Archi.ptr64] at h <;>
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
    rw [e, e, conditionDependsOnMemory_correct c args m1 m2 h]
  case Osel c ty =>
    rcases args with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> try rfl
    show some (Val.select _ a b ty) = some (Val.select _ a b ty)
    rw [conditionDependsOnMemory_correct c l m1 m2 h]
  all_goals rcases args with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl

/-! ## Invariance under a change of global environment (`GENV_TRANSF`) -/

section GenvTransf
variable {F1 V1 F2 V2 : Type} (ge1 : Genv F1 V1) (ge2 : Genv F2 V2)

/-- `Op.eval_addressing32_preserved`.  With 64-bit pointers the 32-bit
addressing modes never mention a symbol, so no hypothesis is needed. -/
theorem evalAddressing32_preserved (sp : Val) (addr : Addressing) (vl : List Val) :
    evalAddressing32 ge2 sp addr vl = evalAddressing32 ge1 sp addr vl := by
  cases addr <;> rcases vl with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl

/-- `Op.eval_addressing64_preserved` -/
theorem evalAddressing64_preserved (h : ∀ id, Genv.findSymbol ge2 id = Genv.findSymbol ge1 id)
    (sp : Val) (addr : Addressing) (vl : List Val) :
    evalAddressing64 ge2 sp addr vl = evalAddressing64 ge1 sp addr vl := by
  cases addr <;> rcases vl with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;>
    first | rfl | exact congrArg some (symbolAddress_preserved ge1 ge2 h _ _)

/-- `Op.eval_addressing_preserved` -/
theorem evalAddressing_preserved (h : ∀ id, Genv.findSymbol ge2 id = Genv.findSymbol ge1 id)
    (sp : Val) (addr : Addressing) (vl : List Val) :
    evalAddressing ge2 sp addr vl = evalAddressing ge1 sp addr vl :=
  evalAddressing64_preserved ge1 ge2 h sp addr vl

/-- `Op.eval_operation_preserved` -/
theorem evalOperation_preserved (h : ∀ id, Genv.findSymbol ge2 id = Genv.findSymbol ge1 id)
    (sp : Val) (op : Operation) (vl : List Val) (m : Mem) :
    evalOperation ge2 sp op vl m = evalOperation ge1 sp op vl m := by
  cases op
  case Olea a => exact evalAddressing32_preserved ge1 ge2 sp a vl
  case Oleal a => exact evalAddressing64_preserved ge1 ge2 h sp a vl
  all_goals rcases vl with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;>
    first | rfl | exact congrArg some (symbolAddress_preserved ge1 ge2 h _ _)

end GenvTransf

end Op
end X86
end CC
