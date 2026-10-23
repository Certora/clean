/-
  [x86-64 instance of `CCLib/backend/Bounds.lean`: the same development, in
  namespace `CC.X86`, over the x86-64 operators, registers and conventions.]

  Resource bounds for Linear code — port of `backend/Bounds.v`.

  Ported: the `bounds` record (with its invariants), `mreg_within_bounds`,
  `slot_within_bounds`, `instr_within_bounds`, `function_within_bounds`,
  `record_reg(s)`, `record_regs_of_instr`, `record_regs_of_function`,
  `slots_of_locs`, `slots_of_instr`, `max_over_list`, `max_over_instrs`,
  `max_over_slots_of_instr`, `max_over_slots_of_funct`, `local_slot`,
  `outgoing_slot`, `outgoing_space`, `function_bounds`, the correctness
  lemmas ending in `function_is_within_bounds`, `size_callee_save_area(_rec)`
  with `size_callee_save_area_incr`, and `frame_env`.

  Differences from Rocq:
  * `RegSet` (an AVL set of machine registers) is a duplicate-free list;
    `RegSet.elements` sorts it by `IndexedMreg.index` (insertion sort), so
    it lists the registers in the same order as Rocq's.
  * `Archi.win64` (a Rocq `Parameter`, used by `size_arguments` and
    `is_callee_save`) is an explicit argument `win64`; the `Bounds` record is
    indexed by it, since `used_callee_save_prop` refers to `is_callee_save`.
-/
import CCLib.x86.Linear
import CCLib.cfrontend.CtypesTheory

namespace CC
namespace X86

/- `Archi.win64` (a Rocq `Parameter`): whether the Windows x86-64 ABI is used. -/
variable (win64 : Bool)
namespace Bounds

open Linear Conventions1 Conventions

/-- `Bounds.bounds` -/
structure Bounds (win64 : Bool) where
  used_callee_save : List Mreg
  bound_local : Z
  bound_outgoing : Z
  bound_stack_data : Z
  bound_local_pos : bound_local ≥ 0
  bound_outgoing_pos : bound_outgoing ≥ 0
  bound_stack_data_pos : bound_stack_data ≥ 0
  used_callee_save_norepet : used_callee_save.Nodup
  used_callee_save_prop : ∀ r, r ∈ used_callee_save → isCalleeSave win64 r = true

section WITHIN_BOUNDS
variable {win64 : Bool} (b : Bounds win64)

/-- `Bounds.mreg_within_bounds` -/
def MregWithinBounds (r : Mreg) : Prop := isCalleeSave win64 r = true → r ∈ b.used_callee_save

/-- `Bounds.slot_within_bounds` -/
def SlotWithinBounds (sl : Slot) (ofs : Z) (ty : ATyp) : Prop :=
  match sl with
  | .Local => ofs + typesize ty ≤ b.bound_local
  | .Outgoing => ofs + typesize ty ≤ b.bound_outgoing
  | .Incoming => True

end WITHIN_BOUNDS

/-- `Bounds.instr_within_bounds` -/
def InstrWithinBounds (win64 : Bool) (b : Bounds win64) (i : Instruction) : Prop :=
  match i with
  | .Lgetstack sl ofs ty r => SlotWithinBounds b sl ofs ty ∧ MregWithinBounds b r
  | .Lsetstack _ sl ofs ty => SlotWithinBounds b sl ofs ty
  | .Lop _ _ res => MregWithinBounds b res
  | .Lload _ _ _ dst => MregWithinBounds b dst
  | .Lcall sig _ => sizeArguments win64 sig ≤ b.bound_outgoing
  | .Lbuiltin ef args res =>
      (∀ r, r ∈ BuiltinRes.params res ∨ r ∈ destroyedByBuiltin ef → MregWithinBounds b r) ∧
      (∀ sl ofs ty, Loc.S sl ofs ty ∈ BuiltinArg.paramsList args → SlotWithinBounds b sl ofs ty)
  | _ => True

/-- `Bounds.function_within_bounds` -/
def FunctionWithinBounds (win64 : Bool) (f : Linear.Function) (b : Bounds win64) : Prop :=
  ∀ instr, instr ∈ f.fn_code → InstrWithinBounds win64 b instr

/-! ## Inference of resource bounds -/

/-- `Bounds.RegSet.t`, as a duplicate-free list. -/
abbrev RegSet := List Mreg

/-- Insertion in a list sorted by increasing `IndexedMreg.index`. -/
def insertByIndex (r : Mreg) : List Mreg → List Mreg
  | [] => [r]
  | x :: l => if (Mreg.index r).toNat ≤ (Mreg.index x).toNat then r :: x :: l
              else x :: insertByIndex r l

theorem perm_insertByIndex (r : Mreg) : ∀ (l : List Mreg), (insertByIndex r l).Perm (r :: l)
  | [] => List.Perm.refl _
  | x :: l => by
    unfold insertByIndex
    split
    · exact List.Perm.refl _
    · exact ((perm_insertByIndex r l).cons x).trans (List.Perm.swap r x l)

/-- `RegSet.elements`: the elements in increasing order of `IndexedMreg.index`
    (an insertion sort, so that it reduces in the kernel). -/
def RegSet.elements : RegSet → List Mreg
  | [] => []
  | r :: l => insertByIndex r (RegSet.elements l)

theorem RegSet.perm_elements : ∀ (u : RegSet), (RegSet.elements u).Perm u
  | [] => List.Perm.refl _
  | r :: l => (perm_insertByIndex r _).trans ((RegSet.perm_elements l).cons r)

section BOUNDS
variable (win64 : Bool) (f : Linear.Function)

/-- `Bounds.record_reg` -/
def recordReg (u : RegSet) (r : Mreg) : RegSet :=
  if isCalleeSave win64 r then (if r ∈ u then u else r :: u) else u

/-- `Bounds.record_regs` -/
def recordRegs (u : RegSet) (rl : List Mreg) : RegSet := rl.foldl (recordReg win64) u

/-- `Bounds.record_regs_of_instr` -/
def recordRegsOfInstr (u : RegSet) (i : Instruction) : RegSet :=
  match i with
  | .Lgetstack _ _ _ r => recordReg win64 u r
  | .Lsetstack r _ _ _ => recordReg win64 u r
  | .Lop _ _ res => recordReg win64 u res
  | .Lload _ _ _ dst => recordReg win64 u dst
  | .Lbuiltin ef _ res => recordRegs win64 (recordRegs win64 u (BuiltinRes.params res)) (destroyedByBuiltin ef)
  | _ => u

/-- `Bounds.record_regs_of_function` -/
def recordRegsOfFunction : RegSet := f.fn_code.foldl (recordRegsOfInstr win64) []

/-- `Bounds.slots_of_locs` -/
def slotsOfLocs : List Loc → List (Slot × Z × ATyp)
  | [] => []
  | .S sl ofs ty :: l' => (sl, ofs, ty) :: slotsOfLocs l'
  | .R _ :: l' => slotsOfLocs l'

/-- `Bounds.slots_of_instr` -/
def slotsOfInstr (i : Instruction) : List (Slot × Z × ATyp) :=
  match i with
  | .Lgetstack sl ofs ty _ => [(sl, ofs, ty)]
  | .Lsetstack _ sl ofs ty => [(sl, ofs, ty)]
  | .Lbuiltin _ args _ => slotsOfLocs (BuiltinArg.paramsList args)
  | _ => []

/-- `Bounds.max_over_list` -/
def maxOverList {A : Type} (valu : A → Z) (l : List A) : Z :=
  l.foldl (fun m x => max m (valu x)) 0

/-- `Bounds.max_over_instrs` -/
def maxOverInstrs (valu : Instruction → Z) : Z := maxOverList valu f.fn_code

/-- `Bounds.max_over_slots_of_instr` -/
def maxOverSlotsOfInstr (valu : Slot × Z × ATyp → Z) (i : Instruction) : Z :=
  maxOverList valu (slotsOfInstr i)

/-- `Bounds.max_over_slots_of_funct` -/
def maxOverSlotsOfFunct (valu : Slot × Z × ATyp → Z) : Z :=
  maxOverInstrs f (maxOverSlotsOfInstr valu)

/-- `Bounds.local_slot` -/
def localSlot : Slot × Z × ATyp → Z
  | (.Local, ofs, ty) => ofs + typesize ty
  | _ => 0

/-- `Bounds.outgoing_slot` -/
def outgoingSlot : Slot × Z × ATyp → Z
  | (.Outgoing, ofs, ty) => ofs + typesize ty
  | _ => 0

/-- `Bounds.outgoing_space` -/
def outgoingSpace (i : Instruction) : Z :=
  match i with
  | .Lcall sig _ => sizeArguments win64 sig
  | _ => 0

theorem foldl_max_ge {A : Type} (valu : A → Z) :
    ∀ (l : List A) (z : Z), z ≤ l.foldl (fun m x => max m (valu x)) z
  | [], _ => Int.le_refl _
  | a :: l, z => Int.le_trans (Int.le_max_left z (valu a)) (foldl_max_ge valu l _)

/-- `Bounds.max_over_list_pos` -/
theorem maxOverList_pos {A : Type} (valu : A → Z) (l : List A) : maxOverList valu l ≥ 0 :=
  foldl_max_ge valu l 0

/-- `Bounds.max_over_slots_of_funct_pos` -/
theorem maxOverSlotsOfFunct_pos (valu : Slot × Z × ATyp → Z) : maxOverSlotsOfFunct f valu ≥ 0 :=
  maxOverList_pos _ _

/-- `Bounds.only_callee_saves` -/
def OnlyCalleeSaves (u : RegSet) : Prop := ∀ r, r ∈ u → isCalleeSave win64 r = true

/-- Duplicate-freedom and callee-save-ness, the invariant of the `RegSet` operations. -/
def GoodSet (u : RegSet) : Prop := u.Nodup ∧ OnlyCalleeSaves win64 u

theorem recordReg_good {u : RegSet} (r : Mreg) (h : GoodSet win64 u) : GoodSet win64 (recordReg win64 u r) := by
  unfold recordReg
  split
  · next hcs =>
    split
    · exact h
    · next hn =>
      refine ⟨List.nodup_cons.mpr ⟨hn, h.1⟩, ?_⟩
      intro r' hr'
      rcases List.mem_cons.mp hr' with rfl | hr'
      · exact hcs
      · exact h.2 r' hr'
  · exact h

theorem recordRegs_good (rl : List Mreg) : ∀ {u : RegSet}, GoodSet win64 u → GoodSet win64 (recordRegs win64 u rl) := by
  induction rl with
  | nil => exact id
  | cons r rl ih => intro u h; exact ih (recordReg_good win64 r h)

theorem recordRegsOfInstr_good {u : RegSet} (i : Instruction) (h : GoodSet win64 u) :
    GoodSet win64 (recordRegsOfInstr win64 u i) := by
  cases i <;> simp only [recordRegsOfInstr] <;>
    first | exact recordReg_good win64 _ h | exact recordRegs_good win64 _ (recordRegs_good win64 _ h) | exact h

theorem foldl_recordRegsOfInstr_good :
    ∀ (c : Linear.Code) {u : RegSet}, GoodSet win64 u → GoodSet win64 (c.foldl (recordRegsOfInstr win64) u)
  | [], _, h => h
  | i :: c, _, h => foldl_recordRegsOfInstr_good c (recordRegsOfInstr_good win64 i h)

/-- `Bounds.record_regs_of_function_only` (with duplicate-freedom). -/
theorem recordRegsOfFunction_good : GoodSet win64 (recordRegsOfFunction win64 f) :=
  foldl_recordRegsOfInstr_good win64 _ ⟨List.nodup_nil, fun _ h => by cases h⟩

theorem mem_elements {u : RegSet} {r : Mreg} : r ∈ RegSet.elements u ↔ r ∈ u :=
  (RegSet.perm_elements u).mem_iff

/-- `Bounds.function_bounds` -/
def functionBounds : Bounds win64 where
  used_callee_save := RegSet.elements (recordRegsOfFunction win64 f)
  bound_local := maxOverSlotsOfFunct f localSlot
  bound_outgoing := max (maxOverInstrs f (outgoingSpace win64)) (maxOverSlotsOfFunct f outgoingSlot)
  bound_stack_data := max f.fn_stacksize 0
  bound_local_pos := maxOverSlotsOfFunct_pos f _
  bound_outgoing_pos := Int.le_trans (maxOverSlotsOfFunct_pos f _) (Int.le_max_right _ _)
  bound_stack_data_pos := Int.le_max_right _ _
  used_callee_save_norepet :=
    (RegSet.perm_elements _).nodup_iff.mpr (recordRegsOfFunction_good win64 f).1
  used_callee_save_prop r hr := (recordRegsOfFunction_good win64 f).2 r (mem_elements.mp hr)

/-! ### Correctness of the inferred bounds -/

theorem recordReg_incr {u : RegSet} {r' : Mreg} (r : Mreg) (h : r' ∈ u) : r' ∈ recordReg win64 u r := by
  unfold recordReg; split
  · split
    · exact h
    · exact List.mem_cons_of_mem _ h
  · exact h

theorem recordReg_ok (u : RegSet) {r : Mreg} (h : isCalleeSave win64 r = true) : r ∈ recordReg win64 u r := by
  unfold recordReg; rw [if_pos h]; split
  · assumption
  · exact List.mem_cons_self

theorem recordRegs_incr {r' : Mreg} (rl : List Mreg) : ∀ {u : RegSet}, r' ∈ u → r' ∈ recordRegs win64 u rl := by
  induction rl with
  | nil => exact id
  | cons r rl ih => intro u h; exact ih (recordReg_incr win64 r h)

theorem recordRegs_ok {r : Mreg} (rl : List Mreg) (hr : r ∈ rl) (hcs : isCalleeSave win64 r = true) :
    ∀ (u : RegSet), r ∈ recordRegs win64 u rl := by
  induction rl with
  | nil => cases hr
  | cons a rl ih =>
    intro u
    rcases List.mem_cons.mp hr with rfl | hr
    · exact recordRegs_incr win64 rl (recordReg_ok win64 u hcs)
    · exact ih hr _

theorem recordRegsOfInstr_incr {r' : Mreg} {u : RegSet} (i : Instruction) (h : r' ∈ u) :
    r' ∈ recordRegsOfInstr win64 u i := by
  cases i <;> simp only [recordRegsOfInstr] <;>
    first | exact recordReg_incr win64 _ h | exact recordRegs_incr win64 _ (recordRegs_incr win64 _ h) | exact h

/-- `Bounds.defined_by_instr` -/
def DefinedByInstr (r' : Mreg) (i : Instruction) : Prop :=
  match i with
  | .Lgetstack _ _ _ r => r' = r
  | .Lop _ _ res => r' = res
  | .Lload _ _ _ dst => r' = dst
  | .Lbuiltin ef _ res => r' ∈ BuiltinRes.params res ∨ r' ∈ destroyedByBuiltin ef
  | _ => False

theorem recordRegsOfInstr_ok {r' : Mreg} (u : RegSet) (i : Instruction) (hd : DefinedByInstr r' i)
    (hcs : isCalleeSave win64 r' = true) : r' ∈ recordRegsOfInstr win64 u i := by
  cases i <;> simp only [DefinedByInstr] at hd <;> simp only [recordRegsOfInstr]
  all_goals first
    | (subst hd; exact recordReg_ok win64 _ hcs)
    | skip
  case Lbuiltin ef args res =>
    rcases hd with hd | hd
    · exact recordRegs_incr win64 _ (recordRegs_ok win64 _ hd hcs _)
    · exact recordRegs_ok win64 _ hd hcs _

theorem foldl_recordRegsOfInstr_incr {r : Mreg} :
    ∀ (c : Linear.Code) {u : RegSet}, r ∈ u → r ∈ c.foldl (recordRegsOfInstr win64) u
  | [], _, h => h
  | i :: c, _, h => foldl_recordRegsOfInstr_incr c (recordRegsOfInstr_incr win64 i h)

theorem foldl_recordRegsOfInstr_ok {r : Mreg} {i : Instruction} (hd : DefinedByInstr r i)
    (hcs : isCalleeSave win64 r = true) :
    ∀ (c : Linear.Code) (u : RegSet), i ∈ c → r ∈ c.foldl (recordRegsOfInstr win64) u
  | [], _, h => by cases h
  | j :: c, u, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact foldl_recordRegsOfInstr_incr win64 c (recordRegsOfInstr_ok win64 u _ hd hcs)
    · exact foldl_recordRegsOfInstr_ok hd hcs c _ h

/-- `Bounds.record_regs_of_function_ok` -/
theorem recordRegsOfFunction_ok (r : Mreg) (i : Instruction) (hi : i ∈ f.fn_code)
    (hd : DefinedByInstr r i) (hcs : isCalleeSave win64 r = true) : r ∈ recordRegsOfFunction win64 f :=
  foldl_recordRegsOfInstr_ok win64 hd hcs _ _ hi

theorem foldl_max_bound {A : Type} (valu : A → Z) (x : A) :
    ∀ (l : List A) (z : Z), x ∈ l → valu x ≤ l.foldl (fun m y => max m (valu y)) z
  | [], _, h => by cases h
  | a :: l, z, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact Int.le_trans (Int.le_max_right _ _) (foldl_max_ge valu l _)
    · exact foldl_max_bound valu x l _ h

/-- `Bounds.max_over_list_bound` -/
theorem maxOverList_bound {A : Type} (valu : A → Z) (l : List A) (x : A) (h : x ∈ l) :
    valu x ≤ maxOverList valu l :=
  foldl_max_bound valu x l 0 h

/-- `Bounds.max_over_slots_of_funct_bound` -/
theorem maxOverSlotsOfFunct_bound (valu : Slot × Z × ATyp → Z) (i : Instruction)
    (s : Slot × Z × ATyp) (hi : i ∈ f.fn_code) (hs : s ∈ slotsOfInstr i) :
    valu s ≤ maxOverSlotsOfFunct f valu :=
  Int.le_trans (maxOverList_bound valu _ s hs) (maxOverList_bound _ _ i hi)

/-- `Bounds.mreg_is_within_bounds` -/
theorem mreg_is_within_bounds (i : Instruction) (hi : i ∈ f.fn_code) (r : Mreg)
    (hd : DefinedByInstr r i) : MregWithinBounds (functionBounds win64 f) r := fun hcs =>
  mem_elements.mpr (recordRegsOfFunction_ok win64 f r i hi hd hcs)

/-- `Bounds.slot_is_within_bounds` -/
theorem slot_is_within_bounds (i : Instruction) (hi : i ∈ f.fn_code) (sl : Slot) (ty : ATyp)
    (ofs : Z) (hs : (sl, ofs, ty) ∈ slotsOfInstr i) :
    SlotWithinBounds (functionBounds win64 f) sl ofs ty := by
  cases sl with
  | Local => exact maxOverSlotsOfFunct_bound f localSlot i _ hi hs
  | Incoming => trivial
  | Outgoing =>
    exact Int.le_trans (maxOverSlotsOfFunct_bound f outgoingSlot i _ hi hs) (Int.le_max_right _ _)

/-- `Bounds.slots_of_locs_charact` -/
theorem slotsOfLocs_charact (sl : Slot) (ofs : Z) (ty : ATyp) :
    ∀ (l : List Loc), (sl, ofs, ty) ∈ slotsOfLocs l ↔ Loc.S sl ofs ty ∈ l
  | [] => by simp [slotsOfLocs]
  | .R r :: l => by simp [slotsOfLocs, slotsOfLocs_charact sl ofs ty l]
  | .S sl' ofs' ty' :: l => by
    simp only [slotsOfLocs, List.mem_cons, slotsOfLocs_charact sl ofs ty l, Prod.mk.injEq,
      Loc.S.injEq]

/-- `Bounds.instr_is_within_bounds` -/
theorem instr_is_within_bounds (i : Instruction) (hi : i ∈ f.fn_code) :
    InstrWithinBounds win64 (functionBounds win64 f) i := by
  have hm := mreg_is_within_bounds win64 f i hi
  have hs := slot_is_within_bounds win64 f i hi
  cases i with
  | Lgetstack sl ofs ty r =>
    exact ⟨hs sl ty ofs (List.mem_singleton.mpr rfl), hm r rfl⟩
  | Lsetstack r sl ofs ty => exact hs sl ty ofs (List.mem_singleton.mpr rfl)
  | Lop op args res => exact hm res rfl
  | Lload chunk addr args dst => exact hm dst rfl
  | Lcall sig ros =>
    exact Int.le_trans (maxOverList_bound (outgoingSpace win64) _ _ hi) (Int.le_max_left _ _)
  | Lbuiltin ef args res =>
    exact ⟨fun r hr => hm r hr,
      fun sl ofs ty h => hs sl ty ofs ((slotsOfLocs_charact sl ofs ty _).mpr h)⟩
  | _ => trivial

/-- `Bounds.function_is_within_bounds` -/
theorem function_is_within_bounds : FunctionWithinBounds win64 f (functionBounds win64 f) :=
  fun i hi => instr_is_within_bounds win64 f i hi

end BOUNDS

/-! ## Size of the callee-save area and frame environments -/

variable {win64 : Bool}

/-- `Bounds.size_callee_save_area_rec` -/
def sizeCalleeSaveAreaRec : List Mreg → Z → Z
  | [], ofs => ofs
  | r :: l, ofs =>
      let sz := (Mreg.type r).size
      sizeCalleeSaveAreaRec l (align ofs sz + sz)

/-- `Bounds.size_callee_save_area` -/
def sizeCalleeSaveArea (b : Bounds win64) (ofs : Z) : Z := sizeCalleeSaveAreaRec b.used_callee_save ofs

/-- `Bounds.size_callee_save_area_rec_incr` -/
theorem sizeCalleeSaveAreaRec_incr : ∀ (l : List Mreg) (ofs : Z), ofs ≤ sizeCalleeSaveAreaRec l ofs
  | [], _ => Int.le_refl _
  | r :: l, ofs => by
    simp only [sizeCalleeSaveAreaRec]
    have hpos : (0 : Z) < (Mreg.type r).size := by rw [Mreg.type_eq_any64]; decide
    have := align_le ofs _ hpos
    exact Int.le_trans (Int.le_trans this (Int.le_add_of_nonneg_right (Int.le_of_lt hpos)))
      (sizeCalleeSaveAreaRec_incr l _)

/-- `Bounds.size_callee_save_area_incr` -/
theorem sizeCalleeSaveArea_incr (b : Bounds win64) (ofs : Z) : ofs ≤ sizeCalleeSaveArea b ofs :=
  sizeCalleeSaveAreaRec_incr _ _

/-- `Bounds.frame_env` -/
structure FrameEnv where
  fe_size : Z
  fe_ofs_link : Z
  fe_ofs_retaddr : Z
  fe_ofs_local : Z
  fe_ofs_callee_save : Z
  fe_stack_data : Z
  fe_used_callee_save : List Mreg

end Bounds
end X86
end CC
