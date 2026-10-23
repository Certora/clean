/-
  Calling conventions of the RISC-V back end — port of `riscV/Conventions1.v`
  (callee-save registers, register allocation preferences, `loc_result`,
  `loc_arguments` with the vararg handling of the RISC-V ELF psABI, the
  normalization predicates) with its lemmas, and of the target-independent
  definitions of `backend/Conventions.v` instantiated with the RISC-V
  locations.

  `Archi.ptr64` is `true` in this port (RV64); the `ptr64 = false` branches
  (register pairs for 64-bit values, `split_long_arg`) are kept for fidelity.
-/
import CCLib.riscV.Locations
import CCLib.backend.Conventions
import CCLib.cfrontend.CtypesTheory

namespace CC
namespace RiscV
namespace Conventions1

open Mreg
export CC.Conventions1 (projSigRes projSigArgs)

/-- `Conventions1.is_callee_save` -/
def isCalleeSave : Mreg → Bool
  | .R8 | .R9 | .R18 | .R19 | .R20 | .R21 | .R22 | .R23 | .R24 | .R25 | .R26 | .R27 | .F8 | .F9 | .F18 | .F19 | .F20 | .F21 | .F22 | .F23 | .F24 | .F25 | .F26 | .F27 => true
  | _ => false

/-- `Conventions1.int_caller_save_regs` -/
def intCallerSaveRegs : List Mreg :=
  [.R5, .R6, .R7, .R10, .R11, .R12, .R13, .R14, .R15, .R16, .R17, .R28, .R29, .R30]

/-- `Conventions1.float_caller_save_regs` -/
def floatCallerSaveRegs : List Mreg :=
  [.F0, .F1, .F2, .F3, .F4, .F5, .F6, .F7, .F10, .F11, .F12, .F13, .F14, .F15, .F16, .F17, .F28, .F29, .F30, .F31]

/-- `Conventions1.int_callee_save_regs` -/
def intCalleeSaveRegs : List Mreg :=
  [.R8, .R9, .R18, .R19, .R20, .R21, .R22, .R23, .R24, .R25, .R26, .R27]

/-- `Conventions1.float_callee_save_regs` -/
def floatCalleeSaveRegs : List Mreg :=
  [.F8, .F9, .F18, .F19, .F20, .F21, .F22, .F23, .F24, .F25, .F26, .F27]

/-- `Conventions1.destroyed_at_call` -/
def destroyedAtCall : List Mreg := allMregs.filter (fun r => !isCalleeSave r)

/-- `Conventions1.dummy_int_reg` -/
def dummyIntReg : Mreg := .R6
/-- `Conventions1.dummy_float_reg` -/
def dummyFloatReg : Mreg := .F0
/-- `Conventions1.callee_save_type` -/
def calleeSaveType : Mreg → ATyp := Mreg.type

/-- `Conventions1.is_float_reg` -/
def isFloatReg : Mreg → Bool
  | .R5 | .R6 | .R7 | .R8 | .R9 | .R10 | .R11 | .R12 | .R13 | .R14 | .R15 | .R16 | .R17 | .R18 | .R19 | .R20 | .R21 | .R22 | .R23 | .R24 | .R25 | .R26 | .R27 | .R28 | .R29 | .R30 => false
  | _ => true

/-- `Conventions1.alloc_regs` -/
structure AllocRegs where
  preferred_int_regs : List Mreg
  remaining_int_regs : List Mreg
  preferred_float_regs : List Mreg
  remaining_float_regs : List Mreg

/-- `Conventions1.allocatable_registers`: caller-save registers first, and
among them `x10`–`x15`, which have compact encodings. -/
def allocatableRegisters (_ : Unit) : AllocRegs :=
  { preferred_int_regs := [.R10, .R11, .R12, .R13, .R14, .R15],
    remaining_int_regs := [.R5, .R6, .R7, .R16, .R17, .R28, .R29, .R30] ++ intCalleeSaveRegs,
    preferred_float_regs := floatCallerSaveRegs,
    remaining_float_regs := floatCalleeSaveRegs }

/-! ## Location of function results -/

/-- `Conventions1.loc_result` -/
def locResult (s : Signature) : RPair Mreg :=
  match projSigRes s with
  | .Tint | .Tany32 => .One .R10
  | .Tfloat | .Tsingle | .Tany64 => .One .F10
  | .Tlong => if Archi.ptr64 then .One .R10 else .Twolong .R11 .R10

/-- `Conventions1.loc_result_type` -/
theorem locResult_type (s : Signature) :
    ATyp.subtype (projSigRes s) ((locResult s).typ Mreg.type) = true := by
  unfold locResult
  cases projSigRes s <;> rfl

/-- `Conventions1.loc_result_caller_save` -/
theorem locResult_callerSave (s : Signature) :
    (locResult s).Forall (fun r => isCalleeSave r = false) := by
  unfold locResult
  cases projSigRes s <;> rfl

/-- `Conventions1.loc_result_pair` -/
theorem locResult_pair (s : Signature) :
    match locResult s with
    | .One _ => True
    | .Twolong r1 r2 =>
        r1 ≠ r2 ∧ projSigRes s = .Tlong ∧ ATyp.subtype .Tint (Mreg.type r1) = true ∧
        ATyp.subtype .Tint (Mreg.type r2) = true ∧ Archi.ptr64 = false := by
  unfold locResult
  cases projSigRes s <;> trivial

/-- `Conventions1.loc_result_exten` -/
theorem locResult_exten {s1 s2 : Signature} (h : s1.sig_res = s2.sig_res) :
    locResult s1 = locResult s2 := by
  simp only [locResult, projSigRes, h]

/-! ## Location of function arguments -/

/-- `Conventions1.int_param_regs` (`a0`–`a7`) -/
def intParamRegs : List Mreg := [.R10, .R11, .R12, .R13, .R14, .R15, .R16, .R17]
/-- `Conventions1.float_param_regs` (`fa0`–`fa7`) -/
def floatParamRegs : List Mreg := [.F10, .F11, .F12, .F13, .F14, .F15, .F16, .F17]
/-- `Conventions1.float_extra_param_regs`: FP registers holding FP arguments
that must be passed in integer registers (fixed up by `Asmexpand`). -/
def floatExtraParamRegs : List Mreg := [.F0, .F1, .F2, .F3, .F4, .F5, .F6, .F7]

/-- `Conventions1.int_arg` -/
def intArg (ri rf ofs : Z) (ty : ATyp) (rec : Z → Z → Z → List (RPair Loc)) :
    List (RPair Loc) :=
  match CminorSel.listNthZ intParamRegs ri with
  | some r => .One (.R r) :: rec (ri + 1) rf ofs
  | none =>
      let ofs := align ofs (typesize ty)
      .One (.S .Outgoing ofs ty) :: rec ri rf (ofs + (if Archi.ptr64 then 2 else typesize ty))

/-- `Conventions1.float_arg` -/
def floatArg (va : Bool) (ri rf ofs : Z) (ty : ATyp) (rec : Z → Z → Z → List (RPair Loc)) :
    List (RPair Loc) :=
  match CminorSel.listNthZ (if va then [] else floatParamRegs) rf with
  | some r => .One (.R r) :: rec ri (rf + 1) ofs
  | none =>
      let regpair := !Archi.ptr64 && decide (typesize ty = 2)
      let ri' := if va && regpair then align ri 2 else ri
      match CminorSel.listNthZ floatExtraParamRegs ri' with
      | some r =>
          let ri'' := ri' + (if Archi.ptr64 then 1 else typesize ty)
          let ofs'' := if regpair && decide (ri' = 7) then ofs + 1 else ofs
          .One (.R r) :: rec ri'' rf ofs''
      | none =>
          let ofs := align ofs (typesize ty)
          .One (.S .Outgoing ofs ty) :: rec ri' rf (ofs + (if Archi.ptr64 then 2 else typesize ty))

/-- `Conventions1.split_long_arg` (RV32 only) -/
def splitLongArg (va : Bool) (ri rf ofs : Z) (rec : Z → Z → Z → List (RPair Loc)) :
    List (RPair Loc) :=
  let ri := if va then align ri 2 else ri
  match CminorSel.listNthZ intParamRegs ri, CminorSel.listNthZ intParamRegs (ri + 1) with
  | some r1, some r2 => .Twolong (.R r2) (.R r1) :: rec (ri + 2) rf ofs
  | some r1, none => .Twolong (.S .Outgoing ofs .Tint) (.R r1) :: rec (ri + 1) rf (ofs + 1)
  | none, _ =>
      let ofs := align ofs 2
      .Twolong (.S .Outgoing (ofs + 1) .Tint) (.S .Outgoing ofs .Tint) :: rec ri rf (ofs + 2)

/-- `Conventions1.loc_arguments_rec` -/
def locArgumentsRec : List ATyp → Z → Z → Z → Z → List (RPair Loc)
  | [], _, _, _, _ => []
  | ty :: tys, fixed, ri, rf, ofs =>
      match ty with
      | .Tint | .Tany32 => intArg ri rf ofs ty (locArgumentsRec tys (fixed - 1))
      | .Tsingle => floatArg (decide (fixed ≤ 0)) ri rf ofs ty (locArgumentsRec tys (fixed - 1))
      | .Tlong =>
          if Archi.ptr64 then intArg ri rf ofs ty (locArgumentsRec tys (fixed - 1))
          else splitLongArg (decide (fixed ≤ 0)) ri rf ofs (locArgumentsRec tys (fixed - 1))
      | .Tfloat | .Tany64 =>
          floatArg (decide (fixed ≤ 0)) ri rf ofs ty (locArgumentsRec tys (fixed - 1))

/-- `Conventions1.fixed_arguments` -/
def fixedArguments (s : Signature) : Z :=
  match s.sig_cc.cc_vararg with
  | some n => n
  | none => (s.sig_args.length : Z)

/-- `Conventions1.loc_arguments` -/
def locArguments (s : Signature) : List (RPair Loc) :=
  locArgumentsRec (projSigArgs s) (fixedArguments s) 0 0 0

/-- `Conventions1.loc_argument_acceptable` -/
def LocArgumentAcceptable : Loc → Prop
  | .R r => isCalleeSave r = false
  | .S .Outgoing ofs ty => ofs ≥ 0 ∧ typealign ty ∣ ofs
  | _ => False

theorem listNthZ_mem {A : Type} {l : List A} {n : Z} {x : A}
    (h : CminorSel.listNthZ l n = some x) : x ∈ l := by
  induction l generalizing n with
  | nil => cases h
  | cons a l ih =>
    simp only [CminorSel.listNthZ] at h
    split at h
    · cases h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

private def OK (l : List (RPair Loc)) : Prop := ∀ p ∈ l, p.Forall LocArgumentAcceptable
private def OKF (f : Z → Z → Z → List (RPair Loc)) : Prop :=
  ∀ ri rf ofs, ofs ≥ 0 → OK (f ri rf ofs)

private theorem CSI : ∀ r ∈ intParamRegs, isCalleeSave r = false := by decide
private theorem CSF : ∀ r ∈ floatParamRegs, isCalleeSave r = false := by decide
private theorem CSFX : ∀ r ∈ floatExtraParamRegs, isCalleeSave r = false := by decide

private theorem AL (ofs : Z) (ty : ATyp) (h : ofs ≥ 0) : align ofs (typesize ty) ≥ 0 :=
  Int.le_trans h (align_le ofs (typesize ty) (typesize_pos ty))

private theorem ALD (ofs : Z) (ty : ATyp) : typealign ty ∣ align ofs (typesize ty) :=
  Int.dvd_trans (typealign_typesize ty) (align_divides _ _)

private theorem OK_cons {p : RPair Loc} {l : List (RPair Loc)}
    (hp : p.Forall LocArgumentAcceptable) (hl : OK l) : OK (p :: l) := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact hp
  · exact hl q hq

private theorem intArg_ok (ri rf ofs : Z) (ty : ATyp) (f : Z → Z → Z → List (RPair Loc))
    (hf : OKF f) (ho : ofs ≥ 0) : OK (intArg ri rf ofs ty f) := by
  unfold intArg
  split
  · rename_i r h
    exact OK_cons (CSI r (listNthZ_mem h)) (hf _ _ _ ho)
  · refine OK_cons ⟨AL ofs ty ho, ALD ofs ty⟩ (hf _ _ _ ?_)
    simp only [Archi.ptr64, if_true]
    exact Int.le_trans (AL ofs ty ho) (Int.le_add_of_nonneg_right (by decide))

private theorem floatArg_ok (va : Bool) (ri rf ofs : Z) (ty : ATyp)
    (f : Z → Z → Z → List (RPair Loc)) (hf : OKF f) (ho : ofs ≥ 0) :
    OK (floatArg va ri rf ofs ty f) := by
  unfold floatArg
  split
  · rename_i r h
    refine OK_cons ?_ (hf _ _ _ ho)
    cases va
    · exact CSF r (listNthZ_mem h)
    · cases h
  · simp only [Archi.ptr64, Bool.not_true, Bool.false_and, Bool.and_false,
      if_true]
    split
    · rename_i r h
      exact OK_cons (CSFX r (listNthZ_mem h)) (hf _ _ _ ho)
    · refine OK_cons ⟨AL ofs ty ho, ALD ofs ty⟩ (hf _ _ _ ?_)
      exact Int.le_trans (AL ofs ty ho) (Int.le_add_of_nonneg_right (by decide))

/-- `Conventions1.loc_arguments_rec_charact` -/
theorem locArgumentsRec_charact (tyl : List ATyp) (fixed ri rf ofs : Z) (p : RPair Loc)
    (ho : ofs ≥ 0) (hp : p ∈ locArgumentsRec tyl fixed ri rf ofs) :
    p.Forall LocArgumentAcceptable := by
  suffices H : ∀ tyl fixed, OKF (locArgumentsRec tyl fixed) from H tyl fixed ri rf ofs ho p hp
  intro tyl
  induction tyl with
  | nil => intro _ _ _ _ _ p hp; cases hp
  | cons ty tys ih =>
    intro fixed ri rf ofs ho
    cases ty <;> simp only [locArgumentsRec, Archi.ptr64, if_true]
    all_goals first
      | exact intArg_ok _ _ _ _ _ (ih _) ho
      | exact floatArg_ok _ _ _ _ _ _ (ih _) ho

/-- `Conventions1.loc_arguments_acceptable` -/
theorem locArguments_acceptable (s : Signature) (p : RPair Loc)
    (hp : p ∈ locArguments s) : p.Forall LocArgumentAcceptable :=
  locArgumentsRec_charact _ _ 0 0 0 p (Int.le_refl 0) hp

/-- `Conventions1.loc_arguments_main` -/
theorem locArguments_main : locArguments signature_main = [] := rfl

/-! ## Normalization of function results and parameters -/

/-- `Conventions1.return_value_needs_normalization` (RISC-V): none needed. -/
def returnValueNeedsNormalization (_t : XType) : Bool := false

/-- `Conventions1.parameter_needs_normalization` (RISC-V): none needed. -/
def parameterNeedsNormalization (_t : XType) : Bool := false

end Conventions1

namespace Conventions

open Conventions1

/-- `Conventions.max_outgoing_1` -/
def maxOutgoing1 (accu : Z) : Loc → Z
  | .S .Outgoing ofs ty => max accu (ofs + typesize ty)
  | _ => accu

/-- `Conventions.max_outgoing_2` -/
def maxOutgoing2 (accu : Z) : RPair Loc → Z
  | .One l => maxOutgoing1 accu l
  | .Twolong l1 l2 => maxOutgoing1 (maxOutgoing1 accu l1) l2

/-- `Conventions.size_arguments` -/
def sizeArguments (s : Signature) : Z :=
  (locArguments s).foldl maxOutgoing2 0

/-- `Conventions.parameter_of_argument` -/
def parameterOfArgument : Loc → Loc
  | .S .Outgoing n ty => .S .Incoming n ty
  | l => l

/-- `Conventions.loc_parameters` -/
def locParameters (s : Signature) : List (RPair Loc) :=
  (locArguments s).map (RPair.map parameterOfArgument)

/-- `Conventions.tailcall_possible` -/
def TailcallPossible (s : Signature) : Prop :=
  ∀ l ∈ RPair.regsList (locArguments s), match l with | .R _ => True | .S .. => False

/-- `Conventions.tailcall_is_possible` -/
def tailcallIsPossible (sg : Signature) : Bool :=
  (RPair.regsList (locArguments sg)).all
    (fun l => match l with | .R _ => true | .S .. => false)

/-- `Conventions.tailcall_is_possible_correct` -/
theorem tailcallIsPossible_correct {s} (h : tailcallIsPossible s = true) :
    TailcallPossible s := by
  intro l hl
  have := List.all_eq_true.mp h l hl
  cases l <;> simp_all

/-- `Conventions.callee_save_loc` -/
def CalleeSaveLoc : Loc → Prop
  | .R r => isCalleeSave r = true
  | .S sl _ _ => sl ≠ .Outgoing

/-- `Conventions.agree_callee_save` -/
def AgreeCalleeSave (ls1 ls2 : Locmap) : Prop :=
  ∀ l, CalleeSaveLoc l → ls1 l = ls2 l

/-! ## Processor-independent properties (`backend/Conventions.v`) -/

/-- `Conventions.loc_arguments_acceptable_2` -/
theorem locArguments_acceptable_2 (s : Signature) (l : Loc)
    (h : l ∈ RPair.regsList (locArguments s)) : LocArgumentAcceptable l := by
  obtain ⟨p, hp, hl⟩ := RPair.in_regsList_inv h
  have := locArguments_acceptable s p hp
  cases p with
  | One r =>
    simp only [RPair.regs, List.mem_singleton] at hl; subst hl; exact this
  | Twolong r1 r2 =>
    simp only [RPair.regs, List.mem_cons, List.not_mem_nil, or_false] at hl
    simp only [RPair.Forall] at this
    rcases hl with rfl | rfl
    · exact this.1
    · exact this.2

private theorem maxOutgoing1_above (n : Z) (l : Loc) : maxOutgoing1 n l ≥ n := by
  unfold maxOutgoing1; split <;> zomega

/-- `Conventions.fold_max_outgoing_above` -/
theorem fold_maxOutgoing_above : ∀ (l : List (RPair Loc)) (n : Z), l.foldl maxOutgoing2 n ≥ n
  | [], n => by simp
  | a :: l, n => by
    simp only [List.foldl_cons]
    have h1 := fold_maxOutgoing_above l (maxOutgoing2 n a)
    have h2 : maxOutgoing2 n a ≥ n := by
      cases a with
      | One l => exact maxOutgoing1_above _ _
      | Twolong l1 l2 =>
        have := maxOutgoing1_above n l1
        have := maxOutgoing1_above (maxOutgoing1 n l1) l2
        simp only [maxOutgoing2]; zomega
    zomega

/-- `Conventions.size_arguments_above` -/
theorem sizeArguments_above (s : Signature) : sizeArguments s ≥ 0 :=
  fold_maxOutgoing_above _ _

/-- `Conventions.loc_arguments_bounded` -/
theorem locArguments_bounded (s : Signature) (ofs : Z) (ty : ATyp)
    (h : Loc.S .Outgoing ofs ty ∈ RPair.regsList (locArguments s)) :
    ofs + typesize ty ≤ sizeArguments s := by
  have B : ∀ p n, Loc.S .Outgoing ofs ty ∈ RPair.regs p →
      ofs + typesize ty ≤ maxOutgoing2 n p := by
    intro p n hp
    cases p with
    | One l =>
      simp only [RPair.regs, List.mem_singleton] at hp; subst hp
      simp only [maxOutgoing2, maxOutgoing1]; zomega
    | Twolong l1 l2 =>
      simp only [RPair.regs, List.mem_cons, List.not_mem_nil, or_false] at hp
      simp only [maxOutgoing2]
      rcases hp with rfl | rfl
      · have := maxOutgoing1_above (maxOutgoing1 n (.S .Outgoing ofs ty)) l2
        simp only [maxOutgoing1] at this ⊢; zomega
      · simp only [maxOutgoing1]; zomega
  have C : ∀ l n, Loc.S .Outgoing ofs ty ∈ RPair.regsList l →
      ofs + typesize ty ≤ l.foldl maxOutgoing2 n := by
    intro l
    induction l with
    | nil => intro n h; simp [RPair.regsList] at h
    | cons a l ih =>
      intro n h
      simp only [RPair.regsList, List.mem_append] at h
      simp only [List.foldl_cons]
      rcases h with h | h
      · have := B a n h
        have := fold_maxOutgoing_above l (maxOutgoing2 n a)
        zomega
      · exact ih _ h
  exact C _ _ h

/-- `Conventions.incoming_slot_in_parameters` -/
theorem incoming_slot_in_parameters (ofs : Z) (ty : ATyp) (sg : Signature)
    (h : Loc.S .Incoming ofs ty ∈ RPair.regsList (locParameters sg)) :
    Loc.S .Outgoing ofs ty ∈ RPair.regsList (locArguments sg) := by
  have E : ∀ l : List (RPair Loc), RPair.regsList (l.map (RPair.map parameterOfArgument)) =
      (RPair.regsList l).map parameterOfArgument := by
    intro l
    induction l with
    | nil => rfl
    | cons p l ih =>
      simp only [List.map_cons, RPair.regsList, List.map_append, ih]
      cases p <;> rfl
  unfold locParameters at h
  rw [E] at h
  obtain ⟨x, hx, hxe⟩ := List.mem_map.mp h
  have hacc := locArguments_acceptable_2 sg x hx
  cases x with
  | R r => cases hxe
  | S sl o t =>
    cases sl <;> simp only [parameterOfArgument, Loc.S.injEq, reduceCtorEq] at hxe
    all_goals first
      | (simp [LocArgumentAcceptable] at hacc; done)
      | (obtain ⟨-, rfl, rfl⟩ := hxe; exact hx)

/-- `Conventions.zero_size_arguments_tailcall_possible` -/
theorem zero_size_arguments_tailcall_possible (sg : Signature)
    (h : sizeArguments sg = 0) : TailcallPossible sg := by
  intro l hl
  have hacc := locArguments_acceptable_2 sg l hl
  cases l with
  | R _ => trivial
  | S sl ofs ty =>
    cases sl <;> simp only [LocArgumentAcceptable] at hacc
    have := locArguments_bounded sg ofs ty hl
    have := typesize_pos ty
    zomega

/-- `Conventions.locmap_get_set_loc_result` -/
theorem locmap_get_set_loc_result (sg : Signature) (v : Val) (rs : Locmap) (l : Loc)
    (h : match l with | .R r => isCalleeSave r = true | .S .. => True) :
    Locmap.setpair (locResult sg) v rs l = rs l := by
  apply Locmap.gpo
  have X : ∀ r, isCalleeSave r = false → Loc.diff l (.R r) := by
    intro r hr
    cases l with
    | R r' =>
      simp only [Loc.diff]
      intro e; subst e; simp only at h; rw [hr] at h; cases h
    | S _ _ _ => simp [Loc.diff]
  have := locResult_callerSave sg
  cases hp : locResult sg with
  | One r => rw [hp] at this; exact X r this
  | Twolong r1 r2 =>
    rw [hp] at this
    exact ⟨X r1 this.1, X r2 this.2⟩

/-- `Conventions.locmap_get_set_loc_result_callee_save` -/
theorem locmap_get_set_loc_result_callee_save (sg : Signature) (v : Val) (rs : Locmap) (l : Loc)
    (h : CalleeSaveLoc l) : Locmap.setpair (locResult sg) v rs l = rs l := by
  apply locmap_get_set_loc_result
  cases l with
  | R r => exact h
  | S _ _ _ => trivial

end Conventions
end RiscV
end CC
