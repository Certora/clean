/-
  Calling conventions of the x86 back end — port of `x86/Conventions1.v`
  (callee-save registers, register allocation preferences, `loc_result`,
  `loc_arguments` for the x86-32, x86-64 ELF and Win64 ABIs, the
  normalization predicates) with its lemmas, and of the target-independent
  definitions of `backend/Conventions.v` instantiated with the x86 locations.

  Differences from Rocq: `Archi.win64` (a Rocq `Parameter` set by the
  driver) is an explicit argument `win64 : Bool` of the functions that
  depend on it.  `Archi.ptr64` is `true` in this port, so `loc_result` and
  `loc_arguments` reduce to their 64-bit versions; the 32-bit versions are
  kept for fidelity.
-/
import CCLib.x86.Locations
import CCLib.backend.Conventions

namespace CC
namespace X86
namespace Conventions1

open Mreg
open CC.Conventions1 (projSigRes projSigArgs)
export CC.Conventions1 (projSigRes projSigArgs)

/-- `Conventions1.is_callee_save` -/
def isCalleeSave (win64 : Bool) : Mreg → Bool
  | .AX | .CX | .DX => false
  | .BX | .BP => true
  | .SI | .DI => !Archi.ptr64 || win64
  | .R8 | .R9 | .R10 | .R11 => false
  | .R12 | .R13 | .R14 | .R15 => true
  | .X0 | .X1 | .X2 | .X3 | .X4 | .X5 => false
  | .X6 | .X7 | .X8 | .X9 | .X10 | .X11 | .X12 | .X13 | .X14 | .X15 => win64
  | .FP0 => false

/-- `Conventions1.int_caller_save_regs` -/
def intCallerSaveRegs (win64 : Bool) : List Mreg :=
  if Archi.ptr64 then
    if win64 then [.AX, .CX, .DX, .R8, .R9, .R10, .R11]
    else [.AX, .CX, .DX, .SI, .DI, .R8, .R9, .R10, .R11]
  else [.AX, .CX, .DX]

/-- `Conventions1.float_caller_save_regs` -/
def floatCallerSaveRegs (win64 : Bool) : List Mreg :=
  if Archi.ptr64 then
    if win64 then [.X0, .X1, .X2, .X3, .X4, .X5]
    else [.X0, .X1, .X2, .X3, .X4, .X5, .X6, .X7,
          .X8, .X9, .X10, .X11, .X12, .X13, .X14, .X15]
  else [.X0, .X1, .X2, .X3, .X4, .X5, .X6, .X7]

/-- `Conventions1.int_callee_save_regs` -/
def intCalleeSaveRegs (win64 : Bool) : List Mreg :=
  if Archi.ptr64 then
    if win64 then [.BX, .SI, .DI, .BP, .R12, .R13, .R14, .R15]
    else [.BX, .BP, .R12, .R13, .R14, .R15]
  else [.BX, .SI, .DI, .BP]

/-- `Conventions1.float_callee_save_regs` -/
def floatCalleeSaveRegs (win64 : Bool) : List Mreg :=
  if Archi.ptr64 && win64 then [.X6, .X7, .X8, .X9, .X10, .X11, .X12, .X13, .X14, .X15]
  else []

/-- `Conventions1.destroyed_at_call` -/
def destroyedAtCall (win64 : Bool) : List Mreg :=
  allMregs.filter (fun r => !isCalleeSave win64 r)

/-- `Conventions1.is_float_reg` -/
def isFloatReg : Mreg → Bool
  | .AX | .BX | .CX | .DX | .SI | .DI | .BP
  | .R8 | .R9 | .R10 | .R11 | .R12 | .R13 | .R14 | .R15 => false
  | _ => true

/-- `Conventions1.dummy_int_reg` -/
def dummyIntReg : Mreg := .AX
/-- `Conventions1.dummy_float_reg` -/
def dummyFloatReg : Mreg := .X0
/-- `Conventions1.callee_save_type` -/
def calleeSaveType : Mreg → ATyp := Mreg.type

/-- `Conventions1.alloc_regs` -/
structure AllocRegs where
  preferred_int_regs : List Mreg
  remaining_int_regs : List Mreg
  preferred_float_regs : List Mreg
  remaining_float_regs : List Mreg

/-- `Conventions1.allocatable_registers` -/
def allocatableRegisters (win64 : Bool) (_ : Unit) : AllocRegs :=
  { preferred_int_regs := intCallerSaveRegs win64,
    remaining_int_regs := intCalleeSaveRegs win64,
    preferred_float_regs := floatCallerSaveRegs win64,
    remaining_float_regs := floatCalleeSaveRegs win64 }

/-! ## Location of function results -/

/-- `Conventions1.loc_result_32` -/
def locResult32 (s : Signature) : RPair Mreg :=
  match projSigRes s with
  | .Tint | .Tany32 => .One .AX
  | .Tfloat | .Tsingle => .One .FP0
  | .Tany64 => .One .X0
  | .Tlong => .Twolong .DX .AX

/-- `Conventions1.loc_result_64` -/
def locResult64 (s : Signature) : RPair Mreg :=
  match projSigRes s with
  | .Tint | .Tlong | .Tany32 | .Tany64 => .One .AX
  | .Tfloat | .Tsingle => .One .X0

/-- `Conventions1.loc_result` -/
def locResult (s : Signature) : RPair Mreg :=
  if Archi.ptr64 then locResult64 s else locResult32 s

/-- `Conventions1.loc_result_type` -/
theorem locResult_type (s : Signature) :
    ATyp.subtype (projSigRes s) ((locResult s).typ Mreg.type) = true := by
  simp only [locResult, locResult64, Archi.ptr64, if_true]
  cases projSigRes s <;> rfl

/-- `Conventions1.loc_result_caller_save` -/
theorem locResult_callerSave (win64 : Bool) (s : Signature) :
    (locResult s).Forall (fun r => isCalleeSave win64 r = false) := by
  simp only [locResult, locResult64, Archi.ptr64, if_true]
  cases projSigRes s <;> rfl

/-- `Conventions1.loc_result_pair`: on x86-64 results are never split. -/
theorem locResult_pair (s : Signature) :
    match locResult s with
    | .One _ => True
    | .Twolong r1 r2 =>
        r1 ≠ r2 ∧ projSigRes s = .Tlong ∧ ATyp.subtype .Tint (Mreg.type r1) = true ∧
        ATyp.subtype .Tint (Mreg.type r2) = true ∧ Archi.ptr64 = false := by
  simp only [locResult, locResult64, Archi.ptr64, if_true]
  cases projSigRes s <;> trivial

/-- `Conventions1.loc_result_exten` -/
theorem locResult_exten {s1 s2 : Signature} (h : s1.sig_res = s2.sig_res) :
    locResult s1 = locResult s2 := by
  simp only [locResult, locResult64, locResult32, projSigRes, h]

/-! ## Location of function arguments -/

/-- `Conventions1.loc_arguments_32`: all arguments on the stack. -/
def locArguments32 : List ATyp → Z → List (RPair Loc)
  | [], _ => []
  | ty :: tys, ofs =>
      (match ty with
       | .Tlong => .Twolong (.S .Outgoing (ofs + 1) .Tint) (.S .Outgoing ofs .Tint)
       | _ => .One (.S .Outgoing ofs ty))
      :: locArguments32 tys (ofs + typesize ty)

/-- `Conventions1.int_param_regs_elf64` -/
def intParamRegsElf64 : List Mreg := [.DI, .SI, .DX, .CX, .R8, .R9]
/-- `Conventions1.float_param_regs_elf64` -/
def floatParamRegsElf64 : List Mreg := [.X0, .X1, .X2, .X3, .X4, .X5, .X6, .X7]

/-- `Conventions1.loc_arguments_elf64` -/
def locArgumentsElf64 : List ATyp → Z → Z → Z → List (RPair Loc)
  | [], _, _, _ => []
  | ty :: tys, ir, fr, ofs =>
      match ty with
      | .Tint | .Tlong | .Tany32 | .Tany64 =>
          match CminorSel.listNthZ intParamRegsElf64 ir with
          | none => .One (.S .Outgoing ofs ty) :: locArgumentsElf64 tys ir fr (ofs + 2)
          | some ireg => .One (.R ireg) :: locArgumentsElf64 tys (ir + 1) fr ofs
      | .Tfloat | .Tsingle =>
          match CminorSel.listNthZ floatParamRegsElf64 fr with
          | none => .One (.S .Outgoing ofs ty) :: locArgumentsElf64 tys ir fr (ofs + 2)
          | some freg => .One (.R freg) :: locArgumentsElf64 tys ir (fr + 1) ofs

/-- `Conventions1.int_param_regs_win64` -/
def intParamRegsWin64 : List Mreg := [.CX, .DX, .R8, .R9]
/-- `Conventions1.float_param_regs_win64` -/
def floatParamRegsWin64 : List Mreg := [.X0, .X1, .X2, .X3]

/-- `Conventions1.loc_arguments_win64` -/
def locArgumentsWin64 : List ATyp → Z → Z → List (RPair Loc)
  | [], _, _ => []
  | ty :: tys, r, ofs =>
      match ty with
      | .Tint | .Tlong | .Tany32 | .Tany64 =>
          match CminorSel.listNthZ intParamRegsWin64 r with
          | none => .One (.S .Outgoing ofs ty) :: locArgumentsWin64 tys r (ofs + 2)
          | some ireg => .One (.R ireg) :: locArgumentsWin64 tys (r + 1) ofs
      | .Tfloat | .Tsingle =>
          match CminorSel.listNthZ floatParamRegsWin64 r with
          | none => .One (.S .Outgoing ofs ty) :: locArgumentsWin64 tys r (ofs + 2)
          | some freg => .One (.R freg) :: locArgumentsWin64 tys (r + 1) ofs

/-- `Conventions1.loc_arguments` -/
def locArguments (win64 : Bool) (s : Signature) : List (RPair Loc) :=
  if Archi.ptr64 then
    if win64 then locArgumentsWin64 (projSigArgs s) 0 0
    else locArgumentsElf64 (projSigArgs s) 0 0 0
  else locArguments32 (projSigArgs s) 0

/-- `Conventions1.loc_argument_acceptable` -/
def LocArgumentAcceptable (win64 : Bool) : Loc → Prop
  | .R r => isCalleeSave win64 r = false
  | .S .Outgoing ofs ty => ofs ≥ 0 ∧ typealign ty ∣ ofs
  | _ => False

/-- `Conventions1.loc_argument_elf64_charact` -/
def LocArgumentElf64Charact (ofs : Z) : Loc → Prop
  | .R r => r ∈ intParamRegsElf64 ∨ r ∈ floatParamRegsElf64
  | .S .Outgoing ofs' _ => ofs' ≥ ofs ∧ (2 : Z) ∣ ofs'
  | _ => False

/-- `Conventions1.loc_argument_win64_charact` -/
def LocArgumentWin64Charact (ofs : Z) : Loc → Prop
  | .R r => r ∈ intParamRegsWin64 ∨ r ∈ floatParamRegsWin64
  | .S .Outgoing ofs' _ => ofs' ≥ ofs ∧ (2 : Z) ∣ ofs'
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

/-- `Conventions1.loc_arguments_elf64_charact` -/
theorem locArgumentsElf64_charact (tyl : List ATyp) (ir fr ofs : Z) (p : RPair Loc)
    (hp : p ∈ locArgumentsElf64 tyl ir fr ofs) (hofs : (2 : Z) ∣ ofs) :
    p.Forall (LocArgumentElf64Charact ofs) := by
  induction tyl generalizing ir fr ofs p with
  | nil => cases hp
  | cons ty tys ih =>
    have weaken : ∀ q, q ∈ locArgumentsElf64 tys ir fr (ofs + 2) →
        q.Forall (LocArgumentElf64Charact ofs) := by
      intro q hq
      have := ih ir fr (ofs + 2) q hq (by obtain ⟨k, hk⟩ := hofs; exact ⟨k + 1, by omega⟩)
      cases q with
      | One l =>
        cases l with
        | R r => exact this
        | S sl o t =>
          cases sl <;> simp only [RPair.Forall, LocArgumentElf64Charact] at this ⊢
          exact ⟨Int.le_trans (Int.le_add_of_nonneg_right (by decide)) this.1, this.2⟩
      | Twolong l1 l2 =>
        simp only [RPair.Forall] at this ⊢
        refine ⟨?_, ?_⟩
        · cases l1 with
          | R r => exact this.1
          | S sl o t =>
            have h1 := this.1
            cases sl <;> simp only [LocArgumentElf64Charact] at h1 ⊢
            exact ⟨Int.le_trans (Int.le_add_of_nonneg_right (by decide)) h1.1, h1.2⟩
        · cases l2 with
          | R r => exact this.2
          | S sl o t =>
            have h2 := this.2
            cases sl <;> simp only [LocArgumentElf64Charact] at h2 ⊢
            exact ⟨Int.le_trans (Int.le_add_of_nonneg_right (by decide)) h2.1, h2.2⟩
    cases ty <;> simp only [locArgumentsElf64] at hp <;> split at hp <;>
      rcases List.mem_cons.mp hp with rfl | hp
    all_goals first
      | exact weaken _ hp
      | exact ih _ _ _ _ hp hofs
      | (simp only [RPair.Forall, LocArgumentElf64Charact]; exact ⟨Int.le_refl _, hofs⟩)
      | (rename_i h; simp only [RPair.Forall, LocArgumentElf64Charact]; exact .inl (listNthZ_mem h))
      | (rename_i h; simp only [RPair.Forall, LocArgumentElf64Charact]; exact .inr (listNthZ_mem h))

/-- `Conventions1.loc_arguments_win64_charact` -/
theorem locArgumentsWin64_charact (tyl : List ATyp) (r ofs : Z) (p : RPair Loc)
    (hp : p ∈ locArgumentsWin64 tyl r ofs) (hofs : (2 : Z) ∣ ofs) :
    p.Forall (LocArgumentWin64Charact ofs) := by
  induction tyl generalizing r ofs p with
  | nil => cases hp
  | cons ty tys ih =>
    have weaken : ∀ q, q ∈ locArgumentsWin64 tys r (ofs + 2) →
        q.Forall (LocArgumentWin64Charact ofs) := by
      intro q hq
      have := ih r (ofs + 2) q hq (by obtain ⟨k, hk⟩ := hofs; exact ⟨k + 1, by omega⟩)
      cases q with
      | One l =>
        cases l with
        | R r => exact this
        | S sl o t =>
          cases sl <;> simp only [RPair.Forall, LocArgumentWin64Charact] at this ⊢
          exact ⟨Int.le_trans (Int.le_add_of_nonneg_right (by decide)) this.1, this.2⟩
      | Twolong l1 l2 =>
        simp only [RPair.Forall] at this ⊢
        refine ⟨?_, ?_⟩
        · cases l1 with
          | R r => exact this.1
          | S sl o t =>
            have h1 := this.1
            cases sl <;> simp only [LocArgumentWin64Charact] at h1 ⊢
            exact ⟨Int.le_trans (Int.le_add_of_nonneg_right (by decide)) h1.1, h1.2⟩
        · cases l2 with
          | R r => exact this.2
          | S sl o t =>
            have h2 := this.2
            cases sl <;> simp only [LocArgumentWin64Charact] at h2 ⊢
            exact ⟨Int.le_trans (Int.le_add_of_nonneg_right (by decide)) h2.1, h2.2⟩
    cases ty <;> simp only [locArgumentsWin64] at hp <;> split at hp <;>
      rcases List.mem_cons.mp hp with rfl | hp
    all_goals first
      | exact weaken _ hp
      | exact ih _ _ _ hp hofs
      | (simp only [RPair.Forall, LocArgumentWin64Charact]; exact ⟨Int.le_refl _, hofs⟩)
      | (rename_i h; simp only [RPair.Forall, LocArgumentWin64Charact]; exact .inl (listNthZ_mem h))
      | (rename_i h; simp only [RPair.Forall, LocArgumentWin64Charact]; exact .inr (listNthZ_mem h))

theorem typealign_dvd_of_two_dvd (ty : ATyp) {ofs : Z} (h : (2 : Z) ∣ ofs) :
    typealign ty ∣ ofs := by
  have : typealign ty = 1 ∨ typealign ty = 2 := by cases ty <;> decide
  rcases this with e | e <;> rw [e]
  · exact Int.one_dvd _
  · exact h

/-- `Conventions1.loc_arguments_acceptable` -/
theorem locArguments_acceptable (win64 : Bool) (s : Signature) (p : RPair Loc)
    (hp : p ∈ locArguments win64 s) : p.Forall (LocArgumentAcceptable win64) := by
  simp only [locArguments, Archi.ptr64, if_true] at hp
  cases win64 with
  | false =>
    have := locArgumentsElf64_charact _ 0 0 0 p hp (Int.dvd_zero _)
    have key : ∀ l, LocArgumentElf64Charact 0 l → LocArgumentAcceptable false l := by
      intro l hl
      cases l with
      | R r =>
        simp only [LocArgumentElf64Charact, intParamRegsElf64, floatParamRegsElf64] at hl
        simp only [LocArgumentAcceptable]
        rcases hl with hl | hl <;> simp at hl <;> rcases hl with rfl | hl <;>
          (try rcases hl with rfl | hl) <;> (try rcases hl with rfl | hl) <;>
          (try rcases hl with rfl | hl) <;> (try rcases hl with rfl | hl) <;>
          (try rcases hl with rfl | hl) <;> (try rcases hl with rfl | hl) <;>
          (try subst hl) <;> rfl
      | S sl o t =>
        cases sl <;> simp only [LocArgumentElf64Charact] at hl
        exact ⟨hl.1, typealign_dvd_of_two_dvd t hl.2⟩
    cases p with
    | One l => exact key l this
    | Twolong l1 l2 => exact ⟨key l1 this.1, key l2 this.2⟩
  | true =>
    have := locArgumentsWin64_charact _ 0 0 p hp (Int.dvd_zero _)
    have key : ∀ l, LocArgumentWin64Charact 0 l → LocArgumentAcceptable true l := by
      intro l hl
      cases l with
      | R r =>
        simp only [LocArgumentWin64Charact, intParamRegsWin64, floatParamRegsWin64] at hl
        simp only [LocArgumentAcceptable]
        rcases hl with hl | hl <;> simp at hl <;> rcases hl with rfl | hl <;>
          (try rcases hl with rfl | hl) <;> (try rcases hl with rfl | hl) <;>
          (try subst hl) <;> rfl
      | S sl o t =>
        cases sl <;> simp only [LocArgumentWin64Charact] at hl
        exact ⟨hl.1, typealign_dvd_of_two_dvd t hl.2⟩
    cases p with
    | One l => exact key l this
    | Twolong l1 l2 => exact ⟨key l1 this.1, key l2 this.2⟩

/-! ## Normalization of small integer results and parameters -/

/-- `Conventions1.return_value_needs_normalization` (x86) -/
def returnValueNeedsNormalization (t : XType) : Bool :=
  match t with
  | .Xint8signed | .Xint8unsigned | .Xint16signed | .Xint16unsigned => true
  | _ => false

/-- `Conventions1.parameter_needs_normalization` (x86): parameters are
passed in normalized form. -/
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
def sizeArguments (win64 : Bool) (s : Signature) : Z :=
  (locArguments win64 s).foldl maxOutgoing2 0

/-- `Conventions.parameter_of_argument` -/
def parameterOfArgument : Loc → Loc
  | .S .Outgoing n ty => .S .Incoming n ty
  | l => l

/-- `Conventions.loc_parameters` -/
def locParameters (win64 : Bool) (s : Signature) : List (RPair Loc) :=
  (locArguments win64 s).map (RPair.map parameterOfArgument)

/-- `Conventions.tailcall_possible` -/
def TailcallPossible (win64 : Bool) (s : Signature) : Prop :=
  ∀ l ∈ RPair.regsList (locArguments win64 s), match l with | .R _ => True | .S .. => False

/-- `Conventions.tailcall_is_possible` -/
def tailcallIsPossible (win64 : Bool) (sg : Signature) : Bool :=
  (RPair.regsList (locArguments win64 sg)).all
    (fun l => match l with | .R _ => true | .S .. => false)

/-- `Conventions.tailcall_is_possible_correct` -/
theorem tailcallIsPossible_correct {win64 s} (h : tailcallIsPossible win64 s = true) :
    TailcallPossible win64 s := by
  intro l hl
  have := List.all_eq_true.mp h l hl
  cases l <;> simp_all

/-- `Conventions.callee_save_loc` -/
def CalleeSaveLoc (win64 : Bool) : Loc → Prop
  | .R r => isCalleeSave win64 r = true
  | .S sl _ _ => sl ≠ .Outgoing

/-- `Conventions.agree_callee_save` -/
def AgreeCalleeSave (win64 : Bool) (ls1 ls2 : Locmap) : Prop :=
  ∀ l, CalleeSaveLoc win64 l → ls1 l = ls2 l

/-! ## Processor-independent properties (`backend/Conventions.v`) -/

/-- `Conventions.loc_arguments_acceptable_2` -/
theorem locArguments_acceptable_2 (win64 : Bool) (s : Signature) (l : Loc)
    (h : l ∈ RPair.regsList (locArguments win64 s)) : LocArgumentAcceptable win64 l := by
  obtain ⟨p, hp, hl⟩ := RPair.in_regsList_inv h
  have := locArguments_acceptable win64 s p hp
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
theorem sizeArguments_above (win64 : Bool) (s : Signature) : sizeArguments win64 s ≥ 0 :=
  fold_maxOutgoing_above _ _

/-- `Conventions.loc_arguments_bounded` -/
theorem locArguments_bounded (win64 : Bool) (s : Signature) (ofs : Z) (ty : ATyp)
    (h : Loc.S .Outgoing ofs ty ∈ RPair.regsList (locArguments win64 s)) :
    ofs + typesize ty ≤ sizeArguments win64 s := by
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
theorem incoming_slot_in_parameters (win64 : Bool) (ofs : Z) (ty : ATyp) (sg : Signature)
    (h : Loc.S .Incoming ofs ty ∈ RPair.regsList (locParameters win64 sg)) :
    Loc.S .Outgoing ofs ty ∈ RPair.regsList (locArguments win64 sg) := by
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
  have hacc := locArguments_acceptable_2 win64 sg x hx
  cases x with
  | R r => cases hxe
  | S sl o t =>
    cases sl <;> simp only [parameterOfArgument, Loc.S.injEq, reduceCtorEq] at hxe
    all_goals first
      | (simp [LocArgumentAcceptable] at hacc; done)
      | (obtain ⟨-, rfl, rfl⟩ := hxe; exact hx)

/-- `Conventions.zero_size_arguments_tailcall_possible` -/
theorem zero_size_arguments_tailcall_possible (win64 : Bool) (sg : Signature)
    (h : sizeArguments win64 sg = 0) : TailcallPossible win64 sg := by
  intro l hl
  have hacc := locArguments_acceptable_2 win64 sg l hl
  cases l with
  | R _ => trivial
  | S sl ofs ty =>
    cases sl <;> simp only [LocArgumentAcceptable] at hacc
    have := locArguments_bounded win64 sg ofs ty hl
    have := typesize_pos ty
    zomega

/-- `Conventions.locmap_get_set_loc_result` -/
theorem locmap_get_set_loc_result (win64 : Bool) (sg : Signature) (v : Val) (rs : Locmap) (l : Loc)
    (h : match l with | .R r => isCalleeSave win64 r = true | .S .. => True) :
    Locmap.setpair (locResult sg) v rs l = rs l := by
  apply Locmap.gpo
  have X : ∀ r, isCalleeSave win64 r = false → Loc.diff l (.R r) := by
    intro r hr
    cases l with
    | R r' =>
      simp only [Loc.diff]
      intro e; subst e; simp only at h; rw [hr] at h; cases h
    | S _ _ _ => simp [Loc.diff]
  have := locResult_callerSave win64 sg
  cases hp : locResult sg with
  | One r => rw [hp] at this; exact X r this
  | Twolong r1 r2 =>
    rw [hp] at this
    exact ⟨X r1 this.1, X r2 this.2⟩

/-- `Conventions.locmap_get_set_loc_result_callee_save` -/
theorem locmap_get_set_loc_result_callee_save (win64 : Bool) (sg : Signature) (v : Val) (rs : Locmap) (l : Loc)
    (h : CalleeSaveLoc win64 l) : Locmap.setpair (locResult sg) v rs l = rs l := by
  apply locmap_get_set_loc_result
  cases l with
  | R r => exact h
  | S _ _ _ => trivial

/-- `Conventions1.loc_arguments_main` -/
theorem locArguments_main (win64 : Bool) : locArguments win64 signature_main = [] := by
  cases win64 <;> rfl

end Conventions
end X86
end CC
