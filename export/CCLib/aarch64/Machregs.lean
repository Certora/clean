/-
  Machine registers of the aarch64 back end — port of `aarch64/Machregs.v`.

  Differences from Rocq: `IndexedMreg.index` is `Mreg.index`; the `Finite`
  instance is the list `allMregs` with its completeness lemma.
-/
import CCLib.aarch64.Op

namespace CC

open Op

/-- `Machregs.mreg` -/
inductive Mreg where
  | R0 | R1 | R2 | R3 | R4 | R5 | R6 | R7 | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15 | R17 | R19 | R20 | R21 | R22 | R23 | R24 | R25 | R26 | R27 | R28 | R29
  | F0 | F1 | F2 | F3 | F4 | F5 | F6 | F7 | F8 | F9 | F10 | F11 | F12 | F13 | F14 | F15 | F16 | F17 | F18 | F19 | F20 | F21 | F22 | F23 | F24 | F25 | F26 | F27 | F28 | F29 | F30 | F31
  deriving DecidableEq, Repr, Inhabited

namespace Mreg

/-- `Machregs.all_mregs` -/
def allMregs : List Mreg :=
  [.R0, .R1, .R2, .R3, .R4, .R5, .R6, .R7, .R8, .R9, .R10, .R11, .R12, .R13, .R14, .R15, .R17, .R19, .R20, .R21, .R22, .R23, .R24, .R25, .R26, .R27, .R28, .R29, .F0, .F1, .F2, .F3, .F4, .F5, .F6, .F7, .F8, .F9, .F10, .F11, .F12, .F13, .F14, .F15, .F16, .F17, .F18, .F19, .F20, .F21, .F22, .F23, .F24, .F25, .F26, .F27, .F28, .F29, .F30, .F31]

/-- `Machregs.all_mregs_complete` -/
theorem allMregs_complete (r : Mreg) : r ∈ allMregs := by
  cases r <;> decide

/-- `Machregs.mreg_type` -/
def type (_r : Mreg) : ATyp := .Tany64

/-- `Machregs.IndexedMreg.index` -/
def index : Mreg → Positive
  | .R0 => Positive.ofNat 1
  | .R1 => Positive.ofNat 2
  | .R2 => Positive.ofNat 3
  | .R3 => Positive.ofNat 4
  | .R4 => Positive.ofNat 5
  | .R5 => Positive.ofNat 6
  | .R6 => Positive.ofNat 7
  | .R7 => Positive.ofNat 8
  | .R8 => Positive.ofNat 9
  | .R9 => Positive.ofNat 10
  | .R10 => Positive.ofNat 11
  | .R11 => Positive.ofNat 12
  | .R12 => Positive.ofNat 13
  | .R13 => Positive.ofNat 14
  | .R14 => Positive.ofNat 15
  | .R15 => Positive.ofNat 16
  | .R17 => Positive.ofNat 17
  | .R19 => Positive.ofNat 19
  | .R20 => Positive.ofNat 20
  | .R21 => Positive.ofNat 21
  | .R22 => Positive.ofNat 22
  | .R23 => Positive.ofNat 23
  | .R24 => Positive.ofNat 24
  | .R25 => Positive.ofNat 25
  | .R26 => Positive.ofNat 26
  | .R27 => Positive.ofNat 27
  | .R28 => Positive.ofNat 28
  | .R29 => Positive.ofNat 29
  | .F0 => Positive.ofNat 32
  | .F1 => Positive.ofNat 33
  | .F2 => Positive.ofNat 34
  | .F3 => Positive.ofNat 35
  | .F4 => Positive.ofNat 36
  | .F5 => Positive.ofNat 37
  | .F6 => Positive.ofNat 38
  | .F7 => Positive.ofNat 39
  | .F8 => Positive.ofNat 40
  | .F9 => Positive.ofNat 41
  | .F10 => Positive.ofNat 42
  | .F11 => Positive.ofNat 43
  | .F12 => Positive.ofNat 44
  | .F13 => Positive.ofNat 45
  | .F14 => Positive.ofNat 46
  | .F15 => Positive.ofNat 47
  | .F16 => Positive.ofNat 48
  | .F17 => Positive.ofNat 49
  | .F18 => Positive.ofNat 50
  | .F19 => Positive.ofNat 51
  | .F20 => Positive.ofNat 52
  | .F21 => Positive.ofNat 53
  | .F22 => Positive.ofNat 54
  | .F23 => Positive.ofNat 55
  | .F24 => Positive.ofNat 56
  | .F25 => Positive.ofNat 57
  | .F26 => Positive.ofNat 58
  | .F27 => Positive.ofNat 59
  | .F28 => Positive.ofNat 60
  | .F29 => Positive.ofNat 61
  | .F30 => Positive.ofNat 62
  | .F31 => Positive.ofNat 63

/-- Inverse of `index` (used to prove its injectivity). -/
def ofIndexNat : Nat → Option Mreg
  | 1 => some .R0
  | 2 => some .R1
  | 3 => some .R2
  | 4 => some .R3
  | 5 => some .R4
  | 6 => some .R5
  | 7 => some .R6
  | 8 => some .R7
  | 9 => some .R8
  | 10 => some .R9
  | 11 => some .R10
  | 12 => some .R11
  | 13 => some .R12
  | 14 => some .R13
  | 15 => some .R14
  | 16 => some .R15
  | 17 => some .R17
  | 19 => some .R19
  | 20 => some .R20
  | 21 => some .R21
  | 22 => some .R22
  | 23 => some .R23
  | 24 => some .R24
  | 25 => some .R25
  | 26 => some .R26
  | 27 => some .R27
  | 28 => some .R28
  | 29 => some .R29
  | 32 => some .F0
  | 33 => some .F1
  | 34 => some .F2
  | 35 => some .F3
  | 36 => some .F4
  | 37 => some .F5
  | 38 => some .F6
  | 39 => some .F7
  | 40 => some .F8
  | 41 => some .F9
  | 42 => some .F10
  | 43 => some .F11
  | 44 => some .F12
  | 45 => some .F13
  | 46 => some .F14
  | 47 => some .F15
  | 48 => some .F16
  | 49 => some .F17
  | 50 => some .F18
  | 51 => some .F19
  | 52 => some .F20
  | 53 => some .F21
  | 54 => some .F22
  | 55 => some .F23
  | 56 => some .F24
  | 57 => some .F25
  | 58 => some .F26
  | 59 => some .F27
  | 60 => some .F28
  | 61 => some .F29
  | 62 => some .F30
  | 63 => some .F31
  | _ => none

theorem ofIndexNat_index (r : Mreg) : ofIndexNat (index r).toNat = some r := by
  cases r <;> rfl

/-- `Machregs.IndexedMreg.index_inj` -/
theorem index_inj (r1 r2 : Mreg) (h : index r1 = index r2) : r1 = r2 := by
  have := ofIndexNat_index r1
  rw [h, ofIndexNat_index r2] at this
  exact (Option.some.inj this).symm

/-- `Machregs.is_stack_reg` -/
def isStackReg (_r : Mreg) : Bool := false

/-- `Machregs.register_names` -/
def registerNames : List (String × Mreg) :=
  [("X0", .R0), ("X1", .R1), ("X2", .R2), ("X3", .R3),
   ("X4", .R4), ("X5", .R5), ("X6", .R6), ("X7", .R7),
   ("X8", .R8), ("X9", .R9), ("X10", .R10), ("X11", .R11),
   ("X12", .R12), ("X13", .R13), ("X14", .R14), ("X15", .R15),
   ("X17", .R17), ("X19", .R19), ("X20", .R20), ("X21", .R21),
   ("X22", .R22), ("X23", .R23), ("X24", .R24), ("X25", .R25),
   ("X26", .R26), ("X27", .R27), ("X28", .R28), ("X29", .R29),
   ("D0", .F0), ("D1", .F1), ("D2", .F2), ("D3", .F3),
   ("D4", .F4), ("D5", .F5), ("D6", .F6), ("D7", .F7),
   ("D8", .F8), ("D9", .F9), ("D10", .F10), ("D11", .F11),
   ("D12", .F12), ("D13", .F13), ("D14", .F14), ("D15", .F15),
   ("D16", .F16), ("D17", .F17), ("D18", .F18), ("D19", .F19),
   ("D20", .F20), ("D21", .F21), ("D22", .F22), ("D23", .F23),
   ("D24", .F24), ("D25", .F25), ("D26", .F26), ("D27", .F27),
   ("D28", .F28), ("D29", .F29), ("D30", .F30), ("D31", .F31)]

/-- `Machregs.register_aliases` -/
def registerAliases : List (String × Mreg) :=
  [("W0", .R0), ("W1", .R1), ("W2", .R2), ("W3", .R3),
   ("W4", .R4), ("W5", .R5), ("W6", .R6), ("W7", .R7),
   ("W8", .R8), ("W9", .R9), ("W10", .R10), ("W11", .R11),
   ("W12", .R12), ("W13", .R13), ("W14", .R14), ("W15", .R15),
   ("W17", .R17), ("W19", .R19), ("W20", .R20), ("W21", .R21),
   ("W22", .R22), ("W23", .R23), ("W24", .R24), ("W25", .R25),
   ("W26", .R26), ("W27", .R27), ("W28", .R28), ("W29", .R29),
   ("V0", .F0), ("V1", .F1), ("V2", .F2), ("V3", .F3),
   ("V4", .F4), ("V5", .F5), ("V6", .F6), ("V7", .F7),
   ("V8", .F8), ("V9", .F9), ("V10", .F10), ("V11", .F11),
   ("V12", .F12), ("V13", .F13), ("V14", .F14), ("V15", .F15),
   ("V16", .F16), ("V17", .F17), ("V18", .F18), ("V19", .F19),
   ("V20", .F20), ("V21", .F21), ("V22", .F22), ("V23", .F23),
   ("V24", .F24), ("V25", .F25), ("V26", .F26), ("V27", .F27),
   ("V28", .F28), ("V29", .F29), ("V30", .F30), ("V31", .F31),
   ("Q0", .F0), ("Q1", .F1), ("Q2", .F2), ("Q3", .F3),
   ("Q4", .F4), ("Q5", .F5), ("Q6", .F6), ("Q7", .F7),
   ("Q8", .F8), ("Q9", .F9), ("Q10", .F10), ("Q11", .F11),
   ("Q12", .F12), ("Q13", .F13), ("Q14", .F14), ("Q15", .F15),
   ("Q16", .F16), ("Q17", .F17), ("Q18", .F18), ("Q19", .F19),
   ("Q20", .F20), ("Q21", .F21), ("Q22", .F22), ("Q23", .F23),
   ("Q24", .F24), ("Q25", .F25), ("Q26", .F26), ("Q27", .F27),
   ("Q28", .F28), ("Q29", .F29), ("Q30", .F30), ("Q31", .F31),
   ("S0", .F0), ("S1", .F1), ("S2", .F2), ("S3", .F3),
   ("S4", .F4), ("S5", .F5), ("S6", .F6), ("S7", .F7),
   ("S8", .F8), ("S9", .F9), ("S10", .F10), ("S11", .F11),
   ("S12", .F12), ("S13", .F13), ("S14", .F14), ("S15", .F15),
   ("S16", .F16), ("S17", .F17), ("S18", .F18), ("S19", .F19),
   ("S20", .F20), ("S21", .F21), ("S22", .F22), ("S23", .F23),
   ("S24", .F24), ("S25", .F25), ("S26", .F26), ("S27", .F27),
   ("S28", .F28), ("S29", .F29), ("S30", .F30), ("S31", .F31),
   ("H0", .F0), ("H1", .F1), ("H2", .F2), ("H3", .F3),
   ("H4", .F4), ("H5", .F5), ("H6", .F6), ("H7", .F7),
   ("H8", .F8), ("H9", .F9), ("H10", .F10), ("H11", .F11),
   ("H12", .F12), ("H13", .F13), ("H14", .F14), ("H15", .F15),
   ("H16", .F16), ("H17", .F17), ("H18", .F18), ("H19", .F19),
   ("H20", .F20), ("H21", .F21), ("H22", .F22), ("H23", .F23),
   ("H24", .F24), ("H25", .F25), ("H26", .F26), ("H27", .F27),
   ("H28", .F28), ("H29", .F29), ("H30", .F30), ("H31", .F31),
   ("B0", .F0), ("B1", .F1), ("B2", .F2), ("B3", .F3),
   ("B4", .F4), ("B5", .F5), ("B6", .F6), ("B7", .F7),
   ("B8", .F8), ("B9", .F9), ("B10", .F10), ("B11", .F11),
   ("B12", .F12), ("B13", .F13), ("B14", .F14), ("B15", .F15),
   ("B16", .F16), ("B17", .F17), ("B18", .F18), ("B19", .F19),
   ("B20", .F20), ("B21", .F21), ("B22", .F22), ("B23", .F23),
   ("B24", .F24), ("B25", .F25), ("B26", .F26), ("B27", .F27),
   ("B28", .F28), ("B29", .F29), ("B30", .F30), ("B31", .F31)]

/-- `Machregs.register_by_name` -/
def registerByName (s : String) : Option Mreg :=
  match registerNames.lookup s with
  | some res => some res
  | none => registerAliases.lookup s

end Mreg

/-- `Machregs.destroyed_by_op` -/
def destroyedByOp : Operation → List Mreg
  | .Oshrximm _ | .Oshrlximm _ => [.R17]
  | _ => []

/-- `Machregs.destroyed_by_load` -/
def destroyedByLoad (_chunk : Chunk) (_addr : Addressing) : List Mreg := []
/-- `Machregs.destroyed_by_store` -/
def destroyedByStore (_chunk : Chunk) (_addr : Addressing) : List Mreg := []
/-- `Machregs.destroyed_by_cond` -/
def destroyedByCond (_cond : Condition) : List Mreg := []
/-- `Machregs.destroyed_by_jumptable` -/
def destroyedByJumptable : List Mreg := [.R17]

/-- `Machregs.destroyed_by_clobber` -/
def destroyedByClobber : List String → List Mreg
  | [] => []
  | c1 :: cl =>
      match Mreg.registerByName c1 with
      | some r => r :: destroyedByClobber cl
      | none => destroyedByClobber cl

/-- `Machregs.destroyed_by_builtin` -/
def destroyedByBuiltin : ExtFun → List Mreg
  | .EF_memcpy _ _ => [.R14, .R15, .R17]
  | .EF_inline_asm _ _ clob => destroyedByClobber clob
  | _ => []

/-- `Machregs.destroyed_by_setstack` -/
def destroyedBySetstack (_ty : ATyp) : List Mreg := []
/-- `Machregs.destroyed_at_function_entry` -/
def destroyedAtFunctionEntry : List Mreg := [.R15]
/-- `Machregs.destroyed_at_indirect_call` -/
def destroyedAtIndirectCall : List Mreg := []
/-- `Machregs.temp_for_parent_frame` -/
def tempForParentFrame : Mreg := .R15

/-- `Machregs.mregs_for_operation` -/
def mregsForOperation (_op : Operation) : List (Option Mreg) × Option Mreg := ([], none)
/-- `Machregs.mregs_for_builtin` -/
def mregsForBuiltin (_ef : ExtFun) : List (Option Mreg) × List (Option Mreg) := ([], [])

/-- `Machregs.two_address_op` -/
def twoAddressOp : Operation → Bool
  | .Olowlong => true
  | _ => false

/-- `Machregs.builtin_constraints` -/
def builtinConstraints : ExtFun → List BuiltinArgConstraint
  | .EF_vload _ => [.OK_addressing]
  | .EF_vstore _ => [.OK_addressing, .OK_default]
  | .EF_memcpy _ _ => [.OK_addrstack, .OK_addrstack]
  | .EF_annot _ _ targs => targs.map (fun _ => .OK_all)
  | .EF_debug _ _ targs => targs.map (fun _ => .OK_all)
  | _ => []

end CC
