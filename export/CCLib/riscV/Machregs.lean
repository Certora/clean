/-
  Machine registers of the RISC-V back end — port of `riscV/Machregs.v`.

  Differences from Rocq: `IndexedMreg.index` is `Mreg.index`; the `Finite`
  instance is the list `allMregs` with its completeness lemma.
  `Archi.ptr64` is `true` in this port (RV64), so the integer registers have
  type `Tany64`.  The zero, link, stack, global and thread pointers
  (`x0`–`x4`) and the assembler temporary `x31` are not allocatable.
-/
import CCLib.riscV.Op
import CCLib.lib.Positive

namespace CC
namespace RiscV

open Op

/-- `Machregs.mreg` (RISC-V): allocatable integer registers `x5`–`x30` and
double-precision float registers `f0`–`f31`. -/
inductive Mreg where
  | R5 | R6 | R7 | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15 | R16 | R17 | R18 | R19 | R20 | R21 | R22 | R23 | R24 | R25 | R26 | R27 | R28 | R29 | R30
  | F0 | F1 | F2 | F3 | F4 | F5 | F6 | F7 | F8 | F9 | F10 | F11 | F12 | F13 | F14 | F15 | F16 | F17 | F18 | F19 | F20 | F21 | F22 | F23 | F24 | F25 | F26 | F27 | F28 | F29 | F30 | F31
  deriving DecidableEq, Repr, Inhabited

namespace Mreg

/-- `Machregs.all_mregs` -/
def allMregs : List Mreg :=
  [.R5, .R6, .R7, .R8, .R9, .R10, .R11, .R12, .R13, .R14, .R15, .R16, .R17, .R18, .R19, .R20, .R21, .R22, .R23, .R24, .R25, .R26, .R27, .R28, .R29, .R30, .F0, .F1, .F2, .F3, .F4, .F5, .F6, .F7, .F8, .F9, .F10, .F11, .F12, .F13, .F14, .F15, .F16, .F17, .F18, .F19, .F20, .F21, .F22, .F23, .F24, .F25, .F26, .F27, .F28, .F29, .F30, .F31]

/-- `Machregs.all_mregs_complete` -/
theorem allMregs_complete (r : Mreg) : r ∈ allMregs := by
  cases r <;> decide

/-- `Machregs.mreg_type` -/
def type : Mreg → ATyp
  | .R5 | .R6 | .R7 | .R8 | .R9 | .R10 | .R11 | .R12 | .R13 | .R14 | .R15 | .R16 | .R17 | .R18 | .R19 | .R20 | .R21 | .R22 | .R23 | .R24 | .R25 | .R26 | .R27 | .R28 | .R29 | .R30 =>
      if Archi.ptr64 then .Tany64 else .Tany32
  | _ => .Tany64

/-- On RV64 (`Archi.ptr64 = true`) every machine register has type `Tany64`. -/
theorem type_eq_any64 (r : Mreg) : type r = .Tany64 := by
  cases r <;> rfl

/-- `Machregs.IndexedMreg.index` -/
def index : Mreg → Positive
  | .R5 => Positive.ofNat 1
  | .R6 => Positive.ofNat 2
  | .R7 => Positive.ofNat 3
  | .R8 => Positive.ofNat 4
  | .R9 => Positive.ofNat 5
  | .R10 => Positive.ofNat 6
  | .R11 => Positive.ofNat 7
  | .R12 => Positive.ofNat 8
  | .R13 => Positive.ofNat 9
  | .R14 => Positive.ofNat 10
  | .R15 => Positive.ofNat 11
  | .R16 => Positive.ofNat 12
  | .R17 => Positive.ofNat 13
  | .R18 => Positive.ofNat 14
  | .R19 => Positive.ofNat 15
  | .R20 => Positive.ofNat 16
  | .R21 => Positive.ofNat 17
  | .R22 => Positive.ofNat 18
  | .R23 => Positive.ofNat 19
  | .R24 => Positive.ofNat 20
  | .R25 => Positive.ofNat 21
  | .R26 => Positive.ofNat 22
  | .R27 => Positive.ofNat 23
  | .R28 => Positive.ofNat 24
  | .R29 => Positive.ofNat 25
  | .R30 => Positive.ofNat 26
  | .F0 => Positive.ofNat 28
  | .F1 => Positive.ofNat 29
  | .F2 => Positive.ofNat 30
  | .F3 => Positive.ofNat 31
  | .F4 => Positive.ofNat 32
  | .F5 => Positive.ofNat 33
  | .F6 => Positive.ofNat 34
  | .F7 => Positive.ofNat 35
  | .F8 => Positive.ofNat 36
  | .F9 => Positive.ofNat 37
  | .F10 => Positive.ofNat 38
  | .F11 => Positive.ofNat 39
  | .F12 => Positive.ofNat 40
  | .F13 => Positive.ofNat 41
  | .F14 => Positive.ofNat 42
  | .F15 => Positive.ofNat 43
  | .F16 => Positive.ofNat 44
  | .F17 => Positive.ofNat 45
  | .F18 => Positive.ofNat 46
  | .F19 => Positive.ofNat 47
  | .F20 => Positive.ofNat 48
  | .F21 => Positive.ofNat 49
  | .F22 => Positive.ofNat 50
  | .F23 => Positive.ofNat 51
  | .F24 => Positive.ofNat 52
  | .F25 => Positive.ofNat 53
  | .F26 => Positive.ofNat 54
  | .F27 => Positive.ofNat 55
  | .F28 => Positive.ofNat 56
  | .F29 => Positive.ofNat 57
  | .F30 => Positive.ofNat 58
  | .F31 => Positive.ofNat 59

/-- Inverse of `index` (used to prove `index_inj`). -/
def ofIndexNat : Nat → Option Mreg
  | 1 => some .R5
  | 2 => some .R6
  | 3 => some .R7
  | 4 => some .R8
  | 5 => some .R9
  | 6 => some .R10
  | 7 => some .R11
  | 8 => some .R12
  | 9 => some .R13
  | 10 => some .R14
  | 11 => some .R15
  | 12 => some .R16
  | 13 => some .R17
  | 14 => some .R18
  | 15 => some .R19
  | 16 => some .R20
  | 17 => some .R21
  | 18 => some .R22
  | 19 => some .R23
  | 20 => some .R24
  | 21 => some .R25
  | 22 => some .R26
  | 23 => some .R27
  | 24 => some .R28
  | 25 => some .R29
  | 26 => some .R30
  | 28 => some .F0
  | 29 => some .F1
  | 30 => some .F2
  | 31 => some .F3
  | 32 => some .F4
  | 33 => some .F5
  | 34 => some .F6
  | 35 => some .F7
  | 36 => some .F8
  | 37 => some .F9
  | 38 => some .F10
  | 39 => some .F11
  | 40 => some .F12
  | 41 => some .F13
  | 42 => some .F14
  | 43 => some .F15
  | 44 => some .F16
  | 45 => some .F17
  | 46 => some .F18
  | 47 => some .F19
  | 48 => some .F20
  | 49 => some .F21
  | 50 => some .F22
  | 51 => some .F23
  | 52 => some .F24
  | 53 => some .F25
  | 54 => some .F26
  | 55 => some .F27
  | 56 => some .F28
  | 57 => some .F29
  | 58 => some .F30
  | 59 => some .F31
  | _ => none

theorem ofIndexNat_index (r : Mreg) : ofIndexNat (index r).toNat = some r := by
  cases r <;> rfl

/-- `Machregs.IndexedMreg.index_inj` -/
theorem index_inj (r1 r2 : Mreg) (h : index r1 = index r2) : r1 = r2 := by
  have := ofIndexNat_index r1
  rw [h, ofIndexNat_index r2] at this
  exact (Option.some.inj this).symm

/-- `Machregs.is_stack_reg` -/
def isStackReg (_ : Mreg) : Bool := false

/-- `Machregs.register_names` -/
def registerNames : List (String × Mreg) :=
  [("X5", .R5),
   ("X6", .R6),
   ("X7", .R7),
   ("X8", .R8),
   ("X9", .R9),
   ("X10", .R10),
   ("X11", .R11),
   ("X12", .R12),
   ("X13", .R13),
   ("X14", .R14),
   ("X15", .R15),
   ("X16", .R16),
   ("X17", .R17),
   ("X18", .R18),
   ("X19", .R19),
   ("X20", .R20),
   ("X21", .R21),
   ("X22", .R22),
   ("X23", .R23),
   ("X24", .R24),
   ("X25", .R25),
   ("X26", .R26),
   ("X27", .R27),
   ("X28", .R28),
   ("X29", .R29),
   ("X30", .R30),
   ("F0", .F0),
   ("F1", .F1),
   ("F2", .F2),
   ("F3", .F3),
   ("F4", .F4),
   ("F5", .F5),
   ("F6", .F6),
   ("F7", .F7),
   ("F8", .F8),
   ("F9", .F9),
   ("F10", .F10),
   ("F11", .F11),
   ("F12", .F12),
   ("F13", .F13),
   ("F14", .F14),
   ("F15", .F15),
   ("F16", .F16),
   ("F17", .F17),
   ("F18", .F18),
   ("F19", .F19),
   ("F20", .F20),
   ("F21", .F21),
   ("F22", .F22),
   ("F23", .F23),
   ("F24", .F24),
   ("F25", .F25),
   ("F26", .F26),
   ("F27", .F27),
   ("F28", .F28),
   ("F29", .F29),
   ("F30", .F30),
   ("F31", .F31)]

/-- `Machregs.register_by_name` -/
def registerByName (s : String) : Option Mreg := registerNames.lookup s

end Mreg

/-- `Machregs.destroyed_by_op` -/
def destroyedByOp : Operation → List Mreg
  | .Ointoffloat | .Ointuoffloat | .Ointofsingle | .Ointuofsingle
  | .Olongoffloat | .Olonguoffloat | .Olongofsingle | .Olonguofsingle => [.F6]
  | _ => []

/-- `Machregs.destroyed_by_load` -/
def destroyedByLoad (_chunk : Chunk) (_addr : Addressing) : List Mreg := []
/-- `Machregs.destroyed_by_store` -/
def destroyedByStore (_chunk : Chunk) (_addr : Addressing) : List Mreg := []
/-- `Machregs.destroyed_by_cond` -/
def destroyedByCond (_cond : Condition) : List Mreg := []
/-- `Machregs.destroyed_by_jumptable` -/
def destroyedByJumptable : List Mreg := [.R6]

/-- `Machregs.destroyed_by_clobber` -/
def destroyedByClobber : List String → List Mreg
  | [] => []
  | c1 :: cl =>
      match Mreg.registerByName c1 with
      | some r => r :: destroyedByClobber cl
      | none => destroyedByClobber cl

/-- `Machregs.destroyed_by_builtin` -/
def destroyedByBuiltin : ExtFun → List Mreg
  | .EF_inline_asm _ _ clob => destroyedByClobber clob
  | .EF_memcpy _ _ => [.R5, .R6, .R7, .F0]
  | .EF_builtin name _ =>
      if name = "__builtin_clz" || name = "__builtin_clzl" || name = "__builtin_clzll" then
        [.R5, .R8, .R9]
      else if name = "__builtin_ctz" || name = "__builtin_ctzl" || name = "__builtin_ctzll" then
        [.R6, .R8, .R9]
      else []
  | _ => []

/-- `Machregs.destroyed_by_setstack` -/
def destroyedBySetstack (_ : ATyp) : List Mreg := []
/-- `Machregs.destroyed_at_function_entry` -/
def destroyedAtFunctionEntry : List Mreg := [.R30]
/-- `Machregs.temp_for_parent_frame` -/
def tempForParentFrame : Mreg := .R30
/-- `Machregs.destroyed_at_indirect_call` -/
def destroyedAtIndirectCall : List Mreg := [.R10, .R11, .R12, .R13, .R14, .R15, .R16, .R17]

/-- `Machregs.mregs_for_operation` -/
def mregsForOperation (_ : Operation) : List (Option Mreg) × Option Mreg := ([], none)

/-- `Machregs.mregs_for_builtin` -/
def mregsForBuiltin : ExtFun → List (Option Mreg) × List (Option Mreg)
  | .EF_builtin name _ =>
      if !Archi.ptr64 && name = "__builtin_bswap64" then
        ([some .R6, some .R5], [some .R5, some .R6])
      else if name = "__builtin_clz" || name = "__builtin_clzl" then
        ([some .R5], [some .R7])
      else if name = "__builtin_clzll" then
        if Archi.ptr64 then ([some .R5], [some .R7])
        else ([some .R6, some .R5], [some .R7])
      else if name = "__builtin_ctz" || name = "__builtin_ctzl" then
        ([some .R6], [some .R7])
      else if name = "__builtin_ctzll" then
        if Archi.ptr64 then ([some .R6], [some .R7])
        else ([some .R6, some .R5], [some .R7])
      else ([], [])
  | _ => ([], [])

/-- `Machregs.two_address_op`: `Ocast32signed` and `Ocast32unsigned` expand
to no-ops (32-bit integers are kept sign-extended in 64-bit registers). -/
def twoAddressOp : Operation → Bool
  | .Ocast32signed | .Ocast32unsigned => true
  | _ => false

/-- `Machregs.builtin_constraints` -/
def builtinConstraints : ExtFun → List BuiltinArgConstraint
  | .EF_builtin _ _ => []
  | .EF_vload _ => [.OK_addressing]
  | .EF_vstore _ => [.OK_addressing, .OK_default]
  | .EF_memcpy _ _ => [.OK_addrstack, .OK_addrstack]
  | .EF_annot _ _ targs => targs.map (fun _ => .OK_all)
  | .EF_debug _ _ targs => targs.map (fun _ => .OK_all)
  | _ => []

end RiscV
end CC
