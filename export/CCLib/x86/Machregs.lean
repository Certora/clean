/-
  Machine registers of the x86 back end — port of `x86/Machregs.v`.

  Differences from Rocq: `IndexedMreg.index` is `Mreg.index`; the `Finite`
  instance is the list `allMregs` with its completeness lemma.
  `Archi.ptr64` is `true` in this port (x86-64), so the integer registers
  have type `Tany64` and `R8`–`R15`, `X8`–`X15` are available.
-/
import CCLib.x86.Op
import CCLib.lib.Positive

namespace CC
namespace X86

open Op

/-- `Machregs.mreg` (x86): the allocatable integer and SSE registers, and the
top of the x87 stack `FP0`. -/
inductive Mreg where
  | AX | BX | CX | DX | SI | DI | BP
  | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15
  | X0 | X1 | X2 | X3 | X4 | X5 | X6 | X7
  | X8 | X9 | X10 | X11 | X12 | X13 | X14 | X15
  | FP0
  deriving DecidableEq, Repr, Inhabited

namespace Mreg

/-- `Machregs.all_mregs` -/
def allMregs : List Mreg :=
  [.AX, .BX, .CX, .DX, .SI, .DI, .BP, .R8, .R9, .R10, .R11, .R12, .R13, .R14, .R15, .X0, .X1, .X2, .X3, .X4, .X5, .X6, .X7, .X8, .X9, .X10, .X11, .X12, .X13, .X14, .X15, .FP0]

/-- `Machregs.all_mregs_complete` -/
theorem allMregs_complete (r : Mreg) : r ∈ allMregs := by
  cases r <;> decide

/-- `Machregs.mreg_type` -/
def type : Mreg → ATyp
  | .AX | .BX | .CX | .DX | .SI | .DI | .BP => if Archi.ptr64 then .Tany64 else .Tany32
  | _ => .Tany64

/-- On x86-64 (`Archi.ptr64 = true`) every machine register has type `Tany64`. -/
theorem type_eq_any64 (r : Mreg) : type r = .Tany64 := by
  cases r <;> rfl

/-- `Machregs.IndexedMreg.index` -/
def index : Mreg → Positive
  | .AX => Positive.ofNat 1
  | .BX => Positive.ofNat 2
  | .CX => Positive.ofNat 3
  | .DX => Positive.ofNat 4
  | .SI => Positive.ofNat 5
  | .DI => Positive.ofNat 6
  | .BP => Positive.ofNat 7
  | .R8 => Positive.ofNat 8
  | .R9 => Positive.ofNat 9
  | .R10 => Positive.ofNat 10
  | .R11 => Positive.ofNat 11
  | .R12 => Positive.ofNat 12
  | .R13 => Positive.ofNat 13
  | .R14 => Positive.ofNat 14
  | .R15 => Positive.ofNat 15
  | .X0 => Positive.ofNat 16
  | .X1 => Positive.ofNat 17
  | .X2 => Positive.ofNat 18
  | .X3 => Positive.ofNat 19
  | .X4 => Positive.ofNat 20
  | .X5 => Positive.ofNat 21
  | .X6 => Positive.ofNat 22
  | .X7 => Positive.ofNat 23
  | .X8 => Positive.ofNat 24
  | .X9 => Positive.ofNat 25
  | .X10 => Positive.ofNat 26
  | .X11 => Positive.ofNat 27
  | .X12 => Positive.ofNat 28
  | .X13 => Positive.ofNat 29
  | .X14 => Positive.ofNat 30
  | .X15 => Positive.ofNat 31
  | .FP0 => Positive.ofNat 32

/-- Inverse of `index` (used to prove `index_inj`). -/
def ofIndexNat : Nat → Option Mreg
  | 1 => some .AX
  | 2 => some .BX
  | 3 => some .CX
  | 4 => some .DX
  | 5 => some .SI
  | 6 => some .DI
  | 7 => some .BP
  | 8 => some .R8
  | 9 => some .R9
  | 10 => some .R10
  | 11 => some .R11
  | 12 => some .R12
  | 13 => some .R13
  | 14 => some .R14
  | 15 => some .R15
  | 16 => some .X0
  | 17 => some .X1
  | 18 => some .X2
  | 19 => some .X3
  | 20 => some .X4
  | 21 => some .X5
  | 22 => some .X6
  | 23 => some .X7
  | 24 => some .X8
  | 25 => some .X9
  | 26 => some .X10
  | 27 => some .X11
  | 28 => some .X12
  | 29 => some .X13
  | 30 => some .X14
  | 31 => some .X15
  | 32 => some .FP0
  | _ => none

theorem ofIndexNat_index (r : Mreg) : ofIndexNat (index r).toNat = some r := by
  cases r <;> rfl

/-- `Machregs.IndexedMreg.index_inj` -/
theorem index_inj (r1 r2 : Mreg) (h : index r1 = index r2) : r1 = r2 := by
  have := ofIndexNat_index r1
  rw [h, ofIndexNat_index r2] at this
  exact (Option.some.inj this).symm

/-- `Machregs.is_stack_reg` -/
def isStackReg : Mreg → Bool
  | .FP0 => true
  | _ => false

/-- `Machregs.register_names` -/
def registerNames : List (String × Mreg) :=
  [("RAX", .AX),
   ("RBX", .BX),
   ("RCX", .CX),
   ("RDX", .DX),
   ("RSI", .SI),
   ("RDI", .DI),
   ("RBP", .BP),
   ("EAX", .AX),
   ("EBX", .BX),
   ("ECX", .CX),
   ("EDX", .DX),
   ("ESI", .SI),
   ("EDI", .DI),
   ("EBP", .BP),
   ("R8", .R8),
   ("R9", .R9),
   ("R10", .R10),
   ("R11", .R11),
   ("R12", .R12),
   ("R13", .R13),
   ("R14", .R14),
   ("R15", .R15),
   ("XMM0", .X0),
   ("XMM1", .X1),
   ("XMM2", .X2),
   ("XMM3", .X3),
   ("XMM4", .X4),
   ("XMM5", .X5),
   ("XMM6", .X6),
   ("XMM7", .X7),
   ("XMM8", .X8),
   ("XMM9", .X9),
   ("XMM10", .X10),
   ("XMM11", .X11),
   ("XMM12", .X12),
   ("XMM13", .X13),
   ("XMM14", .X14),
   ("XMM15", .X15),
   ("ST0", .FP0)]

/-- `Machregs.register_by_name` -/
def registerByName (s : String) : Option Mreg := registerNames.lookup s

end Mreg

/-- `Machregs.destroyed_by_op` -/
def destroyedByOp : Operation → List Mreg
  | .Ocast8signed | .Ocast8unsigned => [.AX]
  | .Omulhs | .Omulhu | .Odiv | .Odivu | .Omod | .Omodu => [.AX, .DX]
  | .Oshrximm _ => [.CX]
  | .Omullhs | .Omullhu | .Odivl | .Odivlu | .Omodl | .Omodlu => [.AX, .DX]
  | .Oshrxlimm _ => [.DX]
  | .Ocmp _ => [.AX, .CX]
  | _ => []

/-- `Machregs.destroyed_by_load` -/
def destroyedByLoad (_chunk : Chunk) (_addr : Addressing) : List Mreg := []

/-- `Machregs.destroyed_by_store` -/
def destroyedByStore (chunk : Chunk) (_addr : Addressing) : List Mreg :=
  match chunk with
  | .Mbool | .Mint8signed | .Mint8unsigned => if Archi.ptr64 then [] else [.AX, .CX]
  | _ => []

/-- `Machregs.destroyed_by_cond` -/
def destroyedByCond (_cond : Condition) : List Mreg := []
/-- `Machregs.destroyed_by_jumptable` -/
def destroyedByJumptable : List Mreg := [.AX, .DX]

/-- `Machregs.destroyed_by_clobber` -/
def destroyedByClobber : List String → List Mreg
  | [] => []
  | c1 :: cl =>
      match Mreg.registerByName c1 with
      | some r => r :: destroyedByClobber cl
      | none => destroyedByClobber cl

/-- `Machregs.destroyed_by_builtin` -/
def destroyedByBuiltin : ExtFun → List Mreg
  | .EF_memcpy sz _ => if sz ≤ 32 then [.CX, .X7] else [.CX, .SI, .DI]
  | .EF_vstore .Mint8unsigned | .EF_vstore .Mint8signed =>
      if Archi.ptr64 then [] else [.AX, .CX]
  | .EF_builtin name _ =>
      if name = "__builtin_va_start" then [.AX]
      else if name = "__builtin_write16_reversed" || name = "__builtin_write32_reversed"
      then [.CX, .DX]
      else []
  | .EF_inline_asm _ _ clob => destroyedByClobber clob
  | _ => []

/-- `Machregs.destroyed_at_function_entry` -/
def destroyedAtFunctionEntry : List Mreg := [.AX, .FP0]

/-- `Machregs.destroyed_by_setstack` -/
def destroyedBySetstack : ATyp → List Mreg
  | .Tfloat | .Tsingle => [.FP0]
  | _ => []

/-- `Machregs.destroyed_at_indirect_call` -/
def destroyedAtIndirectCall : List Mreg := [.AX]
/-- `Machregs.temp_for_parent_frame` -/
def tempForParentFrame : Mreg := .AX

/-- `Machregs.mregs_for_operation` -/
def mregsForOperation : Operation → List (Option Mreg) × Option Mreg
  | .Omulhs | .Omulhu => ([some .AX, none], some .DX)
  | .Odiv | .Odivu => ([some .AX, some .CX], some .AX)
  | .Omod | .Omodu => ([some .AX, some .CX], some .DX)
  | .Oshl | .Oshr | .Oshru => ([none, some .CX], none)
  | .Oshrximm _ => ([some .AX], some .AX)
  | .Omullhs | .Omullhu => ([some .AX, none], some .DX)
  | .Odivl | .Odivlu => ([some .AX, some .CX], some .AX)
  | .Omodl | .Omodlu => ([some .AX, some .CX], some .DX)
  | .Oshll | .Oshrl | .Oshrlu => ([none, some .CX], none)
  | .Oshrxlimm _ => ([some .AX], some .AX)
  | _ => ([], none)

/-- `Machregs.mregs_for_builtin` -/
def mregsForBuiltin : ExtFun → List (Option Mreg) × List (Option Mreg)
  | .EF_memcpy sz _ =>
      if sz ≤ 32 then ([some .AX, some .DX], []) else ([some .DI, some .SI], [])
  | .EF_builtin name _ =>
      if name = "__builtin_negl" then
        ([some .DX, some .AX], [some .DX, some .AX])
      else if name = "__builtin_addl" || name = "__builtin_subl" then
        ([some .DX, some .AX, some .CX, some .BX], [some .DX, some .AX])
      else if name = "__builtin_mull" then
        ([some .AX, some .DX], [some .DX, some .AX])
      else if name = "__builtin_va_start" then
        ([some .DX], [])
      else if !Archi.ptr64 && name = "__builtin_bswap64" then
        ([some .AX, some .DX], [some .DX, some .AX])
      else ([], [])
  | _ => ([], [])

/-- `Machregs.two_address_op`: the first argument and the result must be in
the same location. -/
def twoAddressOp : Operation → Bool
  | .Oneg | .Osub | .Omul | .Omulimm _ | .Oand | .Oandimm _ | .Oor | .Oorimm _ | .Oxor | .Oxorimm _ | .Onot | .Oshl | .Oshlimm _ | .Oshr | .Oshrimm _ | .Oshru | .Oshruimm _ | .Ororimm _ | .Oshldimm _ | .Omakelong | .Olowlong | .Ohighlong | .Onegl | .Oaddlimm _ | .Osubl | .Omull | .Omullimm _ | .Oandl | .Oandlimm _ | .Oorl | .Oorlimm _ | .Oxorl | .Oxorlimm _ | .Onotl | .Oshll | .Oshllimm _ | .Oshrl | .Oshrlimm _ | .Oshrlu | .Oshrluimm _ | .Ororlimm _ | .Onegf | .Oabsf | .Oaddf | .Osubf | .Omulf | .Odivf | .Omaxf | .Ominf | .Onegfs | .Oabsfs | .Oaddfs | .Osubfs | .Omulfs | .Odivfs | .Osel _ _ => true
  | _ => false

/-- `Machregs.builtin_constraints` -/
def builtinConstraints : ExtFun → List BuiltinArgConstraint
  | .EF_vload _ => [.OK_addressing]
  | .EF_vstore _ => [.OK_addressing, .OK_default]
  | .EF_memcpy _ _ => [.OK_addrstack, .OK_addrstack]
  | .EF_annot _ _ targs => targs.map (fun _ => .OK_all)
  | .EF_debug _ _ targs => targs.map (fun _ => .OK_all)
  | _ => []

end X86
end CC
