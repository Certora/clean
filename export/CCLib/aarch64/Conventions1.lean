/-
  The part of `aarch64/Conventions1.v` used by the C front-end passes:
  whether a function result or parameter of a small integer type must be
  normalized (sign- or zero-extended) by the receiver.

  Rocq's `Archi.abi` is a `Parameter` set by the OCaml driver; here it is an
  explicit argument of type `AbiKind`.
-/
import CCLib.common.AST

namespace CC
namespace Conventions1

/-- `Archi.abi_kind` (aarch64): the standard AAPCS64 ABI or Apple's variant. -/
inductive AbiKind where
  | AAPCS64
  | Apple
  deriving DecidableEq, Repr

/-- `Conventions1.return_value_needs_normalization` (aarch64). -/
def returnValueNeedsNormalization (abi : AbiKind) (t : XType) : Bool :=
  match abi with
  | .Apple => false
  | .AAPCS64 =>
    match t with
    | .Xbool | .Xint8signed | .Xint8unsigned | .Xint16signed | .Xint16unsigned => true
    | _ => false

/-- `Conventions1.parameter_needs_normalization` (aarch64). -/
def parameterNeedsNormalization (abi : AbiKind) (t : XType) : Bool :=
  returnValueNeedsNormalization abi t

end Conventions1
end CC
