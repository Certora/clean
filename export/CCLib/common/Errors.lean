/-
  The error monad — port of `common/Errors.v` (simplified).

  CompCert's `errmsg` is a list of message items carrying identifiers and
  numbers; here an error carries a plain `String`, which is enough since
  nothing in the semantics or the proofs inspects it.  With that choice
  `Res A` is core's `Except String A` up to the constructor names (`OK` /
  `Error` instead of `ok` / `error`); `Res.toExcept`/`Res.ofExcept` convert.
-/

namespace CC

/-- `Errors.res`: a result, or an error message. -/
inductive Res (A : Type) where
  | OK (a : A)
  | Error (msg : String)
  deriving DecidableEq, Inhabited

namespace Res
def isOK {A : Type} : Res A → Bool
  | .OK _ => true
  | .Error _ => false

def toOption {A : Type} : Res A → Option A
  | .OK a => some a
  | .Error _ => none

def bind {A B : Type} : Res A → (A → Res B) → Res B
  | .OK a, f => f a
  | .Error m, _ => .Error m

instance : Monad Res where
  pure := .OK
  bind := bind
end Res

namespace Res
/-- `Res A` is `Except String A`. -/
def toExcept {A : Type} : Res A → Except String A
  | .OK a => .ok a
  | .Error m => .error m

/-- Inverse of `toExcept`. -/
def ofExcept {A : Type} : Except String A → Res A
  | .ok a => .OK a
  | .error m => .Error m

theorem ofExcept_toExcept {A : Type} (r : Res A) : ofExcept (toExcept r) = r := by
  cases r <;> rfl

theorem toExcept_ofExcept {A : Type} (r : Except String A) : toExcept (ofExcept r) = r := by
  cases r <;> rfl
end Res

end CC
