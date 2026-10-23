/-
  Multi-way branches — port of the semantic part of `common/Switch.v`
  (`table`, `switch_target`, `switch_argument`).

  Also ported: comparison trees (`comptree`, `comptree_match`) and their
  validator (`split_lt`, `split_eq`, `split_between`, `refine_low_bound`,
  `refine_high_bound`, `validate_jumptable`, `validate`,
  `validate_switch`), used by `Selection`.  The correctness proof of the
  validator (`validate_switch_correct`) is in `SwitchProof.lean`.
-/
import CCLib.common.Values
import CCLib.lib.Maps

namespace CC
namespace Switch

/-- `Switch.table` -/
abbrev Table := List (Z × Nat)

/-- `Switch.switch_target` -/
def switchTarget (n : Z) (dfl : Nat) : Table → Nat
  | [] => dfl
  | (key, action) :: rem => if n = key then action else switchTarget n dfl rem

/-- `Switch.switch_argument` -/
inductive SwitchArgument : Bool → Val → Z → Prop where
  | arg32 (i : Integers.Int) : SwitchArgument false (.Vint i) (Integers.Int.unsigned i)
  | arg64 (i : Integers.Int64) : SwitchArgument true (.Vlong i) (Integers.Int64.unsigned i)

theorem switchArgument_determ {b v n1 n2} (h1 : SwitchArgument b v n1)
    (h2 : SwitchArgument b v n2) : n1 = n2 := by
  cases h1 <;> cases h2 <;> rfl

/-- `Switch.comptree` -/
inductive Comptree where
  | CTaction (act : Nat)
  | CTifeq (key : Z) (act : Nat) (cne : Comptree)
  | CTiflt (key : Z) (clt cge : Comptree)
  | CTjumptable (ofs sz : Z) (acts : List Nat) (cother : Comptree)

/-- `Coqlib.list_nth_z` -/
def listNthZ {A : Type} : List A → Z → Option A
  | [], _ => none
  | hd :: tl, n => if n = 0 then some hd else listNthZ tl (n - 1)

section COMPTREE
variable (modulus : Z)

/-- `Switch.comptree_match` -/
def comptreeMatch (n : Z) : Comptree → Option Nat
  | .CTaction act => some act
  | .CTifeq key act t' => if n = key then some act else comptreeMatch n t'
  | .CTiflt key t1 t2 => if n < key then comptreeMatch n t1 else comptreeMatch n t2
  | .CTjumptable ofs sz tbl t' =>
      let delta := (n - ofs) % modulus
      if delta < sz then listNthZ tbl (delta % Integers.Int.modulus) else comptreeMatch n t'

/-- `Switch.split_lt` -/
def splitLt (pivot : Z) : Table → Table × Table
  | [] => ([], [])
  | (key, act) :: rem =>
      let (l, r) := splitLt pivot rem
      if key < pivot then ((key, act) :: l, r) else (l, (key, act) :: r)

/-- `Switch.split_eq` -/
def splitEq (pivot : Z) : Table → Option Nat × Table
  | [] => (none, [])
  | (key, act) :: rem =>
      let (same, others) := splitEq pivot rem
      if key = pivot then (some act, others) else (same, (key, act) :: others)

/-- `Switch.split_between` -/
def splitBetween (dfl : Nat) (ofs sz : Z) : Table → ZMap Nat × Table
  | [] => (ZMap.init dfl, [])
  | (key, act) :: rem =>
      let (inside, outside) := splitBetween dfl ofs sz rem
      if (key - ofs) % modulus < sz then (ZMap.set key act inside, outside)
      else (inside, (key, act) :: outside)

/-- `Switch.refine_low_bound` -/
def refineLowBound (v lo : Z) : Z := if v = lo then lo + 1 else lo

/-- `Switch.refine_high_bound` -/
def refineHighBound (v hi : Z) : Z := if v = hi then hi - 1 else hi

/-- `Switch.validate_jumptable` -/
def validateJumptable (cases : ZMap Nat) : List Nat → Z → Bool
  | [], _ => true
  | act :: rem, n => act == ZMap.get n cases && validateJumptable cases rem (n + 1)

/-- `Switch.validate` -/
def validate (default : Nat) : Table → Comptree → Z → Z → Bool
  | cases, .CTaction act, lo, hi =>
      match cases with
      | [] => act == default
      | (key1, act1) :: _ => decide (key1 = lo) && decide (lo = hi) && act == act1
  | cases, .CTifeq pivot act t', lo, hi =>
      decide (0 ≤ pivot) && decide (pivot < modulus) &&
      match splitEq pivot cases with
      | (none, _) => false
      | (some act', others) =>
          act == act' && validate default others t' (refineLowBound pivot lo)
            (refineHighBound pivot hi)
  | cases, .CTiflt pivot t1 t2, lo, hi =>
      decide (0 ≤ pivot) && decide (pivot < modulus) &&
      match splitLt pivot cases with
      | (lcases, rcases) =>
          validate default lcases t1 lo (pivot - 1) && validate default rcases t2 pivot hi
  | cases, .CTjumptable ofs sz tbl t', lo, hi =>
      let tblLen : Z := tbl.length
      decide (0 ≤ ofs) && decide (ofs < modulus) && decide (0 ≤ sz) && decide (sz < modulus) &&
      decide (ofs + sz ≤ modulus) && decide (sz ≤ tblLen) && decide (sz < Integers.Int.modulus) &&
      match splitBetween modulus default ofs sz cases with
      | (inside, outside) =>
          validateJumptable inside tbl ofs && validate default outside t' lo hi

/-- `Switch.validate_switch` -/
def validateSwitch (default : Nat) (cases : Table) (t : Comptree) : Bool :=
  validate modulus default cases t 0 (modulus - 1)

end COMPTREE

end Switch
end CC
