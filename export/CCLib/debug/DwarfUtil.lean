/-
  Port of `debug/DwarfUtil.ml`: utility functions for the DWARF debugging
  types.

  The iteration functions `list_iter_with_next` / `entry_iter_sib` take
  monadic callbacks (OCaml uses side effects).  OCaml `int` arithmetic of
  `sizeof_sleb128` (logical shift `lsr` on 63-bit integers) is reproduced
  exactly, including for negative arguments.
-/
import CCLib.debug.DwarfTypes

namespace CC
namespace DwarfUtil

open DwarfTypes

/-- `new_entry`: generate a new entry from a given tag. -/
def new_entry (id : Reference) (tag : DwTag) : DwEntry :=
  { tag := tag, children := [], id := id }

/-- `add_child`: add an entry as child to another entry. -/
def add_child (entry child : DwEntry) : DwEntry :=
  { entry with children := child :: entry.children }

/-- `add_children`: add entries as children to another entry. -/
def add_children (entry : DwEntry) (children : List DwEntry) : DwEntry :=
  { entry with children := entry.children ++ children }

/-- `list_iter_with_next` -/
def list_iter_with_next {m : Type → Type} [Monad m]
    (f : Option Reference → DwEntry → m Unit) : List DwEntry → m Unit
  | [] => pure ()
  | [a] => f none a
  | a :: b :: rest => do f (some b.id) a; list_iter_with_next f (b :: rest)

mutual
/-- inner function `aux` of `entry_iter_sib` -/
def entry_iter_sib_aux {m : Type → Type} [Monad m]
    (f : Option Reference → DwEntry → m Unit) (g : DwEntry → m Unit)
    (sib : Option Reference) : DwEntry → m Unit
  | e@⟨_, cs, _⟩ => do
    f sib e
    entry_iter_sib_list f g cs
    g e
/-- `list_iter_with_next aux`, specialised for termination -/
def entry_iter_sib_list {m : Type → Type} [Monad m]
    (f : Option Reference → DwEntry → m Unit) (g : DwEntry → m Unit) :
    List DwEntry → m Unit
  | [] => pure ()
  | [a] => entry_iter_sib_aux f g none a
  | a :: b :: rest => do
    entry_iter_sib_aux f g (some b.id) a
    entry_iter_sib_list f g (b :: rest)
end

/-- `entry_iter_sib`: iterate over the tree and pass the sibling id. -/
def entry_iter_sib {m : Type → Type} [Monad m]
    (f : Option Reference → DwEntry → m Unit) (g : DwEntry → m Unit)
    (entry : DwEntry) : m Unit :=
  entry_iter_sib_aux f g none entry

mutual
/-- `entry_fold`: fold over the tree in prefix order. -/
def entry_fold {α : Type} (f : α → DwTag → α) (acc : α) : DwEntry → α
  | ⟨t, cs, _⟩ => entry_fold_list f (f acc t) cs
/-- `List.fold_left (entry_fold f)` -/
def entry_fold_list {α : Type} (f : α → DwTag → α) (acc : α) : List DwEntry → α
  | [] => acc
  | c :: cs => entry_fold_list f (entry_fold f acc c) cs
end

/-- `code_of_dw_form`: the code and the corresponding comment for a
    `DW_FORM`. -/
def code_of_dw_form : DwForm → Nat × String
  | .DW_FORM_addr => (0x01, "DW_FORM_addr")
  | .DW_FORM_block2 => (0x03, "DW_FORM_block2")
  | .DW_FORM_block4 => (0x04, "DW_FORM_block4")
  | .DW_FORM_data2 => (0x05, "DW_FORM_data2")
  | .DW_FORM_data4 => (0x06, "DW_FORM_data4")
  | .DW_FORM_data8 => (0x07, "DW_FORM_data8")
  | .DW_FORM_string => (0x08, "DW_FORM_string")
  | .DW_FORM_block => (0x09, "DW_FORM_block")
  | .DW_FORM_block1 => (0x0a, "DW_FORM_block1")
  | .DW_FORM_data1 => (0x0b, "DW_FORM_data1")
  | .DW_FORM_flag => (0x0c, "DW_FORM_flag")
  | .DW_FORM_sdata => (0x0d, "DW_FORM_sdata")
  | .DW_FORM_strp => (0x0e, "DW_FORM_strp")
  | .DW_FORM_udata => (0x0f, "DW_FORM_udata")
  | .DW_FORM_ref_addr => (0x10, "DW_FORM_ref_addr")
  | .DW_FORM_ref1 => (0x11, "DW_FORM_ref1")
  | .DW_FORM_ref2 => (0x12, "DW_FORM_ref2")
  | .DW_FORM_ref4 => (0x13, "DW_FORM_ref4")
  | .DW_FORM_ref8 => (0x14, "DW_FORM_ref8")
  | .DW_FORM_ref_udata => (0x15, "DW_FORM_ref_udata")
  | .DW_FORM_ref_indirect => (0x16, "DW_FORM_ref_indirect")

/-! Attribute form encoding -/
def dw_form_addr : Nat := 0x01
def dw_form_block2 : Nat := 0x03
def dw_form_block4 : Nat := 0x04
def dw_form_data2 : Nat := 0x05
def dw_form_data4 : Nat := 0x06
def dw_form_data8 : Nat := 0x07
def dw_form_string : Nat := 0x08
def dw_form_block : Nat := 0x09
def dw_form_block1 : Nat := 0x0a
def dw_form_data1 : Nat := 0x0b
def dw_form_flag : Nat := 0x0c
def dw_form_sdata : Nat := 0x0d
def dw_form_strp : Nat := 0x0e
def dw_form_udata : Nat := 0x0f
def dw_form_ref_addr : Nat := 0x10
def dw_form_ref1 : Nat := 0x11
def dw_form_ref2 : Nat := 0x12
def dw_form_ref4 : Nat := 0x13
def dw_form_ref8 : Nat := 0x14
def dw_ref_udata : Nat := 0x15
def dw_ref_indirect : Nat := 0x16

/-! Operation encoding -/
def dw_op_addr : Nat := 0x3
def dw_op_plus_uconst : Nat := 0x23
def dw_op_reg0 : Nat := 0x50
def dw_op_regx : Nat := 0x90
def dw_op_bregx : Nat := 0x92
def dw_op_piece : Nat := 0x93

/-- `string_of_dw_tag` -/
def string_of_dw_tag : DwTag → String
  | .DW_TAG_array_type _ => "DW_TAG_array_type"
  | .DW_TAG_compile_unit _ => "DW_TAG_compile_unit"
  | .DW_TAG_base_type _ => "DW_TAG_base_type"
  | .DW_TAG_const_type _ => "DW_TAG_const_type"
  | .DW_TAG_enumeration_type _ => "DW_TAG_enumeration_type"
  | .DW_TAG_enumerator _ => "DW_TAG_enumerator"
  | .DW_TAG_formal_parameter _ => "DW_TAG_formal_parameter"
  | .DW_TAG_label _ => "DW_TAG_label"
  | .DW_TAG_lexical_block _ => "DW_TAG_lexical_block"
  | .DW_TAG_member _ => "DW_TAG_member"
  | .DW_TAG_pointer_type _ => "DW_TAG_pointer_type"
  | .DW_TAG_structure_type _ => "DW_TAG_structure_type"
  | .DW_TAG_subprogram _ => "DW_TAG_subprogram"
  | .DW_TAG_subrange_type _ => "DW_TAG_subrange_type"
  | .DW_TAG_subroutine_type _ => "DW_TAG_subroutine_type"
  | .DW_TAG_typedef _ => "DW_TAG_typedef"
  | .DW_TAG_union_type _ => "DW_TAG_union_type"
  | .DW_TAG_unspecified_parameter _ => "DW_TAG_unspecified_parameter"
  | .DW_TAG_variable _ => "DW_TAG_variable"
  | .DW_TAG_volatile_type _ => "DW_TAG_volatile_type"

/-- OCaml's 63-bit `int`, viewed as an unsigned number (what `lsr` and
    `land 0x7f` see). -/
def ocamlUnsigned (v : Int) : Nat :=
  if v < 0 then (v + 2 ^ 63).toNat else v.toNat

/-- `sizeof_uleb128` on a non-negative number. -/
def sizeof_uleb128_nat (value : Nat) : Nat :=
  if value < 128 then 1 else 1 + sizeof_uleb128_nat (value / 128)
termination_by value
decreasing_by omega

/-- `sizeof_uleb128` (OCaml semantics: `lsr` is a logical shift). -/
def sizeof_uleb128 (value : Int) : Nat :=
  sizeof_uleb128_nat (ocamlUnsigned value)

/-- `sizeof_sleb128` (OCaml semantics: `lsr` is a logical shift). -/
def sizeof_sleb128 (value : Int) : Nat :=
  let u := ocamlUnsigned value
  -- after the first logical shift `value` is non-negative, so the
  -- `!value = -1` exit of the OCaml loop is only reachable before it;
  -- at most 10 iterations are needed for 63 bits.
  go 12 1 (u % 128) (u / 128)
where
  go : Nat → Nat → Nat → Nat → Nat
  | 0, size, _, _ => size
  | fuel + 1, size, byte, value =>
    if value = 0 && byte &&& 0x40 = 0 then size
    else go fuel (size + 1) (value % 128) (value / 128)

/-- `size_of_loc_expr` -/
def size_of_loc_expr : LocationExpression → Nat
  | .DW_OP_bregx a b => 1 + sizeof_uleb128 a + sizeof_sleb128 b
  | .DW_OP_plus_uconst a | .DW_OP_piece a => 1 + sizeof_uleb128 a
  | .DW_OP_reg i => if i < 32 then 1 else 1 + sizeof_uleb128 i

#guard sizeof_uleb128 127 = 1
#guard sizeof_uleb128 128 = 2
#guard sizeof_sleb128 63 = 1
#guard sizeof_sleb128 64 = 2
#guard sizeof_sleb128 (-8) = 10

end DwarfUtil
end CC
