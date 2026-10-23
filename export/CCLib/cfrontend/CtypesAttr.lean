/-
  Port of the parts of `cfrontend/Ctypes.v` that the OCaml front end
  (`C2C`) uses through `extraction/extraction.v` and that were not yet in the
  port:
  * the attribute operations `attr_union` and `merge_attributes`
    (`change_attributes` is in `CCLib.cfrontend.Ctyping`,
    `remove_attributes` in `CCLib.cfrontend.Ctypes`);
  * `field_zero_or_padding`, `layout_struct_rec` and `layout_struct` (the
    layout of the named fields of a struct, used for debug information);
  * `make_program` (for `Csyntax.Program`, whose record carries the proof
    `prog_comp_env_eq`).

  Difference from Rocq: `attr_alignas` is a `Nat` (log2 of the alignment),
  not an `N`, so `N.max` is `Nat.max`.
-/
import CCLib.cfrontend.Ctyping

namespace CC

/-- `Ctypes.attr_union`: add extra attributes to the top-level attributes of
    a type. -/
def attrUnion (a1 a2 : Attr) : Attr :=
  { attr_volatile := a1.attr_volatile || a2.attr_volatile
    attr_alignas :=
      match a1.attr_alignas, a2.attr_alignas with
      | none, al => al
      | al, none => al
      | some n1, some n2 => some (Nat.max n1 n2) }

/-- `Ctypes.merge_attributes` -/
def mergeAttributes (ty : Ty) (a : Attr) : Ty :=
  Ctyping.changeAttributes (attrUnion a) ty

theorem attrUnion_noattr_left (a : Attr) : attrUnion noattr a = a := by
  cases a with
  | mk v al => cases al <;> simp [attrUnion, noattr]

theorem attrUnion_noattr_right (a : Attr) : attrUnion a noattr = a := by
  cases a with
  | mk v al => cases al <;> simp [attrUnion, noattr]

theorem attrUnion_comm (a1 a2 : Attr) : attrUnion a1 a2 = attrUnion a2 a1 := by
  cases a1 with
  | mk v1 al1 =>
    cases a2 with
    | mk v2 al2 =>
      cases al1 <;> cases al2 <;> simp [attrUnion, Bool.or_comm, Nat.max_comm]

theorem attrUnion_assoc (a1 a2 a3 : Attr) :
    attrUnion (attrUnion a1 a2) a3 = attrUnion a1 (attrUnion a2 a3) := by
  cases a1 with
  | mk v1 al1 =>
    cases a2 with
    | mk v2 al2 =>
      cases a3 with
      | mk v3 al3 =>
        cases al1 <;> cases al2 <;> cases al3 <;>
          simp [attrUnion, Bool.or_assoc, Nat.max_assoc]

theorem attrUnion_idem (a : Attr) : attrUnion a a = a := by
  cases a with
  | mk v al => cases al <;> simp [attrUnion]

/-- Merging no attributes leaves a type unchanged. -/
theorem mergeAttributes_noattr (ty : Ty) : mergeAttributes ty noattr = ty := by
  cases ty <;> simp [mergeAttributes, Ctyping.changeAttributes, attrUnion_noattr_left]

/-- Merging attributes does not change the shape of a type: removing the
    attributes afterwards gives the same result as before. -/
theorem removeAttributes_mergeAttributes (ty : Ty) (a : Attr) :
    removeAttributes (mergeAttributes ty a) = removeAttributes ty := by
  cases ty <;> simp [mergeAttributes, Ctyping.changeAttributes, removeAttributes, tattr]

/-- Merging attributes twice is merging their union. -/
theorem mergeAttributes_mergeAttributes (ty : Ty) (a1 a2 : Attr) :
    mergeAttributes (mergeAttributes ty a1) a2 = mergeAttributes ty (attrUnion a2 a1) := by
  cases ty <;> simp [mergeAttributes, Ctyping.changeAttributes, attrUnion_assoc]

/-! ## Layout of structs -/

/-- `Ctypes.field_zero_or_padding`: a zero-width bit field or an unnamed
    (padding) bit field. -/
def fieldZeroOrPadding : Member → Bool
  | .Member_plain _ _ => false
  | .Member_bitfield _ _ _ _ w p => decide (w ≤ 0) || p

/-- `Ctypes.layout_struct_rec` -/
def layoutStructRec (env : CompositeEnv) :
    List Member → List (Ident × Z × Bitfield) → Z → Res (List (Ident × Z × Bitfield))
  | [], accu, _ => .OK accu
  | m :: ms, accu, pos =>
    if fieldZeroOrPadding m then layoutStructRec env ms accu (nextField env pos m)
    else
      match layoutField env pos m with
      | .Error e => .Error e
      | .OK (p, b) => layoutStructRec env ms ((m.name, p, b) :: accu) (nextField env pos m)

/-- `Ctypes.layout_struct env ms`: the offset and bit-field designation of
    every named, non-zero-width field of a struct with members `ms`. -/
def layoutStruct (env : CompositeEnv) (ms : List Member) : Res (List (Ident × Z × Bitfield)) :=
  layoutStructRec env ms [] 0

/-- Every entry of `layout_struct_rec` comes from the accumulator or from a
    member that is neither zero-width nor padding. -/
theorem layoutStructRec_mem (env : CompositeEnv) (ms : List Member)
    (accu : List (Ident × Z × Bitfield)) (pos : Z) (l : List (Ident × Z × Bitfield))
    (h : layoutStructRec env ms accu pos = .OK l) (x : Ident × Z × Bitfield) (hx : x ∈ l) :
    x ∈ accu ∨ ∃ m ∈ ms, fieldZeroOrPadding m = false ∧ x.1 = m.name := by
  induction ms generalizing accu pos with
  | nil => simp [layoutStructRec] at h; subst h; exact .inl hx
  | cons m ms ih =>
    unfold layoutStructRec at h
    split at h
    · rcases ih _ _ h with h1 | ⟨m', hm', h2⟩
      · exact .inl h1
      · exact .inr ⟨m', List.mem_cons_of_mem _ hm', h2⟩
    · next hz =>
      split at h
      · cases h
      · rcases ih _ _ h with h1 | ⟨m', hm', h2⟩
        · rcases List.mem_cons.mp h1 with rfl | h1
          · exact .inr ⟨m, List.mem_cons_self, by simpa using hz, rfl⟩
          · exact .inl h1
        · exact .inr ⟨m', List.mem_cons_of_mem _ hm', h2⟩

/-- Every entry of `layout_struct` is a named, non-zero-width field. -/
theorem layoutStruct_mem (env : CompositeEnv) (ms : List Member)
    (l : List (Ident × Z × Bitfield)) (h : layoutStruct env ms = .OK l)
    (x : Ident × Z × Bitfield) (hx : x ∈ l) :
    ∃ m ∈ ms, fieldZeroOrPadding m = false ∧ x.1 = m.name := by
  rcases layoutStructRec_mem env ms [] 0 l h x hx with h1 | h2
  · cases h1
  · exact h2

/-! ## Building a program -/

/-- `Ctypes.make_program`: build the composite environment of `types`, and
    the program if it is well formed. -/
def makeProgram (types : List CompositeDef) (defs : List (Ident × GlobDef Csyntax.FunDef Ty))
    (pub : List Ident) (main : Ident) : Res Csyntax.Program :=
  match h : buildCompositeEnv types with
  | .Error e => .Error e
  | .OK ce =>
    .OK { prog_defs := defs, prog_public := pub, prog_main := main,
          prog_types := types, prog_comp_env := ce, prog_comp_env_eq := h }

/-- `make_program` succeeds exactly when the composite definitions are well
    formed, and then returns a program with the given components. -/
theorem makeProgram_OK (types : List CompositeDef)
    (defs : List (Ident × GlobDef Csyntax.FunDef Ty)) (pub : List Ident) (main : Ident)
    (p : Csyntax.Program) (h : makeProgram types defs pub main = .OK p) :
    p.prog_defs = defs ∧ p.prog_public = pub ∧ p.prog_main = main ∧
      p.prog_types = types ∧ buildCompositeEnv types = .OK p.prog_comp_env := by
  unfold makeProgram at h
  split at h
  · cases h
  · cases h; exact ⟨rfl, rfl, rfl, rfl, by assumption⟩

end CC
