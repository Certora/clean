/-
  [x86-64 instance of `CCLib/backend/Liveness.lean`: the same development, in
  namespace `CC.X86`, over the x86-64 operators, registers and conventions.]

  Liveness analysis over RTL — port of `backend/Liveness.v`, together with
  `Registers.Regset` (from `backend/Registers.v`) and the lattice functor
  `Lattice.LFSet` (from `lib/Lattice.v`) instantiated at `Regset`.

  Ported: `reg_live`, `reg_dead`, `reg_option_live`, `reg_sum_live`,
  `reg_list_live`, `reg_list_dead`, `transfer`, `RegsetLat`, `analyze`,
  `analyze_solution`, `last_uses_at`, `last_uses`.

  Differences from Rocq:
  * `Regset` (an AVL set, `FSetAVL.Make(OrderedPositive)`) is a list of
    registers; `add` checks membership first, so lists built with the
    operations below have no duplicates.  Only membership matters: the
    lattice equality is extensional set equality.
-/
import CCLib.x86.RTL
import CCLib.backend.Kildall

namespace CC
namespace X86

/-! ## `Registers.Regset` -/

/-- `Registers.Regset.t`, as a list of registers. -/
abbrev Regset := List Reg

namespace Regset
def empty : Regset := []
def mem (r : Reg) (s : Regset) : Bool := s.contains r
def add (r : Reg) (s : Regset) : Regset := if mem r s then s else r :: s
def remove (r : Reg) (s : Regset) : Regset := s.filter (fun x => x != r)
def union (s1 s2 : Regset) : Regset := s1.foldr add s2
def subset (s1 s2 : Regset) : Bool := s1.all (fun r => mem r s2)
def equal (s1 s2 : Regset) : Bool := subset s1 s2 && subset s2 s1
/-- `Regset.In` -/
def In (r : Reg) (s : Regset) : Prop := r ∈ s
/-- `Regset.Subset` -/
def Subset (s1 s2 : Regset) : Prop := ∀ r, r ∈ s1 → r ∈ s2
/-- `Regset.Equal` -/
def Equal (s1 s2 : Regset) : Prop := ∀ r, r ∈ s1 ↔ r ∈ s2

theorem mem_iff {r : Reg} {s : Regset} : mem r s = true ↔ r ∈ s := by
  simp [mem]

theorem mem_add {r x : Reg} {s : Regset} : r ∈ add x s ↔ r = x ∨ r ∈ s := by
  unfold add
  split
  · next h =>
    rw [mem_iff] at h
    constructor
    · exact .inr
    · rintro (rfl | h')
      · exact h
      · exact h'
  · simp

theorem mem_remove {r x : Reg} {s : Regset} : r ∈ remove x s ↔ r ≠ x ∧ r ∈ s := by
  simp [remove, and_comm]

theorem mem_union {r : Reg} {s1 s2 : Regset} : r ∈ union s1 s2 ↔ r ∈ s1 ∨ r ∈ s2 := by
  induction s1 with
  | nil => simp [union]
  | cons x l ih =>
    show r ∈ add x (union l s2) ↔ _
    rw [mem_add, ih]
    simp only [List.mem_cons]
    constructor
    · rintro (h | h | h)
      · exact .inl (.inl h)
      · exact .inl (.inr h)
      · exact .inr h
    · rintro ((h | h) | h)
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr h)

theorem subset_iff {s1 s2 : Regset} : subset s1 s2 = true ↔ Subset s1 s2 := by
  simp [subset, Subset, mem]

end Regset

/-! ## `Lattice.LFSet(Regset)` -/

/-- `Lattice.LFSet` instantiated at `Regset`: sets ordered by inclusion. -/
instance RegsetLat : Semilattice Regset where
  eq := Regset.Equal
  eq_refl _ _ := Iff.rfl
  eq_sym h r := (h r).symm
  eq_trans h1 h2 r := (h1 r).trans (h2 r)
  beq := Regset.equal
  beq_correct h r := by
    simp only [Regset.equal, Bool.and_eq_true, Regset.subset_iff] at h
    exact ⟨h.1 r, h.2 r⟩
  ge x y := Regset.Subset y x
  ge_refl h r hr := (h r).mpr hr
  ge_trans h1 h2 r hr := h1 r (h2 r hr)
  bot := Regset.empty
  ge_bot _ r hr := by simp [Regset.empty] at hr
  lub := Regset.union
  ge_lub_left _ _ _ hr := Regset.mem_union.mpr (.inl hr)
  ge_lub_right _ _ _ hr := Regset.mem_union.mpr (.inr hr)

/-! ## `Liveness.v` -/

namespace Liveness

open RTL

/-- `Liveness.reg_live` -/
abbrev regLive := Regset.add
/-- `Liveness.reg_dead` -/
abbrev regDead := Regset.remove

/-- `Liveness.reg_option_live` -/
def regOptionLive (or : Option Reg) (lv : Regset) : Regset :=
  match or with
  | none => lv
  | some r => regLive r lv

/-- `Liveness.reg_sum_live` -/
def regSumLive (ros : Sum Reg Ident) (lv : Regset) : Regset :=
  match ros with
  | .inl r => regLive r lv
  | .inr _ => lv

/-- `Liveness.reg_list_live` -/
def regListLive : List Reg → Regset → Regset
  | [], lv => lv
  | r1 :: rs, lv => regListLive rs (regLive r1 lv)

/-- `Liveness.reg_list_dead` -/
def regListDead : List Reg → Regset → Regset
  | [], lv => lv
  | r1 :: rs, lv => regListDead rs (regDead r1 lv)

/-- `Liveness.transfer`: the registers live before `pc`, given those live after. -/
def transfer (f : RTL.Function) (pc : Node) (after : Regset) : Regset :=
  match f.fn_code.get pc with
  | none => Regset.empty
  | some i =>
    match i with
    | .Inop _ => after
    | .Iop _ args res _ =>
        if Regset.mem res after then regListLive args (regDead res after) else after
    | .Iload _ _ args dst _ =>
        if Regset.mem dst after then regListLive args (regDead dst after) else after
    | .Istore _ _ args src _ => regListLive args (regLive src after)
    | .Icall _ ros args res _ => regListLive args (regSumLive ros (regDead res after))
    | .Itailcall _ ros args => regListLive args (regSumLive ros Regset.empty)
    | .Ibuiltin _ args res _ =>
        regListLive (BuiltinArg.paramsList args) (regListDead (BuiltinRes.params res) after)
    | .Icond _ args _ _ => regListLive args after
    | .Ijumptable arg _ => regLive arg after
    | .Ireturn optarg => regOptionLive optarg Regset.empty

/-- `Liveness.analyze`: `DS.fixpoint` with `DS := Backward_Dataflow_Solver(RegsetLat)(NodeSetBackward)`. -/
def analyze (f : RTL.Function) : Option (PMap Regset) :=
  Kildall.Backward.fixpoint (L := Regset) (NS := NodeSetBackward) f.fn_code successorsInstr (transfer f)

/-- `Liveness.analyze_solution` -/
theorem analyze_solution (f : RTL.Function) (live : PMap Regset) (n : Node) (i : Instruction)
    (s : Node) (h : analyze f = some live) (hc : f.fn_code.get n = some i)
    (hs : s ∈ successorsInstr i) :
    Regset.Subset (transfer f s (live.get s)) (live.get n) := by
  have := Kildall.Backward.fixpoint_solution (L := Regset) (NS := NodeSetBackward)
    f.fn_code successorsInstr (transfer f) live n i s h hc hs (by
      intro n a hn
      show Regset.Equal _ _
      simp only [transfer, hn]
      exact fun _ => Iff.rfl)
  exact this

/-- `Liveness.last_uses_at` -/
def lastUsesAt (live : PMap Regset) (pc : Node) (i : Instruction) : List Reg :=
  let l := live.get pc
  let lu := (instrUses i).filter (fun r => !Regset.mem r l)
  match instrDefs i with
  | none => lu
  | some r => if Regset.mem r l then lu else r :: lu

/-- `Liveness.last_uses` -/
def lastUses (f : RTL.Function) : PTree (List Reg) :=
  match analyze f with
  | none => PTree.empty
  | some live => PTree.map (lastUsesAt live) f.fn_code

end Liveness
end X86
end CC
