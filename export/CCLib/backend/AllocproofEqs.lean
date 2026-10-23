/-
  Correctness of register allocation, part 2 — port of the "properties of
  equations" section of `backend/Allocproof.v`: `sel_val`, `satisf`, and the
  lemmas relating the operations on sets of equations (`add_equation`,
  `remove_equation`, `subst_reg`, `subst_loc`, `reg_unconstrained`,
  `loc_unconstrained`, `can_undef`, …) to `satisf`.

  Differences from Rocq: sets of equations are duplicate-free lists (see
  `backend/Allocation.lean`), so the reasoning on `EqSet.elements_between`
  and `EqSet.fold` becomes reasoning on `List.filter` and `List.foldl`; the
  characterisation of the location range (`select_loc_charact`) is
  `selectLoc_false_diff`.  The lemmas used only by the 32-bit targets
  (`subst_reg_kind_*`, `subst_loc_part_*`, `subst_loc_pair_*`,
  `val_longofwords_eq_*`) are not ported: on this (64-bit) configuration the
  corresponding moves and block shapes are rejected by the validator
  (`Archi.ptr64 = true`, `Archi.splitlong = false`).
-/
import CCLib.backend.AllocproofShape
import CCLib.backend.RTLtypingSubject

namespace CC
namespace Allocproof

open Op Allocation LTL RTLtyping Conventions1 Conventions
open Allocation.Eqs (add remove)

/-- `Allocproof.sel_val` -/
def selVal (k : EquationKind) (v : Val) : Val :=
  match k with
  | .Full => v
  | .Low => Val.loword v
  | .High => Val.hiword v

/-- `Allocproof.satisf` -/
def Satisf (rs : RTL.Regset) (ls : Locset) (e : Eqs) : Prop :=
  ∀ q ∈ e, Val.Lessdef (selVal q.ekind (rs.get q.ereg)) (ls q.eloc)

/-- `Allocproof.empty_eqs_satisf` -/
theorem empty_eqs_satisf (rs : RTL.Regset) (ls : Locset) : Satisf rs ls Eqs.empty :=
  fun _ h => by cases h

/-- `Allocproof.satisf_incr` -/
theorem satisf_incr {rs : RTL.Regset} {ls : Locset} {e1 e2 : Eqs} (h : Satisf rs ls e2)
    (hs : Eqs.Subset e1 e2) : Satisf rs ls e1 :=
  fun q hq => h q (hs q hq)

/-- `Allocproof.satisf_undef_reg` -/
theorem satisf_undef_reg {rs : RTL.Regset} {ls : Locset} {e : Eqs} (r : Reg)
    (h : Satisf rs ls e) : Satisf (rs.set r .Vundef) ls e := by
  intro q hq
  rw [PMap.gsspec]
  split
  · cases q.ekind <;> exact .undef _
  · exact h q hq

/-- `Allocproof.add_equation_lessdef` -/
theorem add_equation_lessdef {rs : RTL.Regset} {ls : Locset} {q : Equation} {e : Eqs}
    (h : Satisf rs ls (add q e)) : Val.Lessdef (selVal q.ekind (rs.get q.ereg)) (ls q.eloc) :=
  h q (Eqs.mem_add.mpr (.inl rfl))

/-- `Allocproof.add_equation_satisf` -/
theorem add_equation_satisf {rs : RTL.Regset} {ls : Locset} {q : Equation} {e : Eqs}
    (h : Satisf rs ls (add q e)) : Satisf rs ls e :=
  satisf_incr h (fun _ hx => Eqs.mem_add.mpr (.inr hx))

/-- `Allocproof.add_equations_satisf` -/
theorem add_equations_satisf {rs : RTL.Regset} {ls : Locset} :
    ∀ {rl : List Reg} {ml : List Mreg} {e e' : Eqs},
    addEquations rl ml e = some e' → Satisf rs ls e' → Satisf rs ls e
  | [], [], _, _, h, hs => by cases h; exact hs
  | [], _ :: _, _, _, h, _ => by cases h
  | _ :: _, [], _, _, h, _ => by cases h
  | _ :: _, _ :: _, _, _, h, hs => add_equation_satisf (add_equations_satisf h hs)

/-- `Allocproof.add_equations_lessdef` -/
theorem add_equations_lessdef {rs : RTL.Regset} {ls : Locset} :
    ∀ {rl : List Reg} {ml : List Mreg} {e e' : Eqs},
    addEquations rl ml e = some e' → Satisf rs ls e' →
    Val.LessdefList (rs.getList rl) (reglist ls ml)
  | [], [], _, _, _, _ => .nil
  | [], _ :: _, _, _, h, _ => by cases h
  | _ :: _, [], _, _, h, _ => by cases h
  | r :: rl, m :: ml, e, _, h, hs =>
    .cons (add_equation_lessdef (q := ⟨.Full, r, .R m⟩) (e := e) (add_equations_satisf h hs))
      (add_equations_lessdef h hs)

/-- `Allocproof.add_equations_args_satisf` -/
theorem add_equations_args_satisf {rs : RTL.Regset} {ls : Locset} :
    ∀ {rl : List Reg} {tyl : List ATyp} {ll : List (RPair Loc)} {e e' : Eqs},
    addEquationsArgs rl tyl ll e = some e' → Satisf rs ls e' → Satisf rs ls e
  | [], [], [], _, _, h, hs => by cases h; exact hs
  | r :: rl, ty :: tyl, .One l :: ll, e, e', h, hs => by
    simp only [addEquationsArgs] at h
    exact add_equation_satisf (add_equations_args_satisf h hs)
  | r :: rl, ty :: tyl, .Twolong l1 l2 :: ll, e, e', h, hs => by
    cases ty <;> simp [addEquationsArgs, Archi.ptr64] at h
  | [], [], _ :: _, _, _, h, _ => by cases h
  | [], _ :: _, _, _, _, h, _ => by cases h
  | _ :: _, [], _, _, _, h, _ => by cases h
  | _ :: _, _ :: _, [], _, _, h, _ => by cases h

/-- `Allocproof.add_equations_args_lessdef` (64-bit version: every argument
    is passed in one location). -/
theorem add_equations_args_lessdef {rs : RTL.Regset} {ls : Locset} :
    ∀ {rl : List Reg} {tyl : List ATyp} {ll : List (RPair Loc)} {e e' : Eqs},
    addEquationsArgs rl tyl ll e = some e' → Satisf rs ls e' →
    Val.LessdefList (rs.getList rl) (ll.map (fun p => Locmap.getpair p ls))
  | [], [], [], _, _, _, _ => .nil
  | r :: rl, ty :: tyl, .One l :: ll, e, e', h, hs => by
    simp only [addEquationsArgs] at h
    exact .cons (add_equation_lessdef (q := ⟨.Full, r, l⟩) (e := e)
      (add_equations_args_satisf h hs)) (add_equations_args_lessdef h hs)
  | r :: rl, ty :: tyl, .Twolong l1 l2 :: ll, e, e', h, hs => by
    cases ty <;> simp [addEquationsArgs, Archi.ptr64] at h
  | [], [], _ :: _, _, _, h, _ => by cases h
  | [], _ :: _, _, _, _, h, _ => by cases h
  | _ :: _, [], _, _, _, h, _ => by cases h
  | _ :: _, _ :: _, [], _, _, h, _ => by cases h

/-- `Allocproof.add_equation_ros_satisf` -/
theorem add_equation_ros_satisf {rs : RTL.Regset} {ls : Locset} {ros : Sum Reg Ident}
    {mos : Sum Mreg Ident} {e e' : Eqs} (h : addEquationRos ros mos e = some e')
    (hs : Satisf rs ls e') : Satisf rs ls e := by
  unfold addEquationRos at h
  split at h
  · cases h; exact add_equation_satisf hs
  · split at h
    · cases h; exact hs
    · cases h
  · cases h

/-- `Allocproof.remove_equation_satisf` -/
theorem remove_equation_satisf {rs : RTL.Regset} {ls : Locset} {q : Equation} {e : Eqs}
    (h : Satisf rs ls e) : Satisf rs ls (remove q e) :=
  satisf_incr h (fun _ hx => (Eqs.mem_remove.mp hx).2)

/-- `Allocproof.remove_equation_res_satisf` -/
theorem remove_equation_res_satisf {rs : RTL.Regset} {ls : Locset} {r : Reg} {l : RPair Mreg}
    {e e' : Eqs} (h : removeEquationsRes r l e = some e') (hs : Satisf rs ls e) :
    Satisf rs ls e' := by
  unfold removeEquationsRes at h
  split at h
  · cases h; exact remove_equation_satisf hs
  · split at h
    · cases h
    · cases h; exact remove_equation_satisf (remove_equation_satisf hs)

/-- `Allocproof.reg_unconstrained_sound` -/
theorem reg_unconstrained_sound {r : Reg} {e : Eqs} {q : Equation}
    (h : regUnconstrained r e = true) (hq : q ∈ e) : q.ereg ≠ r := by
  intro heq
  simp only [regUnconstrained, Bool.not_eq_true', List.any_eq_false] at h
  exact h q hq (by simp [selectReg, heq])

/-- `Allocproof.reg_unconstrained_satisf` -/
theorem reg_unconstrained_satisf {r : Reg} {e : Eqs} {rs : RTL.Regset} {ls : Locset} {v : Val}
    (h : regUnconstrained r e = true) (hs : Satisf rs ls e) : Satisf (rs.set r v) ls e := by
  intro q hq
  rw [PMap.gso _ _ _ _ (Ne.symm (reg_unconstrained_sound h hq))]
  exact hs q hq

/-- `Allocproof.select_loc_charact`, one direction: an equation outside the
    location range of `l` is on a location that does not overlap `l`. -/
theorem selectLoc_false_diff (l : Loc) (q : Equation) (h : selectLoc l q = false) :
    Loc.diff l q.eloc := by
  have hidx : ∀ r1 r2 : Mreg, (Mreg.index r1).toNat = (Mreg.index r2).toNat → r1 = r2 := by
    intro r1 r2 h
    have h1 := Mreg.ofIndexNat_index r1
    rw [h, Mreg.ofIndexNat_index] at h1
    cases h1; rfl
  obtain ⟨k0, r0, l'⟩ := q
  simp only [selectLoc, selectLocL, selectLocH, Bool.and_eq_false_iff, bne_eq_false_iff_eq] at h
  cases l with
  | R r =>
    cases l' with
    | R r' =>
      simp only [OrderedLoc.diffLowBound, OrderedLoc.diffHighBound, OrderedLoc.compare,
        _root_.Nat.compare_eq_lt, _root_.Nat.compare_eq_gt] at h
      simp only [Loc.diff]
      rintro rfl; omega
    | S => trivial
  | S sl ofs ty =>
    cases l' with
    | R r' => trivial
    | S sl' ofs' ty' =>
      simp only [OrderedLoc.diffLowBound, OrderedLoc.diffHighBound, OrderedLoc.compare,
        Ordering.then_eq_lt, Ordering.then_eq_gt, _root_.Nat.compare_eq_lt,
        _root_.Nat.compare_eq_gt, _root_.Nat.compare_eq_eq, _root_.Int.compare_eq_lt,
        _root_.Int.compare_eq_gt] at h
      simp only [Loc.diff]
      by_cases hs : sl = sl'
      · subst hs
        right
        have hsz : ∀ t, 1 ≤ typesize t ∧ typesize t ≤ 2 := by intro t; cases t <;> decide
        have h1 := hsz ty; have h2 := hsz ty'
        have hcmp : ∀ (a b : Z), compare a b = .eq ↔ a = b := fun a b => by
          constructor
          · intro h; exact Std.LawfulEqCmp.eq_of_compare h
          · rintro rfl; exact Std.ReflCmp.compare_self
        simp only [hcmp] at h
        simp only [Z] at *
        rcases h with h | h
        · rcases h with h | ⟨_, h | ⟨rfl, h⟩⟩
          · omega
          · omega
          · right
            cases ty' <;> simp [OrderedLoc.typIndex] at h <;> simp [typesize] <;> omega
        · rcases h with h | ⟨_, h | ⟨rfl, h⟩⟩
          · omega
          · omega
          · cases ty' <;> simp [OrderedLoc.typIndex] at h
      · left; exact hs

/-- `Allocproof.loc_unconstrained_sound` -/
theorem loc_unconstrained_sound {l : Loc} {e : Eqs} {q : Equation}
    (h : locUnconstrained l e = true) (hq : q ∈ e) : Loc.diff l q.eloc := by
  simp only [locUnconstrained, Bool.not_eq_true', List.any_eq_false] at h
  exact selectLoc_false_diff l q (by simpa using h q hq)

/-- `Allocproof.loc_unconstrained_satisf` -/
theorem loc_unconstrained_satisf {rs : RTL.Regset} {ls : Locset} {k : EquationKind} {r : Reg}
    {mr : Mreg} {e : Eqs} {v : Val} (hs : Satisf rs ls (remove ⟨k, r, .R mr⟩ e))
    (hu : locUnconstrained (.R mr) (remove ⟨k, r, .R mr⟩ e) = true)
    (hv : Val.Lessdef (selVal k (rs.get r)) v) : Satisf rs (Locmap.set (.R mr) v ls) e := by
  intro q hq
  by_cases hqe : q = ⟨k, r, .R mr⟩
  · subst hqe; simp only [Locmap.gss_reg]; exact hv
  · have hq' : q ∈ remove ⟨k, r, .R mr⟩ e := Eqs.mem_remove.mpr ⟨hqe, hq⟩
    rw [Locmap.gso (loc_unconstrained_sound hu hq')]
    exact hs q hq'

/-- `Allocproof.reg_loc_unconstrained_sound` -/
theorem reg_loc_unconstrained_sound {r : Reg} {l : Loc} {e : Eqs} {q : Equation}
    (h : regLocUnconstrained r l e = true) (hq : q ∈ e) : q.ereg ≠ r ∧ Loc.diff l q.eloc := by
  simp only [regLocUnconstrained, Bool.and_eq_true] at h
  exact ⟨reg_unconstrained_sound h.1 hq, loc_unconstrained_sound h.2 hq⟩

/-- `Allocproof.parallel_assignment_satisf` -/
theorem parallel_assignment_satisf {k : EquationKind} {r : Reg} {mr : Mreg} {e : Eqs}
    {rs : RTL.Regset} {ls : Locset} {v v' : Val} (hv : Val.Lessdef (selVal k v) v')
    (hu : regLocUnconstrained r (.R mr) (remove ⟨k, r, .R mr⟩ e) = true)
    (hs : Satisf rs ls (remove ⟨k, r, .R mr⟩ e)) :
    Satisf (rs.set r v) (Locmap.set (.R mr) v' ls) e := by
  intro q hq
  by_cases hqe : q = ⟨k, r, .R mr⟩
  · subst hqe; simp only [PMap.gss, Locmap.gss_reg]; exact hv
  · have hq' : q ∈ remove ⟨k, r, .R mr⟩ e := Eqs.mem_remove.mpr ⟨hqe, hq⟩
    obtain ⟨A, B⟩ := reg_loc_unconstrained_sound hu hq'
    rw [PMap.gso _ _ _ _ (Ne.symm A), Locmap.gso B]
    exact hs q hq'

/-- `Allocproof.parallel_assignment_satisf_2` (64-bit version: results are
    returned in one register). -/
theorem parallel_assignment_satisf_2 {rs : RTL.Regset} {ls : Locset} {res : Reg} {mr : Mreg}
    {e e' : Eqs} {v v' : Val} (h : removeEquationsRes res (.One mr) e = some e')
    (hs : Satisf rs ls e') (hu : regUnconstrained res e' = true)
    (hl : locUnconstrained (.R mr) e' = true) (hv : Val.Lessdef v v') :
    Satisf (rs.set res v) (Locmap.setpair (.One mr) v' ls) e := by
  simp only [removeEquationsRes] at h
  cases h
  exact parallel_assignment_satisf (k := .Full) hv (by simp [regLocUnconstrained, hu, hl]) hs

/-! ### Substitutions -/

/-- The fold of `subst_reg` and `subst_loc`: replacing each equation `x` of
    `L` by `g x`. -/
private theorem foldl_subst_mem (g : Equation → Equation) (hg : ∀ q, g (g q) = g q) :
    ∀ (L : List Equation) (e0 : Eqs) (q : Equation), q ∈ e0 →
    (q ∈ L → g q ∈ L.foldl (fun e x => add (g x) (remove x e)) e0) ∧
    (q ∉ L → q ∈ L.foldl (fun e x => add (g x) (remove x e)) e0)
  | [], e0, q, hq => ⟨fun h => (by cases h), fun _ => hq⟩
  | x :: L, e0, q, hq => by
    simp only [List.foldl_cons]
    have IH := foldl_subst_mem g hg L (add (g x) (remove x e0))
    have hgx : g x ∈ add (g x) (remove x e0) := Eqs.mem_add.mpr (.inl rfl)
    have Kgx : g x ∈ L.foldl (fun e x => add (g x) (remove x e)) (add (g x) (remove x e0)) := by
      by_cases hL : g x ∈ L
      · have := (IH (g x) hgx).1 hL; rwa [hg] at this
      · exact (IH (g x) hgx).2 hL
    by_cases hqx : q = x
    · subst hqx
      refine ⟨fun _ => Kgx, fun hn => absurd List.mem_cons_self hn⟩
    · have hq1 : q ∈ add (g x) (remove x e0) :=
        Eqs.mem_add.mpr (.inr (Eqs.mem_remove.mpr ⟨hqx, hq⟩))
      refine ⟨fun hm => ?_, fun hn => ?_⟩
      · rcases List.mem_cons.mp hm with rfl | hm
        · exact absurd rfl hqx
        · exact (IH q hq1).1 hm
      · exact (IH q hq1).2 (fun hm => hn (List.mem_cons_of_mem _ hm))

/-- `Allocproof.in_subst_reg` -/
theorem in_subst_reg {r1 r2 : Reg} {q : Equation} {e : Eqs} (hq : q ∈ e) :
    (q.ereg = r1 ∧ (⟨q.ekind, r2, q.eloc⟩ : Equation) ∈ substReg r1 r2 e) ∨
    (q.ereg ≠ r1 ∧ q ∈ substReg r1 r2 e) := by
  have := foldl_subst_mem (fun x => ⟨x.ekind, r2, x.eloc⟩) (fun _ => rfl) (eqsOfReg r1 e) e q hq
  by_cases h : q.ereg = r1
  · exact .inl ⟨h, this.1 (List.mem_filter.mpr ⟨hq, by simp [selectReg, h]⟩)⟩
  · exact .inr ⟨h, this.2 (fun hm => h (by simpa [selectReg] using (List.mem_filter.mp hm).2))⟩

/-- `Allocproof.subst_reg_satisf` -/
theorem subst_reg_satisf {src dst : Reg} {rs : RTL.Regset} {ls : Locset} {e : Eqs}
    (h : Satisf rs ls (substReg dst src e)) : Satisf (rs.set dst (rs.get src)) ls e := by
  intro q hq
  rcases in_subst_reg (r2 := src) hq with ⟨A, B⟩ | ⟨A, B⟩
  · rw [A, PMap.gss]; exact h _ B
  · rw [PMap.gso _ _ _ _ (Ne.symm A)]; exact h q B

/-- The fold of `subst_loc`. -/
private theorem foldl_substLoc_mem (l1 l2 : Loc) :
    ∀ (L : List Equation) (e0 e' : Eqs),
    L.foldl (fun opte q => match opte with
      | none => none
      | some e => if l1 = q.eloc then some (add ⟨q.ekind, q.ereg, l2⟩ (remove q e)) else none)
      (some e0) = some e' →
    (∀ x ∈ L, l1 = x.eloc) ∧
    ∀ q ∈ e0, (q ∈ L → (⟨q.ekind, q.ereg, l2⟩ : Equation) ∈ e') ∧ (q ∉ L → q ∈ e')
  | [], e0, e', h => by
    cases h; exact ⟨fun _ h => (by cases h), fun q hq => ⟨fun h => (by cases h), fun _ => hq⟩⟩
  | x :: L, e0, e', h => by
    simp only [List.foldl_cons] at h
    have hnone : ∀ L' : List Equation, L'.foldl (fun opte q => match opte with
        | none => none
        | some e => if l1 = q.eloc then some (add ⟨q.ekind, q.ereg, l2⟩ (remove q e))
            else none) none = none := by
      intro L'; induction L' with
      | nil => rfl
      | cons _ _ ih => exact ih
    split at h
    · next hx =>
      obtain ⟨HL, IH⟩ := foldl_substLoc_mem l1 l2 L _ e' h
      let gx : Equation := ⟨x.ekind, x.ereg, l2⟩
      have hgx : gx ∈ add gx (remove x e0) := Eqs.mem_add.mpr (.inl rfl)
      have Kgx : gx ∈ e' := by
        by_cases hL : gx ∈ L
        · exact (IH gx hgx).1 hL
        · exact (IH gx hgx).2 hL
      refine ⟨fun y hy => ?_, fun q hq => ?_⟩
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact hx
        · exact HL y hy
      · by_cases hqx : q = x
        · subst hqx
          exact ⟨fun _ => Kgx, fun hn => absurd List.mem_cons_self hn⟩
        · have hq1 : q ∈ add gx (remove x e0) :=
            Eqs.mem_add.mpr (.inr (Eqs.mem_remove.mpr ⟨hqx, hq⟩))
          refine ⟨fun hm => ?_, fun hn => ?_⟩
          · rcases List.mem_cons.mp hm with rfl | hm
            · exact absurd rfl hqx
            · exact (IH q hq1).1 hm
          · exact (IH q hq1).2 (fun hm => hn (List.mem_cons_of_mem _ hm))
    · rw [hnone] at h; cases h

/-- `Allocproof.in_subst_loc` -/
theorem in_subst_loc {l1 l2 : Loc} {q : Equation} {e e' : Eqs} (hq : q ∈ e)
    (h : substLoc l1 l2 e = some e') :
    (q.eloc = l1 ∧ (⟨q.ekind, q.ereg, l2⟩ : Equation) ∈ e') ∨ (Loc.diff l1 q.eloc ∧ q ∈ e') := by
  obtain ⟨HL, H⟩ := foldl_substLoc_mem l1 l2 (eqsOfLoc l1 e) e e' h
  by_cases hm : q ∈ eqsOfLoc l1 e
  · exact .inl ⟨(HL q hm).symm, (H q hq).1 hm⟩
  · refine .inr ⟨selectLoc_false_diff l1 q ?_, (H q hq).2 hm⟩
    cases hs : selectLoc l1 q
    · rfl
    · exact absurd (List.mem_filter.mpr ⟨hq, hs⟩) hm

/-- `Allocproof.loc_type_compat_charact` -/
theorem loc_type_compat_charact {env : Regenv} {l : Loc} {e : Eqs} {q : Equation}
    (h : locTypeCompat env l e = true) (hq : q ∈ e) :
    ATyp.subtype (selType q.ekind (env q.ereg)) l.type = true ∨ Loc.diff l q.eloc := by
  cases hs : selectLoc l q
  · exact .inr (selectLoc_false_diff l q hs)
  · left
    simp only [locTypeCompat, List.all_eq_true] at h
    exact h q (List.mem_filter.mpr ⟨hq, hs⟩)

/-- `Allocproof.well_typed_move_charact` -/
theorem well_typed_move_charact {env : Regenv} {l : Loc} {e : Eqs} {k : EquationKind} {r : Reg}
    {rs : RTL.Regset} (h : wellTypedMove env l e = true) (hq : (⟨k, r, l⟩ : Equation) ∈ e)
    (hwt : WtRegset env rs) :
    match l with
    | .R _ => True
    | .S _ _ ty => Val.HasType (selVal k (rs.get r)) ty := by
  cases l with
  | R _ => trivial
  | S sl ofs ty =>
    simp only [wellTypedMove] at h
    rcases loc_type_compat_charact h hq with A | A
    · refine Val.has_subtype A ?_
      have := hwt r
      cases k with
      | Full => exact this
      | Low => simp only [selVal]; cases rs.get r <;> rfl
      | High => simp only [selVal]; cases rs.get r <;> rfl
    · exact absurd A (Loc.same_not_diff _)

/-- `Allocproof.val_lessdef_normalize` -/
theorem val_lessdef_normalize {v v' : Val} {ty : ATyp} (ht : Val.HasType v ty)
    (hl : Val.Lessdef v v') : Val.Lessdef v (Val.loadResult (Chunk.ofTyp ty) v') := by
  cases hl with
  | refl => rw [Val.load_result_same ht]; exact .refl _
  | undef => exact .undef _

/-- The value stored in location `l` by `Locmap.set l v`. -/
private theorem set_lessdef {env : Regenv} {rs : RTL.Regset} {k : EquationKind} {r : Reg}
    {l : Loc} {v : Val} {e : Eqs} (hw : wellTypedMove env l e = true)
    (hq : (⟨k, r, l⟩ : Equation) ∈ e) (hwt : WtRegset env rs)
    (hv : Val.Lessdef (selVal k (rs.get r)) v) {ls : Locset} :
    Val.Lessdef (selVal k (rs.get r)) (Locmap.set l v ls l) := by
  have W := well_typed_move_charact hw hq hwt
  rw [Locmap.gss]
  cases l with
  | R _ => exact hv
  | S sl ofs ty => exact val_lessdef_normalize W hv

/-- `Allocproof.subst_loc_satisf` -/
theorem subst_loc_satisf {env : Regenv} {src dst : Loc} {rs : RTL.Regset} {ls : Locset}
    {e e' : Eqs} (h : substLoc dst src e = some e') (hw : wellTypedMove env dst e = true)
    (hwt : WtRegset env rs) (hs : Satisf rs ls e') : Satisf rs (Locmap.set dst (ls src) ls) e := by
  intro q hq
  rcases in_subst_loc hq h with ⟨A, B⟩ | ⟨A, B⟩
  · obtain ⟨k, r, l⟩ := q
    simp only at A B ⊢
    subst A
    exact set_lessdef hw hq hwt (hs _ B)
  · rw [Locmap.gso A]; exact hs q B

/-- `Allocproof.can_undef_sound` -/
theorem can_undef_sound {e : Eqs} :
    ∀ {ml : List Mreg} {q : Equation}, canUndef ml e = true → q ∈ e →
    Loc.notin q.eloc (ml.map Loc.R)
  | [], _, _, _ => trivial
  | m :: ml, q, h, hq => by
    simp only [canUndef, List.all_cons, Bool.and_eq_true] at h
    exact ⟨Loc.diff_sym (loc_unconstrained_sound h.1 hq), can_undef_sound h.2 hq⟩

/-- `Allocproof.undef_regs_outside` -/
theorem undef_regs_outside :
    ∀ {ml : List Mreg} {ls : Locset} {l : Loc}, Loc.notin l (ml.map Loc.R) →
    LTL.undefRegs ml ls l = ls l
  | [], _, _, _ => rfl
  | _ :: _, _, _, h => by
    simp only [LTL.undefRegs]
    rw [Locmap.gso (Loc.diff_sym h.1), undef_regs_outside h.2]

/-- `Allocproof.can_undef_satisf` -/
theorem can_undef_satisf {ml : List Mreg} {e : Eqs} {rs : RTL.Regset} {ls : Locset}
    (h : canUndef ml e = true) (hs : Satisf rs ls e) : Satisf rs (LTL.undefRegs ml ls) e := by
  intro q hq
  rw [undef_regs_outside (can_undef_sound h hq)]
  exact hs q hq

/-- `Allocproof.can_undef_except_sound` -/
theorem can_undef_except_sound {lx : Loc} {e : Eqs} :
    ∀ {ml : List Mreg} {q : Equation}, canUndefExcept lx ml e = true → q ∈ e →
    Loc.diff q.eloc lx → Loc.notin q.eloc (ml.map Loc.R)
  | [], _, _, _, _ => trivial
  | m :: ml, q, h, hq, hd => by
    simp only [canUndefExcept, List.all_cons, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq] at h
    refine ⟨?_, can_undef_except_sound h.2 hq hd⟩
    rcases h.1 with h1 | h1
    · subst h1; exact hd
    · exact Loc.diff_sym (loc_unconstrained_sound h1 hq)

/-- `Allocproof.subst_loc_undef_satisf` -/
theorem subst_loc_undef_satisf {env : Regenv} {src dst : Loc} {rs : RTL.Regset} {ls : Locset}
    {ml : List Mreg} {e e' : Eqs} (h : substLoc dst src e = some e')
    (hw : wellTypedMove env dst e = true) (hu : canUndefExcept dst ml e = true)
    (hwt : WtRegset env rs) (hs : Satisf rs ls e') :
    Satisf rs (Locmap.set dst (ls src) (LTL.undefRegs ml ls)) e := by
  intro q hq
  rcases in_subst_loc hq h with ⟨A, B⟩ | ⟨A, B⟩
  · obtain ⟨k, r, l⟩ := q
    simp only at A B ⊢
    subst A
    exact set_lessdef hw hq hwt (hs _ B)
  · rw [Locmap.gso A, undef_regs_outside (can_undef_except_sound hu hq (Loc.diff_sym A))]
    exact hs q B

/-- `Allocproof.transfer_use_def_satisf` -/
theorem transfer_use_def_satisf {args : List Reg} {res : Reg} {args' : List Mreg} {res' : Mreg}
    {und : List Mreg} {e e' : Eqs} {rs : RTL.Regset} {ls : Locset}
    (h : transferUseDef args res args' res' und e = some e') (hs : Satisf rs ls e') :
    Val.LessdefList (rs.getList args) (reglist ls args') ∧
    ∀ v v', Val.Lessdef v v' →
      Satisf (rs.set res v) (Locmap.set (.R res') v' (LTL.undefRegs und ls)) e := by
  unfold transferUseDef at h
  simp only at h
  split at h
  · next hc =>
    simp only [Bool.and_eq_true] at hc
    refine ⟨add_equations_lessdef h hs, fun v v' hv => ?_⟩
    exact parallel_assignment_satisf (k := .Full) hv hc.1
      (can_undef_satisf hc.2 (add_equations_satisf h hs))
  · cases h

/-- `Allocproof.add_equations_res_lessdef` (64-bit version). -/
theorem add_equations_res_lessdef {r : Reg} {ty : ATyp} {l : RPair Mreg} {e e' : Eqs}
    {rs : RTL.Regset} {ls : Locset} (h : addEquationsRes r ty l e = some e')
    (hs : Satisf rs ls e') : Val.Lessdef (rs.get r) (Locmap.getpair (l.map Loc.R) ls) := by
  cases l with
  | One mr =>
    simp only [addEquationsRes] at h
    cases h; exact add_equation_lessdef (q := ⟨.Full, r, .R mr⟩) hs
  | Twolong mr1 mr2 => cases ty <;> simp [addEquationsRes, Archi.ptr64] at h

/-- `Allocproof.return_regs_agree_callee_save` -/
theorem return_regs_agree_callee_save (caller callee : Locset) :
    AgreeCalleeSave caller (LTL.returnRegs caller callee) := by
  intro l hl
  cases l with
  | R r => simp only [CalleeSaveLoc] at hl; simp [LTL.returnRegs, hl]
  | S sl ofs ty => cases sl <;> simp_all [CalleeSaveLoc, LTL.returnRegs]

/-- `Allocproof.no_caller_saves_sound` -/
theorem no_caller_saves_sound {e : Eqs} {q : Equation} (h : noCallerSaves e = true)
    (hq : q ∈ e) : CalleeSaveLoc q.eloc := by
  simp only [noCallerSaves, List.all_eq_true] at h
  have := h q hq
  revert this
  cases q.eloc with
  | R r => simp [CalleeSaveLoc]
  | S sl _ _ => cases sl <;> simp [CalleeSaveLoc]

end Allocproof
end CC
