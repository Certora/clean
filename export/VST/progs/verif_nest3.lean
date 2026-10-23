/-
  Port of VST's `progs/verif_nest3.v`: `get` and `set` of
  `vst/progs/nest3.c`, which read and write the doubly nested field
  `p.z2.y2.x2` of the global struct `p`.

      struct a {int x1,x2;};
      struct b {struct a y1, y2;};
      struct c {struct b z1,z2;};
      struct c p;
      int get(void) { int i; i = p.z2.y2.x2; return i; }
      void set(int i) { p.z2.y2.x2 = i; }

  VST's specifications:

      DECLARE _get
       WITH v : reptype' t_struct_c, gv: globals
       PRE  [] PROP () PARAMS() GLOBALS (gv)
               SEP(data_at Ews t_struct_c (repinj _ v) (gv _p))
       POST [ tint ] PROP() RETURN (Vint (snd (snd (snd v))))
               SEP (data_at Ews t_struct_c (repinj _ v) (gv _p)).

      DECLARE _set
       WITH i : int, v : reptype' t_struct_c, gv : globals
       PRE  [ tint ] PROP () PARAMS (Vint i) GLOBALS (gv)
               SEP(data_at Ews t_struct_c (repinj _ v) (gv _p))
       POST [ tvoid ] PROP() RETURN()
               SEP(data_at Ews t_struct_c (repinj _ (update222 i v)) (gv _p)).

  `struct c` is eight `int`s laid out contiguously (no padding).  The value
  `v` is represented by the field `x2 = p.z2.y2.x2` (at offset 28) and the
  seven other cells, given as a list `others` of `int`s stored at offsets
  `0, 4, …, 24`.  `data_at sh t_struct_c v (gv _p)` is `structC`.  The
  theorems assume that the program's composite environment is the one of
  `ge`.  (VST's `multi_command` functions are not specified by
  `verif_nest3.v` either.)
-/
import VST.progs.nest3
import CCLib
open CC CC.Sep CC.HProp
open Nest3

namespace VST.Verif.Nest3

/-! ## The layout of `struct c` -/

theorem composite_c : prog.prog_comp_env.get _c = some
    { co_su := SU.Struct,
      co_members := [Member.Member_plain _z1 (Ty.Tstruct _b noattr),
        Member.Member_plain _z2 (Ty.Tstruct _b noattr)],
      co_attr := noattr, co_sizeof := 32, co_alignof := 4, co_rank := 2 } := by
  decide

theorem composite_b : prog.prog_comp_env.get _b = some
    { co_su := SU.Struct,
      co_members := [Member.Member_plain _y1 (Ty.Tstruct _a noattr),
        Member.Member_plain _y2 (Ty.Tstruct _a noattr)],
      co_attr := noattr, co_sizeof := 16, co_alignof := 4, co_rank := 1 } := by
  decide

theorem composite_a : prog.prog_comp_env.get _a = some
    { co_su := SU.Struct,
      co_members := [Member.Member_plain _x1 tint, Member.Member_plain _x2 tint],
      co_attr := noattr, co_sizeof := 8, co_alignof := 4, co_rank := 0 } := by
  decide

theorem offset_z2 : fieldOffset prog.prog_comp_env _z2
    [Member.Member_plain _z1 (Ty.Tstruct _b noattr),
      Member.Member_plain _z2 (Ty.Tstruct _b noattr)] = .OK (16, .Full) := by
  decide

theorem offset_y2 : fieldOffset prog.prog_comp_env _y2
    [Member.Member_plain _y1 (Ty.Tstruct _a noattr),
      Member.Member_plain _y2 (Ty.Tstruct _a noattr)] = .OK (8, .Full) := by
  decide

theorem offset_x2 : fieldOffset prog.prog_comp_env _x2
    [Member.Member_plain _x1 tint, Member.Member_plain _x2 tint] = .OK (4, .Full) := by
  decide

/-- The address of `p.z2`. -/
abbrev ofsZ2 : Integers.Ptrofs := Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.repr 16)
/-- The address of `p.z2.y2`. -/
abbrev ofsY2 : Integers.Ptrofs := Integers.Ptrofs.add ofsZ2 (Integers.Ptrofs.repr 8)
/-- The address of `p.z2.y2.x2`. -/
abbrev ofsX2 : Integers.Ptrofs := Integers.Ptrofs.add ofsY2 (Integers.Ptrofs.repr 4)

theorem ofsX2_unsigned : Integers.Ptrofs.unsigned ofsX2 = 28 := by decide

/-! ## Specifications -/

/-- The cells `others[k]` at offsets `4 * (start + k)` of block `pb`. -/
def intCells (perm : Permission) (pb : Block) : Nat → List Integers.Int → HProp
  | _, [] => emp
  | start, v :: vs => mapsto .Mint32 perm pb (4 * start) (.Vint v) ∗ intCells perm pb (start + 1) vs

/-- `data_at sh t_struct_c v (gv _p)`: the field `p.z2.y2.x2` (offset 28)
    holding `x2`, and the seven other `int` fields holding `others`. -/
def structC (perm : Permission) (pb : Block) (others : List Integers.Int)
    (x2 : Integers.Int) : HProp :=
  mapsto .Mint32 perm pb 28 (.Vint x2) ∗ intCells perm pb 0 others

/-- `get_spec` -/
def getSpec (perm : Permission) (pb : Block) (others : List Integers.Int)
    (x2 : Integers.Int) : Sep.FunSpec where
  tyargs := []
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [] ∧ others.length = 7 ∧ structC perm pb others x2 hp
  post := fun v hp => v = .Vint x2 ∧ structC perm pb others x2 hp
  measure := fun _ => 0

/-- `set_spec` (`update222 i v` replaces `x2` by `i`) -/
def setSpec (perm : Permission) (pb : Block) (i : Integers.Int) (others : List Integers.Int)
    (x2 : Integers.Int) : Sep.FunSpec where
  tyargs := [tint]
  tyres := tvoid
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vint i] ∧ others.length = 7 ∧ structC perm pb others x2 hp
  post := fun _ hp => structC perm pb others i hp
  measure := fun _ => 0

/-! ## Evaluating `p.z2.y2.x2` -/

section
variable {ge : CGenv} (hcenv : ge.genv_cenv = prog.prog_comp_env) {pb : Block}
  (hsym : Genv.findSymbol ge.genv_genv _p = some pb)
include hcenv hsym

/-- The l-value `p.z2.y2.x2` is at `pb + 28`. -/
theorem lvalue_x2 (le : TempEnv) (m : Mem) :
    EvalLvalue ge emptyEnv le m
      (.Efield (.Efield (.Efield (.Evar _p (Ty.Tstruct _c noattr)) _z2 (Ty.Tstruct _b noattr))
        _y2 (Ty.Tstruct _a noattr)) _x2 tint)
      pb ofsX2 .Full :=
  EvalLvalue.Efield_struct _ _ _ pb ofsY2 _a _ noattr 4 .Full
    (eval_field_copy rfl rfl (hcenv ▸ composite_b) (hcenv ▸ offset_y2)
      (eval_field_copy rfl rfl (hcenv ▸ composite_c) (hcenv ▸ offset_z2)
        (EvalExpr.Elvalue _ pb _ .Full _ (EvalLvalue.Evar_global _ _ _ (PTree.gempty _) hsym)
          (DerefLoc.copy rfl))))
    rfl (hcenv ▸ composite_a) (hcenv ▸ offset_x2)

/-- **`get` satisfies `get_spec`** (VST's `body_get`). -/
theorem get_satisfies (perm : Permission) (hpr : permOrder perm .Readable = true)
    (others : List Integers.Int) (x2 : Integers.Int) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_get) (getSpec perm pb others x2) [] := by
  let L : TempEnv := createUndefTemps f_get.fn_temps
  let P : TempEnv → Sep.Assn := fun L e le hp =>
    e = emptyEnv ∧ le = L ∧ structC perm pb others x2 hp
  refine satisfies_internal_noVars ge _ f_get _ _ (P L)
    (fun _ => ⟨L, FunctionEntry2.intro (by decide) (by decide) (by decide)
      (AllocVariables.nil _ _) rfl, fun hp h => ⟨rfl, rfl, h.2.2⟩⟩) ?_
  refine Sep.triple_seq_only ge _ f_get (Q := P (L.set _i (.Vint x2))) ?_ ?_
  · refine Sep.triple_set ge _ f_get _ _ _ _ fun e le hp m h hag => ?_
    obtain ⟨rfl, rfl, hS⟩ := h
    obtain ⟨h1, h2, hd, rfl, hx2, _⟩ := hS
    refine ⟨.Vint x2, ?_, rfl, rfl, ⟨h1, h2, hd, rfl, hx2, ‹_›⟩⟩
    refine EvalExpr.Elvalue _ pb ofsX2 .Full _ (lvalue_x2 hcenv hsym _ m)
      (DerefLoc.value .Mint32 _ rfl ?_)
    rw [Mem.loadv_ptr _ _ _ _ (Or.inl rfl), ofsX2_unsigned]
    exact mapsto_load hpr hx2 (Heap.Agrees_union_left hag)
  · refine Sep.triple_return ge _ f_get _ _ _ fun e le hp m h _ => ?_
    obtain ⟨rfl, rfl, hS⟩ := h
    exact ⟨_, _, m, hp, EvalExpr.Etempvar _ tint _ (PTree.gss _ _ _), semCast_int m _,
      freeList_emptyEnv _ _, ⟨rfl, hS⟩, fun _ hdj hag => ⟨hdj, hag⟩⟩

/-- **`set` satisfies `set_spec`** (VST's `body_set`). -/
theorem set_satisfies (perm : Permission) (hpw : permOrder perm .Writable = true)
    (i : Integers.Int) (others : List Integers.Int) (x2 : Integers.Int) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_set) (setSpec perm pb i others x2)
      [.Vint i] := by
  let L : TempEnv := (createUndefTemps f_set.fn_temps).set _i (.Vint i)
  refine satisfies_internal_noVars_void ge _ f_set _ _
    (fun e le hp => e = emptyEnv ∧ le = L ∧ structC perm pb others x2 hp)
    (fun _ => ⟨L, FunctionEntry2.intro (by decide) (by decide) (by decide)
      (AllocVariables.nil _ _) rfl, fun hp h => ⟨rfl, rfl, h.2.2⟩⟩) ?_
  refine Sep.triple_conseq ge _ f_set
    (Sep.triple_assign ge _ f_set _ (fun e _ hp => e = emptyEnv ∧ structC perm pb others i hp)
      _ _ .Mint32 perm pb ofsX2 hpw rfl (fun e le hp m h _ => ?_))
    (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim)
    (fun _ _ x => x.elim)
  obtain ⟨rfl, rfl, hS⟩ := h
  obtain ⟨h1, h2, hd, rfl, hx2, hrest⟩ := hS
  refine ⟨.Vint x2, .Vint i, h1, h2, hd, rfl, by rw [ofsX2_unsigned]; exact hx2,
    lvalue_x2 hcenv hsym _ m, ⟨.Vint i, EvalExpr.Etempvar _ tint _ (PTree.gss _ _ _),
      semCast_int m _⟩, fun h1' hx2' hd' => ⟨rfl, h1', h2, hd', rfl, ?_, hrest⟩⟩
  rwa [ofsX2_unsigned] at hx2'

end

end VST.Verif.Nest3
