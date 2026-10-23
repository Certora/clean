/-
  Port of VST's `progs/verif_nest2.v`: `get` and `set` of
  `vst/progs/nest2.c`, which read and write the nested field `p.y2.x2` of the
  global struct `p`.

      struct a {double x1; int x2;};
      struct b {int y1; struct a y2;};
      struct b p;
      int get(void) { int i; i = p.y2.x2; return i; }
      void set(int i) { p.y2.x2 = i; }

  VST's specifications:

      DECLARE _get
       WITH v : reptype' t_struct_b, gv: globals
       PRE  [] PROP () PARAMS() GLOBALS (gv)
               SEP(data_at Ews t_struct_b (repinj _ v) (gv _p))
       POST [ tint ] PROP() RETURN (Vint (snd (snd v)))
               SEP (data_at Ews t_struct_b (repinj _ v) (gv _p)).

      DECLARE _set
       WITH i : int, v : reptype' t_struct_b, gv: globals
       PRE  [ tint ] PROP () PARAMS (Vint i) GLOBALS (gv)
               SEP (data_at Ews t_struct_b (repinj _ v) (gv _p))
       POST [ tvoid ] PROP() RETURN()
               SEP(data_at Ews t_struct_b (repinj _ (update22 i v)) (gv _p)).

  Here `v = (y1, (x1, x2))`, `gv _p` is the block `pb` the symbol `p`
  resolves to, and `data_at Ews t_struct_b v (gv _p)` is `structB`: the three
  scalar fields at their offsets in the layout CompCert computes from the
  generated composite environment (`y1` at 0, `y2.x1` at 8, `y2.x2` at 16;
  the facts `offset_*` are checked by `decide`), owned at permission `perm`
  (readable for `get`, writable for `set`).  The padding bytes, which VST's
  `data_at` also owns, are not described.  The theorems assume that the
  program's composite environment is the one of `ge`.
-/
import VST.progs.nest2
import CCLib
open CC CC.Sep CC.HProp
open Nest2

namespace VST.Verif.Nest2

/-! ## The layout of `struct b` -/

theorem composite_b : prog.prog_comp_env.get _b = some
    { co_su := SU.Struct,
      co_members := [Member.Member_plain _y1 tint, Member.Member_plain _y2 (Ty.Tstruct _a noattr)],
      co_attr := noattr, co_sizeof := 24, co_alignof := 8, co_rank := 1 } := by
  decide

theorem composite_a : prog.prog_comp_env.get _a = some
    { co_su := SU.Struct,
      co_members := [Member.Member_plain _x1 tdouble, Member.Member_plain _x2 tint],
      co_attr := noattr, co_sizeof := 16, co_alignof := 8, co_rank := 0 } := by
  decide

theorem offset_y2 : fieldOffset prog.prog_comp_env _y2
    [Member.Member_plain _y1 tint, Member.Member_plain _y2 (Ty.Tstruct _a noattr)]
      = .OK (8, .Full) := by
  decide

theorem offset_x2 : fieldOffset prog.prog_comp_env _x2
    [Member.Member_plain _x1 tdouble, Member.Member_plain _x2 tint] = .OK (8, .Full) := by
  decide

/-- The address of `p.y2`. -/
abbrev ofsY2 : Integers.Ptrofs := Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.repr 8)
/-- The address of `p.y2.x2`. -/
abbrev ofsX2 : Integers.Ptrofs := Integers.Ptrofs.add ofsY2 (Integers.Ptrofs.repr 8)

theorem ofsY2_unsigned : Integers.Ptrofs.unsigned ofsY2 = 8 := by decide
theorem ofsX2_unsigned : Integers.Ptrofs.unsigned ofsX2 = 16 := by decide

/-! ## Specifications -/

/-- `data_at sh t_struct_b (y1, (x1, x2)) (gv _p)`, field by field. -/
def structB (perm : Permission) (pb : Block) (y1 : Integers.Int) (x1 : Floats.Float)
    (x2 : Integers.Int) : HProp :=
  mapsto .Mint32 perm pb 16 (.Vint x2) ∗
    (mapsto .Mint32 perm pb 0 (.Vint y1) ∗ mapsto .Mfloat64 perm pb 8 (.Vfloat x1))

/-- `get_spec` -/
def getSpec (perm : Permission) (pb : Block) (y1 : Integers.Int) (x1 : Floats.Float)
    (x2 : Integers.Int) : Sep.FunSpec where
  tyargs := []
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [] ∧ structB perm pb y1 x1 x2 hp
  post := fun v hp => v = .Vint x2 ∧ structB perm pb y1 x1 x2 hp
  measure := fun _ => 0

/-- `set_spec` (`update22 i v` replaces `x2` by `i`) -/
def setSpec (perm : Permission) (pb : Block) (i y1 : Integers.Int) (x1 : Floats.Float)
    (x2 : Integers.Int) : Sep.FunSpec where
  tyargs := [tint]
  tyres := tvoid
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vint i] ∧ structB perm pb y1 x1 x2 hp
  post := fun _ hp => structB perm pb y1 x1 i hp
  measure := fun _ => 0

/-! ## Evaluating `p.y2.x2` -/

section
variable {ge : CGenv} (hcenv : ge.genv_cenv = prog.prog_comp_env) {pb : Block}
  (hsym : Genv.findSymbol ge.genv_genv _p = some pb)
include hcenv hsym

/-- The l-value `p.y2.x2` is at `pb + 16`. -/
theorem lvalue_x2 (le : TempEnv) (m : Mem) :
    EvalLvalue ge emptyEnv le m
      (.Efield (.Efield (.Evar _p (Ty.Tstruct _b noattr)) _y2 (Ty.Tstruct _a noattr)) _x2 tint)
      pb ofsX2 .Full :=
  EvalLvalue.Efield_struct _ _ _ pb ofsY2 _a _ noattr 8 .Full
    (eval_field_copy rfl rfl (hcenv ▸ composite_b) (hcenv ▸ offset_y2)
      (EvalExpr.Elvalue _ pb _ .Full _ (EvalLvalue.Evar_global _ _ _ (PTree.gempty _) hsym)
        (DerefLoc.copy rfl)))
    rfl (hcenv ▸ composite_a) (hcenv ▸ offset_x2)

/-- **`get` satisfies `get_spec`** (VST's `body_get`). -/
theorem get_satisfies (perm : Permission) (hpr : permOrder perm .Readable = true)
    (y1 : Integers.Int) (x1 : Floats.Float) (x2 : Integers.Int) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_get) (getSpec perm pb y1 x1 x2) [] := by
  let L : TempEnv := createUndefTemps f_get.fn_temps
  let P : TempEnv → Sep.Assn := fun L e le hp =>
    e = emptyEnv ∧ le = L ∧ structB perm pb y1 x1 x2 hp
  refine satisfies_internal_noVars ge _ f_get _ _ (P L)
    (fun _ => ⟨L, FunctionEntry2.intro (by decide) (by decide) (by decide)
      (AllocVariables.nil _ _) rfl, fun hp h => ⟨rfl, rfl, h.2⟩⟩) ?_
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
    (i y1 : Integers.Int) (x1 : Floats.Float) (x2 : Integers.Int) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_set) (setSpec perm pb i y1 x1 x2)
      [.Vint i] := by
  let L : TempEnv := (createUndefTemps f_set.fn_temps).set _i (.Vint i)
  refine satisfies_internal_noVars_void ge _ f_set _ _
    (fun e le hp => e = emptyEnv ∧ le = L ∧ structB perm pb y1 x1 x2 hp)
    (fun _ => ⟨L, FunctionEntry2.intro (by decide) (by decide) (by decide)
      (AllocVariables.nil _ _) rfl, fun hp h => ⟨rfl, rfl, h.2⟩⟩) ?_
  refine Sep.triple_conseq ge _ f_set
    (Sep.triple_assign ge _ f_set _ (fun e _ hp => e = emptyEnv ∧ structB perm pb y1 x1 i hp)
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

end VST.Verif.Nest2
