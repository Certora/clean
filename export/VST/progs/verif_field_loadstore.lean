/-
  Port of VST's `progs/verif_field_loadstore.v`: `sub1`, `sub2` and `sub3`
  of `vst/progs/field_loadstore.c` copy the field `p.y2[1].x2` of the global
  `p` into its field `p.y1`.

      struct a {double x1; char x2;};
      struct b {int y1; struct a y2[3];};
      struct b p;

      void sub1(void) { int i;         i = p.y2[1].x2;        p.y1 = i; }
      void sub2(void) { char i;        i = p.y2[1].x2;        p.y1 = i; }
      void sub3(void) { char i; int j; i = p.y2[1].x2; j = i; p.y1 = j; }

  VST's specification (`sub_spec`):

      DECLARE sub_id
       WITH v : val * list (val*val) , gv: globals
       PRE  []
         PROP  (is_int I8 Signed (snd (nth 1%nat (snd v) (Vundef, Vundef))))
         PARAMS() GLOBALS (gv)
         SEP   (data_at Ews t_struct_b v (gv _p))
       POST [ tvoid ]
         PROP() RETURN()
         SEP(data_at Ews t_struct_b (snd (nth 1%nat (snd v) (Vundef, Vundef)), snd v) (gv _p)).

  Differences:

  * The program is generated for AArch64, where `char` is *unsigned*
    (`tuchar`), so the field holds an `unsigned char`: VST's
    `is_int I8 Signed x2` becomes `x2 = n` with `n < 256`.
  * The precondition owns only the two fields the functions touch, `p.y1`
    (offset `0`) and `p.y2[1].x2` (offset `8 + 16 * 1 + 8 = 32`; the offsets
    are computed from the generated composite environment).  The triples
    carry an arbitrary frame (`Sep.SatisfiesAt`), so the rest of `p` — what
    `data_at` of the whole struct adds — is preserved untouched, which is
    VST's postcondition for those parts.
  * `gv _p` is the block `pb` the symbol `p` resolves to.
-/
import VST.progs.field_loadstore
import CCLib.logic.ExactTempsHeap
import CCLib.logic.FunspecVoid
open CC CC.Sep CC.HProp
open Field_loadstore

namespace VST.Verif.FieldLoadstore

/-! ## The layout of `struct a` and `struct b` -/

/-- `struct a`, as computed from the generated composite definitions. -/
def coA : Composite :=
  match prog.prog_comp_env.get _a with
  | some co => co
  | none => { co_su := .Struct, co_members := [], co_attr := noattr,
              co_sizeof := 0, co_alignof := 1, co_rank := 0 }

/-- `struct b`. -/
def coB : Composite :=
  match prog.prog_comp_env.get _b with
  | some co => co
  | none => { co_su := .Struct, co_members := [], co_attr := noattr,
              co_sizeof := 0, co_alignof := 1, co_rank := 0 }

theorem get_a : prog.prog_comp_env.get _a = some coA := rfl
theorem get_b : prog.prog_comp_env.get _b = some coB := rfl
theorem sizeof_a : sizeof prog.prog_comp_env (Ty.Tstruct _a noattr) = 16 := by decide
theorem offset_x2 : fieldOffset prog.prog_comp_env _x2 coA.co_members = .OK (8, .Full) := by
  decide
theorem offset_y1 : fieldOffset prog.prog_comp_env _y1 coB.co_members = .OK (0, .Full) := by
  decide
theorem offset_y2 : fieldOffset prog.prog_comp_env _y2 coB.co_members = .OK (8, .Full) := by
  decide

/-- The address of `p.y2[1]`, as `Cop` computes it. -/
def ofsY21 : Integers.Ptrofs :=
  Integers.Ptrofs.add (Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.repr 8))
    (Integers.Ptrofs.mul (Integers.Ptrofs.repr 16) (Cop.ptrofsOfInt .Signed (Integers.Int.repr 1)))

theorem ofsY21_x2 :
    Integers.Ptrofs.unsigned (Integers.Ptrofs.add ofsY21 (Integers.Ptrofs.repr 8))
      = Integers.Ptrofs.unsigned ofsY21 + 8 := by decide

theorem ofsY21_unsigned : Integers.Ptrofs.unsigned ofsY21 + 8 = 32 := by decide

theorem ofsY1_unsigned :
    Integers.Ptrofs.unsigned (Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.repr 0))
      = 0 := by decide

/-! ## The specification -/

/-- The two fields of `p` the functions use: `p.y1 = y1` and
    `p.y2[1].x2 = n`. -/
def Fields (perm : Permission) (pb : Block) (y1 : Val) (n : Nat) : HProp :=
  mapsto .Mint32 perm pb 0 y1 ∗ mapsto .Mint8unsigned perm pb 32 (.Vint (Integers.Int.repr n))

/-- `sub_spec`: afterwards `p.y1` is `p.y2[1].x2`. -/
def subSpec (perm : Permission) (pb : Block) (y1 : Val) (n : Nat) : Sep.FunSpec where
  tyargs := []
  tyres := tvoid
  cc := cc_default
  pre := fun vargs hp => vargs = [] ∧ Fields perm pb y1 n hp
  post := fun _ hp => Fields perm pb (.Vint (Integers.Int.repr n)) n hp
  measure := fun _ => 0

/-! ## The proof -/

/-- The locals are exactly `L`, and the fragment holds the two fields. -/
def AtF (perm : Permission) (pb : Block) (y1 : Val) (n : Nat) (L : TempEnv) : Sep.Assn :=
  Sep.AtH L (Fields perm pb y1 n)

/-- `p.y2[1].x2` -/
def x2Expr : Expr :=
  .Efield
    (.Ederef
      (.Ebinop .Oadd (.Efield (.Evar _p (Ty.Tstruct _b noattr)) _y2
          (tarray (Ty.Tstruct _a noattr) 3))
        (.Econst_int (Integers.Int.repr 1) tint) (tptr (Ty.Tstruct _a noattr)))
      (Ty.Tstruct _a noattr)) _x2 tuchar

/-- `p.y1 = x;` where the temporary `x` has type `ty`. -/
def storeY1 (x : Ident) (ty : Ty) : Stmt :=
  .Sassign (.Efield (.Evar _p (Ty.Tstruct _b noattr)) _y1 tint) (.Etempvar x ty)

theorem sub1_body : f_sub1.fn_body = .Ssequence (.Sset _i x2Expr) (storeY1 _i tint) := rfl
theorem sub2_body : f_sub2.fn_body =
    .Ssequence (.Ssequence (.Sset _t'1 x2Expr) (.Sset _i (.Ecast (.Etempvar _t'1 tuchar) tuchar)))
      (storeY1 _i tuchar) := rfl
theorem sub3_body : f_sub3.fn_body =
    .Ssequence (.Ssequence (.Sset _t'1 x2Expr) (.Sset _i (.Ecast (.Etempvar _t'1 tuchar) tuchar)))
      (.Ssequence (.Sset _j (.Etempvar _i tuchar)) (storeY1 _j tint)) := rfl

/-- Casting an `unsigned char` value to `unsigned char` or to `int`
    leaves it unchanged. -/
theorem semCast_uchar_uchar (m : Mem) (n : Nat) (hn : n < 256) :
    Cop.semCast (.Vint (Integers.Int.repr n)) tuchar tuchar m
      = some (.Vint (Integers.Int.repr n)) := by
  simp only [Cop.semCast, Cop.classifyCast, tuchar, Cop.castIntInt]
  rw [zero_ext8_repr n hn]

theorem semCast_uchar_int (m : Mem) (v : Integers.Int) :
    Cop.semCast (.Vint v) tuchar tint m = some (.Vint v) := by
  simp [Cop.semCast, Cop.classifyCast, tuchar, tint, Cop.castIntInt]

section
variable (ge : CGenv) (perm : Permission) (pb : Block) (n : Nat) (hn : n < 256)
  (hcenv : ge.genv_cenv = prog.prog_comp_env)
  (hsym : Genv.findSymbol ge.genv_genv _p = some pb)
  (hpw : permOrder perm .Writable = true)

include hsym in
/-- The global `p`, as the operand of a field access. -/
theorem eval_p (le : TempEnv) (m : Mem) :
    EvalExpr ge emptyEnv le m (.Evar _p (Ty.Tstruct _b noattr)) (.Vptr pb Integers.Ptrofs.zero) :=
  EvalExpr.Elvalue _ _ _ .Full _ (EvalLvalue.Evar_global _p pb _ (PTree.gempty _) hsym)
    (DerefLoc.copy rfl)

include hn hcenv hsym hpw in
/-- Reading `p.y2[1].x2`. -/
theorem eval_x2 (y1 : Val) (le : TempEnv) (m : Mem) (hp : Heap)
    (hF : Fields perm pb y1 n hp) (hag : Heap.Agrees hp m) :
    EvalExpr ge emptyEnv le m x2Expr (.Vint (Integers.Int.repr n)) := by
  obtain ⟨h1, h2, hd, rfl, _, hx2⟩ := hF
  have hag2 := Heap.Agrees_union_right hd hag
  have hy2 := eval_field_array (sid := _b) (att := noattr) (fld := _y2)
    (ty := tarray (Ty.Tstruct _a noattr) 3) rfl rfl (hcenv ▸ get_b) (hcenv ▸ offset_y2)
    (eval_p ge pb hsym le m)
  have hadd := EvalExpr.Ebinop (ge := ge) (e := emptyEnv) (le := le) (m := m) .Oadd _
    (.Econst_int (Integers.Int.repr 1) tint) (tptr (Ty.Tstruct _a noattr)) _ _ _ hy2
    (EvalExpr.Econst_int _ tint) (semAdd_ptr_int _ _ _ _ _ rfl)
  rw [hcenv, sizeof_a] at hadd
  have hderef : EvalExpr ge emptyEnv le m (.Ederef (.Ebinop .Oadd (.Efield (.Evar _p
      (Ty.Tstruct _b noattr)) _y2 (tarray (Ty.Tstruct _a noattr) 3))
      (.Econst_int (Integers.Int.repr 1) tint) (tptr (Ty.Tstruct _a noattr)))
      (Ty.Tstruct _a noattr)) (.Vptr pb ofsY21) :=
    EvalExpr.Elvalue _ _ _ .Full _ (EvalLvalue.Ederef _ _ _ _ hadd) (DerefLoc.copy rfl)
  have hm : fieldAt .Mint8unsigned perm pb (Integers.Ptrofs.unsigned ofsY21) 8
      (.Vint (Integers.Int.repr n)) h2 := by
    unfold fieldAt; rw [ofsY21_unsigned]; exact hx2
  have h := eval_field_scalar (sid := _a) (att := noattr) (fld := _x2) (ty := tuchar) rfl
    (readable_of_writable hpw) rfl (hcenv ▸ get_a) (hcenv ▸ offset_x2) hm hag2 hderef
    ofsY21_x2
  simp only [Val.loadResult, zero_ext8_repr n hn] at h
  exact h

include hcenv hsym hpw in
/-- `p.y1 = x;` where `x` holds `n`. -/
theorem store_y1 (f : Function) (x : Ident) (ty : Ty) (L : TempEnv)
    (hx : L.get x = some (.Vint (Integers.Int.repr n)))
    (hcast : ∀ m, Cop.semCast (.Vint (Integers.Int.repr n)) ty tint m
      = some (.Vint (Integers.Int.repr n))) (y1 : Val) :
    Sep.Triple ge (FunctionEntry2 ge) f (AtF perm pb y1 n L) (storeY1 x ty)
      (.only fun e _ hp => e = emptyEnv ∧ Fields perm pb (.Vint (Integers.Int.repr n)) n hp) := by
  refine Sep.triple_assign ge _ f _ _ _ _ .Mint32 perm pb
    (Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.repr 0)) hpw rfl
    (fun e le hp m hP _ => ?_)
  obtain ⟨rfl, rfl, h1, h2, hd, rfl, hy1, hx2⟩ := hP
  refine ⟨y1, .Vint (Integers.Int.repr n), h1, h2, hd, rfl, by rw [ofsY1_unsigned]; exact hy1,
    EvalLvalue.Efield_struct _ _ _ pb _ _b coB noattr 0 .Full (eval_p ge pb hsym _ m) rfl
      (hcenv ▸ get_b) (hcenv ▸ offset_y1),
    ⟨_, EvalExpr.Etempvar _ ty _ hx, hcast m⟩, fun h1' hm' hd' => ⟨rfl, h1', h2, hd', rfl, ?_, hx2⟩⟩
  rw [ofsY1_unsigned] at hm'
  exact hm'

include hn hcenv hsym hpw

/-- **`sub1` satisfies `sub_spec`** (VST's `body_sub1`). -/
theorem sub1_satisfies (y1 : Val) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_sub1) (subSpec perm pb y1 n) [] := by
  let L := createUndefTemps f_sub1.fn_temps
  refine satisfies_internal_noVars_void ge _ f_sub1 _ _ (AtF perm pb y1 n L)
    (fun _ => ⟨L, FunctionEntry2.intro (by decide) (by decide) (by decide)
      (AllocVariables.nil _ _) rfl, fun hp h => ⟨rfl, rfl, h.2⟩⟩) ?_
  rw [sub1_body]
  refine Sep.triple_seq ge _ f_sub1 _ (AtF perm pb y1 n (L.set _i (.Vint (Integers.Int.repr n))))
    _ _ _ ?_ ?_
  · refine Sep.triple_fallthrough ge _ f_sub1 _ _ _ _ ?_ (fun _ _ _ x => x)
    exact Sep.triple_set ge _ f_sub1 _ _ _ _ (fun e le hp m hP hag => by
      obtain ⟨rfl, rfl, hF⟩ := hP
      exact ⟨_, eval_x2 ge perm pb n hn hcenv hsym hpw y1 _ m hp hF hag, rfl, rfl, hF⟩)
  · exact Sep.triple_fallthrough ge _ f_sub1 _ _ _ _
      (store_y1 ge perm pb n hcenv hsym hpw f_sub1 _i tint _ (PTree.gss _ _ _)
        (fun m => semCast_int m _) y1) (fun _ _ _ x => x)

/-- `t'1 = p.y2[1].x2; i = (unsigned char) t'1;`, the common prefix of
    `sub2` and `sub3`. -/
theorem load_cast (f : Function) (L : TempEnv) (y1 : Val) (R : Sep.ExitConds) :
    Sep.Triple ge (FunctionEntry2 ge) f (AtF perm pb y1 n L)
      (.Ssequence (.Sset _t'1 x2Expr) (.Sset _i (.Ecast (.Etempvar _t'1 tuchar) tuchar)))
      { R with normal := AtF perm pb y1 n ((L.set _t'1 (.Vint (Integers.Int.repr n))).set _i
          (.Vint (Integers.Int.repr n))) } := by
  refine Sep.triple_fallthrough ge _ f _ _ _ _ ?_ (fun _ _ _ x => x)
  refine Sep.triple_seq_only ge _ f (Q := AtF perm pb y1 n (L.set _t'1 (.Vint (Integers.Int.repr n))))
    ?_ ?_
  · exact Sep.triple_set ge _ f _ _ _ _ (fun e le hp m hP hag => by
      obtain ⟨rfl, rfl, hF⟩ := hP
      exact ⟨_, eval_x2 ge perm pb n hn hcenv hsym hpw y1 _ m hp hF hag, rfl, rfl, hF⟩)
  · exact Sep.triple_set ge _ f _ _ _ _ (fun e le hp m hP _ => by
      obtain ⟨rfl, rfl, hF⟩ := hP
      exact ⟨_, EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ tuchar _ (PTree.gss _ _ _))
        (semCast_uchar_uchar m n hn), rfl, rfl, hF⟩)

/-- **`sub2` satisfies `sub_spec`** (VST's `body_sub2`). -/
theorem sub2_satisfies (y1 : Val) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_sub2) (subSpec perm pb y1 n) [] := by
  let L := createUndefTemps f_sub2.fn_temps
  refine satisfies_internal_noVars_void ge _ f_sub2 _ _ (AtF perm pb y1 n L)
    (fun _ => ⟨L, FunctionEntry2.intro (by decide) (by decide) (by decide)
      (AllocVariables.nil _ _) rfl, fun hp h => ⟨rfl, rfl, h.2⟩⟩) ?_
  rw [sub2_body]
  refine Sep.triple_seq ge _ f_sub2 _ _ _ _ _
    (load_cast ge perm pb n hn hcenv hsym hpw f_sub2 L y1 _) ?_
  exact Sep.triple_fallthrough ge _ f_sub2 _ _ _ _
    (store_y1 ge perm pb n hcenv hsym hpw f_sub2 _i tuchar _ (PTree.gss _ _ _)
      (fun m => semCast_uchar_int m _) y1) (fun _ _ _ x => x)

/-- **`sub3` satisfies `sub_spec`** (VST's `body_sub3`). -/
theorem sub3_satisfies (y1 : Val) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_sub3) (subSpec perm pb y1 n) [] := by
  let L := createUndefTemps f_sub3.fn_temps
  refine satisfies_internal_noVars_void ge _ f_sub3 _ _ (AtF perm pb y1 n L)
    (fun _ => ⟨L, FunctionEntry2.intro (by decide) (by decide) (by decide)
      (AllocVariables.nil _ _) rfl, fun hp h => ⟨rfl, rfl, h.2⟩⟩) ?_
  rw [sub3_body]
  let L2 := (L.set _t'1 (.Vint (Integers.Int.repr n))).set _i (.Vint (Integers.Int.repr n))
  refine Sep.triple_seq ge _ f_sub3 _ _ _ _ _
    (load_cast ge perm pb n hn hcenv hsym hpw f_sub3 L y1 _) ?_
  refine Sep.triple_seq ge _ f_sub3 _ (AtF perm pb y1 n (L2.set _j (.Vint (Integers.Int.repr n))))
    _ _ _ ?_ ?_
  · refine Sep.triple_fallthrough ge _ f_sub3 _ _ _ _ ?_ (fun _ _ _ x => x)
    exact Sep.triple_set ge _ f_sub3 _ _ _ _ (fun e le hp m hP _ => by
      obtain ⟨rfl, rfl, hF⟩ := hP
      exact ⟨_, EvalExpr.Etempvar _ tuchar _ (PTree.gss _ _ _), rfl, rfl, hF⟩)
  · exact Sep.triple_fallthrough ge _ f_sub3 _ _ _ _
      (store_y1 ge perm pb n hcenv hsym hpw f_sub3 _j tint _ (PTree.gss _ _ _)
        (fun m => semCast_int m _) y1) (fun _ _ _ x => x)

end

end VST.Verif.FieldLoadstore
