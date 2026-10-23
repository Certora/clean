/-
  Port of VST's `progs/verif_float.v`: `main` of `vst/progs/float.c`, which
  reads `float`/`double` fields of a global struct, converts between `float`,
  `double` and `int`, and copies a `double` array element.

      struct foo {int x; float y; double z;};
      struct foo s = {5, 3.41, 0.0};
      double a[] = {0.0,1.1};

      int main() {
       double y1 = s.y;
       int x1 = s.x;
       int y2 = s.y;
       y1 = s.z;
       a[0]=a[1];
       return 0;
      }

  VST's specification is `main_pre prog tt gv` / `main_post prog gv`: `main`
  starts from the initialised globals `s` and `a`.  Here `s` and `a` are the
  blocks `sb`, `ab` their symbols resolve to, owned (at a writable `perm`)
  field by field: `sAt` (`s.x` at offset 0, `s.y` at 4, `s.z` at 8) and `aAt`
  (`a[0]` at 0, `a[1]` at 8).  `main_satisfies` is stated for arbitrary
  contents, with the one hypothesis the program needs: the conversion
  `(int) s.y` is defined (`Float32.toInt s.y = some n`).  The postcondition
  says that `main` returns `0` and that afterwards `a[0] = a[1]`, `s`
  unchanged.  `main_satisfies_init` instantiates it at the initial values of
  the globals (`s = {5, 3.41f, 0.0}`, `a = {0.0, 1.1}`), where the conversion
  is decided (`(int) 3.41f = 3`) with the exact IEEE-754 model of the port.
-/
import VST.progs.float
import CCLib
open CC CC.Sep CC.HProp
open Float

namespace VST.Verif.Float

/-! ## The layout of `struct foo` -/

/-- `struct foo` -/
abbrev tfoo : Ty := Ty.Tstruct _foo noattr

def coFoo : Composite :=
  match prog.prog_comp_env.get _foo with
  | some co => co
  | none => { co_su := .Struct, co_members := [], co_attr := noattr,
              co_sizeof := 0, co_alignof := 1, co_rank := 0 }

theorem get_foo : prog.prog_comp_env.get _foo = some coFoo := rfl
theorem offset_x : fieldOffset prog.prog_comp_env _x coFoo.co_members = .OK (0, .Full) := by
  decide
theorem offset_y : fieldOffset prog.prog_comp_env _y coFoo.co_members = .OK (4, .Full) := by
  decide
theorem offset_z : fieldOffset prog.prog_comp_env _z coFoo.co_members = .OK (8, .Full) := by
  decide

/-! ## The globals -/

/-- `data_at Ews t_struct_foo (x, (y, z)) (gv _s)` -/
def sAt (perm : Permission) (sb : Block) (x : Integers.Int) (fy : Floats.Float32)
    (fz : Floats.Float) : HProp :=
  mapsto .Mint32 perm sb 0 (.Vint x)
    ∗ (mapsto .Mfloat32 perm sb 4 (.Vsingle fy) ∗ mapsto .Mfloat64 perm sb 8 (.Vfloat fz))

/-- `data_at Ews (tarray tdouble 2) [a0; a1] (gv _a)` -/
def aAt (perm : Permission) (ab : Block) (a0 a1 : Floats.Float) : HProp :=
  mapsto .Mfloat64 perm ab 0 (.Vfloat a0) ∗ mapsto .Mfloat64 perm ab 8 (.Vfloat a1)

/-- `main_spec`, for globals holding `s = {x, fy, fz}` and `a = {a0, a1}`. -/
def mainSpec (perm : Permission) (sb ab : Block) (x : Integers.Int) (fy : Floats.Float32)
    (fz a0 a1 : Floats.Float) : Sep.FunSpec where
  tyargs := []
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [] ∧ (aAt perm ab a0 a1 ∗ sAt perm sb x fy fz) hp
  post := fun v hp => v = .Vint (Integers.Int.repr 0)
    ∧ (aAt perm ab a1 a1 ∗ sAt perm sb x fy fz) hp
  measure := fun _ => 0

/-! ## Addresses -/

section
variable {ge : CGenv} {le : TempEnv} {m : Mem}

/-- `s.fld` as an l-value. -/
theorem lvalue_s_field (hcenv : ge.genv_cenv = prog.prog_comp_env) {sb : Block}
    (hsym : Genv.findSymbol ge.genv_genv _s = some sb) {fld : Ident} {ty : Ty} {delta : Z}
    (hoff : fieldOffset prog.prog_comp_env fld coFoo.co_members = .OK (delta, .Full)) :
    EvalLvalue ge emptyEnv le m (.Efield (.Evar _s tfoo) fld ty) sb
      (Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.repr delta)) .Full :=
  EvalLvalue.Efield_struct _ fld ty sb Integers.Ptrofs.zero _foo coFoo noattr delta .Full
    (EvalExpr.Elvalue _ sb Integers.Ptrofs.zero .Full _
      (EvalLvalue.Evar_global _s sb _ (PTree.gempty _) hsym) (DerefLoc.copy rfl))
    rfl (hcenv ▸ get_foo) (hcenv ▸ hoff)

/-- `a[i]` as an l-value. -/
theorem lvalue_a_idx {ab : Block} (hsym : Genv.findSymbol ge.genv_genv _a = some ab)
    (i : Integers.Int) :
    EvalLvalue ge emptyEnv le m
      (.Ederef (.Ebinop .Oadd (.Evar _a (tarray tdouble 2)) (.Econst_int i tint) (tptr tdouble))
        tdouble) ab (idxOfs ge.genv_cenv tdouble .Signed Integers.Ptrofs.zero i) .Full :=
  eval_index_lvalue (EvalExpr.Elvalue _ ab Integers.Ptrofs.zero .Full _
      (EvalLvalue.Evar_global _a ab _ (PTree.gempty _) hsym) (DerefLoc.reference rfl))
    (EvalExpr.Econst_int _ _) rfl

end

theorem idxOfs_double0 (ce : CompositeEnv) :
    Integers.Ptrofs.unsigned
      (idxOfs ce tdouble .Signed Integers.Ptrofs.zero (Integers.Int.repr 0)) = 0 := by
  have hsz : sizeof ce tdouble = 8 := by simp [sizeof, tdouble]
  rw [idxOfs, hsz]; decide

theorem idxOfs_double1 (ce : CompositeEnv) :
    Integers.Ptrofs.unsigned
      (idxOfs ce tdouble .Signed Integers.Ptrofs.zero (Integers.Int.repr 1)) = 8 := by
  have hsz : sizeof ce tdouble = 8 := by simp [sizeof, tdouble]
  rw [idxOfs, hsz]; decide

/-! ## Conversions -/

theorem semCast_single_double (m : Mem) (f : Floats.Float32) :
    Cop.semCast (.Vsingle f) tfloat tdouble m = some (.Vfloat (Floats.Float.ofSingle f)) := by
  simp [Cop.semCast, Cop.classifyCast, tfloat, tdouble]

theorem semCast_single_int (m : Mem) (f : Floats.Float32) (n : Integers.Int)
    (h : Floats.Float32.toInt f = some n) :
    Cop.semCast (.Vsingle f) tfloat tint m = some (.Vint n) := by
  simp [Cop.semCast, Cop.classifyCast, tfloat, tint, Cop.castSingleInt, h]

theorem semCast_double (m : Mem) (f : Floats.Float) :
    Cop.semCast (.Vfloat f) tdouble tdouble m = some (.Vfloat f) := by
  simp [Cop.semCast, Cop.classifyCast, tdouble]

/-! ## The proof -/

section
variable (ge : CGenv) (perm : Permission) (sb ab : Block) (x : Integers.Int)
  (fy : Floats.Float32) (n : Integers.Int) (fz a0 a1 : Floats.Float)
  (hcenv : ge.genv_cenv = prog.prog_comp_env)
  (hpw : permOrder perm .Writable = true)
  (hsym_s : Genv.findSymbol ge.genv_genv _s = some sb)
  (hsym_a : Genv.findSymbol ge.genv_genv _a = some ab)
  (hy : Floats.Float32.toInt fy = some n)
include hcenv hpw hsym_s hsym_a hy

/-- **`main` satisfies `main_spec`** (VST's `body_main`), for any contents of
    the globals for which `(int) s.y` is defined. -/
theorem main_satisfies :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_main)
      (mainSpec perm sb ab x fy fz a0 a1) [] := by
  have hpr := readable_of_writable hpw
  let H := aAt perm ab a0 a1 ∗ sAt perm sb x fy fz
  let L0 : TempEnv := createUndefTemps f_main.fn_temps
  let L1 := L0.set _t'1 (.Vsingle fy)
  let L2 := L1.set _y1 (.Vfloat (Floats.Float.ofSingle fy))
  let L3 := L2.set _x1 (.Vint x)
  let L4 := L3.set _t'2 (.Vsingle fy)
  let L5 := L4.set _y2 (.Vint n)
  let L6 := L5.set _y1 (.Vfloat fz)
  let L7 := L6.set _t'3 (.Vfloat a1)
  -- reading `s.y`
  have read_y : ∀ (L : TempEnv) m hp, H hp → Heap.Agrees hp m →
      EvalExpr ge emptyEnv L m (.Efield (.Evar _s tfoo) _y tfloat) (.Vsingle fy) := by
    intro L m hp hH hag
    obtain ⟨_, hs, hag1⟩ := sep_right_agrees hH hag
    obtain ⟨_, hyz, hag2⟩ := sep_right_agrees hs hag1
    obtain ⟨_, hm, hag3⟩ := sep_left_agrees hyz hag2
    exact eval_lvalue_mapsto (chunk := .Mfloat32) (v := .Vsingle fy) rfl hpr
      (lvalue_s_field hcenv hsym_s offset_y) (by decide) hm hag3
  refine satisfies_internal_noVars ge _ f_main _ _ (AtH L0 H)
    (fun _ => ⟨L0, FunctionEntry2.intro (by decide) (by decide) (by decide)
      (AllocVariables.nil _ _) rfl, fun hp h => ⟨rfl, rfl, h.2⟩⟩) ?_
  -- the trailing `return 0;` is unreachable
  refine Sep.triple_seq ge _ f_main _ Sep.Assn.no _ _ _ ?_ (Sep.triple_vacuous ge _ f_main _ _)
  -- `t'1 = s.y; y1 = (double) t'1;`
  refine triple_seq_only ge _ f_main (triple_seq_only ge _ f_main
    (triple_set_atH ge _ f_main L0 H _ _ _ (read_y L0))
    (triple_set_atH ge _ f_main L1 H _ _ _ fun m _ _ _ =>
      EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ _ _ rfl) (semCast_single_double m fy))) ?_
  -- `x1 = s.x;`
  refine triple_seq_only ge _ f_main
    (triple_set_atH ge _ f_main L2 H _ _ (.Vint x) fun m hp hH hag => by
      obtain ⟨_, hs, hag1⟩ := sep_right_agrees hH hag
      obtain ⟨_, hm, hag2⟩ := sep_left_agrees hs hag1
      exact eval_lvalue_mapsto (chunk := .Mint32) (v := .Vint x) rfl hpr
        (lvalue_s_field hcenv hsym_s offset_x) (by decide) hm hag2) ?_
  -- `t'2 = s.y; y2 = (int) t'2;`
  refine triple_seq_only ge _ f_main (triple_seq_only ge _ f_main
    (triple_set_atH ge _ f_main L3 H _ _ _ (read_y L3))
    (triple_set_atH ge _ f_main L4 H _ _ _ fun m _ _ _ =>
      EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ _ _ rfl) (semCast_single_int m fy n hy))) ?_
  -- `y1 = s.z;`
  refine triple_seq_only ge _ f_main
    (triple_set_atH ge _ f_main L5 H _ _ (.Vfloat fz) fun m hp hH hag => by
      obtain ⟨_, hs, hag1⟩ := sep_right_agrees hH hag
      obtain ⟨_, hyz, hag2⟩ := sep_right_agrees hs hag1
      obtain ⟨_, hm, hag3⟩ := sep_right_agrees hyz hag2
      exact eval_lvalue_mapsto (chunk := .Mfloat64) (v := .Vfloat fz) rfl hpr
        (lvalue_s_field hcenv hsym_s offset_z) (by decide) hm hag3 (Or.inr (by decide))) ?_
  -- `t'3 = a[1]; a[0] = t'3;`
  refine triple_seq_only ge _ f_main (Q := AtH L7 (aAt perm ab a1 a1 ∗ sAt perm sb x fy fz))
    (triple_seq_only ge _ f_main
      (triple_set_atH ge _ f_main L6 H _ _ (.Vfloat a1) fun m hp hH hag => by
        obtain ⟨_, ha, hag1⟩ := sep_left_agrees hH hag
        obtain ⟨_, hm, hag2⟩ := sep_right_agrees ha hag1
        exact eval_lvalue_mapsto (chunk := .Mfloat64) (v := .Vfloat a1) rfl hpr
          (lvalue_a_idx hsym_a _) (idxOfs_double1 _) hm hag2 (Or.inr (by decide)))
      (Sep.triple_assign ge _ f_main _ _ _ _ .Mfloat64 perm ab
        (idxOfs ge.genv_cenv tdouble .Signed Integers.Ptrofs.zero (Integers.Int.repr 0)) hpw rfl
        (fun e le hp m hP _ => ?_)
        (Or.inr (by rw [idxOfs_double0]; decide)))) ?_
  · obtain ⟨rfl, rfl, h1, h2, hd, rfl, ⟨h3, h4, hd34, rfl, hm0, hm1⟩, hs⟩ := hP
    have hd' := Heap.disjoint_union_left.mp hd
    refine ⟨.Vfloat a0, .Vfloat a1, h3, Heap.union h4 h2, ?_, by rw [Heap.union_assoc],
      by rw [idxOfs_double0]; exact hm0, lvalue_a_idx hsym_a _,
      ⟨_, EvalExpr.Etempvar _ _ _ rfl, semCast_double m a1⟩, fun h1' hm' hd1' => ?_⟩
    · rw [Heap.disjoint_union_right]; exact ⟨hd34, hd'.1⟩
    · rw [Heap.disjoint_union_right] at hd1'
      refine ⟨rfl, rfl, Heap.union h1' h4, h2, ?_, by rw [Heap.union_assoc],
        ⟨h1', h4, hd1'.1, rfl, by rw [idxOfs_double0] at hm'; exact hm', hm1⟩, hs⟩
      rw [Heap.disjoint_union_left]; exact ⟨hd1'.2, hd'.2⟩
  -- `return 0;`
  · exact triple_return_atH ge _ f_main _ _ _ _ _ (fun _ _ _ _ => EvalExpr.Econst_int _ _)
      (fun m => semCast_int m _)

end

/-- **`main` satisfies `main_spec` from the initial values of the globals**
    (`s = {5, 3.41f, 0.0}`, `a = {0.0, 1.1}`): `(int) 3.41f` is `3`. -/
theorem main_satisfies_init (ge : CGenv) (perm : Permission) (sb ab : Block)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hpw : permOrder perm .Writable = true)
    (hsym_s : Genv.findSymbol ge.genv_genv _s = some sb)
    (hsym_a : Genv.findSymbol ge.genv_genv _a = some ab) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_main)
      (mainSpec perm sb ab (Integers.Int.repr 5)
        (Floats.Float32.ofBits (Integers.Int.repr 1079655793))
        (Floats.Float.ofBits (Integers.Int64.repr 0)) (Floats.Float.ofBits (Integers.Int64.repr 0))
        (Floats.Float.ofBits (Integers.Int64.repr 4607632778762754458))) [] :=
  main_satisfies ge perm sb ab _ _ (Integers.Int.repr 3) _ _ _ hcenv hpw hsym_s hsym_a
    (by decide)

end VST.Verif.Float
