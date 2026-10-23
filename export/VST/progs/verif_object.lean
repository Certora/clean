/-
  Port of VST's `progs/verif_object.v`: the two methods of the "foo" object
  in `vst/progs/object.c`.

      struct foo_object {struct methods *mtable; int data;};

      void foo_reset(struct object *self) {
        ((struct foo_object *)self)->data=0;
      }

      int foo_twiddle(struct object *self, int i) {
        int d = ((struct foo_object *)self)->data;
        ((struct foo_object *)self)->data = d+2*i;
        return d+i;
      }

  VST specifies both methods against the object invariant

      foo_invariant history p :=
        withspacer Ews (sizeof size_t + sizeof tint) (2 * sizeof size_t)
          (field_at Ews (Tstruct _foo_object noattr) [StructField _data]
             (Vint (Int.repr (2 * fold_right Z.add 0 history)))) p
        * malloc_token Ews (Tstruct _foo_object noattr) p

      reset_spec:   WITH self, history
        PRE PARAMS (self) SEP (instance history self)
        POST RETURN () SEP (instance nil self)

      twiddle_spec: WITH self, i, history
        PRE PROP (0 < i <= Int.max_signed / 4;
                  0 <= fold_right Z.add 0 history <= Int.max_signed / 4)
            PARAMS (self; Vint (Int.repr i)) SEP (instance history self)
        POST EX v, PROP (2 * fold_right Z.add 0 history < v
                           <= 2 * fold_right Z.add 0 (i :: history))
          RETURN (Vint (Int.repr v)) SEP (instance (i :: history) self)

  Here the invariant is the `data` cell (offset 8 of `struct foo_object`)
  holding `2 * history.sum` (`fooInv`); the spacer is padding and the
  `malloc_token` is ownership bookkeeping, neither of which these method
  bodies touch.  The object must lie inside the address space (part of VST's
  `field_compatible`): `hP`.  The bound on `history.sum` in `twiddle_spec`
  turns out to be unnecessary (machine arithmetic wraps the same way on both
  sides), so only `0 < i` is assumed.

  VST's `body_make_foo` and `body_main` (dynamic dispatch through the method
  table) are not ported.
-/
import VST.progs.object
import CCLib
open CC CC.Sep CC.HProp
open Object

namespace VST.Verif.Object

/-! ## The layout of `struct foo_object` -/

abbrev tfoo : Ty := .Tstruct _foo_object noattr
abbrev tobj : Ty := .Tstruct _object noattr

def coFoo : Composite :=
  match prog.prog_comp_env.get _foo_object with
  | some co => co
  | none => { co_su := .Struct, co_members := [], co_attr := noattr,
              co_sizeof := 0, co_alignof := 1, co_rank := 0 }

theorem get_foo : prog.prog_comp_env.get _foo_object = some coFoo := rfl
theorem off_data : fieldOffset prog.prog_comp_env _data coFoo.co_members = .OK (8, .Full) := by
  decide

/-- `foo_invariant history self`: the `data` field of the `struct foo_object`
    at `b + o` holds `2 * history.sum`. -/
def fooInv (perm : Permission) (b : Block) (o : Integers.Ptrofs) (history : List Z) : HProp :=
  mapsto .Mint32 perm b (Integers.Ptrofs.unsigned o + 8)
    (.Vint (Integers.Int.repr (2 * history.sum)))

/-! ## The specifications -/

/-- `foo_reset_spec` (`reset_spec foo_invariant`). -/
def resetSpec (perm : Permission) (b : Block) (o : Integers.Ptrofs) (history : List Z) :
    Sep.FunSpec where
  tyargs := [tptr tobj]
  tyres := tvoid
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr b o] ∧ fooInv perm b o history hp
  post := fun _ hp => fooInv perm b o [] hp
  measure := fun _ => 0

/-- `foo_twiddle_spec` (`twiddle_spec foo_invariant`). -/
def twiddleSpec (perm : Permission) (b : Block) (o : Integers.Ptrofs) (i : Z)
    (history : List Z) : Sep.FunSpec where
  tyargs := [tptr tobj, tint]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr b o, .Vint (Integers.Int.repr i)] ∧
    fooInv perm b o history hp
  post := fun r hp => ∃ v : Z, 2 * history.sum < v ∧ v ≤ 2 * (i :: history).sum ∧
    r = .Vint (Integers.Int.repr v) ∧ fooInv perm b o (i :: history) hp
  measure := fun _ => 0

/-! ## The address of `((struct foo_object *)self)->data` -/

section
variable {ge : CGenv} (hcenv : ge.genv_cenv = prog.prog_comp_env)

include hcenv in
theorem lvalue_data {e : Env} {le : TempEnv} {m : Mem} {b : Block} {o : Integers.Ptrofs}
    (hx : le.get _self = some (.Vptr b o)) :
    EvalLvalue ge e le m (.Efield (.Ederef (.Ecast (.Etempvar _self (tptr tobj)) (tptr tfoo)) tfoo)
      _data tint) b (Integers.Ptrofs.add o (Integers.Ptrofs.repr 8)) .Full :=
  EvalLvalue.Efield_struct _ _data tint b o _foo_object coFoo noattr 8 .Full
    (EvalExpr.Elvalue _ b o .Full _
      (EvalLvalue.Ederef _ _ _ _ (EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ _ _ hx)
        (semCast_ptr_ptr m _ _ _ _ _ (Or.inr ⟨b, o, rfl⟩))))
      (DerefLoc.copy rfl))
    rfl (hcenv ▸ get_foo) (hcenv ▸ off_data)

end

theorem fld8 (o : Integers.Ptrofs) (hP : Integers.Ptrofs.unsigned o + 12 ≤ 18446744073709551616) :
    Integers.Ptrofs.unsigned (Integers.Ptrofs.add o (Integers.Ptrofs.repr 8))
      = Integers.Ptrofs.unsigned o + 8 :=
  ptrofs_add_nonneg_unsigned o 8 (by zomega) (by zomega)

/-! ## `foo_reset` -/

/-- **`foo_reset` satisfies `foo_reset_spec`** (VST's `body_foo_reset`). -/
theorem reset_satisfies (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (perm : Permission) (hpw : permOrder perm .Writable = true) (b : Block)
    (o : Integers.Ptrofs) (history : List Z)
    (hP : Integers.Ptrofs.unsigned o + 12 ≤ 18446744073709551616) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_foo_reset)
      (resetSpec perm b o history) [.Vptr b o] := by
  let L := (createUndefTemps f_foo_reset.fn_temps).set _self (.Vptr b o)
  refine satisfies_internal_noVars_void ge _ f_foo_reset _ _
    (AtH L (fooInv perm b o history ∗ emp))
    (fun _ => ⟨L, FunctionEntry2.intro (by decide) (by decide) (by decide)
      (AllocVariables.nil _ _) rfl, fun hp h => ⟨rfl, rfl, by rw [sep_emp_eq]; exact h.2⟩⟩) ?_
  refine Sep.triple_fallthrough ge _ f_foo_reset _ _ _ _
    (triple_assign_atE_front ge _ f_foo_reset emptyEnv L _ _ _ .Mint32 perm b _
      (Integers.Ptrofs.unsigned o + 8) _ (.Vint (Integers.Int.repr 0)) (.Vint (Integers.Int.repr 0))
      hpw rfl (fld8 o hP) (fun m => lvalue_data hcenv rfl)
      (fun m => EvalExpr.Econst_int _ _) (fun m => semCast_int m _)) ?_
  rintro e le hp ⟨he, -, hH⟩
  refine ⟨he, ?_⟩
  rw [sep_emp_eq] at hH
  exact hH

/-! ## `foo_twiddle` -/

/-- **`foo_twiddle` satisfies `foo_twiddle_spec`** (VST's `body_foo_twiddle`). -/
theorem twiddle_satisfies (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (perm : Permission) (hpw : permOrder perm .Writable = true) (b : Block)
    (o : Integers.Ptrofs) (i : Z) (history : List Z) (hi : 0 < i)
    (hP : Integers.Ptrofs.unsigned o + 12 ≤ 18446744073709551616) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_foo_twiddle)
      (twiddleSpec perm b o i history) [.Vptr b o, .Vint (Integers.Int.repr i)] := by
  have hpr : permOrder perm .Readable = true := readable_of_writable hpw
  let s := history.sum
  let L := ((createUndefTemps f_foo_twiddle.fn_temps).set _self (.Vptr b o)).set _i
    (.Vint (Integers.Int.repr i))
  let H := fooInv perm b o history ∗ emp
  refine satisfies_internal_noVars ge _ f_foo_twiddle _ _ (AtH L H)
    (fun _ => ⟨L, FunctionEntry2.intro (by decide) (by decide) (by decide)
      (AllocVariables.nil _ _) rfl, fun hp h => ⟨rfl, rfl, by
        show (fooInv perm b o history ∗ emp) hp
        rw [sep_emp_eq]; exact h.2⟩⟩) ?_
  -- `d = ((struct foo_object *)self)->data;`
  let L1 := L.set _d (.Vint (Integers.Int.repr (2 * s)))
  refine Sep.triple_seq_only ge _ f_foo_twiddle
    (triple_set_atH ge _ f_foo_twiddle L H _ _ (.Vint (Integers.Int.repr (2 * s)))
      (fun m hp hH hag => by
        rw [show H = fooInv perm b o history from sep_emp_eq _] at hH
        exact eval_lvalue_mapsto rfl hpr (lvalue_data hcenv rfl) (fld8 o hP) hH hag)) ?_
  -- `((struct foo_object *)self)->data = d + 2 * i;`
  refine Sep.triple_seq_only ge _ f_foo_twiddle
    (triple_assign_atE_front ge _ f_foo_twiddle emptyEnv L1 _ _ _ .Mint32 perm b _
      (Integers.Ptrofs.unsigned o + 8) _ (.Vint (Integers.Int.repr (2 * (i + s))))
      (.Vint (Integers.Int.repr (2 * (i + s))))
      hpw rfl (fld8 o hP) (fun m => lvalue_data hcenv rfl)
      (fun m => ?_) (fun m => semCast_int m _)) ?_
  · refine EvalExpr.Ebinop .Oadd _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ rfl)
      (EvalExpr.Ebinop .Omul _ _ _ _ _ _ (EvalExpr.Econst_int _ _) (EvalExpr.Etempvar _ _ _ rfl)
        (semBinop_mul_int _ _ _ _)) ?_
    simp only [typeof]
    have hm : Integers.Int.mul (Integers.Int.repr 2) (Integers.Int.repr i)
        = Integers.Int.repr (2 * i) := (Integers.MI.repr_mul 2 i).symm
    rw [semBinop_add_int, hm, repr_add]
    congr 3
    show 2 * s + 2 * i = 2 * (i + s)
    zomega
  -- `return d + i;`
  refine Sep.triple_conseq ge _ f_foo_twiddle
    (triple_return_atH ge _ f_foo_twiddle L1 _ _ (.Vint (Integers.Int.repr (2 * s + i)))
      (.Vint (Integers.Int.repr (2 * s + i)))
      (fun _ _ _ _ => by
        refine EvalExpr.Ebinop .Oadd _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ rfl)
          (EvalExpr.Etempvar _ _ _ rfl) ?_
        simp only [typeof]
        rw [semBinop_add_int, repr_add])
      (fun m => semCast_int m _))
    (fun _ _ _ x => x) (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim)
    (fun _ _ _ x => x.elim) ?_
  rintro r hp ⟨rfl, hH⟩
  refine ⟨2 * s + i, by zomega, ?_, rfl, ?_⟩
  · show 2 * s + i ≤ 2 * (i + s)
    zomega
  · rw [sep_emp_eq] at hH
    exact hH

end VST.Verif.Object
