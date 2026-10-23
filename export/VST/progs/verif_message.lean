/-
  Port of VST's `progs/verif_message.v` (Appel et al., *Program Logics for
  Certified Compilers*, ch. 29): the serializer and deserializer of
  `struct intpair` in `vst/progs/message.c`.

      struct intpair {int x, y;};

      int intpair_serialize(void *p, unsigned char *buf) {
        int x = ((struct intpair *)p)->x;
        int y = ((struct intpair *)p)->y;
        ((int *)buf)[0]=x;
        ((int *)buf)[1]=y;
        return 8;
      }

      void intpair_deserialize(void *p, unsigned char *buf, int length) {
        int x = ((int *)buf)[0];
        int y = ((int *)buf)[1];
        ((struct intpair *)p)->x = x;
        ((struct intpair *)p)->y = y;
      }

  VST states both functions against the message format `intpair_message`,
  whose `mf_assert sh buf len (x, y)` is `len = 8 ∧ data_at sh (tarray tint 2)
  [x; y] buf`:

      serialize_spec: WITH data, p, buf, sh, sh'
        PRE PROP (readable_share sh; writable_share sh'; ...) PARAMS (p; buf)
          SEP (data_at sh t data p; memory_block sh' 8 buf)
        POST EX len, RETURN (Vint (Int.repr len))
          SEP (data_at sh t data p; mf_assert sh' buf len data; mf_restbuf sh' buf len)

      deserialize_spec: WITH data, p, buf, sh, sh', len
        PRE PROP (readable_share sh'; writable_share sh; 0 <= len <= 8)
          PARAMS (p; buf; Vint (Int.repr len))
          SEP (mf_assert sh' buf len data; data_at_ sh t p)
        POST PROP (mf_data_assert data) RETURN ()
          SEP (mf_assert sh' buf len data; data_at sh t data p)

  Here `struct intpair` and `int[2]` are both two consecutive `int` cells
  (`twoInts`).  `memory_block sh' 8 buf` and `data_at_ sh t p` (contents
  unknown) become two cells holding arbitrary values `v0`, `v1`.  The
  serializer's existential length is the constant `8` it returns, and its
  `mf_restbuf` (a block of `8 - 8 = 0` bytes) is empty.  For the
  deserializer the length argument is unused, so any `length` is allowed.
  The two objects must lie inside the address space (part of VST's
  `field_compatible`): `hP`, `hB`.

  VST's `body_main` (which reaches the two functions through function
  pointers stored in the global `intpair_message`, and keeps `p`, `q` and
  `buf` on the stack) is not ported.
-/
import VST.progs.message
import CCLib
open CC CC.Sep CC.HProp
open Message

namespace VST.Verif.Message

/-! ## The layout of `struct intpair` -/

abbrev tip : Ty := .Tstruct _intpair noattr

def coIP : Composite :=
  match prog.prog_comp_env.get _intpair with
  | some co => co
  | none => { co_su := .Struct, co_members := [], co_attr := noattr,
              co_sizeof := 0, co_alignof := 1, co_rank := 0 }

theorem get_ip : prog.prog_comp_env.get _intpair = some coIP := rfl
theorem off_x : fieldOffset prog.prog_comp_env _x coIP.co_members = .OK (0, .Full) := by decide
theorem off_y : fieldOffset prog.prog_comp_env _y coIP.co_members = .OK (4, .Full) := by decide

/-- Two consecutive `int` cells at `b + X`, holding `v0` and `v1`: a
    `struct intpair` (VST's `data_at sh t_struct_intpair (v0, v1)`) or an
    `int[2]` (VST's `data_at sh (tarray tint 2) [v0; v1]`). -/
def twoInts (perm : Permission) (b : Block) (X : _root_.Int) (v0 v1 : Val) : HProp :=
  mapsto .Mint32 perm b X v0 ∗ mapsto .Mint32 perm b (X + 4) v1

/-! ## The specifications -/

/-- `intpair_serialize_spec` (`serialize_spec intpair_message`). -/
def serializeSpec (perm perm' : Permission) (bp : Block) (op : Integers.Ptrofs) (bb : Block)
    (ob : Integers.Ptrofs) (x y : Integers.Int) : Sep.FunSpec where
  tyargs := [tptr tvoid, tptr tuchar]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr bp op, .Vptr bb ob] ∧ ∃ v0 v1,
    (twoInts perm bp (Integers.Ptrofs.unsigned op) (.Vint x) (.Vint y)
      ∗ twoInts perm' bb (Integers.Ptrofs.unsigned ob) v0 v1) hp
  post := fun v hp => v = .Vint (Integers.Int.repr 8) ∧
    (twoInts perm bp (Integers.Ptrofs.unsigned op) (.Vint x) (.Vint y)
      ∗ twoInts perm' bb (Integers.Ptrofs.unsigned ob) (.Vint x) (.Vint y)) hp
  measure := fun _ => 0

/-- `intpair_deserialize_spec` (`deserialize_spec intpair_message`). -/
def deserializeSpec (perm perm' : Permission) (bp : Block) (op : Integers.Ptrofs) (bb : Block)
    (ob : Integers.Ptrofs) (len x y : Integers.Int) : Sep.FunSpec where
  tyargs := [tptr tvoid, tptr tuchar, tint]
  tyres := tvoid
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr bp op, .Vptr bb ob, .Vint len] ∧ ∃ v0 v1,
    (twoInts perm bp (Integers.Ptrofs.unsigned op) v0 v1
      ∗ twoInts perm' bb (Integers.Ptrofs.unsigned ob) (.Vint x) (.Vint y)) hp
  post := fun _ hp =>
    (twoInts perm bp (Integers.Ptrofs.unsigned op) (.Vint x) (.Vint y)
      ∗ twoInts perm' bb (Integers.Ptrofs.unsigned ob) (.Vint x) (.Vint y)) hp
  measure := fun _ => 0

/-! ## Addresses -/

section
variable {ge : CGenv} (hcenv : ge.genv_cenv = prog.prog_comp_env)

include hcenv in
/-- `((struct intpair *)p)->fld` as an l-value. -/
theorem lvalue_ip {e : Env} {le : TempEnv} {m : Mem} {b : Block} {o : Integers.Ptrofs}
    (hx : le.get _p = some (.Vptr b o)) {fld : Ident} {delta : Z}
    (hoff : fieldOffset prog.prog_comp_env fld coIP.co_members = .OK (delta, .Full)) :
    EvalLvalue ge e le m (.Efield (.Ederef (.Ecast (.Etempvar _p (tptr tvoid)) (tptr tip)) tip)
      fld tint) b (Integers.Ptrofs.add o (Integers.Ptrofs.repr delta)) .Full :=
  EvalLvalue.Efield_struct _ fld tint b o _intpair coIP noattr delta .Full
    (EvalExpr.Elvalue _ b o .Full _
      (EvalLvalue.Ederef _ _ _ _ (EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ _ _ hx)
        (semCast_ptr_ptr m _ _ _ _ _ (Or.inr ⟨b, o, rfl⟩))))
      (DerefLoc.copy rfl))
    rfl (hcenv ▸ get_ip) (hcenv ▸ hoff)

/-- `((int *)buf)[i]` as an l-value. -/
theorem lvalue_buf {e : Env} {le : TempEnv} {m : Mem} {b : Block} {o : Integers.Ptrofs}
    (hx : le.get _buf = some (.Vptr b o)) (iv : Integers.Int) :
    EvalLvalue ge e le m (.Ederef (.Ebinop .Oadd (.Ecast (.Etempvar _buf (tptr tuchar)) (tptr tint))
      (.Econst_int iv tint) (tptr tint)) tint) b (idxOfs ge.genv_cenv tint .Signed o iv) .Full :=
  eval_index_lvalue (EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ _ _ hx)
    (semCast_ptr_ptr m _ _ _ _ _ (Or.inr ⟨b, o, rfl⟩))) (EvalExpr.Econst_int _ _) rfl

end

theorem idx0 (cenv : CompositeEnv) (o : Integers.Ptrofs) (hB : Integers.Ptrofs.unsigned o + 8 ≤ 18446744073709551616) :
    Integers.Ptrofs.unsigned (idxOfs cenv tint .Signed o (Integers.Int.repr 0))
      = Integers.Ptrofs.unsigned o := by
  have := idxOfs_unsigned cenv tint .Signed o 0 4 rfl (by decide) (by decide) (by zomega)
  simpa using this

theorem idx1 (cenv : CompositeEnv) (o : Integers.Ptrofs) (hB : Integers.Ptrofs.unsigned o + 8 ≤ 18446744073709551616) :
    Integers.Ptrofs.unsigned (idxOfs cenv tint .Signed o (Integers.Int.repr 1))
      = Integers.Ptrofs.unsigned o + 4 := by
  have := idxOfs_unsigned cenv tint .Signed o 1 4 rfl (by decide) (by decide) (by zomega)
  simpa using this

theorem fld0 (o : Integers.Ptrofs) (hP : Integers.Ptrofs.unsigned o + 8 ≤ 18446744073709551616) :
    Integers.Ptrofs.unsigned (Integers.Ptrofs.add o (Integers.Ptrofs.repr 0))
      = Integers.Ptrofs.unsigned o := by
  simpa using ptrofs_add_nonneg_unsigned o 0 (by zomega) (by zomega)

theorem fld4 (o : Integers.Ptrofs) (hP : Integers.Ptrofs.unsigned o + 8 ≤ 18446744073709551616) :
    Integers.Ptrofs.unsigned (Integers.Ptrofs.add o (Integers.Ptrofs.repr 4))
      = Integers.Ptrofs.unsigned o + 4 :=
  ptrofs_add_nonneg_unsigned o 4 (by zomega) (by zomega)

/-! ## `intpair_serialize` -/

/-- **`intpair_serialize` satisfies `intpair_serialize_spec`** (VST's
    `body_intpair_serialize`). -/
theorem serialize_satisfies (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (perm perm' : Permission) (hpr : permOrder perm .Readable = true)
    (hpw : permOrder perm' .Writable = true) (bp : Block) (op : Integers.Ptrofs) (bb : Block)
    (ob : Integers.Ptrofs) (x y : Integers.Int)
    (hP : Integers.Ptrofs.unsigned op + 8 ≤ 18446744073709551616)
    (hB : Integers.Ptrofs.unsigned ob + 8 ≤ 18446744073709551616) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_intpair_serialize)
      (serializeSpec perm perm' bp op bb ob x y) [.Vptr bp op, .Vptr bb ob] := by
  let P := Integers.Ptrofs.unsigned op
  let B := Integers.Ptrofs.unsigned ob
  let L := ((createUndefTemps f_intpair_serialize.fn_temps).set _p (.Vptr bp op)).set _buf
    (.Vptr bb ob)
  let S := twoInts perm bp P (.Vint x) (.Vint y)
  refine satisfies_internal_noVars ge _ f_intpair_serialize _ _
    (fun e le hp => ∃ v0 v1, AtH L (S ∗ twoInts perm' bb B v0 v1) e le hp)
    (fun _ => ⟨L, FunctionEntry2.intro (by decide) (by decide) (by decide)
      (AllocVariables.nil _ _) rfl, fun hp h => by
        obtain ⟨-, v0, v1, h⟩ := h
        exact ⟨v0, v1, rfl, rfl, h⟩⟩) ?_
  refine Sep.triple_exists ge _ f_intpair_serialize _ _ _ (fun v0 => ?_)
  refine Sep.triple_exists ge _ f_intpair_serialize _ _ _ (fun v1 => ?_)
  let H := S ∗ twoInts perm' bb B v0 v1
  -- `x = ((struct intpair *)p)->x;`
  let L1 := L.set _x (.Vint x)
  refine Sep.triple_seq_only ge _ f_intpair_serialize
    (triple_set_atH ge _ f_intpair_serialize L H _ _ (.Vint x) (fun m hp hH hag => by
      obtain ⟨h1, h2, hd, rfl, ⟨h11, h12, hd1, rfl, hcx, _⟩, _⟩ := hH
      exact eval_lvalue_mapsto rfl hpr (lvalue_ip hcenv rfl off_x) (fld0 op hP) hcx
        (Heap.Agrees_union_left (Heap.Agrees_union_left hag)))) ?_
  -- `y = ((struct intpair *)p)->y;`
  let L2 := L1.set _y (.Vint y)
  refine Sep.triple_seq_only ge _ f_intpair_serialize
    (triple_set_atH ge _ f_intpair_serialize L1 H _ _ (.Vint y) (fun m hp hH hag => by
      obtain ⟨h1, h2, hd, rfl, ⟨h11, h12, hd1, rfl, _, hcy⟩, _⟩ := hH
      exact eval_lvalue_mapsto rfl hpr (lvalue_ip hcenv rfl off_y) (fld4 op hP) hcy
        (Heap.Agrees_union_right hd1 (Heap.Agrees_union_left hag)))) ?_
  -- `((int *)buf)[0] = x;`
  have e1 : H = mapsto .Mint32 perm' bb B v0 ∗ (S ∗ mapsto .Mint32 perm' bb (B + 4) v1) := by
    simp only [H, twoInts, sep_left_comm_eq]
  rw [show AtH L2 H = AtH L2 _ from congrArg _ e1]
  refine Sep.triple_seq_only ge _ f_intpair_serialize
    (triple_assign_atE_front ge _ f_intpair_serialize emptyEnv L2 _ _ _ .Mint32 perm' bb _ B
      v0 (.Vint x) (.Vint x) hpw rfl (idx0 _ ob hB) (fun m => lvalue_buf rfl _)
      (fun m => EvalExpr.Etempvar _ _ _ rfl) (fun m => semCast_int m _)) ?_
  -- `((int *)buf)[1] = y;`
  have e2 : (mapsto .Mint32 perm' bb B (.Vint x) ∗ (S ∗ mapsto .Mint32 perm' bb (B + 4) v1))
      = mapsto .Mint32 perm' bb (B + 4) v1 ∗ (S ∗ mapsto .Mint32 perm' bb B (.Vint x)) := by
    rw [sep_comm_eq S, sep_left_comm_eq, sep_comm_eq S]
  rw [show AtE emptyEnv L2 _ = AtE emptyEnv L2 _ from congrArg _ e2]
  refine Sep.triple_seq_only ge _ f_intpair_serialize
    (triple_assign_atE_front ge _ f_intpair_serialize emptyEnv L2 _ _ _ .Mint32 perm' bb _ (B + 4)
      v1 (.Vint y) (.Vint y) hpw rfl (idx1 _ ob hB) (fun m => lvalue_buf rfl _)
      (fun m => EvalExpr.Etempvar _ _ _ rfl) (fun m => semCast_int m _)) ?_
  -- `return 8;`
  have e3 : (mapsto .Mint32 perm' bb (B + 4) (.Vint y) ∗ (S ∗ mapsto .Mint32 perm' bb B (.Vint x)))
      = S ∗ twoInts perm' bb B (.Vint x) (.Vint y) := by
    rw [sep_left_comm_eq, twoInts, sep_comm_eq (mapsto .Mint32 perm' bb (B + 4) _)]
  rw [show AtE emptyEnv L2 _ = AtE emptyEnv L2 _ from congrArg _ e3]
  exact triple_return_atH ge _ f_intpair_serialize L2 _ _ _ _
    (fun _ _ _ _ => EvalExpr.Econst_int _ _) (fun m => semCast_int m _)

/-! ## `intpair_deserialize` -/

/-- **`intpair_deserialize` satisfies `intpair_deserialize_spec`** (VST's
    `body_intpair_deserialize`). -/
theorem deserialize_satisfies (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (perm perm' : Permission) (hpw : permOrder perm .Writable = true)
    (hpr : permOrder perm' .Readable = true) (bp : Block) (op : Integers.Ptrofs) (bb : Block)
    (ob : Integers.Ptrofs) (len x y : Integers.Int)
    (hP : Integers.Ptrofs.unsigned op + 8 ≤ 18446744073709551616)
    (hB : Integers.Ptrofs.unsigned ob + 8 ≤ 18446744073709551616) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_intpair_deserialize)
      (deserializeSpec perm perm' bp op bb ob len x y) [.Vptr bp op, .Vptr bb ob, .Vint len] := by
  let P := Integers.Ptrofs.unsigned op
  let B := Integers.Ptrofs.unsigned ob
  let L := (((createUndefTemps f_intpair_deserialize.fn_temps).set _p (.Vptr bp op)).set _buf
    (.Vptr bb ob)).set _length (.Vint len)
  let D := twoInts perm' bb B (.Vint x) (.Vint y)
  refine satisfies_internal_noVars_void ge _ f_intpair_deserialize _ _
    (fun e le hp => ∃ v0 v1, AtH L (twoInts perm bp P v0 v1 ∗ D) e le hp)
    (fun _ => ⟨L, FunctionEntry2.intro (by decide) (by decide) (by decide)
      (AllocVariables.nil _ _) rfl, fun hp h => by
        obtain ⟨-, v0, v1, h⟩ := h
        exact ⟨v0, v1, rfl, rfl, h⟩⟩) ?_
  refine Sep.triple_exists ge _ f_intpair_deserialize _ _ _ (fun v0 => ?_)
  refine Sep.triple_exists ge _ f_intpair_deserialize _ _ _ (fun v1 => ?_)
  let H := twoInts perm bp P v0 v1 ∗ D
  -- `x = ((int *)buf)[0];`
  let L1 := L.set _x (.Vint x)
  refine Sep.triple_seq_only ge _ f_intpair_deserialize
    (triple_set_atH ge _ f_intpair_deserialize L H _ _ (.Vint x) (fun m hp hH hag => by
      obtain ⟨h1, h2, hd, rfl, _, ⟨h21, h22, hd2, rfl, hc0, _⟩⟩ := hH
      exact eval_lvalue_mapsto rfl hpr (lvalue_buf rfl _) (idx0 _ ob hB) hc0
        (Heap.Agrees_union_left (Heap.Agrees_union_right hd hag)))) ?_
  -- `y = ((int *)buf)[1];`
  let L2 := L1.set _y (.Vint y)
  refine Sep.triple_seq_only ge _ f_intpair_deserialize
    (triple_set_atH ge _ f_intpair_deserialize L1 H _ _ (.Vint y) (fun m hp hH hag => by
      obtain ⟨h1, h2, hd, rfl, _, ⟨h21, h22, hd2, rfl, _, hc1⟩⟩ := hH
      exact eval_lvalue_mapsto rfl hpr (lvalue_buf rfl _) (idx1 _ ob hB) hc1
        (Heap.Agrees_union_right hd2 (Heap.Agrees_union_right hd hag)))) ?_
  -- `((struct intpair *)p)->x = x;`
  have e1 : H = mapsto .Mint32 perm bp P v0 ∗ (mapsto .Mint32 perm bp (P + 4) v1 ∗ D) := by
    simp only [H, twoInts, sep_assoc_eq]
  rw [show AtH L2 H = AtH L2 _ from congrArg _ e1]
  refine Sep.triple_seq_only ge _ f_intpair_deserialize
    (triple_assign_atE_front ge _ f_intpair_deserialize emptyEnv L2 _ _ _ .Mint32 perm bp _ P
      v0 (.Vint x) (.Vint x) hpw rfl (fld0 op hP) (fun m => lvalue_ip hcenv rfl off_x)
      (fun m => EvalExpr.Etempvar _ _ _ rfl) (fun m => semCast_int m _)) ?_
  -- `((struct intpair *)p)->y = y;`
  have e2 : (mapsto .Mint32 perm bp P (.Vint x) ∗ (mapsto .Mint32 perm bp (P + 4) v1 ∗ D))
      = mapsto .Mint32 perm bp (P + 4) v1 ∗ (mapsto .Mint32 perm bp P (.Vint x) ∗ D) :=
    sep_left_comm_eq _ _ _
  rw [show AtE emptyEnv L2 _ = AtE emptyEnv L2 _ from congrArg _ e2]
  refine Sep.triple_fallthrough ge _ f_intpair_deserialize _ _ _ _
    (triple_assign_atE_front ge _ f_intpair_deserialize emptyEnv L2 _ _ _ .Mint32 perm bp _
      (P + 4) v1 (.Vint y) (.Vint y) hpw rfl (fld4 op hP) (fun m => lvalue_ip hcenv rfl off_y)
      (fun m => EvalExpr.Etempvar _ _ _ rfl) (fun m => semCast_int m _)) ?_
  rintro e le hp ⟨he, -, hH⟩
  refine ⟨he, ?_⟩
  show (twoInts perm bp P (.Vint x) (.Vint y) ∗ D) hp
  rwa [twoInts, sep_assoc_eq, sep_left_comm_eq]

end VST.Verif.Message
