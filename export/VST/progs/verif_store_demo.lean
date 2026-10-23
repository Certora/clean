/-
  Port of VST's `progs/verif_store_demo.v`: `set22` and `fiddle` of
  `vst/progs/store_demo.c`, which store through computed struct-field and
  array addresses.

      typedef struct int_pair { int fst; int snd; } int_pair_t;
      typedef struct pair_pair { int_pair_t left; int_pair_t right; } pair_pair_t;

      void set22(pair_pair_t* pps, int i, int v) {
        pps[i].right.snd = 0;
        int_pair_t* p = &pps[i].right;
        p->snd = v;
      }

      void fiddle (unsigned int *p) {
        p[-1] = 3;
      }

  VST's specifications:

      DECLARE _set22
       WITH pps: val, i: Z, v: int, x11: int, x12: int, x21: int, x22: int, sh : share
       PRE [ tptr pair_pair_t, tint, tint]
         PROP  (writable_share sh; 0 <= i < array_size)
         PARAMS (pps; Vint (Int.repr i); Vint v)
         SEP   (field_at sh (tarray pair_pair_t array_size) [ArraySubsc i]
                         ((Vint x11, Vint x12), (Vint x21, Vint x22)) pps)
       POST [ tvoid ]
         PROP () RETURN ()
         SEP   (field_at sh (tarray pair_pair_t array_size) [ArraySubsc i]
                         ((Vint x11, Vint x12), (Vint x21, Vint v)) pps).

      DECLARE _fiddle
       WITH p: val, n: Z, tag: Z, contents: list Z
       PRE [ tptr tuint ]
         PROP  (Zlength contents = n)
         PARAMS (p)
         SEP (data_at Ews (tarray tuint (1+n)) (map Vint (map Int.repr (tag::contents)))
                      (offset_val (-sizeof tuint) p))
       POST [ tvoid ]
         PROP () RETURN ()
         SEP (data_at Ews (tarray tuint (1+n)) (map Vint (map Int.repr (3::contents)))
                      (offset_val (-sizeof tuint) p)).

  As in `verif_field_loadstore`, the preconditions own only the memory the
  functions write — `pps[i].right.snd` at byte offset `16 * i + 12`, and the
  header word `p[-1]` — since the triples carry an arbitrary frame, which
  keeps the other fields of `pps[i]` (resp. `contents`) unchanged.  VST's
  `field_at`/`data_at` imply that the objects fit in the address space; this
  is the hypothesis `hno` (resp. `4 ≤ ofs`).
-/
import VST.progs.store_demo
import CCLib.logic.ExactTempsHeap
import CCLib.logic.FunspecVoid
open CC CC.Sep CC.HProp
open Store_demo

namespace VST.Verif.StoreDemo

/-! ## Layout -/

def coIP : Composite :=
  match prog.prog_comp_env.get _int_pair with
  | some co => co
  | none => { co_su := .Struct, co_members := [], co_attr := noattr,
              co_sizeof := 0, co_alignof := 1, co_rank := 0 }

def coPP : Composite :=
  match prog.prog_comp_env.get _pair_pair with
  | some co => co
  | none => { co_su := .Struct, co_members := [], co_attr := noattr,
              co_sizeof := 0, co_alignof := 1, co_rank := 0 }

abbrev tIP : Ty := .Tstruct _int_pair noattr
abbrev tPP : Ty := .Tstruct _pair_pair noattr

theorem get_ip : prog.prog_comp_env.get _int_pair = some coIP := rfl
theorem get_pp : prog.prog_comp_env.get _pair_pair = some coPP := rfl
theorem sizeof_pp : sizeof prog.prog_comp_env tPP = ((16 : Nat) : _root_.Int) := by decide
theorem offset_right : fieldOffset prog.prog_comp_env _right coPP.co_members = .OK (8, .Full) := by
  decide
theorem offset_snd : fieldOffset prog.prog_comp_env _snd coIP.co_members = .OK (4, .Full) := by
  decide

/-- The layout facts the address computations need: `pair_pair_t` is 16
    bytes, `right` is at offset 8 and `snd` at offset 4.  Stated for an
    arbitrary composite environment, so that `verif_load_demo` (whose program
    declares the same two structs) reuses the lemmas below. -/
structure PairLayout (cenv : CompositeEnv) (cPP cIP : Composite) : Prop where
  sz : sizeof cenv tPP = ((16 : Nat) : _root_.Int)
  getPP : cenv.get _pair_pair = some cPP
  getIP : cenv.get _int_pair = some cIP
  right : fieldOffset cenv _right cPP.co_members = .OK (8, .Full)
  snd : fieldOffset cenv _snd cIP.co_members = .OK (4, .Full)

theorem layout : PairLayout prog.prog_comp_env coPP coIP :=
  ⟨sizeof_pp, get_pp, get_ip, offset_right, offset_snd⟩

/-! ## `set22` -/

/-- `set22_spec`: `pps[i].right.snd` becomes `v`. -/
def set22Spec (perm : Permission) (b : Block) (ofs : Integers.Ptrofs) (i : Nat)
    (v x22 : Integers.Int) : Sep.FunSpec where
  tyargs := [tptr tPP, tint, tint]
  tyres := tvoid
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr b ofs, .Vint (Integers.Int.repr i), .Vint v]
    ∧ mapsto .Mint32 perm b (Integers.Ptrofs.unsigned ofs + 16 * i + 12) (.Vint x22) hp
  post := fun _ hp =>
    mapsto .Mint32 perm b (Integers.Ptrofs.unsigned ofs + 16 * i + 12) (.Vint v) hp
  measure := fun _ => 0

/-- `pps[i]`, `pps[i].right`, `pps[i].right.snd` -/
def ppsI : Expr :=
  .Ederef (.Ebinop .Oadd (.Etempvar _pps (tptr tPP)) (.Etempvar _i tint) (tptr tPP)) tPP
def ppsIRight : Expr := .Efield ppsI _right tIP

theorem set22_body : f_set22.fn_body =
    .Ssequence (.Sassign (.Efield ppsIRight _snd tint) (.Econst_int (Integers.Int.repr 0) tint))
      (.Ssequence (.Sset _p (.Eaddrof ppsIRight (tptr tIP)))
        (.Sassign (.Efield (.Ederef (.Etempvar _p (tptr tIP)) tIP) _snd tint)
          (.Etempvar _v tint))) := rfl

section
variable (ge : CGenv) (perm : Permission) (b : Block) (ofs : Integers.Ptrofs) (i : Nat)
  (v x22 : Integers.Int)
  {cPP cIP : Composite} (hL : PairLayout ge.genv_cenv cPP cIP)
  (hpw : permOrder perm .Writable = true)
  (hi : i < 100)
  (hno : Integers.Ptrofs.unsigned ofs + 16 * (i : _root_.Int) + 16 ≤ 18446744073709551616)

/-- The temporaries on entry. -/
def setL : TempEnv :=
  (((createUndefTemps f_set22.fn_temps).set _pps (.Vptr b ofs)).set _i
    (.Vint (Integers.Int.repr i))).set _v (.Vint v)

/-- The address of `pps[i]`. -/
def addrI : Integers.Ptrofs := idxOfs ge.genv_cenv tPP .Signed ofs (Integers.Int.repr i)

include hL hi hno in
theorem addrI_unsigned :
    Integers.Ptrofs.unsigned (addrI ge ofs i) = Integers.Ptrofs.unsigned ofs + 16 * i := by
  refine idxOfs_unsigned _ _ _ _ i 16 (hL.sz) (by omega) (by zomega) (by zomega)

include hL hi hno in
theorem addrRight_unsigned :
    Integers.Ptrofs.unsigned (Integers.Ptrofs.add (addrI ge ofs i) (Integers.Ptrofs.repr 8))
      = Integers.Ptrofs.unsigned ofs + 16 * i + 8 := by
  rw [ptrofs_add_nonneg_unsigned _ _ (by omega) (by rw [addrI_unsigned ge ofs i hL hi hno]; zomega),
    addrI_unsigned ge ofs i hL hi hno]

include hL hi hno in
theorem addrSnd_unsigned :
    Integers.Ptrofs.unsigned (Integers.Ptrofs.add
        (Integers.Ptrofs.add (addrI ge ofs i) (Integers.Ptrofs.repr 8)) (Integers.Ptrofs.repr 4))
      = Integers.Ptrofs.unsigned ofs + 16 * i + 12 := by
  rw [ptrofs_add_nonneg_unsigned _ _ (by omega) (by rw [addrRight_unsigned ge ofs i hL hi hno]; zomega),
    addrRight_unsigned ge ofs i hL hi hno]
  zomega

/-- `pps[i]` evaluates (as a struct, i.e. to its address). -/
theorem eval_ppsI (L : TempEnv) (m : Mem) (hL1 : L.get _pps = some (.Vptr b ofs))
    (hL2 : L.get _i = some (.Vint (Integers.Int.repr i))) :
    EvalExpr ge emptyEnv L m ppsI (.Vptr b (addrI ge ofs i)) :=
  EvalExpr.Elvalue _ _ _ .Full _
    (eval_index_lvalue (EvalExpr.Etempvar _ _ _ hL1) (EvalExpr.Etempvar _ _ _ hL2) rfl)
    (DerefLoc.copy rfl)

include hL in
/-- `pps[i].right` as an l-value. -/
theorem lvalue_right (L : TempEnv) (m : Mem) (hL1 : L.get _pps = some (.Vptr b ofs))
    (hL2 : L.get _i = some (.Vint (Integers.Int.repr i))) :
    EvalLvalue ge emptyEnv L m ppsIRight b
      (Integers.Ptrofs.add (addrI ge ofs i) (Integers.Ptrofs.repr 8)) .Full :=
  EvalLvalue.Efield_struct _ _ _ b _ _pair_pair cPP noattr 8 .Full
    (eval_ppsI ge b ofs i L m hL1 hL2) rfl hL.getPP hL.right

include hL in
/-- `(... ).snd` as an l-value, for any expression of type `int_pair_t`
    evaluating to `pps[i].right`'s address. -/
theorem lvalue_snd (L : TempEnv) (m : Mem) (a : Expr) (ha : typeof a = tIP)
    (hev : EvalExpr ge emptyEnv L m a
      (.Vptr b (Integers.Ptrofs.add (addrI ge ofs i) (Integers.Ptrofs.repr 8)))) :
    EvalLvalue ge emptyEnv L m (.Efield a _snd tint) b
      (Integers.Ptrofs.add (Integers.Ptrofs.add (addrI ge ofs i) (Integers.Ptrofs.repr 8))
        (Integers.Ptrofs.repr 4)) .Full :=
  EvalLvalue.Efield_struct _ _ _ b _ _int_pair cIP noattr 4 .Full hev ha
    hL.getIP hL.snd

end

section
variable (ge : CGenv) (perm : Permission) (b : Block) (ofs : Integers.Ptrofs) (i : Nat)
  (v x22 : Integers.Int)
  (hcenv : ge.genv_cenv = prog.prog_comp_env)
  (hpw : permOrder perm .Writable = true)
  (hi : i < 100)
  (hno : Integers.Ptrofs.unsigned ofs + 16 * (i : _root_.Int) + 16 ≤ 18446744073709551616)
include hcenv hpw hi hno

/-- **`set22` satisfies `set22_spec`** (VST's `body_set22_root_expr`). -/
theorem set22_satisfies :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_set22) (set22Spec perm b ofs i v x22)
      [.Vptr b ofs, .Vint (Integers.Int.repr i), .Vint v] := by
  have hL : PairLayout ge.genv_cenv coPP coIP := hcenv ▸ layout
  let L := setL b ofs i v
  let X := Integers.Ptrofs.unsigned ofs + 16 * (i : _root_.Int) + 12
  have hL1 : L.get _pps = some (.Vptr b ofs) := rfl
  have hL2 : L.get _i = some (.Vint (Integers.Int.repr i)) := rfl
  refine satisfies_internal_noVars_void ge _ f_set22 _ _ (AtH L (mapsto .Mint32 perm b X (.Vint x22)))
    (fun _ => ⟨L, FunctionEntry2.intro (by decide) (by decide) (by decide)
      (AllocVariables.nil _ _) rfl, fun hp h => ⟨rfl, rfl, h.2⟩⟩) ?_
  rw [set22_body]
  refine Sep.triple_seq ge _ f_set22 _ (AtH L (mapsto .Mint32 perm b X (.Vint (Integers.Int.repr 0))))
    _ _ _ ?_ ?_
  · exact Sep.triple_fallthrough ge _ f_set22 _ _ _ _
      (triple_assign_at ge _ f_set22 L _ _ .Mint32 perm b _ X _ _ _ hpw rfl
        (addrSnd_unsigned ge ofs i hL hi hno)
        (fun m => lvalue_snd ge b ofs i hL L m _ rfl
          (eval_field_copy (sid := _pair_pair) (att := noattr) rfl rfl hL.getPP
            hL.right (eval_ppsI ge b ofs i L m hL1 hL2)))
        (fun _ => EvalExpr.Econst_int _ _) (fun m => semCast_int m _))
      (fun _ _ _ x => x)
  let L' := L.set _p (.Vptr b (Integers.Ptrofs.add (addrI ge ofs i) (Integers.Ptrofs.repr 8)))
  refine Sep.triple_seq ge _ f_set22 _
    (AtH L' (mapsto .Mint32 perm b X (.Vint (Integers.Int.repr 0)))) _ _ _ ?_ ?_
  · refine Sep.triple_fallthrough ge _ f_set22 _ _ _ _ ?_ (fun _ _ _ x => x)
    exact Sep.triple_set ge _ f_set22 _ _ _ _ (fun e le hp m hP _ => by
      obtain ⟨rfl, rfl, hm⟩ := hP
      exact ⟨_, EvalExpr.Eaddrof _ _ _ _ (lvalue_right ge b ofs i hL _ m hL1 hL2),
        rfl, rfl, hm⟩)
  · refine Sep.triple_fallthrough ge _ f_set22 _ _ _ _
      (triple_assign_at ge _ f_set22 L' _ _ .Mint32 perm b _ X _ (.Vint v) _ hpw rfl
        (addrSnd_unsigned ge ofs i hL hi hno)
        (fun m => lvalue_snd ge b ofs i hL L' m _ rfl
          (EvalExpr.Elvalue _ _ _ .Full _
            (EvalLvalue.Ederef _ _ _ _ (EvalExpr.Etempvar _ _ _ (PTree.gss _ _ _)))
            (DerefLoc.copy rfl)))
        (fun _ => EvalExpr.Etempvar _ _ _ rfl) (fun m => semCast_int m _))
      (fun e le hp h => ⟨h.1, h.2.2⟩)

end

/-! ## `fiddle` -/

/-- `fiddle_spec`: the header word `p[-1]` becomes `3`. -/
def fiddleSpec (perm : Permission) (b : Block) (ofs : Integers.Ptrofs) (tag : Integers.Int) :
    Sep.FunSpec where
  tyargs := [tptr tuint]
  tyres := tvoid
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr b ofs]
    ∧ mapsto .Mint32 perm b (Integers.Ptrofs.unsigned ofs - 4) (.Vint tag) hp
  post := fun _ hp =>
    mapsto .Mint32 perm b (Integers.Ptrofs.unsigned ofs - 4) (.Vint (Integers.Int.repr 3)) hp
  measure := fun _ => 0

/-- `p - 1` for an `unsigned int *` that does not point at the start of its
    block. -/
theorem addr_minus1 (cenv : CompositeEnv) (ofs : Integers.Ptrofs)
    (h4 : 4 ≤ Integers.Ptrofs.unsigned ofs) :
    Integers.Ptrofs.unsigned (idxOfs cenv tuint .Signed ofs
        (Integers.Int.neg (Integers.Int.repr 1)))
      = Integers.Ptrofs.unsigned ofs - 4 := by
  have hsz : sizeof cenv tuint = 4 := by simp [sizeof, tuint]
  have hm : Integers.Ptrofs.mul (Integers.Ptrofs.repr 4)
      (Cop.ptrofsOfInt .Signed (Integers.Int.neg (Integers.Int.repr 1)))
      = Integers.Ptrofs.repr (-4) := by decide
  rw [idxOfs, hsz, hm, ptrofs_add_neg_unsigned ofs 4 (by decide) h4]

theorem semCast_int_uint (m : Mem) (x : Integers.Int) :
    Cop.semCast (.Vint x) tint tuint m = some (.Vint x) := by
  simp [Cop.semCast, Cop.classifyCast, tint, tuint, Cop.castIntInt]

/-- **`fiddle` satisfies `fiddle_spec`** (VST's `body_fiddle`). -/
theorem fiddle_satisfies (ge : CGenv) (perm : Permission) (b : Block) (ofs : Integers.Ptrofs)
    (tag : Integers.Int) (hpw : permOrder perm .Writable = true)
    (h4 : 4 ≤ Integers.Ptrofs.unsigned ofs) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_fiddle) (fiddleSpec perm b ofs tag)
      [.Vptr b ofs] := by
  let L := (createUndefTemps f_fiddle.fn_temps).set _p (.Vptr b ofs)
  let X := Integers.Ptrofs.unsigned ofs - 4
  refine satisfies_internal_noVars_void ge _ f_fiddle _ _ (AtH L (mapsto .Mint32 perm b X (.Vint tag)))
    (fun _ => ⟨L, FunctionEntry2.intro (by decide) (by decide) (by decide)
      (AllocVariables.nil _ _) rfl, fun hp h => ⟨rfl, rfl, h.2⟩⟩) ?_
  exact Sep.triple_fallthrough ge _ f_fiddle _ _ _ _
    (triple_assign_at ge _ f_fiddle L _ _ .Mint32 perm b _ X _ _ _ hpw rfl
      (addr_minus1 ge.genv_cenv ofs h4)
      (fun m => eval_index_lvalue (EvalExpr.Etempvar _ _ _ rfl)
        (EvalExpr.Eunop .Oneg _ _ _ _ (EvalExpr.Econst_int _ _) (semUnop_neg_int m _)) rfl)
      (fun _ => EvalExpr.Econst_int _ _) (fun m => semCast_int_uint m _))
    (fun e le hp h => ⟨h.1, h.2.2⟩)

end VST.Verif.StoreDemo
