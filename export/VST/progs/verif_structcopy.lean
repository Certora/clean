/-
  Port of VST's `progs/verif_structcopy.v`: `f` of `vst/progs/structcopy.c`
  copies a struct into a local and adds its fields.

      struct foo {unsigned int a,b;};

      unsigned int f(struct foo *p) {
        struct foo q;
        q = *p;
        return q.a + q.b;
      }

  VST's specification:

      DECLARE _f
       WITH p: val, i: Z, j: Z
       PRE  [ tptr tfoo]
           PROP  ( ) PARAMS (p)
           SEP (data_at Ews tfoo (Vint (Int.repr i), Vint (Int.repr j)) p)
       POST [ tuint ]
           PROP() RETURN(Vint (Int.repr (i+j)))
           SEP (data_at Ews tfoo (Vint (Int.repr i), Vint (Int.repr j)) p).

  (In VST itself `body_f` is not proved: `start_function` fails on it, and the
  file ends with `Abort`.)

  Here `p` is `Vptr pb po`; `data_at … p` is the two `unsigned int` fields at
  offsets `0` and `4` (`fooAt`), at a readable permission `perm`; the
  4-alignment of `p` (part of VST's `field_compatible`) is the hypothesis
  `hal`.  `i`, `j` are `Int`s and the result is `Int.add i j`
  (`= Int.repr (i + j)` for VST's `Z`s).  The local `q` lives in memory: its
  entry and exit are `Sep.satisfies_oneLocal` / `Sep.triple_return_oneLocal`,
  and the struct assignment is the block copy `Sep.triple_assign_copy`.
-/
import VST.progs.structcopy
import CCLib
open CC CC.Sep CC.HProp
open Structcopy

namespace VST.Verif.Structcopy

/-! ## The layout of `struct foo` -/

/-- `struct foo` -/
abbrev tfoo : Ty := Ty.Tstruct _foo noattr

def coFoo : Composite :=
  match prog.prog_comp_env.get _foo with
  | some co => co
  | none => { co_su := .Struct, co_members := [], co_attr := noattr,
              co_sizeof := 0, co_alignof := 1, co_rank := 0 }

theorem get_foo : prog.prog_comp_env.get _foo = some coFoo := rfl
theorem sizeof_foo : sizeof prog.prog_comp_env tfoo = 8 := by decide
theorem alignblk_foo : alignofBlockcopy prog.prog_comp_env tfoo = 4 := by decide
theorem offset_a : fieldOffset prog.prog_comp_env _a coFoo.co_members = .OK (0, .Full) := by
  decide
theorem offset_b : fieldOffset prog.prog_comp_env _b coFoo.co_members = .OK (4, .Full) := by
  decide

/-! ## `data_at tfoo (i, j)` -/

/-- The two fields of a `struct foo` at `b + X`: `a = i`, `b = j`. -/
def fooAt (perm : Permission) (b : Block) (X : _root_.Int) (i j : Integers.Int) : HProp :=
  mapsto .Mint32 perm b X (.Vint i) ∗ mapsto .Mint32 perm b (X + 4) (.Vint j)

/-- The bytes of a `struct foo` holding `(i, j)`. -/
def fooBytes (i j : Integers.Int) : List MemVal :=
  encodeVal .Mint32 (.Vint i) ++ encodeVal .Mint32 (.Vint j)

theorem fooBytes_length (i j : Integers.Int) : (fooBytes i j).length = 8 := by
  simp [fooBytes, length_encodeVal]; rfl

/-- At an aligned address, the two fields are the struct's bytes. -/
theorem fooAt_bytes (perm : Permission) (b : Block) (X : _root_.Int) (i j : Integers.Int)
    (hal : X % 4 = 0) : fooAt perm b X i j = bytesPtsTo b perm X (fooBytes i j) := by
  rw [fooAt, mapsto_eq_bytes (chunk := .Mint32) hal,
    mapsto_eq_bytes (chunk := .Mint32) (show (X + 4) % 4 = 0 by omega), fooBytes,
    bytesPtsTo_append, length_encodeVal]
  rfl

/-! ## The specification -/

/-- `f_spec` -/
def fSpec (perm : Permission) (pb : Block) (po : Integers.Ptrofs) (i j : Integers.Int) :
    Sep.FunSpec where
  tyargs := [tptr tfoo]
  tyres := tuint
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr pb po] ∧ fooAt perm pb (Integers.Ptrofs.unsigned po) i j hp
  post := fun v hp => v = .Vint (Integers.Int.add i j)
    ∧ fooAt perm pb (Integers.Ptrofs.unsigned po) i j hp
  measure := fun _ => 0

/-! ## The proof -/

/-- `q.fld`, for the local `q` at block `b`, as an l-value. -/
theorem lvalue_q_field {ge : CGenv} (hcenv : ge.genv_cenv = prog.prog_comp_env) {le : TempEnv}
    {m : Mem} {b : Block} {fld : Ident} {delta : Z}
    (hoff : fieldOffset prog.prog_comp_env fld coFoo.co_members = .OK (delta, .Full)) :
    EvalLvalue ge (emptyEnv.set _q (b, tfoo)) le m (.Efield (.Evar _q tfoo) fld tuint) b
      (Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.repr delta)) .Full :=
  EvalLvalue.Efield_struct _ fld tuint b Integers.Ptrofs.zero _foo coFoo noattr delta .Full
    (EvalExpr.Elvalue _ b Integers.Ptrofs.zero .Full _ eval_lvalue_oneLocal
      (DerefLoc.copy (by decide)))
    rfl (hcenv ▸ get_foo) (hcenv ▸ hoff)

section
variable (ge : CGenv) (perm : Permission) (pb : Block) (po : Integers.Ptrofs) (i j : Integers.Int)
  (hcenv : ge.genv_cenv = prog.prog_comp_env)
  (hpr : permOrder perm .Readable = true)
  (hal : Integers.Ptrofs.unsigned po % 4 = 0)
include hcenv hpr hal

/-- **`f` satisfies `f_spec`** (VST's `body_f`). -/
theorem f_satisfies :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_f) (fSpec perm pb po i j) [.Vptr pb po] := by
  let X := Integers.Ptrofs.unsigned po
  let L : TempEnv := (createUndefTemps f_f.fn_temps).set _p (.Vptr pb po)
  refine satisfies_oneLocal ge f_f _ _ L _q tfoo rfl (by decide) (by decide) rfl
    (by rw [hcenv, sizeof_foo]; decide) fun bq => ?_
  let E : Env := emptyEnv.set _q (bq, tfoo)
  -- `q = *p;` copies the 8 bytes of `*p` into `q`
  refine triple_seq_only ge _ f_f (Q := AtE E L (fooAt perm pb X i j ∗ fooAt .Freeable bq 0 i j))
    (triple_assign_copy ge _ f_f _ _ _ _ perm .Freeable pb po bq Integers.Ptrofs.zero
      (fooBytes i j) (List.replicate 8 .Undef) hpr rfl rfl
      (by simp only [typeof]; rw [fooBytes_length, hcenv, sizeof_foo]; rfl)
      (by rw [fooBytes_length, List.length_replicate])
      (fun _ => by simp only [typeof]; rw [hcenv, alignblk_foo]; exact hal)
      (fun _ => by simp only [typeof]; rw [hcenv, alignblk_foo]; decide)
      (fun e le hp m hP _ => ?_)) ?_
  · obtain ⟨rfl, rfl, h1, h2, hd12, rfl, ⟨_, hfoo⟩, hu⟩ := hP
    rw [hcenv, sizeof_foo] at hu
    refine ⟨h1, h2, Heap.emp, Heap.disjoint_emp_right _,
      (by rw [Heap.union_emp]; exact Heap.disjoint_comm hd12),
      (by rw [Heap.union_emp]; exact Heap.union_comm hd12),
      (by rw [← fooAt_bytes _ _ _ _ _ hal]; exact hfoo), hu, eval_lvalue_oneLocal,
      EvalExpr.Elvalue _ _ _ .Full _ (EvalLvalue.Ederef _ _ _ _ (EvalExpr.Etempvar _ _ _ rfl))
        (DerefLoc.copy rfl), semCast_struct_same _ _ _ _ _ _, fun hDst' hb hd' => ?_⟩
    rw [Heap.union_emp] at hd' ⊢
    exact ⟨rfl, rfl, h1, hDst', Heap.disjoint_comm hd', Heap.union_comm hd', hfoo,
      by rw [fooAt_bytes _ _ _ _ _ (by decide)]; exact hb⟩
  -- reading the fields of `q`
  have hread : ∀ (L' : TempEnv) (fld : Ident) (delta : Z) (Y : _root_.Int) (v : Integers.Int)
      (hoff : fieldOffset prog.prog_comp_env fld coFoo.co_members = .OK (delta, .Full))
      (hY : Integers.Ptrofs.unsigned
        (Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.repr delta)) = Y)
      (hv : ∀ h, fooAt .Freeable bq 0 i j h → (mapsto .Mint32 .Freeable bq Y (.Vint v) ∗ fun _ => True) h)
      (m : Mem) (hp : Heap), (fooAt perm pb X i j ∗ fooAt .Freeable bq 0 i j) hp →
      Heap.Agrees hp m → EvalExpr ge E L' m (.Efield (.Evar _q tfoo) fld tuint) (.Vint v) := by
    intro L' fld delta Y v hoff hY hv m hp hH hag
    obtain ⟨h1, h2, hd, rfl, _, hq⟩ := hH
    obtain ⟨h3, h4, hd', rfl, hm, _⟩ := hv h2 hq
    exact eval_lvalue_mapsto (chunk := .Mint32) (v := .Vint v) rfl rfl (lvalue_q_field hcenv hoff)
      hY hm (Heap.Agrees_union_left (Heap.Agrees_union_right hd hag))
  -- `t'1 = q.a;`
  refine triple_seq_only ge _ f_f
    (triple_set_atE ge _ f_f E L _ _ _ (.Vint i)
      (hread L _a 0 0 i offset_a (by decide) fun h hq => by
        obtain ⟨h3, h4, hd, rfl, hm, _⟩ := hq; exact ⟨h3, h4, hd, rfl, hm, trivial⟩)) ?_
  -- `t'2 = q.b;`
  refine triple_seq_only ge _ f_f
    (triple_set_atE ge _ f_f E _ _ _ _ (.Vint j)
      (hread _ _b 4 4 j offset_b (by decide) fun h hq => by
        obtain ⟨h3, h4, hd, rfl, _, hm⟩ := hq
        exact ⟨h4, h3, Heap.disjoint_comm hd, Heap.union_comm hd, hm, trivial⟩)) ?_
  -- `return t'1 + t'2;` frees `q`
  refine triple_pre ge _ f_f (fun e le hp ⟨he, hl, hH⟩ => ⟨he, hl, by
    rwa [← fooAt_bytes .Freeable bq 0 i j (by decide)]⟩)
    (triple_return_oneLocal ge _ f_f _q tfoo bq _ (fooAt perm pb X i j) (fooBytes i j) _
      (.Vint (Integers.Int.add i j)) (.Vint (Integers.Int.add i j))
      (by rw [fooBytes_length, hcenv, sizeof_foo]; rfl)
      (fun m _ _ _ => EvalExpr.Ebinop .Oadd _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ rfl)
        (EvalExpr.Etempvar _ _ _ rfl) (semBinop_add_uint _ m i j))
      (fun m => semCast_uint m _))

end

end VST.Verif.Structcopy
