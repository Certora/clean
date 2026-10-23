/-
  Port of VST's `progs/verif_load_demo.v`: `get22` and `get_little_endian`
  of `vst/progs/load_demo.c`, which load through computed struct-field and
  array addresses.

      int get22(pair_pair_t* pps, int i) {
        int_pair_t* p = &pps[i].right;
        int res = p->snd;
        return res;
      }

      unsigned int get_little_endian(unsigned char input[4]) {
        unsigned int b0 = (unsigned int) input[0];
        unsigned int b1 = (unsigned int) input[1];
        unsigned int b2 = input[2];
        unsigned int b3 = input[3];
        return (b0 | (b1 << 8) | (b2 << 16) | (b3 << 24));
      }

  VST's specifications:

      DECLARE _get22
       WITH pps: val, i: Z, x11: int, x12: int, x21: int, x22: int, sh : share
       PRE [ tptr pair_pair_t, tint ]
         PROP  (readable_share sh; 0 <= i < array_size)
         PARAMS (pps; Vint (Int.repr i))
         SEP   (field_at sh (tarray pair_pair_t array_size) [ArraySubsc i]
                         ((Vint x11, Vint x12), (Vint x21, Vint x22)) pps)
       POST [ tint ]
         PROP () RETURN (Vint x22)
         SEP   (field_at sh (tarray pair_pair_t array_size) [ArraySubsc i]
                         ((Vint x11, Vint x12), (Vint x21, Vint x22)) pps).

      DECLARE _get_little_endian
       WITH input : val, in_sh : share, arr : list Z
       PRE [ tptr tuchar ]
         PROP (Zlength arr = 4; readable_share in_sh;
               forall i, 0 <= i < 4 -> 0 <= Znth i arr <= Byte.max_unsigned)
         PARAMS (input)
         SEP (data_at in_sh (tarray tuchar 4) (map Vint (map Int.repr arr)) input)
       POST [ tuint ]
         PROP() RETURN (Vint (get_uint32_le arr))
         SEP (data_at in_sh (tarray tuchar 4) (map Vint (map Int.repr arr)) input).

  The program declares the same two structs as `store_demo.c`, so `get22`
  reuses the address lemmas of `verif_store_demo` (through `PairLayout`).  As
  there, the precondition of `get22` owns only the field it reads.  The byte
  buffer of `get_little_endian` is `arrayU8`, the list `arr` a function
  `f : Nat → Nat` of bytes (VST's range hypothesis is `∀ j, f j < 256`).

  `body_fiddle` (a loop over an array whose length is read from a header
  word) is in `verif_load_demo_fiddle`.
-/
import VST.progs.load_demo
import VST.progs.verif_store_demo
open CC CC.Sep CC.HProp
open Load_demo

namespace VST.Verif.LoadDemo

open VST.Verif.StoreDemo (PairLayout tPP tIP addrI addrSnd_unsigned lvalue_right lvalue_snd)

/-! ## `get22` -/

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

/-- `load_demo.c` lays out the two structs as `store_demo.c` does. -/
theorem layout : PairLayout prog.prog_comp_env coPP coIP :=
  ⟨by decide, rfl, rfl, by decide, by decide⟩

/-- `get22_spec`: returns `pps[i].right.snd`. -/
def get22Spec (perm : Permission) (b : Block) (ofs : Integers.Ptrofs) (i : Nat)
    (x22 : Integers.Int) : Sep.FunSpec where
  tyargs := [tptr tPP, tint]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr b ofs, .Vint (Integers.Int.repr i)]
    ∧ mapsto .Mint32 perm b (Integers.Ptrofs.unsigned ofs + 16 * i + 12) (.Vint x22) hp
  post := fun v hp => v = .Vint x22
    ∧ mapsto .Mint32 perm b (Integers.Ptrofs.unsigned ofs + 16 * i + 12) (.Vint x22) hp
  measure := fun _ => 0

/-- **`get22` satisfies `get22_spec`** (VST's `body_get22_root_expr`). -/
theorem get22_satisfies (ge : CGenv) (perm : Permission) (b : Block) (ofs : Integers.Ptrofs)
    (i : Nat) (x22 : Integers.Int)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hpr : permOrder perm .Readable = true) (hi : i < 100)
    (hno : Integers.Ptrofs.unsigned ofs + 16 * (i : _root_.Int) + 16 ≤ 18446744073709551616) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_get22) (get22Spec perm b ofs i x22)
      [.Vptr b ofs, .Vint (Integers.Int.repr i)] := by
  have hL : PairLayout ge.genv_cenv coPP coIP := hcenv ▸ layout
  let L := ((createUndefTemps f_get22.fn_temps).set _pps (.Vptr b ofs)).set _i
    (.Vint (Integers.Int.repr i))
  let X := Integers.Ptrofs.unsigned ofs + 16 * (i : _root_.Int) + 12
  let H := mapsto .Mint32 perm b X (.Vint x22)
  let A8 := Integers.Ptrofs.add (addrI ge ofs i) (Integers.Ptrofs.repr 8)
  refine satisfies_internal_noVars ge _ f_get22 _ _ (AtH L H)
    (fun _ => ⟨L, FunctionEntry2.intro (by decide) (by decide) (by decide)
      (AllocVariables.nil _ _) rfl, fun hp h => ⟨rfl, rfl, h.2⟩⟩) ?_
  refine Sep.triple_seq ge _ f_get22 _ (AtH (L.set _p (.Vptr b A8)) H) _ _ _
    (Sep.triple_fallthrough ge _ f_get22 _ _ _ _
      (triple_set_atH ge _ f_get22 L H _ _ _ (fun m _ _ _ =>
        EvalExpr.Eaddrof _ _ _ _ (lvalue_right ge b ofs i hL L m rfl rfl)))
      (fun _ _ _ x => x)) ?_
  let L' := (L.set _p (.Vptr b A8)).set _res (.Vint x22)
  refine Sep.triple_seq ge _ f_get22 _ (AtH L' H) _ _ _
    (Sep.triple_fallthrough ge _ f_get22 _ _ _ _
      (triple_set_atH ge _ f_get22 _ H _ _ _ (fun m hp hH hag =>
        eval_lvalue_mapsto (v := .Vint x22) rfl hpr
          (lvalue_snd ge b ofs i hL _ m _ rfl
            (EvalExpr.Elvalue _ _ _ .Full _
              (EvalLvalue.Ederef _ _ _ _ (EvalExpr.Etempvar _ _ _ (PTree.gss _ _ _)))
              (DerefLoc.copy rfl)))
          (addrSnd_unsigned ge ofs i hL hi hno) hH hag))
      (fun _ _ _ x => x)) ?_
  exact triple_return_atH ge _ f_get22 L' H _ _ _
    (fun _ _ _ _ => EvalExpr.Etempvar _ _ _ (PTree.gss _ _ _)) (fun m => semCast_int m _)

/-! ## `get_little_endian` -/

/-- VST's `get_uint32_le`: the bytes `f 0 … f 3`, little-endian. -/
def getUint32Le (f : Nat → Nat) : Integers.Int :=
  Integers.Int.or (Integers.Int.or (Integers.Int.or
      (Integers.Int.repr (f 0))
      (Integers.Int.shl (Integers.Int.repr (f 1)) (Integers.Int.repr 8)))
      (Integers.Int.shl (Integers.Int.repr (f 2)) (Integers.Int.repr 16)))
    (Integers.Int.shl (Integers.Int.repr (f 3)) (Integers.Int.repr 24))

/-- `get_little_endian_spec` -/
def getLittleEndianSpec (perm : Permission) (b : Block) (ofs : Integers.Ptrofs)
    (f : Nat → Nat) : Sep.FunSpec where
  tyargs := [tptr tuchar]
  tyres := tuint
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr b ofs] ∧ arrayU8 perm b (Integers.Ptrofs.unsigned ofs) 4 f hp
  post := fun v hp => v = .Vint (getUint32Le f) ∧ arrayU8 perm b (Integers.Ptrofs.unsigned ofs) 4 f hp
  measure := fun _ => 0

theorem semBinop_or_uint (cenv m) (x y : Integers.Int) :
    Cop.semBinaryOperation cenv .Oor (.Vint x) tuint (.Vint y) tuint m
      = some (.Vint (Integers.Int.or x y)) := rfl

theorem semBinop_shl_uint_int (cenv m) (x y : Integers.Int)
    (hy : Integers.Int.ltu y (Integers.Int.repr 32) = true) :
    Cop.semBinaryOperation cenv .Oshl (.Vint x) tuint (.Vint y) tint m
      = some (.Vint (Integers.Int.shl x y)) := by
  show (if Integers.Int.ltu y (Integers.Int.repr 32) then _ else _) = _
  rw [hy]; rfl

theorem semCast_uchar_uint (m : Mem) (x : Integers.Int) :
    Cop.semCast (.Vint x) tuchar tuint m = some (.Vint x) := rfl

/-- `input[k]` -/
def inputAt (k : Nat) : Expr :=
  .Ederef (.Ebinop .Oadd (.Etempvar _input (tptr tuchar))
    (.Econst_int (Integers.Int.repr k) tint) (tptr tuchar)) tuchar

/-- `e << k` and `e1 | e2` at `unsigned int`. -/
def shlU (x : Ident) (k : Nat) : Expr :=
  .Ebinop .Oshl (.Etempvar x tuint) (.Econst_int (Integers.Int.repr k) tint) tuint
def orU (a b : Expr) : Expr := .Ebinop .Oor a b tuint

theorem gle_body : f_get_little_endian.fn_body =
    .Ssequence (.Ssequence (.Sset _t'1 (inputAt 0)) (.Sset _b0 (.Ecast (.Etempvar _t'1 tuchar) tuint)))
      (.Ssequence (.Ssequence (.Sset _t'2 (inputAt 1))
          (.Sset _b1 (.Ecast (.Etempvar _t'2 tuchar) tuint)))
        (.Ssequence (.Sset _b2 (inputAt 2))
          (.Ssequence (.Sset _b3 (inputAt 3))
            (.Sreturn (some (orU (orU (orU (.Etempvar _b0 tuint) (shlU _b1 8)) (shlU _b2 16))
              (shlU _b3 24))))))) := rfl

section
variable (ge : CGenv) (perm : Permission) (b : Block) (ofs : Integers.Ptrofs) (f : Nat → Nat)
  (hpr : permOrder perm .Readable = true) (hb : ∀ j, f j < 256)
  (hno : ofs.toNat + 4 < 18446744073709551616)

include hpr hb hno in
/-- Reading `input[k]`, `k < 4`. -/
theorem eval_inputAt (L : TempEnv) (hL : L.get _input = some (.Vptr b ofs)) (k : Nat)
    (hk : k < 4) (m : Mem) (hp : Heap) (harr : arrayU8 perm b (Integers.Ptrofs.unsigned ofs) 4 f hp)
    (hag : Heap.Agrees hp m) :
    EvalExpr ge emptyEnv L m (inputAt k) (.Vint (Integers.Int.repr (f k))) :=
  eval_index_bytes hpr harr hag hk hb hL (EvalExpr.Econst_int _ _) rfl (by omega) (by omega)

include hpr hb hno in
/-- **`get_little_endian` satisfies `get_little_endian_spec`** (VST's
    `body_get_little_endian`). -/
theorem get_little_endian_satisfies :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_get_little_endian)
      (getLittleEndianSpec perm b ofs f) [.Vptr b ofs] := by
  let H := arrayU8 perm b (Integers.Ptrofs.unsigned ofs) 4 f
  let r : Nat → Val := fun k => .Vint (Integers.Int.repr (f k))
  let L0 := (createUndefTemps f_get_little_endian.fn_temps).set _input (.Vptr b ofs)
  let L1 := (L0.set _t'1 (r 0)).set _b0 (r 0)
  let L2 := (L1.set _t'2 (r 1)).set _b1 (r 1)
  let L3 := L2.set _b2 (r 2)
  let L4 := L3.set _b3 (r 3)
  refine satisfies_internal_noVars ge _ f_get_little_endian _ _ (AtH L0 H)
    (fun _ => ⟨L0, FunctionEntry2.intro (by decide) (by decide) (by decide)
      (AllocVariables.nil _ _) rfl, fun hp h => ⟨rfl, rfl, h.2⟩⟩) ?_
  rw [gle_body]
  refine Sep.triple_seq ge _ _ _ (AtH L1 H) _ _ _
    (Sep.triple_fallthrough ge _ _ _ _ _ _ (Sep.triple_seq_only ge _ _
      (triple_set_atH ge _ _ L0 H _ _ _ (fun m hp hH hag =>
        eval_inputAt ge perm b ofs f hpr hb hno L0 rfl 0 (by decide) m hp hH hag))
      (triple_set_atH ge _ _ _ H _ _ _ (fun _ _ _ _ =>
        EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ _ _ (PTree.gss _ _ _))
          (semCast_uchar_uint _ _)))) (fun _ _ _ x => x)) ?_
  refine Sep.triple_seq ge _ _ _ (AtH L2 H) _ _ _
    (Sep.triple_fallthrough ge _ _ _ _ _ _ (Sep.triple_seq_only ge _ _
      (triple_set_atH ge _ _ L1 H _ _ _ (fun m hp hH hag =>
        eval_inputAt ge perm b ofs f hpr hb hno L1 rfl 1 (by decide) m hp hH hag))
      (triple_set_atH ge _ _ _ H _ _ _ (fun _ _ _ _ =>
        EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ _ _ (PTree.gss _ _ _))
          (semCast_uchar_uint _ _)))) (fun _ _ _ x => x)) ?_
  refine Sep.triple_seq ge _ _ _ (AtH L3 H) _ _ _
    (Sep.triple_fallthrough ge _ _ _ _ _ _
      (triple_set_atH ge _ _ L2 H _ _ _ (fun m hp hH hag =>
        eval_inputAt ge perm b ofs f hpr hb hno L2 rfl 2 (by decide) m hp hH hag))
      (fun _ _ _ x => x)) ?_
  refine Sep.triple_seq ge _ _ _ (AtH L4 H) _ _ _
    (Sep.triple_fallthrough ge _ _ _ _ _ _
      (triple_set_atH ge _ _ L3 H _ _ _ (fun m hp hH hag =>
        eval_inputAt ge perm b ofs f hpr hb hno L3 rfl 3 (by decide) m hp hH hag))
      (fun _ _ _ x => x)) ?_
  have hshl : ∀ (x : Ident) (k j : Nat) (m : Mem),
      Integers.Int.ltu (Integers.Int.repr k) (Integers.Int.repr 32) = true → L4.get x = some (r j) →
      EvalExpr ge emptyEnv L4 m (shlU x k)
        (.Vint (Integers.Int.shl (Integers.Int.repr (f j)) (Integers.Int.repr k))) :=
    fun x k j m hk hx => EvalExpr.Ebinop .Oshl _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ hx)
      (EvalExpr.Econst_int _ _) (semBinop_shl_uint_int _ _ _ _ hk)
  exact triple_return_atH ge _ _ L4 H _ _ _
    (fun m _ _ _ =>
      EvalExpr.Ebinop .Oor _ _ _ _ _ _
        (EvalExpr.Ebinop .Oor _ _ _ _ _ _
          (EvalExpr.Ebinop .Oor _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ rfl)
            (hshl _b1 8 1 m (by decide) rfl) (semBinop_or_uint _ _ _ _))
          (hshl _b2 16 2 m (by decide) rfl) (semBinop_or_uint _ _ _ _))
        (hshl _b3 24 3 m (by decide) rfl) (semBinop_or_uint _ _ _ _))
    (fun m => semCast_uint m _)

end

end VST.Verif.LoadDemo
