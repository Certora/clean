/-
  Port of `body_fiddle` of VST's `progs/verif_load_demo.v`: `fiddle` of
  `vst/progs/load_demo.c` sums an object whose length is stored in its header
  word, one word before the pointer it receives.

      int fiddle (unsigned int *p) {
        unsigned int sum, size, i;
        unsigned int tagword = p[-1];
        sum = tagword & 0xff;
        size = tagword >> 10;
        for (i=0; i<size; i++) {
          unsigned int r = p[i];
          sum += r;
        }
        return sum;
      }

  VST's specification:

      DECLARE _fiddle
       WITH p: val, n: Z, tag: Z, contents: list Z
       PRE [ tptr tuint ]
         PROP  (Int.unsigned (Int.shru (Int.repr tag) (Int.repr 10)) = n)
         PARAMS (p)
         SEP (data_at Ews (tarray tuint (1+n)) (map Vint (map Int.repr (tag::contents)))
                      (offset_val (-sizeof tuint) p))
       POST [ tint ]
         PROP ( )
         RETURN (Vint (Int.add (Int.repr (Z.land tag 255)) (uint_sum contents)))
         SEP (data_at Ews (tarray tuint (1+n)) (map Vint (map Int.repr (tag::contents)))
                      (offset_val (-sizeof tuint) p)).

  Here the object is the header word `tag` at `p - 4` followed by the
  `arrayU32` of the `n = tag >> 10` words `f 0 … f (n-1)` at `p`
  (`Obj`).  `data_at` implies that the object lies in the address space:
  `4 ≤ ofs` and `ofs + 4 n < 2^64`.  `uintSum f n` is VST's `uint_sum`
  (the sum modulo `2^32`).  The loop is proved with the general loop rule,
  the measure being the number of iterations left.
-/
import VST.progs.load_demo
import VST.progs.verif_store_demo
open CC CC.Sep CC.HProp
open Load_demo

namespace VST.Verif.LoadDemo

/-! ## The specification -/

/-- VST's `uint_sum`: `f 0 + … + f (n-1)` modulo `2^32`. -/
def uintSum (f : Nat → Integers.Int) : Nat → Integers.Int
  | 0 => Integers.Int.zero
  | n + 1 => Integers.Int.add (uintSum f n) (f n)

/-- The size field of a header word, `tag >> 10`. -/
def sizeField (tag : Integers.Int) : Integers.Int := Integers.Int.shru tag (Integers.Int.repr 10)

/-- The flags of a header word, `tag & 0xff`. -/
def lowByte (tag : Integers.Int) : Integers.Int := Integers.Int.and tag (Integers.Int.repr 255)

/-- The object: header word `tag` at `p - 4`, then `tag >> 10` words. -/
def Obj (perm : Permission) (b : Block) (ofs : Integers.Ptrofs) (tag : Integers.Int)
    (f : Nat → Integers.Int) : HProp :=
  mapsto .Mint32 perm b (Integers.Ptrofs.unsigned ofs - 4) (.Vint tag)
    ∗ arrayU32 perm b (Integers.Ptrofs.unsigned ofs) (sizeField tag).toNat f

/-- `fiddle_spec` -/
def fiddleSpec (perm : Permission) (b : Block) (ofs : Integers.Ptrofs) (tag : Integers.Int)
    (f : Nat → Integers.Int) : Sep.FunSpec where
  tyargs := [tptr tuint]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr b ofs] ∧ Obj perm b ofs tag f hp
  post := fun v hp =>
    v = .Vint (Integers.Int.add (lowByte tag) (uintSum f (sizeField tag).toNat))
    ∧ Obj perm b ofs tag f hp
  measure := fun _ => 0

/-! ## Arithmetic and operators -/

theorem sizeField_lt (tag : Integers.Int) : (sizeField tag).toNat < 4194304 := by
  show (tag >>> (Integers.Int.repr 10).toNat).toNat < _
  rw [BitVec.toNat_ushiftRight]
  have := tag.isLt
  show tag.toNat >>> 10 < _
  rw [Nat.shiftRight_eq_div_pow]
  omega

theorem ltu_toNat (x y : Integers.Int) : Integers.Int.ltu x y = decide (x.toNat < y.toNat) := by
  simp [Integers.Int.ltu, Integers.MI.ltu, BitVec.ult]

theorem semBinop_and_uint_int (cenv m) (x y : Integers.Int) :
    Cop.semBinaryOperation cenv .Oand (.Vint x) tuint (.Vint y) tint m
      = some (.Vint (Integers.Int.and x y)) := rfl

theorem semBinop_shr_uint_int (cenv m) (x y : Integers.Int)
    (hy : Integers.Int.ltu y (Integers.Int.repr 32) = true) :
    Cop.semBinaryOperation cenv .Oshr (.Vint x) tuint (.Vint y) tint m
      = some (.Vint (Integers.Int.shru x y)) := by
  show (if Integers.Int.ltu y (Integers.Int.repr 32) then _ else _) = _
  rw [hy]; rfl

theorem semBinop_add_uint_int (cenv m) (x y : Integers.Int) :
    Cop.semBinaryOperation cenv .Oadd (.Vint x) tuint (.Vint y) tint m
      = some (.Vint (Integers.Int.add x y)) := rfl

theorem semCast_uint_int (m : Mem) (x : Integers.Int) :
    Cop.semCast (.Vint x) tuint tint m = some (.Vint x) := rfl

/-! ## The parts of the body -/

def hdrLoad : Expr :=
  .Ederef (.Ebinop .Oadd (.Etempvar _p (tptr tuint))
    (.Eunop .Oneg (.Econst_int (Integers.Int.repr 1) tint) tint) (tptr tuint)) tuint
def elemLoad : Expr :=
  .Ederef (.Ebinop .Oadd (.Etempvar _p (tptr tuint)) (.Etempvar _i tuint) (tptr tuint)) tuint
def guardE : Expr := .Ebinop .Olt (.Etempvar _i tuint) (.Etempvar _size tuint) tint
def setSum0 : Stmt :=
  .Sset _sum (.Ebinop .Oand (.Etempvar _tagword tuint) (.Econst_int (Integers.Int.repr 255) tint) tuint)
def setSize : Stmt :=
  .Sset _size (.Ebinop .Oshr (.Etempvar _tagword tuint) (.Econst_int (Integers.Int.repr 10) tint) tuint)
def setR : Stmt := .Sset _r elemLoad
def addSum : Stmt := .Sset _sum (.Ebinop .Oadd (.Etempvar _sum tuint) (.Etempvar _r tuint) tuint)
def incrI : Stmt :=
  .Sset _i (.Ebinop .Oadd (.Etempvar _i tuint) (.Econst_int (Integers.Int.repr 1) tint) tuint)
def loopS : Stmt := .Sloop (.Ssequence (.Sifthenelse guardE .Sskip .Sbreak) (.Ssequence setR addSum)) incrI

theorem fiddle_body : f_fiddle.fn_body =
    .Ssequence (.Sset _tagword hdrLoad) (.Ssequence setSum0 (.Ssequence setSize
      (.Ssequence (.Ssequence (.Sset _i (.Econst_int (Integers.Int.repr 0) tint)) loopS)
        (.Sreturn (some (.Etempvar _sum tuint)))))) := rfl

/-! ## The proof -/

section
variable (ge : CGenv) (perm : Permission) (b : Block) (ofs : Integers.Ptrofs)
  (tag : Integers.Int) (f : Nat → Integers.Int)

/-- The loop invariant after `j` iterations. -/
def Inv (j : Nat) : Sep.Assn := fun e le hp =>
  e = emptyEnv ∧ le.get _p = some (.Vptr b ofs) ∧ le.get _size = some (.Vint (sizeField tag))
  ∧ le.get _i = some (.Vint (Integers.Int.repr j))
  ∧ le.get _sum = some (.Vint (Integers.Int.add (lowByte tag) (uintSum f j)))
  ∧ j ≤ (sizeField tag).toNat ∧ Obj perm b ofs tag f hp

/-- After the body of iteration `j`, before `i++`. -/
def Mid (j : Nat) : Sep.Assn := fun e le hp =>
  e = emptyEnv ∧ le.get _p = some (.Vptr b ofs) ∧ le.get _size = some (.Vint (sizeField tag))
  ∧ le.get _i = some (.Vint (Integers.Int.repr j))
  ∧ le.get _sum = some (.Vint (Integers.Int.add (lowByte tag) (uintSum f (j + 1))))
  ∧ j < (sizeField tag).toNat ∧ Obj perm b ofs tag f hp

/-- After the loop. -/
def Done : Sep.Assn := fun e le hp =>
  e = emptyEnv
  ∧ le.get _sum = some (.Vint (Integers.Int.add (lowByte tag) (uintSum f (sizeField tag).toNat)))
  ∧ Obj perm b ofs tag f hp

variable (fe : EntryRel) (hpr : permOrder perm .Readable = true)
  (hno : Integers.Ptrofs.unsigned ofs + 4 * ((sizeField tag).toNat : _root_.Int)
    < 18446744073709551616)

/-- The guard `i < size`. -/
theorem eval_guard (j : Nat) (e : Env) (le : TempEnv) (hp : Heap) (m : Mem)
    (hI : Inv perm b ofs tag f j e le hp) :
    EvalExpr ge e le m guardE (Val.ofBool (decide (j < (sizeField tag).toNat))) := by
  obtain ⟨_, _, hsz, hi, _, hj, _⟩ := hI
  have h := EvalExpr.Ebinop (ge := ge) (e := e) (le := le) (m := m) .Olt
    (.Etempvar _i tuint) (.Etempvar _size tuint) tint _ _ _ (EvalExpr.Etempvar _ _ _ hi)
    (EvalExpr.Etempvar _ _ _ hsz) (semBinop_ltu_uint _ _ _ _)
  have hlt := sizeField_lt tag
  rwa [ltu_toNat, u32_toNat_repr, Nat.mod_eq_of_lt (by omega)] at h

include hpr hno in
/-- `r = p[i]; sum += r;` -/
theorem body_triple (j : Nat) :
    Sep.Triple ge fe f_fiddle (fun e le hp => Inv perm b ofs tag f j e le hp ∧ j < (sizeField tag).toNat)
      (.Ssequence setR addSum) (.only (Mid perm b ofs tag f j)) := by
  refine Sep.triple_seq_only ge fe f_fiddle (Q := fun e le hp => (Inv perm b ofs tag f j e le hp
    ∧ j < (sizeField tag).toNat) ∧ le.get _r = some (.Vint (f j))) ?_ ?_
  · refine Sep.triple_set ge fe f_fiddle _ _ _ _ (fun e le hp m hP hag => ?_)
    obtain ⟨⟨he, hp_, hsz, hi, hs, hjN, hobj⟩, hj⟩ := hP
    refine ⟨_, ?_, ⟨⟨he, (PTree.gso _ _ _ _ (by decide)).trans hp_,
      (PTree.gso _ _ _ _ (by decide)).trans hsz, (PTree.gso _ _ _ _ (by decide)).trans hi,
      (PTree.gso _ _ _ _ (by decide)).trans hs, hjN, hobj⟩, hj⟩, PTree.gss _ _ _⟩
    obtain ⟨h1, h2, hd, rfl, _, harr⟩ := hobj
    have hsz4 : sizeof ge.genv_cenv tuint = ((4 : Nat) : _root_.Int) := by simp [sizeof, tuint]
    have hlt := sizeField_lt tag
    refine EvalExpr.Elvalue _ _ _ .Full _
      (eval_index_lvalue (EvalExpr.Etempvar _ _ _ hp_) (EvalExpr.Etempvar _ _ _ hi) rfl)
      (DerefLoc.value .Mint32 _ rfl ?_)
    rw [Mem.loadv_ptr _ _ _ _ (Or.inl rfl),
      idxOfs_unsigned _ _ _ _ j 4 hsz4 (by decide) (by zomega) (by zomega)]
    exact arrayU32_load perm b hpr _ f j hj _ h2 m harr (Heap.Agrees_union_right hd hag)
  · refine Sep.triple_set ge fe f_fiddle _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨⟨⟨he, hp_, hsz, hi, hs, _, hobj⟩, hj⟩, hr⟩ := hP
    refine ⟨_, EvalExpr.Ebinop .Oadd _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ hs)
      (EvalExpr.Etempvar _ _ _ hr) (semBinop_add_uint _ _ _ _), he,
      (PTree.gso _ _ _ _ (by decide)).trans hp_, (PTree.gso _ _ _ _ (by decide)).trans hsz,
      (PTree.gso _ _ _ _ (by decide)).trans hi, ?_, hj, hobj⟩
    rw [PTree.gss, uintSum, Integers.Int.add_assoc]

/-- `i++` -/
theorem incr_triple (j : Nat) :
    Sep.Triple ge fe f_fiddle (Mid perm b ofs tag f j) incrI
      (.only (Inv perm b ofs tag f (j + 1))) := by
  refine Sep.triple_set ge fe f_fiddle _ _ _ _ (fun e le hp m hP _ => ?_)
  obtain ⟨he, hp_, hsz, hi, hs, hj, hobj⟩ := hP
  refine ⟨_, EvalExpr.Ebinop .Oadd _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ hi)
    (EvalExpr.Econst_int _ _) (semBinop_add_uint_int _ _ _ _), he,
    (PTree.gso _ _ _ _ (by decide)).trans hp_, (PTree.gso _ _ _ _ (by decide)).trans hsz, ?_,
    (PTree.gso _ _ _ _ (by decide)).trans hs, hj, hobj⟩
  rw [PTree.gss, repr_add]
  rfl

include hpr hno in
/-- The loop, `k` iterations left. -/
theorem loop_triple (k : Nat) :
    Sep.Triple ge fe f_fiddle
      (fun e le hp => ∃ j, Inv perm b ofs tag f j e le hp ∧ (sizeField tag).toNat - j = k) loopS
      { normal := Done perm b ofs tag f, brk := Sep.Assn.no, cont := Sep.Assn.no,
        ret := fun _ _ => False } := by
  refine Sep.triple_loop ge fe f_fiddle _
    (fun k e le hp => ∃ j, Inv perm b ofs tag f j e le hp ∧ (sizeField tag).toNat - j = k)
    (fun k e le hp => ∃ j, Mid perm b ofs tag f j e le hp ∧ (sizeField tag).toNat - j = k) _ _
    (fun k => ?_) (fun k => ?_) k
  · refine Sep.triple_exists ge fe f_fiddle _ _ _ (fun j => ?_)
    refine Sep.triple_seq ge fe f_fiddle _
      (fun e le hp => (Inv perm b ofs tag f j e le hp ∧ j < (sizeField tag).toNat)
        ∧ (sizeField tag).toNat - j = k) _ _ _ ?_ ?_
    · by_cases hjN : j < (sizeField tag).toNat
      · refine Sep.triple_if_true ge fe f_fiddle _ _ _ _ _ (fun e le hp m hP _ => ?_) ?_
        · refine ⟨_, eval_guard ge perm b ofs tag f j e le hp m hP.1, ?_⟩
          simpa [hjN, guardE, typeof] using boolVal_ofBool_int m true
        · exact Sep.triple_fallthrough ge fe f_fiddle _ _ _ _ (Sep.triple_skip ge fe f_fiddle _)
            (fun e le hp h => ⟨⟨h.1, hjN⟩, h.2⟩)
      · refine Sep.triple_if_false ge fe f_fiddle _ _ _ _ _ (fun e le hp m hP _ => ?_) ?_
        · refine ⟨_, eval_guard ge perm b ofs tag f j e le hp m hP.1, ?_⟩
          simpa [hjN, guardE, typeof] using boolVal_ofBool_int m false
        · refine Sep.triple_conseq ge fe f_fiddle (Sep.triple_break ge fe f_fiddle _)
            (fun _ _ _ x => x) (fun _ _ _ x => x.elim) (fun e le hp h => ?_)
            (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
          obtain ⟨⟨he, _, _, _, hs, hj, hobj⟩, _⟩ := h
          have : j = (sizeField tag).toNat := by omega
          subst this
          exact ⟨he, hs, hobj⟩
    · intro kk e le hp hf m hd hag ⟨hP, hk⟩
      obtain ⟨o, hp', hs, hd', hag', hR⟩ := body_triple ge perm b ofs tag f fe hpr hno j kk e le hp hf m hd hag hP
      refine ⟨o, hp', hs, hd', hag', ?_⟩
      cases o with
      | Normal _ _ _ => exact ⟨j, hR, hk⟩
      | _ => exact hR.elim
  · refine Sep.triple_exists ge fe f_fiddle _ _ _ (fun j => ?_)
    intro kk e le hp hf m hd hag ⟨hM, hk⟩
    obtain ⟨o, hp', hs, hd', hag', hR⟩ := incr_triple ge perm b ofs tag f fe j kk e le hp hf m hd hag hM
    refine ⟨o, hp', hs, hd', hag', ?_⟩
    have hj := hM.2.2.2.2.2.1
    cases o with
    | Normal _ _ _ => exact ⟨(sizeField tag).toNat - (j + 1), by omega, j + 1, hR, rfl⟩
    | _ => exact hR.elim

include hpr hno in
/-- **`fiddle` satisfies `fiddle_spec`** (VST's `body_fiddle`). -/
theorem fiddle_satisfies (h4 : 4 ≤ Integers.Ptrofs.unsigned ofs) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_fiddle) (fiddleSpec perm b ofs tag f)
      [.Vptr b ofs] := by
  let H := Obj perm b ofs tag f
  let L0 := (createUndefTemps f_fiddle.fn_temps).set _p (.Vptr b ofs)
  let L1 := L0.set _tagword (.Vint tag)
  let L2 := L1.set _sum (.Vint (lowByte tag))
  let L3 := L2.set _size (.Vint (sizeField tag))
  let L4 := L3.set _i (.Vint (Integers.Int.repr 0))
  refine satisfies_internal_noVars ge _ f_fiddle _ _ (AtH L0 H)
    (fun _ => ⟨L0, FunctionEntry2.intro (by decide) (by decide) (by decide)
      (AllocVariables.nil _ _) rfl, fun hp h => ⟨rfl, rfl, h.2⟩⟩) ?_
  rw [fiddle_body]
  refine Sep.triple_seq ge _ f_fiddle _ (AtH L1 H) _ _ _
    (Sep.triple_fallthrough ge _ f_fiddle _ _ _ _
      (triple_set_atH ge _ f_fiddle L0 H _ _ _ (fun m hp hH hag => by
        obtain ⟨h1, h2, _, rfl, hm, _⟩ := hH
        exact eval_lvalue_mapsto (v := .Vint tag) rfl hpr
          (eval_index_lvalue (EvalExpr.Etempvar _ _ _ rfl)
            (EvalExpr.Eunop .Oneg _ _ _ _ (EvalExpr.Econst_int _ _) (semUnop_neg_int m _)) rfl)
          (VST.Verif.StoreDemo.addr_minus1 ge.genv_cenv ofs h4) hm
          (Heap.Agrees_union_left hag)))
      (fun _ _ _ x => x)) ?_
  refine Sep.triple_seq ge _ f_fiddle _ (AtH L2 H) _ _ _
    (Sep.triple_fallthrough ge _ f_fiddle _ _ _ _
      (triple_set_atH ge _ f_fiddle L1 H _ _ _ (fun _ _ _ _ =>
        EvalExpr.Ebinop .Oand _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ rfl) (EvalExpr.Econst_int _ _)
          (semBinop_and_uint_int _ _ _ _)))
      (fun _ _ _ x => x)) ?_
  refine Sep.triple_seq ge _ f_fiddle _ (AtH L3 H) _ _ _
    (Sep.triple_fallthrough ge _ f_fiddle _ _ _ _
      (triple_set_atH ge _ f_fiddle L2 H _ _ _ (fun _ _ _ _ =>
        EvalExpr.Ebinop .Oshr _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ rfl) (EvalExpr.Econst_int _ _)
          (semBinop_shr_uint_int _ _ _ _ (by decide))))
      (fun _ _ _ x => x)) ?_
  refine Sep.triple_seq ge _ f_fiddle _ (Done perm b ofs tag f) _ _ _ ?_ ?_
  · refine Sep.triple_seq ge _ f_fiddle _ (AtH L4 H) _ _ _
      (Sep.triple_fallthrough ge _ f_fiddle _ _ _ _
        (triple_set_atH ge _ f_fiddle L3 H _ _ _ (fun _ _ _ _ => EvalExpr.Econst_int _ _))
        (fun _ _ _ x => x)) ?_
    refine Sep.triple_conseq ge _ f_fiddle (loop_triple ge perm b ofs tag f _ hpr hno (sizeField tag).toNat)
      (fun e le hp h => ?_) (fun _ _ _ x => x) (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim)
      (fun _ _ x => x.elim)
    obtain ⟨he, rfl, hH⟩ := h
    refine ⟨0, ⟨he, rfl, rfl, rfl, ?_, Nat.zero_le _, hH⟩, Nat.sub_zero _⟩
    show some (Val.Vint (lowByte tag)) = some (.Vint (Integers.Int.add (lowByte tag) Integers.Int.zero))
    rw [Integers.Int.add_zero]
  · refine Sep.triple_return ge _ f_fiddle _ _ _ (fun e le hp m h _ => ?_)
    obtain ⟨he, hs, hobj⟩ := h
    refine ⟨_, _, m, hp, EvalExpr.Etempvar _ _ _ hs, semCast_uint_int m _, ?_, ⟨rfl, hobj⟩,
      fun _ hdj hag => ⟨hdj, hag⟩⟩
    rw [he]; exact freeList_emptyEnv _ _

end

end VST.Verif.LoadDemo
