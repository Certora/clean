/-
  Translation from Clight to Csharpminor: semantic preservation — port of
  `cfrontend/Cshmgenproof.v`, part 1 (section `CONSTRUCTORS`, lines
  193–760): correctness of the Csharpminor expression constructors
  (`make_intconst_correct` … `make_cast_correct`, `make_boolean_correct`,
  the unary operators).

  The port is specialised to the configured target (`Archi.ptr64 = true`).
-/
import CCLib.cfrontend.Cshmgen
import CCLib.cfrontend.CsharpminorSem
import CCLib.lib.FloatsLemmas

namespace CC
namespace Cshmgen

open Cminor (UnaryOperation BinaryOperation)
open Cminor.UnaryOperation Cminor.BinaryOperation

theorem res_bind_eq_OK {A B : Type} {x : Res A} {f : A → Res B} {b : B} :
    (bind x f = Res.OK b) ↔ ∃ a, x = .OK a ∧ f a = .OK b := by
  cases x <;> simp [bind, Res.bind]

section CONSTRUCTORS
variable {ge : Csharpminor.CGenv} {e : Csharpminor.Env} {le : Csharpminor.TempEnv} {m : Mem}

local notation "EV" => Csharpminor.EvalExpr ge e le m

theorem make_intconst_correct (n : Integers.Int) : EV (makeIntconst n) (.Vint n) :=
  .Econst _ _ rfl
theorem make_floatconst_correct (n : Floats.Float) : EV (makeFloatconst n) (.Vfloat n) :=
  .Econst _ _ rfl
theorem make_singleconst_correct (n : Floats.Float32) : EV (makeSingleconst n) (.Vsingle n) :=
  .Econst _ _ rfl
theorem make_longconst_correct (n : Integers.Int64) : EV (makeLongconst n) (.Vlong n) :=
  .Econst _ _ rfl

theorem make_ptrofsconst_correct (n : Z) :
    EV (makePtrofsconst n) (Val.Vptrofs (Integers.Ptrofs.repr n)) := by
  simp only [makePtrofsconst, Val.Vptrofs, Archi.ptr64, if_true]
  have : Integers.Ptrofs.to_int64 (Integers.Ptrofs.repr n) = Integers.Int64.repr n := by
    simp [Integers.Ptrofs.to_int64, Integers.Ptrofs.repr, Integers.Int64.repr, Integers.MI.repr]
  rw [this]; exact make_longconst_correct _

theorem loword_eq_repr (n : Integers.Int64) :
    Integers.Int64.loword n = Integers.Int.repr (Integers.Int64.unsigned n) := by
  simp only [Integers.Int64.loword, Integers.Int.repr, Integers.Int64.unsigned, Integers.MI.repr,
    Integers.MI.unsigned]
  apply BitVec.eq_of_toNat_eq
  simp

theorem make_unop_correct {op : UnaryOperation} {a : Csharpminor.Expr} {v v' : Val}
    (h : EV a v) (hop : Cminor.evalUnop op v = some v') : EV (.Eunop op a) v' :=
  .Eunop _ _ _ _ h hop

theorem make_binop_correct {op : BinaryOperation} {a b : Csharpminor.Expr} {va vb v : Val}
    (ha : EV a va) (hb : EV b vb) (hop : Cminor.evalBinop op va vb m = some v) :
    EV (.Ebinop op a b) v :=
  .Ebinop _ _ _ _ _ _ ha hb hop

theorem ofOptbool_int {ob : Option Bool} {n : Integers.Int} (h : Val.ofOptbool ob = .Vint n) :
    n = (if Integers.Int.eq n Integers.Int.zero then Integers.Int.zero else Integers.Int.one) := by
  rcases ob with _ | _ | _ <;> simp [Val.ofOptbool, Val.ofBool, Val.Vtrue, Val.Vfalse] at h <;>
    subst h <;> decide

theorem mapOfBool_int {ob : Option Bool} {n : Integers.Int}
    (h : ob.map Val.ofBool = some (.Vint n)) :
    n = (if Integers.Int.eq n Integers.Int.zero then Integers.Int.zero else Integers.Int.one) := by
  rcases ob with _ | _ | _ <;> simp [Val.ofBool, Val.Vtrue, Val.Vfalse] at h <;>
    subst h <;> decide

/-- `Cshmgenproof.make_cmpu_ne_zero_correct` -/
theorem make_cmpu_ne_zero_correct {a : Csharpminor.Expr} {n : Integers.Int} (h : EV a (.Vint n)) :
    EV (makeCmpuNeZero a)
      (.Vint (if Integers.Int.eq n Integers.Int.zero then Integers.Int.zero else Integers.Int.one)) := by
  have DEFAULT : EV (.Ebinop (.Ocmpu .Cne) a (makeIntconst Integers.Int.zero))
      (.Vint (if Integers.Int.eq n Integers.Int.zero then Integers.Int.zero else Integers.Int.one)) := by
    refine make_binop_correct h (make_intconst_correct _) ?_
    simp only [Cminor.evalBinop, Val.cmpu, Val.cmpu_bool, Integers.Int.cmpu, Integers.MI.cmpu,
      Val.ofOptbool, Val.ofBool, Integers.Int.eq]
    by_cases hq : Integers.MI.eq n Integers.Int.zero = true <;> simp [hq, Val.Vtrue, Val.Vfalse]
  unfold makeCmpuNeZero
  split
  all_goals first
    | exact DEFAULT
    | (cases h with
       | Ebinop _ _ _ v1 v2 _ h1 h2 hop =>
         simp only [Cminor.evalBinop] at hop
         first
           | (rw [← ofOptbool_int (Option.some.inj hop)]; exact .Ebinop _ _ _ _ _ _ h1 h2 hop)
           | (rw [← mapOfBool_int hop]; exact .Ebinop _ _ _ _ _ _ h1 h2 hop))

/-- `Cshmgenproof.make_cast_int_correct` -/
theorem make_cast_int_correct {a : Csharpminor.Expr} {n : Integers.Int} (sz : IntSize)
    (si : Signedness) (h : EV a (.Vint n)) :
    EV (makeCastInt a sz si) (.Vint (Cop.castIntInt sz si n)) := by
  cases sz <;> cases si <;> simp only [makeCastInt, Cop.castIntInt] <;>
    first
      | exact h
      | exact make_cmpu_ne_zero_correct h
      | exact make_unop_correct h rfl

/-- `Cshmgenproof.make_longofint_correct` -/
theorem make_longofint_correct {a : Csharpminor.Expr} {n : Integers.Int} (si : Signedness)
    (h : EV a (.Vint n)) : EV (makeLongofint a si) (.Vlong (Cop.castIntLong si n)) := by
  cases si <;> exact make_unop_correct h rfl

theorem eval_cmplu_ne_zero_long {a : Csharpminor.Expr} {n : Integers.Int64}
    (h : EV a (.Vlong n)) :
    EV (.Ebinop (.Ocmplu .Cne) a (makeLongconst Integers.Int64.zero))
      (.Vint (if Integers.Int64.eq n Integers.Int64.zero then Integers.Int.zero else Integers.Int.one)) := by
  refine make_binop_correct h (make_longconst_correct _) ?_
  simp only [Cminor.evalBinop, Val.cmplu, Val.cmplu_bool, Integers.Int64.cmpu, Integers.MI.cmpu,
    Integers.Int64.eq, Option.map_some, Val.ofBool]
  by_cases hq : Integers.MI.eq n Integers.Int64.zero = true <;> simp [hq, Val.Vtrue, Val.Vfalse]

theorem eval_cmplu_ne_zero_ptr {a : Csharpminor.Expr} {b : Block} {ofs : Integers.Ptrofs}
    (h : EV a (.Vptr b ofs)) (hw : Mem.weakValidPointer m b (Integers.Ptrofs.unsigned ofs) = true) :
    EV (.Ebinop (.Ocmplu .Cne) a (makeLongconst Integers.Int64.zero)) Val.Vone := by
  refine make_binop_correct h (make_longconst_correct _) ?_
  have hw' : Val.weakValidPtr (Mem.validPointer m) b (Integers.Ptrofs.unsigned ofs) = true := hw
  simp [Cminor.evalBinop, Val.cmplu, Val.cmplu_bool, Archi.ptr64, hw', Val.cmpDifferentBlocks,
    Val.ofBool, Val.Vtrue, Val.Vone]
  rfl

theorem eval_cmpf_ne_zero {a : Csharpminor.Expr} {f : Floats.Float} (h : EV a (.Vfloat f)) :
    EV (.Ebinop (.Ocmpf .Cne) a (makeFloatconst Floats.Float.zero))
      (.Vint (if Floats.Float.cmp .Ceq f Floats.Float.zero then Integers.Int.zero else Integers.Int.one)) := by
  refine make_binop_correct h (make_floatconst_correct _) ?_
  simp only [Cminor.evalBinop, Val.cmpf, Val.cmpf_bool, Floats.Float.cmp_ne_eq, Val.ofOptbool,
    Val.ofBool]
  by_cases hq : Floats.Float.cmp .Ceq f Floats.Float.zero = true <;> simp [hq, Val.Vtrue, Val.Vfalse]

theorem eval_cmpfs_ne_zero {a : Csharpminor.Expr} {f : Floats.Float32} (h : EV a (.Vsingle f)) :
    EV (.Ebinop (.Ocmpfs .Cne) a (makeSingleconst Floats.Float32.zero))
      (.Vint (if Floats.Float32.cmp .Ceq f Floats.Float32.zero then Integers.Int.zero else Integers.Int.one)) := by
  refine make_binop_correct h (make_singleconst_correct _) ?_
  simp only [Cminor.evalBinop, Val.cmpfs, Val.cmpfs_bool, Floats.Float32.cmp_ne_eq, Val.ofOptbool,
    Val.ofBool]
  by_cases hq : Floats.Float32.cmp .Ceq f Floats.Float32.zero = true <;>
    simp [hq, Val.Vtrue, Val.Vfalse]

/-- `Cshmgenproof.make_cast_correct` -/
theorem make_cast_correct {a b : Csharpminor.Expr} {v v' : Val} {ty1 ty2 : Ty}
    (hmk : makeCast ty1 ty2 a = .OK b) (h : EV a v) (hs : Cop.semCast v ty1 ty2 m = some v') :
    EV b v' := by
  unfold makeCast at hmk; unfold Cop.semCast at hs
  cases hc : Cop.classifyCast ty1 ty2 <;> rw [hc] at hmk hs <;> cases hmk <;>
    cases v <;> simp [Archi.ptr64] at hs
  all_goals first
    | (obtain ⟨_, rfl⟩ := hs)
    | subst hs
    | (split at hs <;> cases hs)
  all_goals first
    | exact h
    | exact make_cast_int_correct _ _ h
    | exact make_cmpu_ne_zero_correct h
    | exact make_unop_correct h rfl
    | (cases ‹Signedness› <;> exact make_unop_correct h rfl)
    | (rename_i heq
       cases ‹Signedness› <;>
         simp only [Cop.castFloatInt, Cop.castSingleInt, Cop.castFloatLong,
           Cop.castSingleLong] at heq <;>
         first
           | exact make_cast_int_correct _ _ (make_unop_correct h (by
               simp [Cminor.evalUnop, Val.intoffloat, Val.intuoffloat, Val.intofsingle,
                 Val.intuofsingle, heq]))
           | exact make_unop_correct h (by
               simp [Cminor.evalUnop, Val.longoffloat, Val.longuoffloat, Val.longofsingle,
                 Val.longuofsingle, heq]))
    | exact make_cast_int_correct _ _ (make_unop_correct h (by
        simp [Cminor.evalUnop, Val.loword, loword_eq_repr]))
    | exact eval_cmplu_ne_zero_long h
    | exact eval_cmplu_ne_zero_ptr h ‹_›
    | exact eval_cmpf_ne_zero h
    | exact eval_cmpfs_ne_zero h

theorem boolOfVal_ite (c : Bool) :
    Val.BoolOfVal (.Vint (if c then Integers.Int.zero else Integers.Int.one)) (!c) := by
  cases c
  · exact Val.BoolOfVal.int Integers.Int.one
  · exact Val.BoolOfVal.int Integers.Int.zero

/-- `Cshmgenproof.make_boolean_correct` -/
theorem make_boolean_correct {a : Csharpminor.Expr} {v : Val} {ty : Ty} {b : Bool}
    (h : EV a v) (hb : Cop.boolVal v ty m = some b) :
    ∃ vb, EV (makeBoolean a ty) vb ∧ Val.BoolOfVal vb b := by
  unfold makeBoolean; unfold Cop.boolVal at hb
  cases hc : Cop.classifyBool ty <;> rw [hc] at hb <;> simp only <;>
    cases v <;> simp [Archi.ptr64] at hb
  all_goals first
    | (obtain ⟨_, rfl⟩ := hb)
    | subst hb
    | (have hb' := congrArg (!·) hb; simp only [Bool.not_not] at hb'; subst hb')
  · exact ⟨_, make_cmpu_ne_zero_correct h, boolOfVal_ite _⟩
  · exact ⟨_, eval_cmplu_ne_zero_long h, boolOfVal_ite _⟩
  · exact ⟨_, eval_cmplu_ne_zero_ptr h ‹_›, Val.BoolOfVal.int Integers.Int.one⟩
  · exact ⟨_, eval_cmpf_ne_zero h, boolOfVal_ite _⟩
  · exact ⟨_, eval_cmpfs_ne_zero h, boolOfVal_ite _⟩

/-- `Cshmgenproof.make_neg_correct` -/
theorem make_neg_correct {a c : Csharpminor.Expr} {tya : Ty} {va v : Val}
    (hs : Cop.semNeg va tya = some v) (hmk : makeNeg a tya = .OK c) (h : EV a va) : EV c v := by
  unfold makeNeg at hmk; unfold Cop.semNeg at hs
  cases hc : Cop.classifyNeg tya <;> rw [hc] at hmk hs <;> cases hmk <;>
    cases va <;> simp at hs <;> subst hs <;> exact make_unop_correct h rfl

/-- `Cshmgenproof.make_absfloat_correct` -/
theorem make_absfloat_correct {a c : Csharpminor.Expr} {tya : Ty} {va v : Val}
    (hs : Cop.semAbsfloat va tya = some v) (hmk : makeAbsfloat a tya = .OK c) (h : EV a va) :
    EV c v := by
  unfold makeAbsfloat at hmk; unfold Cop.semAbsfloat at hs
  cases hc : Cop.classifyNeg tya <;> rw [hc] at hmk hs <;> cases hmk <;>
    cases va <;> simp at hs <;> subst hs
  all_goals first
    | exact make_unop_correct h rfl
    | exact make_unop_correct (make_unop_correct h rfl) rfl
    | (cases ‹Signedness› <;> exact make_unop_correct (make_unop_correct h rfl) rfl)

/-- `Cshmgenproof.make_notbool_correct` -/
theorem make_notbool_correct {a c : Csharpminor.Expr} {tya : Ty} {va v : Val}
    (hs : Cop.semNotbool va tya m = some v) (hmk : makeNotbool a tya = .OK c) (h : EV a va) :
    EV c v := by
  unfold makeNotbool at hmk; unfold Cop.semNotbool Cop.boolVal at hs
  cases hc : Cop.classifyBool tya <;> rw [hc] at hmk hs <;> cases hmk <;>
    cases va <;> simp [Archi.ptr64] at hs
  all_goals first
    | (obtain ⟨_, rfl⟩ := hs)
    | subst hs
  · refine make_binop_correct h (make_intconst_correct _) ?_
    simp [Cminor.evalBinop, Val.cmpu, Val.cmpu_bool, Integers.Int.cmpu, Integers.MI.cmpu,
      Val.ofOptbool, Integers.Int.eq]
  · refine make_binop_correct h (make_longconst_correct _) ?_
    simp [Cminor.evalBinop, Val.cmplu, Val.cmplu_bool, Integers.Int64.cmpu, Integers.MI.cmpu,
      Integers.Int64.eq]
  · refine make_binop_correct h (make_longconst_correct _) ?_
    have hw' : Val.weakValidPtr (Mem.validPointer m) _ _ = true := ‹Mem.weakValidPointer m _ _ = true›
    simp [Cminor.evalBinop, Val.cmplu, Val.cmplu_bool, Archi.ptr64, hw', Val.cmpDifferentBlocks]
    rfl
  · refine make_binop_correct h (make_floatconst_correct _) ?_
    simp [Cminor.evalBinop, Val.cmpf, Val.cmpf_bool, Val.ofOptbool]
  · refine make_binop_correct h (make_singleconst_correct _) ?_
    simp [Cminor.evalBinop, Val.cmpfs, Val.cmpfs_bool, Val.ofOptbool]

/-- `Cshmgenproof.make_notint_correct` -/
theorem make_notint_correct {a c : Csharpminor.Expr} {tya : Ty} {va v : Val}
    (hs : Cop.semNotint va tya = some v) (hmk : makeNotint a tya = .OK c) (h : EV a va) : EV c v := by
  unfold makeNotint at hmk; unfold Cop.semNotint at hs
  cases hc : Cop.classifyNotint tya <;> rw [hc] at hmk hs <;> cases hmk <;>
    cases va <;> simp at hs <;> subst hs <;> exact make_unop_correct h rfl

section MAKE_BIN
variable {semInt : Signedness → Integers.Int → Integers.Int → Option Val}
  {semLong : Signedness → Integers.Int64 → Integers.Int64 → Option Val}
  {semFloat : Floats.Float → Floats.Float → Option Val}
  {semSingle : Floats.Float32 → Floats.Float32 → Option Val}
  {iop iopu fop sop lop lopu : BinaryOperation}

/-- `Cshmgenproof.make_binarith_correct` -/
theorem make_binarith_correct
    (iop_ok : ∀ x y m, Cminor.evalBinop iop (.Vint x) (.Vint y) m = semInt .Signed x y)
    (iopu_ok : ∀ x y m, Cminor.evalBinop iopu (.Vint x) (.Vint y) m = semInt .Unsigned x y)
    (lop_ok : ∀ x y m, Cminor.evalBinop lop (.Vlong x) (.Vlong y) m = semLong .Signed x y)
    (lopu_ok : ∀ x y m, Cminor.evalBinop lopu (.Vlong x) (.Vlong y) m = semLong .Unsigned x y)
    (fop_ok : ∀ x y m, Cminor.evalBinop fop (.Vfloat x) (.Vfloat y) m = semFloat x y)
    (sop_ok : ∀ x y m, Cminor.evalBinop sop (.Vsingle x) (.Vsingle y) m = semSingle x y)
    {a b c : Csharpminor.Expr} {tya tyb : Ty} {va vb v : Val}
    (hs : Cop.semBinarith semInt semLong semFloat semSingle va tya vb tyb m = some v)
    (hmk : makeBinarith iop iopu fop sop lop lopu a tya b tyb = .OK c)
    (ha : EV a va) (hb : EV b vb) : EV c v := by
  unfold makeBinarith at hmk; unfold Cop.semBinarith at hs
  simp only [res_bind_eq_OK] at hmk
  obtain ⟨a', A, b', B, C⟩ := hmk
  simp only at hs
  split at hs
  · cases hs
  · next va' Ca =>
    split at hs
    · cases hs
    · next vb' Cb =>
      have EA := make_cast_correct A ha Ca
      have EB := make_cast_correct B hb Cb
      revert C hs
      cases Cop.classifyBinarith tya tyb <;> intro C hs <;> simp only at C hs
      · rename_i sg
        cases va' <;> cases vb' <;> simp at hs
        cases sg <;> cases C
        · exact make_binop_correct EA EB (by rw [iop_ok]; exact hs)
        · exact make_binop_correct EA EB (by rw [iopu_ok]; exact hs)
      · rename_i sg
        cases va' <;> cases vb' <;> simp at hs
        cases sg <;> cases C
        · exact make_binop_correct EA EB (by rw [lop_ok]; exact hs)
        · exact make_binop_correct EA EB (by rw [lopu_ok]; exact hs)
      · cases va' <;> cases vb' <;> simp at hs
        cases C
        exact make_binop_correct EA EB (by rw [fop_ok]; exact hs)
      · cases va' <;> cases vb' <;> simp at hs
        cases C
        exact make_binop_correct EA EB (by rw [sop_ok]; exact hs)
      · cases C

/-- `Cshmgenproof.make_binarith_int_correct` -/
theorem make_binarith_int_correct
    (iop_ok : ∀ x y m, Cminor.evalBinop iop (.Vint x) (.Vint y) m = semInt .Signed x y)
    (iopu_ok : ∀ x y m, Cminor.evalBinop iopu (.Vint x) (.Vint y) m = semInt .Unsigned x y)
    (lop_ok : ∀ x y m, Cminor.evalBinop lop (.Vlong x) (.Vlong y) m = semLong .Signed x y)
    (lopu_ok : ∀ x y m, Cminor.evalBinop lopu (.Vlong x) (.Vlong y) m = semLong .Unsigned x y)
    {a b c : Csharpminor.Expr} {tya tyb : Ty} {va vb v : Val}
    (hs : Cop.semBinarith semInt semLong (fun _ _ => none) (fun _ _ => none) va tya vb tyb m = some v)
    (hmk : makeBinarithInt iop iopu lop lopu a tya b tyb = .OK c)
    (ha : EV a va) (hb : EV b vb) : EV c v := by
  unfold makeBinarithInt at hmk; unfold Cop.semBinarith at hs
  simp only [res_bind_eq_OK] at hmk
  obtain ⟨a', A, b', B, C⟩ := hmk
  simp only at hs
  split at hs
  · cases hs
  · next va' Ca =>
    split at hs
    · cases hs
    · next vb' Cb =>
      have EA := make_cast_correct A ha Ca
      have EB := make_cast_correct B hb Cb
      revert C hs
      cases Cop.classifyBinarith tya tyb <;> intro C hs <;> simp only at C hs
      · rename_i sg
        cases va' <;> cases vb' <;> simp at hs
        cases sg <;> cases C
        · exact make_binop_correct EA EB (by rw [iop_ok]; exact hs)
        · exact make_binop_correct EA EB (by rw [iopu_ok]; exact hs)
      · rename_i sg
        cases va' <;> cases vb' <;> simp at hs
        cases sg <;> cases C
        · exact make_binop_correct EA EB (by rw [lop_ok]; exact hs)
        · exact make_binop_correct EA EB (by rw [lopu_ok]; exact hs)
      all_goals (cases C)

end MAKE_BIN

theorem of_int64_id (x : Integers.Int64) : Integers.Ptrofs.of_int64 x = x := by
  simp [Integers.Ptrofs.of_int64, Integers.MI.repr, Integers.MI.unsigned]

theorem to_int64_id (x : Integers.Ptrofs) : Integers.Ptrofs.to_int64 x = x := by
  simp [Integers.Ptrofs.to_int64]

theorem ptrofsOfInt_eq (si : Signedness) (n : Integers.Int) :
    Cop.ptrofsOfInt si n = Cop.castIntLong si n := by
  cases si
  · rfl
  · simp only [Cop.ptrofsOfInt, Cop.castIntLong, Integers.Ptrofs.of_intu, Integers.Ptrofs.of_int,
      Integers.Int64.repr, Integers.Int.unsigned, Integers.MI.repr, Integers.MI.unsigned]
    apply BitVec.eq_of_toNat_eq
    simp

/-- `Cshmgenproof.transl_sizeof` (whole-program version: the compilation unit
    is the program itself). -/
theorem transl_sizeof {ce : CompositeEnv} {t : Ty} {sz : Z} (h : sizeof ce t = .OK sz) :
    sz = CC.sizeof ce t := by
  unfold sizeof at h; split at h <;> cases h; rfl

theorem make_add_ptr_int_correct {ce : CompositeEnv} {ty : Ty} {si : Signedness}
    {a b c : Csharpminor.Expr} {va vb v : Val}
    (hmk : makeAddPtrInt ce ty si a b = .OK c) (ha : EV a va) (hb : EV b vb)
    (hs : Cop.semAddPtrInt ce ty si va vb = some v) : EV c v := by
  unfold makeAddPtrInt at hmk
  simp only [res_bind_eq_OK] at hmk
  obtain ⟨sz, hsz, hc⟩ := hmk
  rw [transl_sizeof hsz] at hc
  simp only [Archi.ptr64, if_true] at hc
  cases hc
  unfold Cop.semAddPtrInt at hs
  cases va <;> cases vb <;> simp [Archi.ptr64] at hs <;> subst hs
  · exact make_binop_correct ha (make_binop_correct (make_longconst_correct _)
      (make_longofint_correct si hb) rfl) rfl
  · refine make_binop_correct ha (make_binop_correct (make_longconst_correct _)
      (make_longofint_correct si hb) rfl) ?_
    simp [Cminor.evalBinop, Val.addl, Val.mull, Archi.ptr64, of_int64_id, ptrofsOfInt_eq]
    rfl

theorem make_add_ptr_long_correct {ce : CompositeEnv} {ty : Ty}
    {a b c : Csharpminor.Expr} {va vb v : Val}
    (hmk : makeAddPtrLong ce ty a b = .OK c) (ha : EV a va) (hb : EV b vb)
    (hs : Cop.semAddPtrLong ce ty va vb = some v) : EV c v := by
  unfold makeAddPtrLong at hmk
  simp only [res_bind_eq_OK] at hmk
  obtain ⟨sz, hsz, hc⟩ := hmk
  rw [transl_sizeof hsz] at hc
  simp only [Archi.ptr64, if_true] at hc
  cases hc
  unfold Cop.semAddPtrLong at hs
  cases va <;> cases vb <;> simp [Archi.ptr64] at hs <;> subst hs
  · exact make_binop_correct ha (make_binop_correct (make_longconst_correct _) hb rfl) rfl
  · refine make_binop_correct ha (make_binop_correct (make_longconst_correct _) hb rfl) ?_
    simp [Cminor.evalBinop, Val.addl, Val.mull, Archi.ptr64, of_int64_id]
    rfl

/-- `Cshmgenproof.make_add_correct` -/
theorem make_add_correct {ce : CompositeEnv} {a b c : Csharpminor.Expr} {tya tyb : Ty}
    {va vb v : Val} (hs : Cop.semAdd ce va tya vb tyb m = some v)
    (hmk : makeAdd ce a tya b tyb = .OK c) (ha : EV a va) (hb : EV b vb) : EV c v := by
  unfold makeAdd at hmk; unfold Cop.semAdd at hs
  cases hc : Cop.classifyAdd tya tyb <;> rw [hc] at hmk hs <;> simp only at hmk hs
  · exact make_add_ptr_int_correct hmk ha hb hs
  · exact make_add_ptr_long_correct hmk ha hb hs
  · exact make_add_ptr_int_correct hmk hb ha hs
  · exact make_add_ptr_long_correct hmk hb ha hs
  · exact make_binarith_correct (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) hs hmk ha hb

end CONSTRUCTORS

end Cshmgen
end CC
