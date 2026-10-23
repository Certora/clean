/-
  Subject reduction for CompCert C — port of the section "Subject reduction"
  of `cfrontend/Ctyping.v`.
-/
import CCLib.cfrontend.CtypingSound
import CCLib.common.EventsProps

namespace CC
namespace Ctyping

open Csyntax (typeof)

/-! ## Values produced by the operators are well typed -/

/-- `Ctyping.pres_cast_int_int` -/
theorem pres_cast_int_int (sz : IntSize) (sg : Signedness) (n : Integers.Int) :
    WtInt (Cop.castIntInt sz sg n) sz sg := by
  cases sz <;> cases sg <;> simp only [WtInt, Cop.castIntInt]
  · exact Integers.Int.sign_ext_idem (by decide) n
  · exact Integers.Int.zero_ext_idem 8 n
  · exact Integers.Int.sign_ext_idem (by decide) n
  · exact Integers.Int.zero_ext_idem 16 n
  all_goals first | trivial | (split <;> simp)

/-- `Ctyping.wt_val_casted` -/
theorem wt_val_casted {v : Val} {ty : Ty} (h : Cop.ValCasted v ty) : WtVal v ty := by
  cases h with
  | @int sz si attr n hn => exact .int _ _ _ _ (hn ▸ pres_cast_int_int sz si n)
  | float => exact .float _ _
  | single => exact .single _ _
  | long => exact .long _ _ _
  | ptr_ptr => exact .pointer _ _ _ _
  | int_ptr h => exact .int_pointer _ _ _ h
  | ptr_int h => exact .ptr_int _ _ _ _ h
  | long_ptr h => exact .long_pointer _ _ _ h
  | ptr_long h => exact .ptr_long _ _ _ _ h
  | struct => exact .struct _ _ _ _
  | union => exact .union _ _ _ _
  | void => exact .void _

/-- `Ctyping.pres_sem_cast` -/
theorem pres_sem_cast {m : Mem} {v2 : Val} {ty2 : Ty} {v1 : Val} {ty1 : Ty}
    (h : Cop.semCast v1 ty1 ty2 m = some v2) : WtVal v2 ty2 :=
  wt_val_casted (Cop.cast_val_is_casted h)

/-- The result of an integer operation: `None`, an `int` or `Vundef`. -/
def IntRes : Option Val → Prop
  | none | some (.Vint _) | some .Vundef => True
  | _ => False

/-- The result of a long operation. -/
def LongRes : Option Val → Prop
  | none | some (.Vlong _) | some .Vundef => True
  | _ => False

/-- The result of a double operation. -/
def FloatRes : Option Val → Prop
  | none | some (.Vfloat _) | some .Vundef => True
  | _ => False

/-- The result of a single operation. -/
def SingleRes : Option Val → Prop
  | none | some (.Vsingle _) | some .Vundef => True
  | _ => False

theorem IntRes.wt {v : Val} {sg : Signedness} {a : Attr} (h : IntRes (some v)) :
    WtVal v (.Tint .I32 sg a) := by
  cases v
  case Vint n => exact .int _ _ _ _ trivial
  case Vundef => exact .undef _
  all_goals exact (h : False).elim

theorem LongRes.wt {v : Val} {sg : Signedness} {a : Attr} (h : LongRes (some v)) :
    WtVal v (.Tlong sg a) := by
  cases v
  case Vlong n => exact .long _ _ _
  case Vundef => exact .undef _
  all_goals exact (h : False).elim

theorem FloatRes.wt {v : Val} {a : Attr} (h : FloatRes (some v)) :
    WtVal v (.Tfloat .F64 a) := by
  cases v
  case Vfloat n => exact .float _ _
  case Vundef => exact .undef _
  all_goals exact (h : False).elim

theorem SingleRes.wt {v : Val} {a : Attr} (h : SingleRes (some v)) :
    WtVal v (.Tfloat .F32 a) := by
  cases v
  case Vsingle n => exact .single _ _
  case Vundef => exact .undef _
  all_goals exact (h : False).elim

/-- `Ctyping.pres_sem_binarith` -/
theorem pres_sem_binarith
    {semInt : Signedness → Integers.Int → Integers.Int → Option Val}
    {semLong : Signedness → Integers.Int64 → Integers.Int64 → Option Val}
    {semFloat : Floats.Float → Floats.Float → Option Val}
    {semSingle : Floats.Float32 → Floats.Float32 → Option Val}
    {v1 : Val} {ty1 : Ty} {v2 : Val} {ty2 : Ty} {m : Mem} {v : Val} {ty : Ty} {msg : String}
    (hi : ∀ sg n1 n2, IntRes (semInt sg n1 n2))
    (hl : ∀ sg n1 n2, LongRes (semLong sg n1 n2))
    (hf : ∀ n1 n2, FloatRes (semFloat n1 n2))
    (hs : ∀ n1 n2, SingleRes (semSingle n1 n2))
    (h : Cop.semBinarith semInt semLong semFloat semSingle v1 ty1 v2 ty2 m = some v)
    (ht : binarithType ty1 ty2 msg = .OK ty) : WtVal v ty := by
  unfold Cop.semBinarith at h; dsimp only at h
  unfold binarithType at ht
  generalize Cop.classifyBinarith ty1 ty2 = c at h ht
  generalize Cop.semCast v1 ty1 (Cop.binarithType c) m = o1 at h
  generalize Cop.semCast v2 ty2 (Cop.binarithType c) m = o2 at h
  rcases o1 with _ | v1' <;> rcases o2 with _ | v2' <;> simp only [reduceCtorEq] at h
  cases c <;> simp only [Res.OK.injEq, reduceCtorEq] at ht <;> subst ht <;>
    cases v1' <;> cases v2' <;> simp only [reduceCtorEq] at h
  · exact IntRes.wt (h ▸ hi _ _ _)
  · exact LongRes.wt (h ▸ hl _ _ _)
  · exact FloatRes.wt (h ▸ hf _ _)
  · exact SingleRes.wt (h ▸ hs _ _)

/-- `Ctyping.pres_sem_binarith_int` -/
theorem pres_sem_binarith_int
    {semInt : Signedness → Integers.Int → Integers.Int → Option Val}
    {semLong : Signedness → Integers.Int64 → Integers.Int64 → Option Val}
    {v1 : Val} {ty1 : Ty} {v2 : Val} {ty2 : Ty} {m : Mem} {v : Val} {ty : Ty} {msg : String}
    (hi : ∀ sg n1 n2, IntRes (semInt sg n1 n2))
    (hl : ∀ sg n1 n2, LongRes (semLong sg n1 n2))
    (h : Cop.semBinarith semInt semLong (fun _ _ => none) (fun _ _ => none) v1 ty1 v2 ty2 m = some v)
    (ht : binarithIntType ty1 ty2 msg = .OK ty) : WtVal v ty := by
  refine pres_sem_binarith (semFloat := fun _ _ => none) (semSingle := fun _ _ => none)
    (msg := msg) hi hl (fun _ _ => trivial) (fun _ _ => trivial) h ?_
  unfold binarithIntType at ht; unfold binarithType
  split at ht <;> simp_all

/-- `Ctyping.pres_sem_shift` -/
theorem pres_sem_shift
    {semInt : Signedness → Integers.Int → Integers.Int → Integers.Int}
    {semLong : Signedness → Integers.Int64 → Integers.Int64 → Integers.Int64}
    {ty1 ty2 : Ty} {msg : String} {ty : Ty} {v1 v2 v : Val}
    (ht : shiftOpType ty1 ty2 msg = .OK ty)
    (h : Cop.semShift semInt semLong v1 ty1 v2 ty2 = some v) : WtVal v ty := by
  unfold shiftOpType at ht; unfold Cop.semShift at h
  generalize Cop.classifyShift ty1 ty2 = c at h ht
  cases c <;> simp only [Res.OK.injEq, reduceCtorEq] at ht <;> subst ht <;>
    cases v1 <;> cases v2 <;> simp only [reduceCtorEq] at h <;>
    (split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h) <;> subst h <;>
    first | exact .int _ _ _ _ trivial | exact .long _ _ _

theorem wt_ofBool (b : Bool) : WtVal (Val.ofBool b) (.Tint .I32 .Signed noattr) := by
  cases b <;> exact .int _ _ _ _ trivial

theorem wt_cmpPtr {m : Mem} {c : Comparison} {v1 v2 v : Val}
    (h : Cop.cmpPtr m c v1 v2 = some v) : WtVal v (.Tint .I32 .Signed noattr) := by
  unfold Cop.cmpPtr at h
  generalize (if Archi.ptr64 then _ else _ : Option Bool) = o at h
  cases o <;> simp only [Option.map, Option.some.injEq, reduceCtorEq] at h
  subst h; exact wt_ofBool _

/-- Every value computed by `sem_binarith` is computed by one of its four
    arguments. -/
theorem semBinarith_prop {P : Val → Prop}
    {semInt : Signedness → Integers.Int → Integers.Int → Option Val}
    {semLong : Signedness → Integers.Int64 → Integers.Int64 → Option Val}
    {semFloat : Floats.Float → Floats.Float → Option Val}
    {semSingle : Floats.Float32 → Floats.Float32 → Option Val}
    {v1 : Val} {ty1 : Ty} {v2 : Val} {ty2 : Ty} {m : Mem} {v : Val}
    (hi : ∀ sg n1 n2 v, semInt sg n1 n2 = some v → P v)
    (hl : ∀ sg n1 n2 v, semLong sg n1 n2 = some v → P v)
    (hf : ∀ n1 n2 v, semFloat n1 n2 = some v → P v)
    (hs : ∀ n1 n2 v, semSingle n1 n2 = some v → P v)
    (h : Cop.semBinarith semInt semLong semFloat semSingle v1 ty1 v2 ty2 m = some v) : P v := by
  unfold Cop.semBinarith at h; dsimp only at h
  generalize Cop.classifyBinarith ty1 ty2 = c at h
  generalize Cop.semCast v1 ty1 (Cop.binarithType c) m = o1 at h
  generalize Cop.semCast v2 ty2 (Cop.binarithType c) m = o2 at h
  rcases o1 with _ | v1' <;> rcases o2 with _ | v2' <;> simp only [reduceCtorEq] at h
  cases c <;> cases v1' <;> cases v2' <;> simp only [reduceCtorEq] at h
  · exact hi _ _ _ _ h
  · exact hl _ _ _ _ h
  · exact hf _ _ _ h
  · exact hs _ _ _ h

/-- `Ctyping.pres_sem_cmp` -/
theorem pres_sem_cmp {ty1 ty2 : Ty} {msg : String} {ty : Ty} {c : Comparison}
    {v1 v2 : Val} {m : Mem} {v : Val}
    (ht : comparisonType ty1 ty2 msg = .OK ty)
    (h : Cop.semCmp c v1 ty1 v2 ty2 m = some v) : WtVal v ty := by
  unfold comparisonType at ht; unfold Cop.semCmp at h
  cases hcc : Cop.classifyCmp ty1 ty2 <;> simp only [hcc] at h ht
  case default =>
    have hty : ty = .Tint .I32 .Signed noattr := by split at ht <;> simp_all
    subst hty
    refine semBinarith_prop (P := fun v => WtVal v (.Tint .I32 .Signed noattr))
      ?_ ?_ ?_ ?_ h
    · intro sg _ _ _ e; cases sg <;> simp only [Option.some.injEq] at e <;> subst e <;>
        exact wt_ofBool _
    · intro sg _ _ _ e; cases sg <;> simp only [Option.some.injEq] at e <;> subst e <;>
        exact wt_ofBool _
    · intro _ _ _ e; simp only [Option.some.injEq] at e; subst e; exact wt_ofBool _
    · intro _ _ _ e; simp only [Option.some.injEq] at e; subst e; exact wt_ofBool _
  all_goals
    simp only [Res.OK.injEq] at ht; subst ht
    (repeat' split at h) <;>
      (try simp only [reduceCtorEq] at h) <;>
      exact wt_cmpPtr h

theorem wt_semAddPtrInt {cenv : CompositeEnv} {ty : Ty} {si : Signedness} {v1 v2 v : Val}
    {t : Ty} {a : Attr} (h : Cop.semAddPtrInt cenv ty si v1 v2 = some v) :
    WtVal v (.Tpointer t a) := by
  unfold Cop.semAddPtrInt at h
  cases v1 <;> cases v2 <;> simp [Archi.ptr64] at h <;> subst h
  · exact .long_pointer _ _ _ rfl
  · exact .pointer _ _ _ _

theorem wt_semAddPtrLong {cenv : CompositeEnv} {ty : Ty} {v1 v2 v : Val}
    {t : Ty} {a : Attr} (h : Cop.semAddPtrLong cenv ty v1 v2 = some v) :
    WtVal v (.Tpointer t a) := by
  unfold Cop.semAddPtrLong at h
  cases v1 <;> cases v2 <;> simp [Archi.ptr64] at h <;> subst h
  · exact .long_pointer _ _ _ rfl
  · exact .pointer _ _ _ _

/-- `Ctyping.pres_sem_binop` -/
theorem pres_sem_binop {ce : CompositeEnv} {op : Binop} {ty1 ty2 ty : Ty} {v1 v2 v : Val}
    {m : Mem} (TY : typeBinop op ty1 ty2 = .OK ty)
    (SEM : Cop.semBinaryOperation ce op v1 ty1 v2 ty2 m = some v) : WtVal v ty := by
  cases op <;> simp only [typeBinop] at TY <;> simp only [Cop.semBinaryOperation] at SEM
  case Oadd =>
    unfold Cop.semAdd at SEM
    cases hc : Cop.classifyAdd ty1 ty2 <;> simp only [hc, Res.OK.injEq] at TY SEM
    case default =>
      refine pres_sem_binarith ?_ ?_ ?_ ?_ SEM TY <;> intros <;> trivial
    all_goals subst TY
    · exact wt_semAddPtrInt SEM
    · exact wt_semAddPtrLong SEM
    · exact wt_semAddPtrInt SEM
    · exact wt_semAddPtrLong SEM
  case Osub =>
    unfold Cop.semSub at SEM
    cases hc : Cop.classifySub ty1 ty2 <;> simp only [hc, Res.OK.injEq] at TY SEM
    case default =>
      refine pres_sem_binarith ?_ ?_ ?_ ?_ SEM TY <;> intros <;> trivial
    all_goals subst TY
    · cases v1 <;> cases v2 <;> simp [Archi.ptr64] at SEM <;> subst SEM
      · exact .long_pointer _ _ _ rfl
      · exact .pointer _ _ _ _
    · cases v1 <;> cases v2 <;> simp only [reduceCtorEq] at SEM
      split at SEM <;> try simp only [reduceCtorEq] at SEM
      split at SEM <;> simp only [reduceCtorEq, Option.some.injEq] at SEM
      subst SEM
      exact .long _ _ _
    · cases v1 <;> cases v2 <;> simp [Archi.ptr64] at SEM <;> subst SEM
      · exact .long_pointer _ _ _ rfl
      · exact .pointer _ _ _ _
  case Omul =>
    refine pres_sem_binarith ?_ ?_ ?_ ?_ SEM TY <;> intros <;> trivial
  case Odiv =>
    refine pres_sem_binarith ?_ ?_ ?_ ?_ SEM TY
    rotate_left 2; (intros; trivial); (intros; trivial)
    · intro sg _ _; cases sg <;> dsimp only <;> split <;> trivial
    · intro sg _ _; cases sg <;> dsimp only <;> split <;> trivial
  case Omod =>
    refine pres_sem_binarith_int ?_ ?_ SEM TY
    · intro sg _ _; cases sg <;> dsimp only <;> split <;> trivial
    · intro sg _ _; cases sg <;> dsimp only <;> split <;> trivial
  case Oand => (refine pres_sem_binarith_int ?_ ?_ SEM TY <;> intros <;> trivial)
  case Oor => (refine pres_sem_binarith_int ?_ ?_ SEM TY <;> intros <;> trivial)
  case Oxor => (refine pres_sem_binarith_int ?_ ?_ SEM TY <;> intros <;> trivial)
  case Oshl => exact pres_sem_shift TY SEM
  case Oshr => exact pres_sem_shift TY SEM
  all_goals exact pres_sem_cmp TY SEM

/-- `Ctyping.pres_sem_unop` -/
theorem pres_sem_unop {op : Unop} {ty1 ty : Ty} {v1 : Val} {m : Mem} {v : Val}
    (TY : typeUnop op ty1 = .OK ty)
    (SEM : Cop.semUnaryOperation op v1 ty1 m = some v) : WtVal v ty := by
  cases op <;> simp only [typeUnop] at TY <;> simp only [Cop.semUnaryOperation] at SEM
  case Onotbool =>
    have A : ty = .Tint .I32 .Signed noattr := by split at TY <;> simp_all
    subst A
    unfold Cop.semNotbool at SEM
    cases hb : Cop.boolVal v1 ty1 m <;> simp only [hb, Option.map, Option.some.injEq,
      reduceCtorEq] at SEM
    subst SEM; exact wt_ofBool _
  case Onotint =>
    unfold Cop.semNotint at SEM
    split at TY <;> rename_i hc <;> simp only [hc, Res.OK.injEq, reduceCtorEq] at TY SEM <;>
      subst TY <;> cases v1 <;> simp only [Option.some.injEq, reduceCtorEq] at SEM <;> subst SEM
    · exact .int _ _ _ _ trivial
    · exact .long _ _ _
  case Oneg =>
    unfold Cop.semNeg at SEM
    split at TY <;> rename_i hc <;> simp only [hc, Res.OK.injEq, reduceCtorEq] at TY SEM <;>
      subst TY <;> cases v1 <;> simp only [Option.some.injEq, reduceCtorEq] at SEM <;> subst SEM
    · exact .int _ _ _ _ trivial
    · exact .float _ _
    · exact .single _ _
    · exact .long _ _ _
  case Oabsfloat =>
    have A : ty = .Tfloat .F64 noattr := by split at TY <;> simp_all
    subst A
    unfold Cop.semAbsfloat at SEM
    split at SEM <;> cases v1 <;> simp only [Option.some.injEq, reduceCtorEq] at SEM <;>
      subst SEM <;> exact .float _ _

/-! ## Values read from memory are well typed -/

/-- `Ctyping.has_rettype_wt_val` -/
theorem has_rettype_wt_val {v : Val} {ty : Ty} (h : Val.hasRettype v (rettypeOfType ty)) :
    WtVal v ty := by
  rcases ty with _ | ⟨sz, sg, a⟩ | ⟨sg, a⟩ | ⟨fs, a⟩ | ⟨t, a⟩ | ⟨t, n, a⟩ |
      ⟨ta, tr, cc⟩ | ⟨id, a⟩ | ⟨id, a⟩
  · exact .void _
  all_goals cases_sizes <;> cases v <;>
    simp only [rettypeOfType, argtypeOfType, Val.hasRettype, Archi.ptr64, reduceCtorEq] at h <;>
    first
      | exact .undef _
      | exact .int _ _ _ _ h.symm
      | exact .int _ _ _ _ h
      | exact .int _ _ _ _ True.intro
      | exact .long _ _ _
      | exact .ptr_long _ _ _ _ rfl
      | exact .float _ _
      | exact .single _ _
      | exact .pointer _ _ _ _
      | exact .long_pointer _ _ _ rfl
      | exact h.elim

/-- A value of the result type of the chunk used to access a by-value type is
    well typed at that type. -/
theorem wt_of_chunk_xtype {ty : Ty} {chunk : Chunk} {v : Val}
    (hm : accessMode ty = .By_value chunk) (h : Val.hasRettype v chunk.xtype) : WtVal v ty := by
  rcases ty with _ | ⟨sz, sg, a⟩ | ⟨sg, a⟩ | ⟨fs, a⟩ | ⟨t, a⟩ | ⟨t, n, a⟩ |
      ⟨ta, tr, cc⟩ | ⟨id, a⟩ | ⟨id, a⟩ <;> cases_sizes <;>
    simp only [accessMode, Mptr, Archi.ptr64, if_true, AccessMode.By_value.injEq,
      reduceCtorEq] at hm <;> subst hm
  case Tpointer =>
    cases v <;> simp only [Chunk.xtype, Val.hasRettype] at h
    · exact .undef _
    · exact .long_pointer _ _ _ rfl
    · exact .pointer _ _ _ _
  all_goals exact has_rettype_wt_val h

/-- `Ctyping.wt_load_result` -/
theorem wt_load_result {ty : Ty} {chunk : Chunk} (v : Val) (h : accessMode ty = .By_value chunk) :
    WtVal (Val.loadResult chunk v) ty :=
  wt_of_chunk_xtype h (EventsProps.loadResult_hasRettype chunk v)

/-- `Ctyping.wt_decode_val` -/
theorem wt_decode_val {ty : Ty} {chunk : Chunk} (vl : List MemVal)
    (h : accessMode ty = .By_value chunk) : WtVal (decodeVal chunk vl) ty :=
  wt_of_chunk_xtype h (EventsProps.decodeVal_hasRettype chunk vl)

theorem loadv_hasRettype {chunk : Chunk} {m : Mem} {a : Val} {v : Val}
    (h : Mem.loadv chunk m a = some v) : Val.hasRettype v chunk.xtype := by
  unfold Mem.loadv at h
  split at h
  · split at h
    · exact EventsProps.load_hasRettype h
    · cases h
  · cases h

theorem Int_sign_zero_ext_widen {n n' : Nat} (h : n < n') (x : Integers.Int) :
    Integers.Int.sign_ext n' (Integers.Int.zero_ext n x) = Integers.Int.zero_ext n x := by
  apply Integers.MI.same_bits_eq
  intro i hi
  have e1 := Integers.Int.bits_sign_ext (n := n') (by omega) (Integers.Int.zero_ext n x) hi
  have e2 := fun j => Integers.Int.bits_zero_ext n x j
  simp only [Integers.Int.testbit] at e1 e2
  rw [e1]
  split
  · rfl
  · rw [e2, e2]
    have : ¬ (n' - 1 < n) := by omega
    have : ¬ (i < n) := by omega
    simp [*]

theorem Int_zero_ext_one (n : Integers.Int) :
    Integers.Int.zero_ext 1 n = Integers.Int.zero ∨ Integers.Int.zero_ext 1 n = Integers.Int.one := by
  have hr := Integers.Int.zero_ext_range 1 n
  have h0 : 0 ≤ Integers.Int.unsigned (Integers.Int.zero_ext 1 n) := by
    simp [Integers.Int.unsigned, Integers.MI.unsigned]
  have : Integers.Int.unsigned (Integers.Int.zero_ext 1 n) = 0 ∨
      Integers.Int.unsigned (Integers.Int.zero_ext 1 n) = 1 := by
    have : (2 : Z) ^ 1 = 2 := by decide
    rw [this] at hr
    simp only [Z] at *
    omega
  rcases this with e | e
  · exact .inl (Integers.Int.unsigned_inj (e.trans (by decide)))
  · exact .inr (Integers.Int.unsigned_inj (e.trans (by decide)))

/-- `Ctyping.wt_bitfield_normalize` -/
theorem wt_bitfield_normalize {sz : IntSize} {sg : Signedness} {width : Z} {sg1 : Signedness}
    (n : Integers.Int) (h1 : 0 < width) (h2 : width ≤ bitsizeIntsize sz)
    (hsg : sg1 = (if width < bitsizeIntsize sz then Signedness.Signed else sg)) :
    WtInt (Cop.bitfieldNormalize sz sg width n) sz sg1 := by
  simp only [Z] at *
  have hw : 0 < width.toNat := by omega
  cases sz <;> simp only [bitsizeIntsize] at h2 hsg
  · -- I8
    cases sg <;> simp only [Cop.bitfieldNormalize, reduceCtorEq, Bool.or_false,
      decide_false, decide_true, Bool.or_true, if_true, if_false] at *
    · subst hsg; split <;> simp only [WtInt]
      · exact Integers.Int.sign_ext_widen hw (by omega) n
      · exact Integers.Int.sign_ext_widen hw (by omega) n
    · subst hsg; split
      · simp only [WtInt]; exact Int_sign_zero_ext_widen (by omega) n
      · simp only [WtInt]; exact Integers.Int.zero_ext_widen (by omega) n
  · -- I16
    cases sg <;> simp only [Cop.bitfieldNormalize, reduceCtorEq, Bool.or_false,
      decide_false, decide_true, Bool.or_true, if_true, if_false] at *
    · subst hsg; split <;> simp only [WtInt]
      · exact Integers.Int.sign_ext_widen hw (by omega) n
      · exact Integers.Int.sign_ext_widen hw (by omega) n
    · subst hsg; split
      · simp only [WtInt]; exact Int_sign_zero_ext_widen (by omega) n
      · simp only [WtInt]; exact Integers.Int.zero_ext_widen (by omega) n
  · -- I32
    cases sg1 <;> trivial
  · -- IBool
    have : width.toNat = 1 := by omega
    cases sg1 <;> simp only [WtInt, Cop.bitfieldNormalize, decide_true, Bool.true_or,
      if_true, this] <;> exact Int_zero_ext_one n

/-- `Ctyping.wt_deref_loc` -/
theorem wt_deref_loc {ge : Csem.CGenv} {ty : Ty} {m : Mem} {b : Block} {ofs : Integers.Ptrofs}
    {bf : Bitfield} {t : Trace} {v : Val} (h : Csem.DerefLoc ge ty m b ofs bf t v) :
    WtVal v ty := by
  cases h with
  | value chunk v hm _ hl => exact wt_of_chunk_xtype hm (loadv_hasRettype hl)
  | volatile chunk t v hm _ hv =>
    cases hv with
    | vol => exact wt_load_result _ hm
    | nonvol _ _ hl =>
      exact wt_of_chunk_xtype hm (EventsProps.load_hasRettype hl)
  | reference hm =>
    rcases ty with _ | ⟨sz, sg, a⟩ | ⟨sg, a⟩ | ⟨fs, a⟩ | ⟨t, a⟩ | ⟨t, n, a⟩ |
      ⟨ta, tr, cc⟩ | ⟨id, a⟩ | ⟨id, a⟩ <;> cases_sizes <;>
      simp only [accessMode, reduceCtorEq] at hm <;>
      first | exact .array _ _ _ _ _ | exact .function _ _ _ _ _
  | copy hm =>
    rcases ty with _ | ⟨sz, sg, a⟩ | ⟨sg, a⟩ | ⟨fs, a⟩ | ⟨t, a⟩ | ⟨t, n, a⟩ |
      ⟨ta, tr, cc⟩ | ⟨id, a⟩ | ⟨id, a⟩ <;> cases_sizes <;>
      simp only [accessMode, reduceCtorEq] at hm <;>
      first | exact .struct _ _ _ _ | exact .union _ _ _ _
  | bitfield sz sg pos width v hb =>
    cases hb with
    | intro _ _ _ _ _ _ _ _ _ h0 h1 h2 _ hsg _ =>
      exact .int _ _ _ _ (wt_bitfield_normalize _ h1 h2 hsg)

/-- `Ctyping.wt_assign_loc` -/
theorem wt_assign_loc {ge : Csem.CGenv} {ty : Ty} {m : Mem} {b : Block} {ofs : Integers.Ptrofs}
    {bf : Bitfield} {v : Val} {t : Trace} {m' : Mem} {v' : Val}
    (h : Csem.AssignLoc ge ty m b ofs bf v t m' v') (hv : WtVal v ty) : WtVal v' ty := by
  cases h with
  | bitfield sz sg pos width v m' v' hb =>
    cases hb with
    | intro _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 _ hsg _ _ =>
      exact .int _ _ _ _ (wt_bitfield_normalize _ h1 h2 hsg)
  | _ => exact hv

/-! ## Head reductions preserve typing -/

/-- `Ctyping.wt_cast_self` -/
theorem wt_cast_self {t1 t2 : Ty} (h : WtCast t1 t2) : WtCast t2 t2 := by
  unfold WtCast at *
  rcases t2 with _ | ⟨sz, sg, a⟩ | ⟨sg, a⟩ | ⟨fs, a⟩ | ⟨t, a⟩ | ⟨t, n, a⟩ |
      ⟨ta, tr, cc⟩ | ⟨id, a⟩ | ⟨id, a⟩ <;> cases_sizes <;>
    simp_all [Cop.classifyCast, Archi.ptr64]

/-- `Ctyping.binarith_type_int32s` -/
theorem binarith_type_int32s {ty1 : Ty} {msg : String} {ty2 : Ty}
    (h : binarithType ty1 type_int32s msg = .OK ty2) : ty2 = Cop.incrdecrType ty1 := by
  rcases ty1 with _ | ⟨sz, sg, a⟩ | ⟨sg, a⟩ | ⟨fs, a⟩ | ⟨t, a⟩ | ⟨t, n, a⟩ |
      ⟨ta, tr, cc⟩ | ⟨id, a⟩ | ⟨id, a⟩ <;> cases_sizes <;>
    simp [binarithType, Cop.classifyBinarith, type_int32s] at h <;> subst h <;>
    simp [Cop.incrdecrType, typeconv, removeAttributes, tattr, tint]

/-- `Ctyping.type_add_int32s` -/
theorem type_add_int32s {ty1 ty2 : Ty} (h : typeBinop .Oadd ty1 type_int32s = .OK ty2) :
    ty2 = Cop.incrdecrType ty1 := by
  rcases ty1 with _ | ⟨sz, sg, a⟩ | ⟨sg, a⟩ | ⟨fs, a⟩ | ⟨t, a⟩ | ⟨t, n, a⟩ |
      ⟨ta, tr, cc⟩ | ⟨id, a⟩ | ⟨id, a⟩ <;> cases_sizes <;>
    simp [typeBinop, Cop.classifyAdd, binarithType, Cop.classifyBinarith, type_int32s,
      typeconv, removeAttributes, tattr, tint] at h <;> subst h <;>
    simp [Cop.incrdecrType, typeconv, removeAttributes, tattr, tint]

/-- `Ctyping.type_sub_int32s` -/
theorem type_sub_int32s {ty1 ty2 : Ty} (h : typeBinop .Osub ty1 type_int32s = .OK ty2) :
    ty2 = Cop.incrdecrType ty1 := by
  rcases ty1 with _ | ⟨sz, sg, a⟩ | ⟨sg, a⟩ | ⟨fs, a⟩ | ⟨t, a⟩ | ⟨t, n, a⟩ |
      ⟨ta, tr, cc⟩ | ⟨id, a⟩ | ⟨id, a⟩ <;> cases_sizes <;>
    simp [typeBinop, Cop.classifySub, binarithType, Cop.classifyBinarith, type_int32s,
      typeconv, removeAttributes, tattr, tint] at h <;> subst h <;>
    simp [Cop.incrdecrType, typeconv, removeAttributes, tattr, tint]

theorem subtype_bool_int : Subtype type_bool (.Tint .I32 .Signed noattr) := by
  intro v hv
  cases hv with
  | int n _ _ _ _ => exact .int _ _ _ _ True.intro
  | undef => exact .undef _

theorem subtype_refl (ty : Ty) : Subtype ty ty := fun _ h => h

theorem wt_size_t (n : Integers.Ptrofs) : WtVal (Val.Vptrofs n) size_t := by
  simp only [Val.Vptrofs, size_t, Archi.ptr64, if_true]; exact .long _ _ _

/-- `Ctyping.wt_rred` -/
theorem wt_rred {ge : Csem.CGenv} {ce : CompositeEnv} {tenv : Typenv} {a : Csyntax.Expr}
    {m : Mem} {t : Trace} {a' : Csyntax.Expr} {m' : Mem}
    (h : Csem.Rred ge a m t a' m') (WT : WtRvalue ce tenv a) : WtRvalue ce tenv a' := by
  cases h with
  | rvalof b ofs bf ty m t v hd => exact .val _ _ (wt_deref_loc hd)
  | addrof => cases WT; exact .val _ _ (.pointer _ _ _ _)
  | unop op v1 ty1 ty m v hs =>
    cases WT with
    | unop _ _ _ hr ht => cases hr with
      | val _ _ hv => exact .val _ _ (pres_sem_unop ht hs)
  | binop op v1 ty1 v2 ty2 ty m v hs =>
    cases WT with
    | binop _ _ _ _ _ _ ht => exact .val _ _ (pres_sem_binop ht hs)
  | cast ty v1 ty1 m v hs => exact .val _ _ (pres_sem_cast hs)
  | seqand_true =>
    cases WT with
    | seqand _ _ _ h2 _ hb2 => exact .paren _ _ _ h2 (wtBool_cast hb2) subtype_bool_int
  | seqand_false => cases WT; exact .val _ _ (.int _ _ _ _ True.intro)
  | seqor_true => cases WT; exact .val _ _ (.int _ _ _ _ True.intro)
  | seqor_false =>
    cases WT with
    | seqor _ _ _ h2 _ hb2 => exact .paren _ _ _ h2 (wtBool_cast hb2) subtype_bool_int
  | condition v1 ty1 r1 r2 ty b m =>
    cases WT with
    | condition _ _ _ _ _ h2 h3 _ hc2 hc3 =>
      cases b
      · exact .paren _ _ _ h3 hc3 (subtype_refl _)
      · exact .paren _ _ _ h2 hc2 (subtype_refl _)
  | sizeof => cases WT; exact .val _ _ (wt_size_t _)
  | alignof => cases WT; exact .val _ _ (wt_size_t _)
  | assign b ofs ty1 bf v2 ty2 m v t m' v' hc ha =>
    exact .val _ _ (wt_assign_loc ha (pres_sem_cast hc))
  | assignop op b ofs ty1 bf v2 ty2 tyres m t v1 hd =>
    cases WT with
    | assignop _ _ _ _ hl hr ht hc =>
      exact .assign _ _ hl (.binop _ _ _ _ (.val _ _ (wt_deref_loc hd)) hr ht) hc
  | postincr id b ofs ty bf m t v1 op hd hop =>
    cases WT with
    | postincr _ _ ty0 hl ht hc =>
      subst hop
      have hd' := wt_deref_loc hd
      cases id
      · have hty := type_add_int32s ht; subst hty
        exact .comma _ _ (.assign _ _ hl (.binop _ _ _ _ (.val _ _ hd')
          (.val _ _ (.int _ _ _ _ True.intro)) ht) hc) (.val _ _ hd')
      · have hty := type_sub_int32s ht; subst hty
        exact .comma _ _ (.assign _ _ hl (.binop _ _ _ _ (.val _ _ hd')
          (.val _ _ (.int _ _ _ _ True.intro)) ht) hc) (.val _ _ hd')
  | comma v ty1 r2 ty m _ => cases WT with
    | comma _ _ _ h2 => exact h2
  | paren v1 ty1 ty2 ty m v hs =>
    cases WT with
    | paren _ _ _ _ _ hsub => exact .val _ _ (hsub _ (pres_sem_cast hs))
  | builtin ef tyargs el ty m vargs t vres m' hca hec =>
    cases WT with
    | builtin _ _ _ _ _ _ hcase =>
      rcases hcase with ⟨rfl, _⟩ | ⟨rfl, rfl⟩
      · exact .val _ _ (.void _)
      · cases hca with
        | cons v1 ty1 el1 _ _ v1' vl hc1 hca =>
        cases hca with
        | cons v2 ty2 el2 _ _ v2' vl hc2 hca =>
        cases hca with
        | cons v3 ty3 el3 _ _ v3' vl hc3 hca =>
        cases hca
        simp only [externalCall, builtinOrExternalSem, Csem.lookup_sel] at hec
        cases hec with
        | intro _ _ _ _ hs =>
        change Builtins.selectFn _ v1' v2' v3' = some vres at hs
        have A := Cop.cast_val_is_casted hc1
        cases A with
        | @int _ _ _ n _ =>
        simp only [Builtins.selectFn, Option.some.injEq] at hs
        subst hs
        by_cases hty : ty = .Tvoid
        · subst hty; exact .val _ _ (.void _)
        · have C : Cop.ValCasted (if Integers.Int.eq n Integers.Int.zero then v3' else v2') ty := by
            split
            · exact Cop.cast_val_is_casted hc3
            · exact Cop.cast_val_is_casted hc2
          rw [Val.normalize_idem (Cop.val_casted_hasType C hty)]
          exact .val _ _ (wt_val_casted C)

/-- `Ctyping.wt_lred` -/
theorem wt_lred {ge : Csem.CGenv} {ce : CompositeEnv} {tenv : Typenv} {e : Env}
    {a : Csyntax.Expr} {m : Mem} {a' : Csyntax.Expr} {m' : Mem}
    (h : Csem.Lred ge e a m a' m') (_WT : WtLvalue ce tenv a) : WtLvalue ce tenv a' := by
  cases h <;> exact .loc _ _ _ _

/-- `Ctyping.rred_same_type` -/
theorem rred_same_type {ge : Csem.CGenv} {a : Csyntax.Expr} {m : Mem} {t : Trace}
    {a' : Csyntax.Expr} {m' : Mem} (h : Csem.Rred ge a m t a' m') : Csyntax.typeof a' = Csyntax.typeof a := by
  cases h <;> first | rfl | (simp only [Csyntax.typeof]; assumption)

/-- `Ctyping.lred_same_type` -/
theorem lred_same_type {ge : Csem.CGenv} {e : Env} {a : Csyntax.Expr} {m : Mem}
    {a' : Csyntax.Expr} {m' : Mem} (h : Csem.Lred ge e a m a' m') : Csyntax.typeof a' = Csyntax.typeof a := by
  cases h <;> rfl

/-! ## Typing of reduction contexts -/

section WT_CONTEXT

variable {ce : CompositeEnv} {tenv : Typenv} {a a' : Csyntax.Expr}

mutual
/-- `Ctyping.wt_subexpr` -/
theorem wt_subexpr {from_ : Csem.Kind} : ∀ {to C}, Csem.Context from_ to C →
    WtExprKind ce tenv to (C a) → WtExprKind ce tenv from_ a
  | _, _, .top _, h => h
  | _, _, .deref _ _ _ hC, h => by cases h; exact wt_subexpr hC ‹_›
  | _, _, .field _ _ _ _ hC, h => by cases h; exact wt_subexpr hC ‹_›
  | _, _, .rvalof _ _ _ hC, h => by cases h; exact wt_subexpr hC ‹_›
  | _, _, .addrof _ _ _ hC, h => by cases h; exact wt_subexpr hC ‹_›
  | _, _, .unop _ _ _ _ hC, h => by cases h; exact wt_subexpr hC ‹_›
  | _, _, .binop_left _ _ _ _ _ hC, h => by
      cases h with | binop _ _ _ _ h1 _ _ => exact wt_subexpr hC h1
  | _, _, .binop_right _ _ _ _ _ hC, h => by
      cases h with | binop _ _ _ _ _ h2 _ => exact wt_subexpr hC h2
  | _, _, .cast _ _ _ hC, h => by cases h; exact wt_subexpr hC ‹_›
  | _, _, .seqand _ _ _ _ hC, h => by
      cases h with | seqand _ _ h1 _ _ _ => exact wt_subexpr hC h1
  | _, _, .seqor _ _ _ _ hC, h => by
      cases h with | seqor _ _ h1 _ _ _ => exact wt_subexpr hC h1
  | _, _, .condition _ _ _ _ _ hC, h => by
      cases h with | condition _ _ _ _ h1 _ _ _ _ _ => exact wt_subexpr hC h1
  | _, _, .assign_left _ _ _ _ hC, h => by
      cases h with | assign _ _ h1 _ _ => exact wt_subexpr hC h1
  | _, _, .assign_right _ _ _ _ hC, h => by
      cases h with | assign _ _ _ h2 _ => exact wt_subexpr hC h2
  | _, _, .assignop_left _ _ _ _ _ _ hC, h => by
      cases h with | assignop _ _ _ _ h1 _ _ _ => exact wt_subexpr hC h1
  | _, _, .assignop_right _ _ _ _ _ _ hC, h => by
      cases h with | assignop _ _ _ _ _ h2 _ _ => exact wt_subexpr hC h2
  | _, _, .postincr _ _ _ _ hC, h => by
      cases h with | postincr _ _ _ h1 _ _ => exact wt_subexpr hC h1
  | _, _, .call_left _ _ _ _ hC, h => by
      cases h with | call _ _ _ _ _ h1 _ _ _ => exact wt_subexpr hC h1
  | _, _, .call_right _ _ _ _ hC, h => by
      cases h with | call _ _ _ _ _ _ h2 _ _ => exact wt_subexprlist hC h2
  | _, _, .builtin _ _ _ _ _ hC, h => by
      cases h with | builtin _ _ _ _ h1 _ _ => exact wt_subexprlist hC h1
  | _, _, .comma _ _ _ _ hC, h => by
      cases h with | comma _ _ h1 _ => exact wt_subexpr hC h1
  | _, _, .paren _ _ _ _ hC, h => by
      cases h with | paren _ _ _ h1 _ _ => exact wt_subexpr hC h1

/-- `Ctyping.wt_subexprlist` -/
theorem wt_subexprlist {from_ : Csem.Kind} : ∀ {C}, Csem.ContextList from_ C →
    WtExprlist ce tenv (C a) → WtExprKind ce tenv from_ a
  | _, .head _ _ _ hC, h => by
      cases h with | cons _ _ h1 _ => exact wt_subexpr hC h1
  | _, .tail _ _ _ hC, h => by
      cases h with | cons _ _ _ h2 => exact wt_subexprlist hC h2
end

/-- `Ctyping.typeof_context` -/
theorem typeof_context (hty : Csyntax.typeof a' = Csyntax.typeof a) {from_ to C} (h : Csem.Context from_ to C) :
    Csyntax.typeof (C a') = Csyntax.typeof (C a) := by
  cases h <;> first | exact hty | rfl

/-- `Ctyping.wt_arguments_context` -/
theorem wt_arguments_context (hty : Csyntax.typeof a' = Csyntax.typeof a) {k : Csem.Kind} : ∀ {C}, Csem.ContextList k C →
    ∀ {tyl}, WtArguments (C a) tyl → WtArguments (C a') tyl
  | _, .head _ _ _ hC, _, h => by
      cases h with
      | cons _ _ _ _ h1 h2 => exact .cons _ _ _ _ (by rw [typeof_context hty hC]; exact h1) h2
      | extra _ _ hs => exact .extra _ _ hs
  | _, .tail _ _ _ hC, _, h => by
      cases h with
      | cons _ _ _ _ h1 h2 => exact .cons _ _ _ _ h1 (wt_arguments_context hty hC h2)
      | extra _ _ hs => exact .extra _ _ hs

mutual
/-- `Ctyping.wt_context` -/
theorem wt_context (hty : Csyntax.typeof a' = Csyntax.typeof a) {from_ : Csem.Kind} : ∀ {to C}, Csem.Context from_ to C →
    WtExprKind ce tenv to (C a) → WtExprKind ce tenv from_ a' → WtExprKind ce tenv to (C a')
  | _, _, .top _, _, base => base
  | _, _, .deref _ _ _ hC, h, base => by
      cases h with
      | deref _ _ h1 h2 =>
        exact .deref _ _ (wt_context hty hC h1 base) (by rw [typeof_context hty hC]; exact h2)
  | _, _, .field _ _ _ _ hC, h, base => by
      cases h with
      | field _ _ _ _ _ _ h1 h2 h3 h4 =>
        exact .field _ _ _ _ _ _ (wt_context hty hC h1 base)
          (by rw [typeof_context hty hC]; exact h2) h3 h4
  | _, _, .rvalof _ _ _ hC, h, base => by
      cases h with
      | valof _ h1 =>
        show WtRvalue _ _ _
        rw [← typeof_context hty hC]; exact .valof _ (wt_context hty hC h1 base)
  | _, _, .addrof _ _ _ hC, h, base => by
      cases h with
      | addrof _ h1 =>
        show WtRvalue _ _ _
        rw [← typeof_context hty hC]; exact .addrof _ (wt_context hty hC h1 base)
  | _, _, .unop _ _ _ _ hC, h, base => by
      cases h with
      | unop _ _ _ h1 h2 =>
        exact .unop _ _ _ (wt_context hty hC h1 base) (by rw [typeof_context hty hC]; exact h2)
  | _, _, .binop_left _ _ _ _ _ hC, h, base => by
      cases h with
      | binop _ _ _ _ h1 h2 h3 =>
        exact .binop _ _ _ _ (wt_context hty hC h1 base) h2 (by rw [typeof_context hty hC]; exact h3)
  | _, _, .binop_right _ _ _ _ _ hC, h, base => by
      cases h with
      | binop _ _ _ _ h1 h2 h3 =>
        exact .binop _ _ _ _ h1 (wt_context hty hC h2 base) (by rw [typeof_context hty hC]; exact h3)
  | _, _, .cast _ _ _ hC, h, base => by
      cases h with
      | cast _ _ h1 h2 =>
        exact .cast _ _ (wt_context hty hC h1 base) (by rw [typeof_context hty hC]; exact h2)
  | _, _, .seqand _ _ _ _ hC, h, base => by
      cases h with
      | seqand _ _ h1 h2 h3 h4 =>
        exact .seqand _ _ (wt_context hty hC h1 base) h2 (by rw [typeof_context hty hC]; exact h3) h4
  | _, _, .seqor _ _ _ _ hC, h, base => by
      cases h with
      | seqor _ _ h1 h2 h3 h4 =>
        exact .seqor _ _ (wt_context hty hC h1 base) h2 (by rw [typeof_context hty hC]; exact h3) h4
  | _, _, .condition _ _ _ _ _ hC, h, base => by
      cases h with
      | condition _ _ _ _ h1 h2 h3 h4 h5 h6 =>
        exact .condition _ _ _ _ (wt_context hty hC h1 base) h2 h3
          (by rw [typeof_context hty hC]; exact h4) h5 h6
  | _, _, .assign_left _ _ _ _ hC, h, base => by
      cases h with
      | assign _ _ h1 h2 h3 =>
        show WtRvalue _ _ _
        rw [← typeof_context hty hC]
        exact .assign _ _ (wt_context hty hC h1 base) h2 (by rw [typeof_context hty hC]; exact h3)
  | _, _, .assign_right _ _ _ _ hC, h, base => by
      cases h with
      | assign _ _ h1 h2 h3 =>
        exact .assign _ _ h1 (wt_context hty hC h2 base) (by rw [typeof_context hty hC]; exact h3)
  | _, _, .assignop_left _ _ _ _ _ _ hC, h, base => by
      cases h with
      | assignop _ _ _ _ h1 h2 h3 h4 =>
        show WtRvalue _ _ _
        rw [← typeof_context hty hC]
        exact .assignop _ _ _ _ (wt_context hty hC h1 base) h2
          (by rw [typeof_context hty hC]; exact h3) (by rw [typeof_context hty hC]; exact h4)
  | _, _, .assignop_right _ _ _ _ _ _ hC, h, base => by
      cases h with
      | assignop _ _ _ _ h1 h2 h3 h4 =>
        exact .assignop _ _ _ _ h1 (wt_context hty hC h2 base)
          (by rw [typeof_context hty hC]; exact h3) h4
  | _, _, .postincr _ _ _ _ hC, h, base => by
      cases h with
      | postincr _ _ _ h1 h2 h3 =>
        show WtRvalue _ _ _
        rw [← typeof_context hty hC]
        exact .postincr _ _ _ (wt_context hty hC h1 base)
          (by rw [typeof_context hty hC]; exact h2) (by rw [typeof_context hty hC]; exact h3)
  | _, _, .call_left _ _ _ _ hC, h, base => by
      cases h with
      | call _ _ _ _ _ h1 h2 h3 h4 =>
        exact .call _ _ _ _ _ (wt_context hty hC h1 base) h2
          (by rw [typeof_context hty hC]; exact h3) h4
  | _, _, .call_right _ _ _ _ hC, h, base => by
      cases h with
      | call _ _ _ _ _ h1 h2 h3 h4 =>
        exact .call _ _ _ _ _ h1 (wt_contextlist hty hC h2 base) h3 (wt_arguments_context hty hC h4)
  | _, _, .builtin _ _ _ _ _ hC, h, base => by
      cases h with
      | builtin _ _ _ _ h1 h2 h3 =>
        exact .builtin _ _ _ _ (wt_contextlist hty hC h1 base) (wt_arguments_context hty hC h2) h3
  | _, _, .comma _ _ _ _ hC, h, base => by
      cases h with
      | comma _ _ h1 h2 => exact .comma _ _ (wt_context hty hC h1 base) h2
  | _, _, .paren _ _ _ _ hC, h, base => by
      cases h with
      | paren _ _ _ h1 h2 h3 =>
        exact .paren _ _ _ (wt_context hty hC h1 base) (by rw [typeof_context hty hC]; exact h2) h3

/-- `Ctyping.wt_contextlist` -/
theorem wt_contextlist (hty : Csyntax.typeof a' = Csyntax.typeof a) {from_ : Csem.Kind} : ∀ {C}, Csem.ContextList from_ C →
    WtExprlist ce tenv (C a) → WtExprKind ce tenv from_ a' → WtExprlist ce tenv (C a')
  | _, .head _ _ _ hC, h, base => by
      cases h with | cons _ _ h1 h2 => exact .cons _ _ (wt_context hty hC h1 base) h2
  | _, .tail _ _ _ hC, h, base => by
      cases h with | cons _ _ h1 h2 => exact .cons _ _ h1 (wt_contextlist hty hC h2 base)
end

end WT_CONTEXT

end Ctyping
end CC
