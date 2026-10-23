/-
  Abstract domain for neededness analysis — port of `backend/NeedDomain.v`
  (soundness lemmas, part 2): conversions (`zero_ext_sound`,
  `sign_ext_sound`, `loword_sound`, `hiword_sound`, `makelong_sound`,
  `longofintu_sound`, `longofint_sound`), `store_argument_sound`,
  `store_argument_load_result`, `maskzero_sound`, `normalize_sound`,
  `select_sound`, and the redundancy tests (`andimm_redundant_sound` …
  `rolml_redundant_sound`).

  Difference from Rocq: `subl_sound` is not ported; it requires
  `Archi.ptr64 = false`, which does not hold on this (64-bit) target.
-/
import CCLib.backend.NeedDomainProof
import CCLib.common.MemdataTheory
import CCLib.common.MemdataInject
import CCLib.aarch64.OpLessdef

namespace CC
namespace NeedDomain

open Nval Bits

local macro "zomega" : tactic => `(tactic| ((try simp only [Z] at *) <;> omega))

/-! ### Bits of the 32/64-bit conversions -/

theorem getLsbD_ofwords (hi lo : I32) {i : Nat} (h : i < 64) :
    (Integers.Int64.ofwords hi lo).getLsbD i = if i < 32 then lo.getLsbD i else hi.getLsbD (i - 32) := by
  simp only [Integers.Int64.ofwords, BitVec.zeroExtend_eq_setWidth, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases hi32 : i < 32
  · simp [hi32, h]
  · simp only [hi32, if_false, h, decide_true, Bool.true_and, decide_false, Bool.not_false,
      BitVec.getLsbD_of_ge lo i (by omega), Bool.or_false]
    by_cases hh : hi.getLsbD (i - 32) <;> simp [hh] <;> omega

theorem getLsbD_loword (x : I64) (i : Nat) :
    (Integers.Int64.loword x).getLsbD i = (decide (i < 32) && x.getLsbD i) := by
  simp only [Integers.Int64.loword, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth]

theorem getLsbD_hiword (x : I64) {i : Nat} (h : i < 32) :
    (Integers.Int64.hiword x).getLsbD i = x.getLsbD (i + 32) := by
  simp only [Integers.Int64.hiword, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, h, decide_true, Bool.true_and]
  rw [Nat.add_comm]

theorem repr_unsigned_eq (i : I32) :
    Integers.Int64.repr (Integers.Int.unsigned i) = i.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp [Integers.Int64.repr, Integers.MI.repr, Integers.Int.unsigned, Integers.MI.unsigned]

theorem repr_signed_eq (i : I32) :
    Integers.Int64.repr (Integers.Int.signed i) = i.signExtend 64 := rfl

theorem int_repr_toNat {n : Z} (h0 : 0 ≤ n) (h1 : n < 4294967296) :
    (Integers.Int.repr n).toNat = n.toNat := by
  simp only [Integers.Int.repr, Integers.MI.repr, BitVec.toNat_ofInt]
  rw [Int.emod_eq_of_lt h0 (by simpa using h1)]

/-! ### Conversions -/

theorem zero_ext_sound {v w : Val} {x : Nval} (n : Z) (h : vagree v w (zeroExt n x)) :
    vagree (Val.zeroExt n.toNat v) (Val.zeroExt n.toNat w) x := by
  cases x <;> cases v <;> cases w <;> simp only [zeroExt, vagree, Val.zeroExt] at h ⊢ <;>
    first
    | vagree_triv
    | exact bagree_zero_ext h
    | exact Or.inl (congrArg Val.Vint (bagree_mone (bagree_zero_ext (m := BitVec.allOnes _) h)))

theorem sign_ext_sound {v w : Val} {x : Nval} {n : Z} (hn : 0 < n) (h : vagree v w (signExt n x)) :
    vagree (Val.signExt n.toNat v) (Val.signExt n.toNat w) x := by
  have hk : 0 < n.toNat := by zomega
  cases x <;> cases v <;> cases w <;> simp only [signExt, vagree, Val.signExt] at h ⊢ <;>
    try vagree_triv
  · -- `I m`
    rename_i m p q
    apply bagree_sign_ext hk
    · intro i hi hm
      apply h i hi
      show ((Integers.MI.zero_ext _ m) ||| _).getLsbD i = true
      rw [BitVec.getLsbD_or, hm, Bool.true_or]
    · intro hkw
      apply h (n.toNat - 1) (by zomega)
      show ((Integers.MI.zero_ext _ m) |||
        (1#32 <<< (Integers.Int.repr (n - 1)).toNat)).getLsbD _ = true
      have e : (Integers.Int.repr (n - 1)).toNat = n.toNat - 1 := by
        rw [int_repr_toNat (by zomega) (by zomega)]; zomega
      rw [e, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
      simp [show n.toNat - 1 < 32 by zomega]
  · -- `All`
    rename_i p q
    refine Or.inl (congrArg Val.Vint (bagree_mone (bagree_sign_ext hk ?_ ?_)))
    · intro i hi hm
      apply h i hi
      show (Integers.MI.zero_ext _ (BitVec.allOnes 32)).getLsbD i = true
      rw [getLsbD_zero_ext] at hm ⊢; simpa using hm
    · intro hkw
      apply h (n.toNat - 1) (by zomega)
      show (Integers.MI.zero_ext _ (BitVec.allOnes 32)).getLsbD _ = true
      rw [getLsbD_zero_ext, BitVec.getLsbD_allOnes]
      simp only [show n.toNat - 1 < n.toNat by zomega, show n.toNat - 1 < 32 by zomega, decide_true,
        Bool.and_self]

theorem loword_sound {v w : Val} {x : Nval} (h : vagree v w (loword x)) :
    vagree (Val.loword v) (Val.loword w) x := by
  have B : ∀ (p q : I64) (m : I32), bagree p q (Integers.Int64.ofwords Integers.Int.zero m) →
      bagree (Integers.Int64.loword p) (Integers.Int64.loword q) m := by
    intro p q m h i hi hm
    rw [getLsbD_loword, getLsbD_loword]
    rw [h i (by omega) (by rw [getLsbD_ofwords _ _ (by omega), if_pos hi]; exact hm)]
  cases x <;> cases v <;> cases w <;> simp only [loword, vagree, Val.loword] at h ⊢ <;>
    first
    | vagree_triv
    | exact B _ _ _ h
    | exact Or.inl (congrArg Val.Vint (bagree_mone (B _ _ _ h)))

theorem hiword_sound {v w : Val} {x : Nval} (h : vagree v w (hiword x)) :
    vagree (Val.hiword v) (Val.hiword w) x := by
  have B : ∀ (p q : I64) (m : I32), bagree p q (Integers.Int64.ofwords m Integers.Int.zero) →
      bagree (Integers.Int64.hiword p) (Integers.Int64.hiword q) m := by
    intro p q m h i hi hm
    rw [getLsbD_hiword _ hi, getLsbD_hiword _ hi]
    exact h (i + 32) (by omega) (by
      rw [getLsbD_ofwords _ _ (by omega), if_neg (by omega), Nat.add_sub_cancel]; exact hm)
  cases x <;> cases v <;> cases w <;> simp only [hiword, vagree, Val.hiword] at h ⊢ <;>
    first
    | vagree_triv
    | exact B _ _ _ h
    | exact Or.inl (congrArg Val.Vint (bagree_mone (B _ _ _ h)))

theorem makelong_sound {v1 w1 v2 w2 : Val} {x : Nval} (h1 : vagree v1 w1 (makelongHi x))
    (h2 : vagree v2 w2 (makelongLo x)) :
    vagree (Val.longofwords v1 v2) (Val.longofwords w1 w2) x := by
  have B : ∀ (a1 b1 a2 b2 : I32) (m : I64), bagree a1 b1 (Integers.Int64.hiword m) →
      bagree a2 b2 (Integers.Int64.loword m) →
      bagree (Integers.Int64.ofwords a1 a2) (Integers.Int64.ofwords b1 b2) m := by
    intro a1 b1 a2 b2 m h1 h2 i hi hm
    rw [getLsbD_ofwords _ _ hi, getLsbD_ofwords _ _ hi]
    by_cases h32 : i < 32
    · rw [if_pos h32, if_pos h32]
      exact h2 i h32 (by rw [getLsbD_loword]; simp [h32, hm])
    · rw [if_neg h32, if_neg h32]
      exact h1 (i - 32) (by omega) (by
        rw [getLsbD_hiword _ (by omega), show i - 32 + 32 = i by omega]; exact hm)
  cases x with
  | Nothing => trivial
  | I m =>
      cases v1 <;> cases v2 <;> cases w1 <;> cases w2 <;> simp only [vagree, Val.longofwords] <;>
        vagree_triv
  | L m =>
      cases v1 <;> cases w1 <;> simp only [makelongHi, vagree] at h1 <;>
        cases v2 <;> cases w2 <;> simp only [makelongLo, vagree, Val.longofwords] at h2 ⊢ <;>
        first | vagree_triv | exact B _ _ _ _ _ h1 h2
  | All =>
      simp only [makelongHi, makelongLo, vagree] at h1 h2 ⊢
      rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;>
        first | exact Or.inl rfl | (right; cases v1 <;> rfl) | (right; rfl)

theorem longofintu_sound {v w : Val} {x : Nval} (h : vagree v w (longofintu x)) :
    vagree (Val.longofintu v) (Val.longofintu w) x := by
  have B : ∀ (i j : I32) (m : I64), bagree i j (Integers.Int64.loword m) →
      bagree (Integers.Int64.repr (Integers.Int.unsigned i))
        (Integers.Int64.repr (Integers.Int.unsigned j)) m := by
    intro i j m h k hk hm
    rw [repr_unsigned_eq, repr_unsigned_eq, BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth]
    by_cases h32 : k < 32
    · rw [h k h32 (by rw [getLsbD_loword]; simp [h32, hm])]
    · rw [BitVec.getLsbD_of_ge i k (by omega), BitVec.getLsbD_of_ge j k (by omega)]
  cases x <;> cases v <;> cases w <;> simp only [longofintu, vagree, Val.longofintu] at h ⊢ <;>
    first
    | vagree_triv
    | exact B _ _ _ h
    | simp_all

theorem longofint_sound {v w : Val} {x : Nval} (h : vagree v w (longofint x)) :
    vagree (Val.longofint v) (Val.longofint w) x := by
  have B : ∀ (i j : I32) (m : I64),
      bagree i j (Integers.Int.or (Integers.Int64.loword m)
        (Integers.Int.shl Integers.Int.one (Integers.Int.repr 31))) →
      bagree (Integers.Int64.repr (Integers.Int.signed i))
        (Integers.Int64.repr (Integers.Int.signed j)) m := by
    intro i j m h k hk hm
    rw [repr_signed_eq, repr_signed_eq, BitVec.getLsbD_signExtend, BitVec.getLsbD_signExtend]
    by_cases h32 : k < 32
    · rw [if_pos h32, if_pos h32]
      rw [h k h32 (by
        show ((Integers.Int64.loword m) ||| _).getLsbD k = true
        rw [BitVec.getLsbD_or, getLsbD_loword]; simp [h32, hm])]
    · rw [if_neg h32, if_neg h32, BitVec.msb_eq_getLsbD_last, BitVec.msb_eq_getLsbD_last]
      rw [h 31 (by omega) (by
        show ((Integers.Int64.loword m) ||| (1#32 <<< (Integers.Int.repr 31).toNat)).getLsbD 31 = true
        rw [int_repr_toNat (by decide) (by decide), BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
        simp)]
  cases x <;> cases v <;> cases w <;> simp only [longofint, vagree, Val.longofint] at h ⊢ <;>
    first
    | vagree_triv
    | exact B _ _ _ h
    | simp_all

/-! ### Stores, comparisons, selections -/

theorem bagree_unsigned_mod {p q : I32} {k : Nat} (h : bagree p q (lowMask 32 k)) :
    Integers.Int.unsigned p % (2 ^ k : Nat) = Integers.Int.unsigned q % (2 ^ k : Nat) := by
  rw [bagree_lowMask_iff] at h
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth] at this
  simp only [Integers.Int.unsigned, Integers.MI.unsigned]
  rw [← Int.natCast_emod, ← Int.natCast_emod, this]

theorem repr255_eq : Integers.Int.repr 255 = lowMask 32 8 := by decide
theorem repr65535_eq : Integers.Int.repr 65535 = lowMask 32 16 := by decide

theorem memvalInjectList_refl (l : List MemVal) : MemvalInjectList Val.inject_id l l := by
  induction l with
  | nil => exact .nil
  | cons a l ih => exact .cons (memvalLessdef_refl a) ih

/-- `store_argument_sound` -/
theorem store_argument_sound (chunk : Chunk) {v w : Val} (h : vagree v w (storeArgument chunk)) :
    MemvalInjectList Val.inject_id (encodeVal chunk v) (encodeVal chunk w) := by
  have UNDEF : ∀ v, (∀ p, v ≠ .Vint p) →
      (chunk = .Mbool ∨ chunk = .Mint8signed ∨ chunk = .Mint8unsigned ∨
        chunk = .Mint16signed ∨ chunk = .Mint16unsigned) →
      MemvalInjectList Val.inject_id (encodeVal chunk v) (encodeVal chunk w) := by
    intro v hv hc
    have e : encodeVal chunk v = List.replicate (sizeChunkNat chunk) .Undef := by
      rcases hc with rfl | rfl | rfl | rfl | rfl <;> cases v <;>
        first | rfl | exact absurd rfl (hv _)
    rw [e]; exact replicate_Undef_inject_encodeVal chunk w
  cases chunk <;> simp only [storeArgument] at h <;>
    first
    | exact encodeVal_inject _ (Val.lessdef_inject_id.mp (lessdef_vagree h))
    | skip
  all_goals
    cases v with
    | Vint p =>
        cases w with
        | Vint q =>
            simp only [vagree] at h
            first
            | (rw [repr255_eq] at h
               simp only [encodeVal]
               rw [encodeInt_8_mod _ _ (bagree_unsigned_mod (k := 8) h)]
               exact memvalInjectList_refl _)
            | (rw [repr65535_eq] at h
               simp only [encodeVal]
               rw [encodeInt_16_mod _ _ (bagree_unsigned_mod (k := 16) h)]
               exact memvalInjectList_refl _)
        | _ => simp only [vagree] at h
    | _ => exact UNDEF _ (fun _ h => Val.noConfusion h) (by simp)

theorem lowMask_ext_eq {p q : I32} {k : Nat} (hk0 : 0 < k) (hk : k < 32)
    (h : bagree p q (lowMask 32 k)) :
    Integers.Int.zero_ext k p = Integers.Int.zero_ext k q ∧
      Integers.Int.sign_ext k p = Integers.Int.sign_ext k q := by
  have hb : ∀ i, i < k → p.getLsbD i = q.getLsbD i := fun i hi =>
    h i (by omega) (by rw [getLsbD_lowMask]; simp [hi, show i < 32 by omega])
  constructor
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    show (Integers.MI.zero_ext k p).getLsbD i = (Integers.MI.zero_ext k q).getLsbD i
    rw [getLsbD_zero_ext, getLsbD_zero_ext]
    by_cases hik : i < k
    · simp [hik, hb i hik]
    · simp [hik]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    show (Integers.MI.sign_ext k p).getLsbD i = (Integers.MI.sign_ext k q).getLsbD i
    rw [getLsbD_sign_ext hk0 hk p hi, getLsbD_sign_ext hk0 hk q hi]
    split
    · exact hb i ‹_›
    · exact hb (k - 1) (by omega)

/-- `store_argument_load_result` -/
theorem store_argument_load_result (chunk : Chunk) {v w : Val}
    (h : vagree v w (storeArgument chunk)) :
    Val.Lessdef (Val.loadResult chunk v) (Val.loadResult chunk w) := by
  cases chunk <;> simp only [storeArgument] at h <;>
    first
    | exact Val.load_result_lessdef _ (lessdef_vagree h)
    | skip
  all_goals
    cases v with
    | Vint p =>
        cases w with
        | Vint q =>
            simp only [vagree] at h
            first
            | (rw [repr255_eq] at h
               obtain ⟨ez, es⟩ := lowMask_ext_eq (by decide) (by decide) h
               simp only [Val.loadResult, ez, es]; exact .refl _)
            | (rw [repr65535_eq] at h
               obtain ⟨ez, es⟩ := lowMask_ext_eq (by decide) (by decide) h
               simp only [Val.loadResult, ez, es]; exact .refl _)
        | _ => simp only [vagree] at h
    | _ => exact .undef _

/-- `maskzero_sound` -/
theorem maskzero_sound {v w : Val} {n : I32} {b : Bool} (h : vagree v w (maskzero n))
    (hb : Val.maskzero_bool v n = some b) : Val.maskzero_bool w n = some b := by
  cases v <;> cases w <;> simp only [maskzero, vagree, Val.maskzero_bool] at h hb ⊢ <;>
    first
    | exact absurd h id
    | (rw [← hb, (iagree_and_eq _ _ _).1 h])
    | (cases hb)

/-- `normalize_sound` -/
theorem normalize_sound {v w : Val} {x : Nval} (ty : ATyp) (h : vagree v w x) :
    vagree (Val.normalize v ty) (Val.normalize w ty) x := by
  cases x
  · trivial
  all_goals first
    | exact vagree_lessdef _ (Val.normalize_lessdef ty (lessdef_vagree h))
    | (cases v <;> cases w <;> cases ty <;>
        simp only [vagree, Val.normalize, Archi.ptr64, if_true] at h ⊢ <;>
        first | vagree_triv | exact h)

/-- `select_sound` -/
theorem select_sound {ob : Option Bool} {v1 v2 w1 w2 : Val} {x : Nval} (ty : ATyp)
    (h1 : vagree v1 w1 x) (h2 : vagree v2 w2 x) :
    vagree (Val.select ob v1 v2 ty) (Val.select ob w1 w2 ty) x := by
  cases ob with
  | none => exact vagree_same _ _
  | some b => cases b <;> exact normalize_sound ty ‹_›

/-! ### The default abstraction -/

theorem vagreeList_default_lessdef {args1 args2 : List Val} {nv : Nval} (hnv : nv ≠ .Nothing)
    (hl : VagreeList args1 args2 [] ∨ VagreeList args1 args2 [default nv] ∨
      VagreeList args1 args2 [default nv, default nv] ∨
      VagreeList args1 args2 [default nv, default nv, default nv]) :
    Val.LessdefList args1 args2 := by
  have hd : default nv = .All := by cases nv <;> first | rfl | exact absurd rfl hnv
  rw [hd] at hl
  rcases hl with hl | hl | hl | hl
  · exact lessdef_vagree_list hl
  · cases hl with
    | nil => exact .nil
    | cons h1 h2 => exact .cons (lessdef_vagree h1) (lessdef_vagree_list h2)
  · cases hl with
    | nil => exact .nil
    | cons h1 h2 =>
        cases h2 with
        | nil => exact .cons (lessdef_vagree h1) .nil
        | cons h3 h4 => exact .cons (lessdef_vagree h1) (.cons (lessdef_vagree h3) (lessdef_vagree_list h4))
  · cases hl with
    | nil => exact .nil
    | cons h1 h2 =>
        cases h2 with
        | nil => exact .cons (lessdef_vagree h1) .nil
        | cons h3 h4 =>
            cases h4 with
            | nil => exact .cons (lessdef_vagree h1) (.cons (lessdef_vagree h3) .nil)
            | cons h5 h6 =>
                exact .cons (lessdef_vagree h1) (.cons (lessdef_vagree h3)
                  (.cons (lessdef_vagree h5) (lessdef_vagree_list h6)))

section DEFAULT
variable {F V : Type} (ge : Genv F V) (sp : Block) {m1 m2 : Mem}
  (PERM : ∀ b ofs k p, Mem.perm m1 b ofs k p = true → Mem.perm m2 b ofs k p = true)
include PERM

/-- `default_needs_of_condition_sound` -/
theorem default_needs_of_condition_sound {cond : Op.Condition} {args1 args2 : List Val} {b : Bool}
    (h : Op.evalCondition cond args1 m1 = some b) (hl : VagreeList args1 args2 []) :
    Op.evalCondition cond args2 m2 = some b :=
  Op.evalCondition_lessdef_vp (lessdef_vagree_list hl) (fun b ofs hv => PERM b ofs _ _ hv) h

/-- `default_needs_of_operation_sound` -/
theorem default_needs_of_operation_sound {op : Op.Operation} {args1 args2 : List Val} {v1 : Val}
    {nv : Nval}
    (h : Op.evalOperation ge (.Vptr sp Integers.Ptrofs.zero) op args1 m1 = some v1)
    (hl : VagreeList args1 args2 [] ∨ VagreeList args1 args2 [default nv] ∨
      VagreeList args1 args2 [default nv, default nv] ∨
      VagreeList args1 args2 [default nv, default nv, default nv])
    (hnv : nv ≠ .Nothing) :
    ∃ v2, Op.evalOperation ge (.Vptr sp Integers.Ptrofs.zero) op args2 m2 = some v2 ∧
      vagree v1 v2 nv := by
  obtain ⟨v2, h2, hl2⟩ := Op.evalOperation_lessdef_vp ge _ op (vagreeList_default_lessdef hnv hl)
    (fun b ofs hv => PERM b ofs _ _ hv) h
  exact ⟨v2, h2, vagree_lessdef _ hl2⟩

end DEFAULT

/-! ### Operations that are redundant and can be turned into a move -/

theorem bagree_and_redundant {w : Nat} {p q m n : BitVec w} (hr : m &&& ~~~n = 0)
    (h : bagree p q (m &&& n)) : bagree (p &&& n) q m := by
  intro i hi hm
  have hn : n.getLsbD i = true := by
    have := congrArg (fun z => z.getLsbD i) hr
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hm, hi] at this
    simpa using this
  rw [BitVec.getLsbD_and, hn, Bool.and_true]
  exact h i hi (by rw [BitVec.getLsbD_and, hm, hn]; rfl)

theorem bagree_or_redundant {w : Nat} {p q m n : BitVec w} (hr : m &&& n = 0)
    (h : bagree p q (m &&& ~~~n)) : bagree (p ||| n) q m := by
  intro i hi hm
  have hn : n.getLsbD i = false := by
    have := congrArg (fun z => z.getLsbD i) hr
    simp only [BitVec.getLsbD_and, hm] at this
    simpa using this
  rw [BitVec.getLsbD_or, hn, Bool.or_false]
  exact h i hi (by rw [BitVec.getLsbD_and, BitVec.getLsbD_not, hm, hn]; simp [hi])

/-- `andimm_redundant_sound` -/
theorem andimm_redundant_sound {v w : Val} {x : Nval} {n : I32} (hr : andimmRedundant x n = true)
    (h : vagree v w (andimm x n)) : vagree (Val.and v (.Vint n)) w x := by
  cases x <;> simp only [andimmRedundant, decide_eq_true_eq] at hr <;> try trivial
  cases v <;> cases w <;> simp only [andimm, vagree, Val.and] at h ⊢ <;>
    first | vagree_triv | exact bagree_and_redundant hr h

/-- `orimm_redundant_sound` -/
theorem orimm_redundant_sound {v w : Val} {x : Nval} {n : I32} (hr : orimmRedundant x n = true)
    (h : vagree v w (orimm x n)) : vagree (Val.or v (.Vint n)) w x := by
  cases x <;> simp only [orimmRedundant, decide_eq_true_eq] at hr <;> try trivial
  cases v <;> cases w <;> simp only [orimm, vagree, Val.or] at h ⊢ <;>
    first | vagree_triv | exact bagree_or_redundant hr h

/-- `andlimm_redundant_sound` -/
theorem andlimm_redundant_sound {v w : Val} {x : Nval} {n : I64} (hr : andlimmRedundant x n = true)
    (h : vagree v w (andlimm x n)) : vagree (Val.andl v (.Vlong n)) w x := by
  cases x <;> simp only [andlimmRedundant, decide_eq_true_eq] at hr <;> try trivial
  cases v <;> cases w <;> simp only [andlimm, vagree, Val.andl] at h ⊢ <;>
    first | vagree_triv | exact bagree_and_redundant hr h

/-- `orlimm_redundant_sound` -/
theorem orlimm_redundant_sound {v w : Val} {x : Nval} {n : I64} (hr : orlimmRedundant x n = true)
    (h : vagree v w (orlimm x n)) : vagree (Val.orl v (.Vlong n)) w x := by
  cases x <;> simp only [orlimmRedundant, decide_eq_true_eq] at hr <;> try trivial
  cases v <;> cases w <;> simp only [orlimm, vagree, Val.orl] at h ⊢ <;>
    first | vagree_triv | exact bagree_or_redundant hr h

/-- `zero_ext_redundant_sound` -/
theorem zero_ext_redundant_sound {v w : Val} {x : Nval} {n : Z} (hr : zeroExtRedundant n x = true)
    (h : vagree v w (zeroExt n x)) : vagree (Val.zeroExt n.toNat v) w x := by
  cases x <;> simp only [zeroExtRedundant, decide_eq_true_eq] at hr <;> try trivial
  rename_i m
  cases v <;> cases w <;> simp only [zeroExt, vagree, Val.zeroExt] at h ⊢ <;> try vagree_triv
  rename_i p q
  intro i hi hm
  have hm' : (Integers.MI.zero_ext n.toNat m).getLsbD i = true := by
    show (Integers.Int.zero_ext n.toNat m).getLsbD i = true; rw [hr]; exact hm
  have hik : i < n.toNat := by rw [getLsbD_zero_ext] at hm'; simp at hm'; have := hm'.1; zomega
  show (Integers.MI.zero_ext n.toNat p).getLsbD i = q.getLsbD i
  rw [getLsbD_zero_ext]; simp only [hik, decide_true, Bool.true_and]
  exact h i hi hm'

/-- `sign_ext_redundant_sound` -/
theorem sign_ext_redundant_sound {v w : Val} {x : Nval} {n : Z} (hn : 0 < n)
    (hr : signExtRedundant n x = true)
    (h : vagree v w (signExt n x)) : vagree (Val.signExt n.toNat v) w x := by
  cases x <;> simp only [signExtRedundant, decide_eq_true_eq] at hr <;> try trivial
  rename_i m
  cases v <;> cases w <;> simp only [signExt, vagree, Val.signExt] at h ⊢ <;> try vagree_triv
  rename_i p q
  intro i hi hm
  have hm' : (Integers.MI.zero_ext n.toNat m).getLsbD i = true := by
    show (Integers.Int.zero_ext n.toNat m).getLsbD i = true; rw [hr]; exact hm
  have hik : i < n.toNat := by rw [getLsbD_zero_ext] at hm'; simp at hm'; have := hm'.1; zomega
  have hq : p.getLsbD i = q.getLsbD i := h i hi (by
    show ((Integers.MI.zero_ext _ m) ||| _).getLsbD i = true
    rw [BitVec.getLsbD_or, hm', Bool.true_or])
  show (Integers.MI.sign_ext n.toNat p).getLsbD i = q.getLsbD i
  rw [← hq]
  by_cases hkw : n.toNat < 32
  · rw [getLsbD_sign_ext (by zomega) hkw p hi, if_pos hik]
  · unfold Integers.MI.sign_ext; rw [if_neg (by zomega), if_pos (by zomega)]

end NeedDomain
end CC
