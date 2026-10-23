/-
  Soundness of the translation of initializers — port of the last part of
  `cfrontend/Initializersproof.v` (from "Soundness of the translation of
  initializers" to the end), ending in `transl_init_sound`.

  * `ExecAssign`: the effect of the assignment to a (possibly bitfield)
    l-value that initializes a scalar;
  * `ExecInit`, `ExecInitArray`, `ExecInitStruct`: a semantics for general
    initializers, in terms of the CompCert C reduction semantics for the
    scalar initializing expressions;
  * `translInitSingle_sound`, `translInitRec_sound`: soundness of
    `transl_init_single`, `transl_init_rec`, `transl_init_array`,
    `transl_init_struct` and `transl_init_bitfield` with respect to the
    interpretation `MatchState` of initialization states;
  * `translInit_sound`: if an initializer `i` for a variable of type `ty`
    executes from memory `m` to memory `m1` in block `b`, and `transl_init`
    turns it into the initialization data `data`, then storing `data` in `m`
    succeeds and produces the same bytes as `m1` in block `b`.
-/
import CCLib.cfrontend.InitializersproofSimple
import CCLib.cfrontend.InitializersproofMatch
import CCLib.cfrontend.CtypesTheory

namespace CC
namespace Initializersproof

open Initializers Mem Csyntax

local macro "zomega" : tactic => `(tactic| ((try dsimp only [CC.Z] at *) <;> omega))

private theorem res_bind_eq_OK {A B : Type} {x : Res A} {f : A → Res B} {b : B} :
    (bind x f = Res.OK b) ↔ ∃ a, x = .OK a ∧ f a = .OK b := by
  cases x <;> simp [bind, Res.bind]

private theorem assertion_eq_OK {A : Type} {c : Bool} {k : Res A} {a : A}
    (h : assertion c k = .OK a) : c = true ∧ k = .OK a := by
  unfold assertion at h
  split at h
  · exact ⟨by assumption, h⟩
  · cases h

/-! ## Total size properties -/

/-- `Initializersproof.total_size_transl_init_bitfield` -/
theorem totalSize_translInitBitfield {ce : CompositeEnv} {s : Initializers.State} {ty : Ty}
    {sz : IntSize} {p w : Z} {i : Initializer} {pos : Z} {s' : Initializers.State}
    (h : translInitBitfield ce s ty sz p w i pos = .OK s') : s'.total_size = s.total_size := by
  cases i with
  | Init_single a =>
    unfold translInitBitfield at h
    obtain ⟨v, _, h⟩ := res_bind_eq_OK.mp h
    cases v <;> simp only at h <;> try cases h
    obtain ⟨c, _, h⟩ := res_bind_eq_OK.mp h
    exact totalSize_storeData h
  | _ => simp only [translInitBitfield] at h; cases h

mutual
/-- `Initializersproof.total_size_transl_init_rec` -/
theorem totalSize_translInitRec (ce : CompositeEnv) : ∀ (s : Initializers.State) (ty : Ty)
    (i : Initializer) (pos : Z) (s' : Initializers.State),
    translInitRec ce s ty i pos = .OK s' → s'.total_size = s.total_size
  | s, ty, .Init_single a, pos, s', h => by
    simp only [translInitRec] at h
    obtain ⟨d, _, h⟩ := res_bind_eq_OK.mp h
    exact totalSize_storeData h
  | s, ty, .Init_array il, pos, s', h => by
    cases ty <;> simp only [translInitRec] at h <;> try cases h
    exact totalSize_translInitArray ce s _ il pos s' (assertion_eq_OK h).2
  | s, ty, .Init_struct il, pos, s', h => by
    cases ty <;> simp only [translInitRec] at h <;> try cases h
    obtain ⟨co, _, h⟩ := res_bind_eq_OK.mp h
    split at h
    · exact totalSize_translInitStruct ce s _ il pos 0 s' h
    · cases h
  | s, ty, .Init_union f i1, pos, s', h => by
    cases ty <;> simp only [translInitRec] at h <;> try cases h
    obtain ⟨co, _, h⟩ := res_bind_eq_OK.mp h
    split at h
    · cases h
    · obtain ⟨ty1, _, h⟩ := res_bind_eq_OK.mp h
      obtain ⟨⟨delta, layout⟩, _, h⟩ := res_bind_eq_OK.mp h
      split at h
      · exact totalSize_translInitRec ce s ty1 i1 _ s' h
      · exact totalSize_translInitBitfield h

/-- `Initializersproof.total_size_transl_init_array` -/
theorem totalSize_translInitArray (ce : CompositeEnv) : ∀ (s : Initializers.State) (tyelt : Ty)
    (il : InitializerList) (pos : Z) (s' : Initializers.State),
    translInitArray ce s tyelt il pos = .OK s' → s'.total_size = s.total_size
  | s, tyelt, .Init_nil, pos, s', h => by
    simp only [translInitArray] at h; cases h; rfl
  | s, tyelt, .Init_cons i1 il, pos, s', h => by
    simp only [translInitArray] at h
    obtain ⟨s1, h1, h⟩ := res_bind_eq_OK.mp h
    rw [totalSize_translInitArray ce s1 tyelt il _ s' h, totalSize_translInitRec ce s tyelt i1 pos s1 h1]

/-- `Initializersproof.total_size_transl_init_struct` -/
theorem totalSize_translInitStruct (ce : CompositeEnv) : ∀ (s : Initializers.State) (ms : List Member)
    (il : InitializerList) (base pos : Z) (s' : Initializers.State),
    translInitStruct ce s ms il base pos = .OK s' → s'.total_size = s.total_size
  | s, ms, .Init_nil, base, pos, s', h => by
    simp only [translInitStruct] at h; cases h; rfl
  | s, ms, .Init_cons i1 il, base, pos, s', h => by
    simp only [translInitStruct] at h
    split at h
    · cases h
    · obtain ⟨⟨delta, layout⟩, _, h⟩ := res_bind_eq_OK.mp h
      cases layout with
      | Full =>
        obtain ⟨s1, h1, h⟩ := res_bind_eq_OK.mp h
        rw [totalSize_translInitStruct ce s1 _ il base _ s' h]
        exact totalSize_translInitRec ce s _ i1 _ s1 h1
      | Bits sz sg p w =>
        obtain ⟨s1, h1, h⟩ := res_bind_eq_OK.mp h
        rw [totalSize_translInitStruct ce s1 _ il base _ s' h]
        exact totalSize_translInitBitfield h1
end

/-! ## Soundness for single initializers -/

/-- `Initializersproof.exec_assign`: the assignment of value `v` to the
    l-value of type `ty` at offset `ofs` of block `b`, which is a bitfield if
    `bf` is `Bits …`. -/
inductive ExecAssign : Mem → Block → Z → Bitfield → Ty → Val → Mem → Prop where
  | full (m b ofs ty v m' chunk) :
      accessMode ty = .By_value chunk →
      Mem.store chunk m b ofs v = some m' →
      ExecAssign m b ofs .Full ty v m'
  | bits (m b ofs sz sg sg1 attr pos width ty n m' c) :
      typeIsVolatile ty = false →
      0 ≤ pos → 0 < width → pos + width ≤ bitsizeIntsize sz →
      sg1 = (if width < bitsizeIntsize sz then Signedness.Signed else sg) →
      Mem.load (Cop.chunkForCarrier sz) m b ofs = some (.Vint c) →
      Mem.store (Cop.chunkForCarrier sz) m b ofs
        (.Vint (Integers.Int.bitfield_insert (Cop.firstBit sz pos width).toNat width.toNat c n))
        = some m' →
      ExecAssign m b ofs (.Bits sz sg pos width) (.Tint sz sg1 attr) (.Vint n) m'

section SOUNDNESS

variable {ge : Csem.CGenv}

/-- `Initializersproof.transl_init_single_sound` -/
theorem translInitSingle_sound {ty : Ty} {a : Csyntax.Expr} {data : InitData}
    {f : Csyntax.Function} {m : Mem} {v1 : Val} {ty1 : Ty} {m' : Mem} {v : Val} {b : Block}
    {ofs : Z} {m'' : Mem}
    (htr : translInitSingle ge.genv_cenv ty a = .OK data)
    (hsteps : Smallstep.Star (Csem.Step ge) (.ExprState f a .Kstop emptyEnv m) E0
      (.ExprState f (.Eval v1 ty1) .Kstop emptyEnv m'))
    (hcast : Cop.semCast v1 ty1 ty m' = some v)
    (hasg : ExecAssign m' b ofs .Full ty v m'') :
    Genv.storeInitData ge.genv_genv m b ofs data = some m'' ∧ NotSpace data := by
  unfold translInitSingle at htr
  obtain ⟨vc, EQ, htr⟩ := res_bind_eq_OK.mp htr
  unfold constvalCast at EQ
  obtain ⟨v0, E0, E1⟩ := res_bind_eq_OK.mp EQ
  obtain ⟨A, B, C⟩ := constval_steps hsteps E0
  subst A B
  have D := sem_cast_match hcast E1 C
  cases hasg with
  | full =>
  rename_i chunk hacc hst
  cases D with
  | int n =>
    cases ty with
    | Tint sz sg at_ =>
      cases sz <;> simp only at htr <;> cases htr <;> refine ⟨?_, trivial⟩ <;> cases sg <;>
        simp only [accessMode] at hacc <;> cases hacc <;> simp only [Genv.storeInitData] <;>
        first
          | exact hst
          | (rw [← store_signed_unsigned_8]; exact hst)
          | (rw [← store_signed_unsigned_16]; exact hst)
          | (rw [← store_bool_unsigned_8]; exact hst)
    | Tpointer t at_ => simp [assertion] at htr
    | _ => simp only at htr; cases htr
  | long n =>
    cases ty with
    | Tlong sg at_ =>
      simp only at htr; cases htr
      simp only [accessMode] at hacc; cases hacc
      exact ⟨hst, trivial⟩
    | Tpointer t at_ =>
      simp [assertion] at htr; subst htr
      simp only [accessMode] at hacc; cases hacc
      exact ⟨hst, trivial⟩
    | Tint sz sg at_ => cases sz <;> simp only at htr <;> cases htr
    | Tfloat fsz at_ => cases fsz <;> simp only at htr <;> cases htr
    | _ => simp only at htr; cases htr
  | float x =>
    cases ty with
    | Tfloat fsz at_ =>
      cases fsz <;> simp only at htr <;> cases htr
      simp only [accessMode] at hacc; cases hacc
      exact ⟨hst, trivial⟩
    | Tint sz sg at_ => cases sz <;> simp only at htr <;> cases htr
    | _ => simp only at htr; cases htr
  | single x =>
    cases ty with
    | Tfloat fsz at_ =>
      cases fsz <;> simp only at htr <;> cases htr
      simp only [accessMode] at hacc; cases hacc
      exact ⟨hst, trivial⟩
    | Tint sz sg at_ => cases sz <;> simp only at htr <;> cases htr
    | _ => simp only at htr; cases htr
  | @ptr b1 ofs1 b2 ofs2 delta hf hofs =>
    unfold inj at hf
    split at hf
    · next b' hb =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      subst hofs
      have E : Integers.Ptrofs.add ofs1 (Integers.Ptrofs.repr 0) = ofs1 :=
        Integers.Ptrofs.add_zero ofs1
      rw [E] at hst
      have key : ∀ (c : Chunk), c = Mptr → Genv.storeInitData ge.genv_genv m' b ofs
          (.Init_addrof b1 ofs1) = Mem.store c m' b ofs (.Vptr b' ofs1) := by
        intro c hc; subst hc; simp only [Genv.storeInitData, hb]
      cases ty with
      | Tint sz sg at_ => cases sz <;> simp [assertion] at htr
      | Tlong sg at_ =>
        simp [assertion] at htr; subst htr
        simp only [accessMode] at hacc; cases hacc
        exact ⟨(key _ rfl).trans hst, trivial⟩
      | Tpointer t at_ =>
        simp only at htr; cases htr
        simp only [accessMode] at hacc; cases hacc
        exact ⟨(key _ rfl).trans hst, trivial⟩
      | Tfloat fsz at_ => cases fsz <;> simp only at htr <;> cases htr
      | _ => simp only at htr; cases htr
    · cases hf
  | undef v => cases ty <;> simp only at htr <;> cases htr

/-! ## A semantics for general initializers -/

/-- `Initializersproof.dummy_function` -/
def dummyFunction : Csyntax.Function :=
  { fn_return := .Tvoid, fn_callconv := cc_default, fn_params := [], fn_vars := [],
    fn_body := .Sskip }

/-- `Initializersproof.initialized_fields_of_struct`: the offsets, layouts and
    types of the members of a struct that are initialized. -/
def initializedFieldsOfStruct (ce : CompositeEnv) : List Member → Z → Res (List (Z × Bitfield × Ty))
  | [], _ => .OK []
  | m :: ms', pos =>
      let pos' := nextField ce pos m
      if memberNotInitialized m then initializedFieldsOfStruct ce ms' pos'
      else do
        let (ofs, bf) ← layoutField ce pos m
        let l ← initializedFieldsOfStruct ce ms' pos'
        .OK ((ofs, bf, m.type) :: l)

variable (ge) in
mutual
/-- `Initializersproof.exec_init`: executing the initializer `i` for an
    object of type `ty` at offset `ofs` (and layout `bf`) of block `b` turns
    memory `m` into `m'`. -/
inductive ExecInit : Mem → Block → Z → Bitfield → Ty → Initializer → Mem → Prop where
  | single (m b ofs bf ty a v1 ty1 m' v m'') :
      Smallstep.Star (Csem.Step ge) (.ExprState dummyFunction a .Kstop emptyEnv m) E0
        (.ExprState dummyFunction (.Eval v1 ty1) .Kstop emptyEnv m') →
      Cop.semCast v1 ty1 ty m' = some v →
      ExecAssign m' b ofs bf ty v m'' →
      ExecInit m b ofs bf ty (.Init_single a) m''
  | array (m b ofs ty sz a il m') :
      ExecInitArray m b ofs ty sz il m' →
      ExecInit m b ofs .Full (.Tarray ty sz a) (.Init_array il) m'
  | struct (m b ofs id a il co flds m') :
      ge.genv_cenv.get id = some co → co.co_su = .Struct →
      initializedFieldsOfStruct ge.genv_cenv co.co_members 0 = .OK flds →
      ExecInitStruct m b ofs flds il m' →
      ExecInit m b ofs .Full (.Tstruct id a) (.Init_struct il) m'
  | union (m b ofs id a f i co ty pos bf m') :
      ge.genv_cenv.get id = some co → co.co_su = .Union →
      fieldType f co.co_members = .OK ty →
      unionFieldOffset ge.genv_cenv f co.co_members = .OK (pos, bf) →
      ExecInit m b (ofs + pos) bf ty i m' →
      ExecInit m b ofs .Full (.Tunion id a) (.Init_union f i) m'

/-- `Initializersproof.exec_init_array` -/
inductive ExecInitArray : Mem → Block → Z → Ty → Z → InitializerList → Mem → Prop where
  | nil (m b ofs ty sz) :
      sz ≥ 0 → ExecInitArray m b ofs ty sz .Init_nil m
  | cons (m b ofs ty sz i1 il m' m'') :
      ExecInit m b ofs .Full ty i1 m' →
      ExecInitArray m' b (ofs + sizeof ge.genv_cenv ty) ty (sz - 1) il m'' →
      ExecInitArray m b ofs ty sz (.Init_cons i1 il) m''

/-- `Initializersproof.exec_init_struct` -/
inductive ExecInitStruct : Mem → Block → Z → List (Z × Bitfield × Ty) → InitializerList → Mem → Prop where
  | nil (m b ofs) : ExecInitStruct m b ofs [] .Init_nil m
  | cons (m b ofs pos bf ty l i1 il m' m'') :
      ExecInit m b (ofs + pos) bf ty i1 m' →
      ExecInitStruct m' b ofs l il m'' →
      ExecInitStruct m b ofs ((pos, bf, ty) :: l) (.Init_cons i1 il) m''
end

/-- `Initializersproof.exec_init_array_length` -/
theorem execInitArray_length : ∀ {m : Mem} {b : Block} {ofs : Z} {ty : Ty} {sz : Z}
    {il : InitializerList} {m' : Mem}, ExecInitArray ge m b ofs ty sz il m' → sz ≥ 0
  | _, _, _, _, _, _, _, .nil _ _ _ _ _ h => h
  | _, _, _, _, _, _, _, .cons _ _ _ _ _ _ _ _ _ _ h => by
    have := execInitArray_length h
    zomega

/-- The members found by `transl_init_struct` are those listed by
    `initialized_fields_of_struct`. -/
theorem initializedFields_skip {ce : CompositeEnv} : ∀ {ms : List Member} {pos : Z}
    {p : Z} {bf : Bitfield} {ty : Ty} {l : List (Z × Bitfield × Ty)}
    {m1 : Member} {ms' : List Member} {pos' : Z},
    initializedFieldsOfStruct ce ms pos = .OK ((p, bf, ty) :: l) →
    skipUninitialized ce ms pos = some (m1, ms', pos') →
    layoutField ce pos' m1 = .OK (p, bf) ∧ ty = m1.type ∧
      initializedFieldsOfStruct ce ms' (nextField ce pos' m1) = .OK l
  | [], _, _, _, _, _, _, _, _, h, _ => by cases h
  | m :: ms, pos, p, bf, ty, l, m1, ms', pos', h1, h2 => by
    simp only [initializedFieldsOfStruct, skipUninitialized] at h1 h2
    split at h1
    · next hn =>
      rw [if_pos hn] at h2
      exact initializedFields_skip h1 h2
    · next hn =>
      rw [if_neg hn] at h2
      cases h2
      obtain ⟨⟨o, bf'⟩, E1, h1⟩ := res_bind_eq_OK.mp h1
      obtain ⟨l', E2, h1⟩ := res_bind_eq_OK.mp h1
      cases h1
      exact ⟨E1, rfl, E2⟩

/-! ## Soundness of the translation of initializers -/

mutual
/-- `Initializersproof.transl_init_rec_sound`, for single initializers. -/
theorem translInitRec_sound : ∀ {m : Mem} {b : Block} {ofs : Z} {bf : Bitfield} {ty : Ty}
    {i : Initializer} {m' : Mem}, ExecInit ge m b ofs bf ty i m' →
    ∀ {s s' : Initializers.State}, MatchState ge.genv_genv s m b →
    (match bf with
     | .Full => translInitRec ge.genv_cenv s ty i ofs
     | .Bits sz _ p w => translInitBitfield ge.genv_cenv s ty sz p w i ofs) = .OK s' →
    MatchState ge.genv_genv s' m' b
  | _, _, _, _, _, _, _, .single m b ofs bf ty a v1 ty1 m' v m'' STEP CAST ASG, s, s', MS, TR => by
    cases bf with
    | Full =>
      simp only [translInitRec] at TR
      obtain ⟨d, E, TR⟩ := res_bind_eq_OK.mp TR
      obtain ⟨P, Q⟩ := translInitSingle_sound E STEP CAST ASG
      exact storeData_correct MS TR P Q
    | Bits sz sg p w =>
      simp only at TR
      unfold translInitBitfield at TR
      obtain ⟨x, EQ, TR⟩ := res_bind_eq_OK.mp TR
      unfold constvalCast at EQ
      obtain ⟨v0, E0, E1⟩ := res_bind_eq_OK.mp EQ
      obtain ⟨A, B, C⟩ := constval_steps STEP E0
      subst A B
      have D := sem_cast_match CAST E1 C
      cases ASG with
      | bits =>
        cases D with
        | int n =>
          simp only at TR
          obtain ⟨c0, EL, TR⟩ := res_bind_eq_OK.mp TR
          have E := loadInt_correct MS EL (by assumption)
          cases E
          exact storeInt_correct MS TR (by assumption)
        | undef => simp only at TR; cases TR
  | _, _, _, _, _, _, _, .array m b ofs ty sz a il m' H, s, s', MS, TR => by
    simp only [translInitRec] at TR
    exact translInitArray_sound H MS (assertion_eq_OK TR).2
  | _, _, _, _, _, _, _, .struct m b ofs id a il co flds m' H1 H2 H3 H4, s, s', MS, TR => by
    simp only [translInitRec, lookupComposite, H1] at TR
    obtain ⟨co', E, TR⟩ := res_bind_eq_OK.mp TR
    cases E
    rw [H2] at TR
    exact translInitStruct_sound H4 MS H3 TR
  | _, _, _, _, _, _, _, .union m b ofs id a f i co ty pos bf m' H1 H2 H3 H4 H5, s, s', MS, TR => by
    simp only [translInitRec, lookupComposite, H1] at TR
    obtain ⟨co', E, TR⟩ := res_bind_eq_OK.mp TR
    cases E
    rw [H2] at TR
    obtain ⟨ty1, E3, TR⟩ := res_bind_eq_OK.mp TR
    rw [H3] at E3
    cases E3
    obtain ⟨⟨delta, layout⟩, E4, TR⟩ := res_bind_eq_OK.mp TR
    rw [H4] at E4
    cases E4
    exact translInitRec_sound H5 MS TR

/-- `Initializersproof.transl_init_rec_sound`, for array initializers. -/
theorem translInitArray_sound : ∀ {m : Mem} {b : Block} {ofs : Z} {ty : Ty} {sz : Z}
    {il : InitializerList} {m' : Mem}, ExecInitArray ge m b ofs ty sz il m' →
    ∀ {s s' : Initializers.State}, MatchState ge.genv_genv s m b →
    translInitArray ge.genv_cenv s ty il ofs = .OK s' → MatchState ge.genv_genv s' m' b
  | _, _, _, _, _, _, _, .nil m b ofs ty sz _, s, s', MS, TR => by
    simp only [translInitArray] at TR; cases TR; exact MS
  | _, _, _, _, _, _, _, .cons m b ofs ty sz i1 il m' m'' H1 H2, s, s', MS, TR => by
    simp only [translInitArray] at TR
    obtain ⟨s1, E1, TR⟩ := res_bind_eq_OK.mp TR
    exact translInitArray_sound H2 (translInitRec_sound (bf := .Full) H1 MS E1) TR

/-- `Initializersproof.transl_init_rec_sound`, for struct initializers. -/
theorem translInitStruct_sound : ∀ {m : Mem} {b : Block} {ofs : Z} {flds : List (Z × Bitfield × Ty)}
    {il : InitializerList} {m' : Mem}, ExecInitStruct ge m b ofs flds il m' →
    ∀ {s s' : Initializers.State} {ms : List Member} {pos : Z}, MatchState ge.genv_genv s m b →
    initializedFieldsOfStruct ge.genv_cenv ms pos = .OK flds →
    translInitStruct ge.genv_cenv s ms il ofs pos = .OK s' → MatchState ge.genv_genv s' m' b
  | _, _, _, _, _, _, .nil m b ofs, s, s', ms, pos, MS, _, TR => by
    simp only [translInitStruct] at TR; cases TR; exact MS
  | _, _, _, _, _, _, .cons m b ofs p bf ty l i1 il m' m'' H1 H2, s, s', ms, pos, MS, IF, TR => by
    simp only [translInitStruct] at TR
    split at TR
    · cases TR
    · next m1 ms' pos' hskip =>
      obtain ⟨A, B, C⟩ := initializedFields_skip IF hskip
      subst B
      obtain ⟨⟨delta, layout⟩, E1, TR⟩ := res_bind_eq_OK.mp TR
      rw [A] at E1
      cases E1
      cases bf with
      | Full =>
        obtain ⟨s1, E2, TR⟩ := res_bind_eq_OK.mp TR
        exact translInitStruct_sound H2 (translInitRec_sound H1 MS E2) C TR
      | Bits sz sg p w =>
        obtain ⟨s1, E2, TR⟩ := res_bind_eq_OK.mp TR
        exact translInitStruct_sound H2 (translInitRec_sound H1 MS E2) C TR
end

end SOUNDNESS

/-- `Initializersproof.transl_init_sound`: soundness of the translation of
    initializers.  Let `sz` be the size of type `ty`.  Suppose block `b` of
    memory `m` is writable and reads as zeros on `[0, sz)`, executing the
    initializer `i` at offset `0` of `b` turns `m` into `m1`, and
    `transl_init` turns `i` into the initialization data `data`.  Then storing
    `data` at offset `0` of `b` in `m` succeeds, giving a memory `m2` whose
    bytes in block `b` over the size of `data` are the bytes of `m1` in block
    `b` over `[0, sz)`. -/
theorem translInit_sound (p : Csyntax.Program) (m : Mem) (b : Block) (ty : Ty) (i : Initializer)
    (m1 : Mem) (data : List InitData)
    (hperm : Mem.rangePerm m b 0 (sizeof p.prog_comp_env ty) .Cur .Writable = true)
    (hzero : ReadsAsZeros m b 0 (sizeof p.prog_comp_env ty))
    (hexec : ExecInit (Csem.globalenv p) m b 0 .Full ty i m1)
    (htr : translInit p.prog_comp_env ty i = .OK data) :
    ∃ m2, Genv.storeInitDataList (Csem.globalenv p).genv_genv m b 0 data = some m2 ∧
      Mem.loadbytes m2 b 0 (InitData.listSize data) =
        Mem.loadbytes m1 b 0 (sizeof p.prog_comp_env ty) := by
  unfold translInit at htr
  obtain ⟨x, E1, E2⟩ := res_bind_eq_OK.mp htr
  have hsz := sizeof_pos (buildCompositeEnv_wf p.prog_comp_env_eq) ty
  have MS0 : MatchState (Csem.globalenv p).genv_genv (initialState (sizeof p.prog_comp_env ty)) m b :=
    ⟨⟨Int.le_refl _, by simp only [initialState]; zomega⟩, loadbytes_empty _ _ _ (Int.le_refl _),
      trivial, hzero⟩
  have MS1 := translInitRec_sound (bf := .Full) hexec MS0 E1
  have T := totalSize_translInitRec _ _ _ _ _ _ E1
  simp only [initialState] at T
  have := initDataListOfState_correct MS1 E2 (by rw [T]; exact hperm) (by rw [T]; exact hzero)
  rwa [T] at this

end Initializersproof
end CC
