/-
  The "Separate compilation and linking" part of `cfrontend/Ctypes.v`, plus
  the stability lemmas of `Ctypes.v` it relies on:

  * stability of `complete_type`, `sizeof`, `alignof`, `rank_type`,
    `complete_members`, `alignof_composite`, `sizeof_composite` and
    `rank_members` under extension of the composite environment, and
    `composite_consistent` with `composite_consistent_stable`,
    `build_composite_env_consistent`, `composite_of_def_stable`;
  * `Linker_fundef` for Clight's `fundef` (the port's `FunDef` is its own
    inductive, so the instance of `LinkingTheory` for `FunDefGen` does not
    apply to it) and `link_fundef_either`;
  * composite-definition linking: `link_composite_defs`,
    `link_composite_def_inv`, `Linker_composite_defs`,
    `add_composite_definitions_append`, `link_build_composite_env`;
  * program linking, `Linker_program`, and the two commutation theorems
    `link_match_program_gen` / `link_match_program`.

  CompCert's `program` record carries a proof
  `prog_comp_env_eq : build_composite_env prog_types = OK prog_comp_env`.  The
  port's `Program` stores the environment without that proof (see `Clight.lean`),
  so the linker is stated for `WFProgram`, the subtype of programs whose stored
  environment is the one built from their composite definitions.  This is
  exactly CompCert's `program` type.
-/
import CCLib.common.LinkingMatch
import CCLib.cfrontend.CtypesTheory

namespace CC

/-! ## Stability under extension of the composite environment -/

namespace CtypesLinking

/-- `env'` extends `env`. -/
def EnvExtends (env env' : CompositeEnv) : Prop :=
  ∀ id co, env.get id = some co → env'.get id = some co

section Stable
variable {env env' : CompositeEnv} (hext : EnvExtends env env')
include hext

theorem get_isSome_stable {id : Ident} (h : (env.get id).isSome = true) :
    (env'.get id).isSome = true := by
  obtain ⟨co, hco⟩ := Option.isSome_iff_exists.mp h
  rw [hext id co hco]; rfl

/-- `Ctypes.complete_type_stable` -/
theorem completeType_stable : ∀ (t : Ty), completeType env t = true → completeType env' t = true
  | .Tvoid, h => h
  | .Tint _ _ _, h => h
  | .Tlong _ _, h => h
  | .Tfloat _ _, h => h
  | .Tpointer _ _, h => h
  | .Tarray t _ _, h => completeType_stable t h
  | .Tfunction _ _ _, h => h
  | .Tstruct _ _, h => get_isSome_stable hext h
  | .Tunion _ _, h => get_isSome_stable hext h

theorem get_stable {id : Ident} (h : (env.get id).isSome = true) : env'.get id = env.get id := by
  obtain ⟨co, hco⟩ := Option.isSome_iff_exists.mp h
  rw [hext id co hco, hco]

/-- `Ctypes.sizeof_stable` -/
theorem sizeof_stable : ∀ (t : Ty), completeType env t = true → sizeof env' t = sizeof env t
  | .Tvoid, _ => rfl
  | .Tint sz _ _, _ => by cases sz <;> rfl
  | .Tlong _ _, _ => rfl
  | .Tfloat sz _, _ => by cases sz <;> rfl
  | .Tpointer _ _, _ => rfl
  | .Tarray t _ _, h => by simp only [sizeof]; rw [sizeof_stable t h]
  | .Tfunction _ _ _, _ => rfl
  | .Tstruct _ _, h => by simp only [sizeof]; rw [get_stable hext h]
  | .Tunion _ _, h => by simp only [sizeof]; rw [get_stable hext h]

/-- `Ctypes.alignof_stable` -/
theorem alignof_stable : ∀ (t : Ty), completeType env t = true → alignof env' t = alignof env t
  | .Tvoid, _ => rfl
  | .Tint sz _ _, _ => by cases sz <;> rfl
  | .Tlong _ _, _ => rfl
  | .Tfloat sz _, _ => by cases sz <;> rfl
  | .Tpointer _ _, _ => rfl
  | .Tarray t _ _, h => by simp only [alignof]; rw [alignof_stable t h]
  | .Tfunction _ _ _, _ => rfl
  | .Tstruct _ _, h => by simp only [alignof]; rw [get_stable hext h]
  | .Tunion _ _, h => by simp only [alignof]; rw [get_stable hext h]

/-- `Ctypes.rank_type_stable` -/
theorem rankType_stable : ∀ (t : Ty), completeType env t = true → rankType env' t = rankType env t
  | .Tvoid, _ => rfl
  | .Tint _ _ _, _ => rfl
  | .Tlong _ _, _ => rfl
  | .Tfloat _ _, _ => rfl
  | .Tpointer _ _, _ => rfl
  | .Tarray t _ _, h => by simp only [rankType]; rw [rankType_stable t h]
  | .Tfunction _ _ _, _ => rfl
  | .Tstruct _ _, h => by simp only [rankType]; rw [get_stable hext h]
  | .Tunion _ _, h => by simp only [rankType]; rw [get_stable hext h]

/-- `Ctypes.complete_members_stable` -/
theorem completeMembers_stable : ∀ (m : List Member),
    completeMembers env m = true → completeMembers env' m = true
  | [], _ => rfl
  | a :: m, h => by
    simp only [completeMembers, Bool.and_eq_true] at h ⊢
    exact ⟨completeType_stable hext _ h.1, completeMembers_stable m h.2⟩

/-- `Ctypes.alignof_composite_stable` -/
theorem alignofComposite_stable : ∀ (m : List Member),
    completeMembers env m = true → alignofComposite env' m = alignofComposite env m
  | [], _ => rfl
  | a :: m, h => by
    simp only [completeMembers, Bool.and_eq_true] at h
    simp only [alignofComposite]
    rw [alignof_stable hext _ h.1, alignofComposite_stable m h.2]

theorem nextField_stable {pos : Z} {a : Member} (h : completeType env a.type = true) :
    nextField env' pos a = nextField env pos a := by
  cases a with
  | Member_plain id t =>
    simp only [nextField, bitalignof, bitsizeof]
    simp only [Member.type] at h
    rw [alignof_stable hext t h, sizeof_stable hext t h]
  | Member_bitfield => rfl

theorem bitsizeofStruct_stable : ∀ (m : List Member) (cur : Z),
    completeMembers env m = true → bitsizeofStruct env' cur m = bitsizeofStruct env cur m
  | [], _, _ => rfl
  | a :: m, cur, h => by
    simp only [completeMembers, Bool.and_eq_true] at h
    simp only [bitsizeofStruct]
    rw [nextField_stable hext h.1, bitsizeofStruct_stable m _ h.2]

theorem sizeofUnion_stable : ∀ (m : List Member),
    completeMembers env m = true → sizeofUnion env' m = sizeofUnion env m
  | [], _ => rfl
  | a :: m, h => by
    simp only [completeMembers, Bool.and_eq_true] at h
    simp only [sizeofUnion]
    rw [sizeof_stable hext _ h.1, sizeofUnion_stable m h.2]

/-- `Ctypes.sizeof_composite_stable` -/
theorem sizeofComposite_stable (su : SU) (m : List Member) (h : completeMembers env m = true) :
    sizeofComposite env' su m = sizeofComposite env su m := by
  cases su with
  | Struct => simp only [sizeofComposite, sizeofStruct]; rw [bitsizeofStruct_stable hext m 0 h]
  | Union => simp only [sizeofComposite]; rw [sizeofUnion_stable hext m h]

/-- `Ctypes.rank_members_stable` -/
theorem rankMembers_stable : ∀ (m : List Member),
    completeMembers env m = true → rankMembers env' m = rankMembers env m
  | [], _ => rfl
  | a :: m, h => by
    simp only [completeMembers, Bool.and_eq_true] at h
    cases a with
    | Member_plain id t =>
      simp only [rankMembers]
      rw [rankType_stable hext t h.1, rankMembers_stable m h.2]
    | Member_bitfield =>
      simp only [rankMembers]
      exact rankMembers_stable m h.2

end Stable

/-- `Ctypes.composite_consistent`: the size, alignment and rank of a composite
    are those computed from its members in `env`. -/
structure CompositeConsistent (env : CompositeEnv) (co : Composite) : Prop where
  complete : completeMembers env co.co_members = true
  alignof : co.co_alignof = alignAttr co.co_attr (alignofComposite env co.co_members)
  sizeof : co.co_sizeof = align (sizeofComposite env co.co_su co.co_members) co.co_alignof
  rank : co.co_rank = rankMembers env co.co_members

/-- `Ctypes.composite_consistent_stable` -/
theorem compositeConsistent_stable {env env' : CompositeEnv} (hext : EnvExtends env env')
    {co : Composite} (h : CompositeConsistent env co) : CompositeConsistent env' co where
  complete := completeMembers_stable hext _ h.complete
  alignof := by rw [alignofComposite_stable hext _ h.complete]; exact h.alignof
  sizeof := by rw [sizeofComposite_stable hext _ _ h.complete]; exact h.sizeof
  rank := by rw [rankMembers_stable hext _ h.complete]; exact h.rank

/-- `Ctypes.composite_consistent_unique` -/
theorem compositeConsistent_unique {env : CompositeEnv} {co1 co2 : Composite}
    (h1 : CompositeConsistent env co1) (h2 : CompositeConsistent env co2)
    (hsu : co1.co_su = co2.co_su) (hm : co1.co_members = co2.co_members)
    (ha : co1.co_attr = co2.co_attr) : co1 = co2 := by
  obtain ⟨su1, m1, a1, s1, al1, r1⟩ := co1
  obtain ⟨su2, m2, a2, s2, al2, r2⟩ := co2
  obtain ⟨_, ea1, es1, er1⟩ := h1
  obtain ⟨_, ea2, es2, er2⟩ := h2
  simp only at *
  subst hsu hm ha
  have hal : al1 = al2 := by rw [ea1, ea2]
  subst hal
  rw [es1, es2, er1, er2]

theorem compositeOfDef_consistent {env : CompositeEnv} {id : Ident} {su : SU} {m : List Member}
    {a : Attr} {co : Composite} (h : compositeOfDef env id su m a = .OK co) :
    CompositeConsistent env co ∧ co.co_su = su ∧ co.co_members = m ∧ co.co_attr = a ∧
      env.get id = none := by
  unfold compositeOfDef at h
  split at h
  · cases h
  · rename_i hnone
    split at h
    · cases h
    · rename_i hc
      cases h
      simp only [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hnone
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_eq_false] at hc
      exact ⟨⟨hc, rfl, rfl, rfl⟩, rfl, rfl, rfl, hnone⟩

/-- `Ctypes.composite_of_def_eq` -/
theorem compositeOfDef_eq {env : CompositeEnv} {id : Ident} {co : Composite}
    (h : CompositeConsistent env co) (hn : env.get id = none) :
    compositeOfDef env id co.co_su co.co_members co.co_attr = .OK co := by
  unfold compositeOfDef
  rw [hn, h.complete]
  simp only [Option.isSome_none, Bool.false_eq_true, if_false, Bool.not_true]
  obtain ⟨su, m, a, s, al, r⟩ := co
  obtain ⟨_, ea, es, er⟩ := h
  simp only at ea es er
  subst ea es er
  rfl

/-- `Ctypes.composite_of_def_stable` -/
theorem compositeOfDef_stable {env env' : CompositeEnv} (hext : EnvExtends env env')
    {id : Ident} {su : SU} {m : List Member} {a : Attr} {co : Composite}
    (hn : env'.get id = none) (h : compositeOfDef env id su m a = .OK co) :
    compositeOfDef env' id su m a = .OK co := by
  obtain ⟨hc, rfl, rfl, rfl, _⟩ := compositeOfDef_consistent h
  exact compositeOfDef_eq (compositeConsistent_stable hext hc) hn

theorem envExtends_set {env : CompositeEnv} {id : Ident} {co : Composite}
    (hn : env.get id = none) : EnvExtends env (env.set id co) := by
  intro id' co' h
  rw [PTree.gsspec]
  split
  · rename_i he; subst he; rw [hn] at h; cases h
  · exact h

theorem envExtends_refl (env : CompositeEnv) : EnvExtends env env := fun _ _ h => h

theorem envExtends_trans {e1 e2 e3 : CompositeEnv} (h1 : EnvExtends e1 e2)
    (h2 : EnvExtends e2 e3) : EnvExtends e1 e3 := fun id co h => h2 id co (h1 id co h)

/-- Every composite of an environment is consistent with it. -/
def EnvConsistent (env : CompositeEnv) : Prop :=
  ∀ id co, env.get id = some co → CompositeConsistent env co

theorem addCompositeDefinitions_consistent : ∀ (defs : List CompositeDef) {env env' : CompositeEnv},
    EnvConsistent env → addCompositeDefinitions env defs = .OK env' →
    EnvConsistent env' ∧ EnvExtends env env'
  | [], env, env', hc, h => by
    simp only [addCompositeDefinitions, Res.OK.injEq] at h; subst h
    exact ⟨hc, envExtends_refl _⟩
  | .Composite id su m a :: defs, env, env', hc, h => by
    simp only [addCompositeDefinitions] at h
    split at h
    · rename_i co hco
      obtain ⟨hcc, _, _, _, hn⟩ := compositeOfDef_consistent hco
      have hx := envExtends_set (co := co) hn
      have hc' : EnvConsistent (env.set id co) := by
        intro id' co' h'
        rw [PTree.gsspec] at h'
        split at h'
        · cases h'; exact compositeConsistent_stable hx hcc
        · exact compositeConsistent_stable hx (hc id' co' h')
      obtain ⟨r1, r2⟩ := addCompositeDefinitions_consistent defs hc' h
      exact ⟨r1, envExtends_trans hx r2⟩
    · cases h

/-- `Ctypes.build_composite_env_consistent` -/
theorem buildCompositeEnv_consistent {defs : List CompositeDef} {env : CompositeEnv}
    (h : buildCompositeEnv defs = .OK env) {id : Ident} {co : Composite}
    (hco : env.get id = some co) : CompositeConsistent env co :=
  (addCompositeDefinitions_consistent defs (fun _ _ h => by simp at h) h).1 id co hco

/-! ## Linking Clight function definitions (`Ctypes.Linker_fundef`) -/

/-- `Ctypes.link_fundef`, for Clight's `fundef`. -/
def linkFundef : FunDef → FunDef → Option FunDef
  | .Internal _, .Internal _ => none
  | .External ef1 targs1 tres1 cc1, .External ef2 targs2 tres2 cc2 =>
    if ef1 = ef2 ∧ targs1 = targs2 ∧ tres1 = tres2 ∧ cc1 = cc2 then
      some (.External ef1 targs1 tres1 cc1)
    else none
  | .Internal f, .External ef _ _ _ =>
    match ef with
    | .EF_external _ _ => some (.Internal f)
    | _ => none
  | .External ef _ _ _, .Internal f =>
    match ef with
    | .EF_external _ _ => some (.Internal f)
    | _ => none

/-- `Ctypes.linkorder_fundef`, for Clight's `fundef`. -/
inductive LinkorderFundef : FunDef → FunDef → Prop where
  | refl (fd : FunDef) : LinkorderFundef fd fd
  | ext_int (f : Function) (id : String) (sg : Signature) (targs : List Ty) (tres : Ty)
      (cc : CallConv) : LinkorderFundef (.External (.EF_external id sg) targs tres cc) (.Internal f)

theorem linkFundef_linkorder {x y z : FunDef} (h : linkFundef x y = some z) :
    LinkorderFundef x z ∧ LinkorderFundef y z := by
  cases x with
  | Internal f1 =>
    cases y with
    | Internal f2 => simp [linkFundef] at h
    | External ef targs tres cc =>
      cases ef <;> simp [linkFundef] at h
      subst h; exact ⟨.refl _, .ext_int _ _ _ _ _ _⟩
  | External ef targs tres cc =>
    cases y with
    | Internal f2 =>
      cases ef <;> simp [linkFundef] at h
      subst h; exact ⟨.ext_int _ _ _ _ _ _, .refl _⟩
    | External ef2 targs2 tres2 cc2 =>
      simp only [linkFundef] at h
      split at h
      · rename_i hc
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hc
        cases h; exact ⟨.refl _, .refl _⟩
      · cases h

instance instLinkerFundef : Linker FunDef where
  link := linkFundef
  linkorder := LinkorderFundef
  linkorder_refl := .refl
  linkorder_trans := by
    intro x y z h1 h2
    cases h1 with
    | refl => exact h2
    | ext_int => cases h2 with
      | refl => exact .ext_int _ _ _ _ _ _
  link_linkorder := linkFundef_linkorder

/-- `Ctypes.link_fundef_either` -/
theorem link_fundef_either {f1 f2 f : FunDef} (h : Linker.link f1 f2 = some f) :
    f = f1 ∨ f = f2 := by
  change linkFundef f1 f2 = some f at h
  cases f1 with
  | Internal f1 =>
    cases f2 with
    | Internal => simp [linkFundef] at h
    | External ef => cases ef <;> simp [linkFundef] at h; exact .inl h.symm
  | External ef targs tres cc =>
    cases f2 with
    | Internal => cases ef <;> simp [linkFundef] at h; exact .inr h.symm
    | External =>
      simp only [linkFundef] at h
      split at h
      · cases h; exact .inl rfl
      · cases h

/-! ## Linking composite definitions -/

deriving instance DecidableEq for CompositeDef

/-- `Ctypes.check_compat_composite` -/
def checkCompatComposite (l : List CompositeDef) (cd : CompositeDef) : Bool :=
  l.all (fun cd' => if cd'.name = cd.name then decide (cd = cd') else true)

/-- `Ctypes.filter_redefs` -/
def filterRedefs (l1 l2 : List CompositeDef) : List CompositeDef :=
  l2.filter (fun cd => !decide (cd.name ∈ l1.map CompositeDef.name))

/-- `Ctypes.link_composite_defs` -/
def linkCompositeDefs (l1 l2 : List CompositeDef) : Option (List CompositeDef) :=
  if l1.all (checkCompatComposite l2) then some (l1 ++ filterRedefs l1 l2) else none

/-- `Ctypes.link_composite_def_inv` -/
theorem link_composite_def_inv {l1 l2 l : List CompositeDef} (h : linkCompositeDefs l1 l2 = some l) :
    (∀ cd1 cd2, cd1 ∈ l1 → cd2 ∈ l2 → cd2.name = cd1.name → cd2 = cd1) ∧
    l = l1 ++ filterRedefs l1 l2 ∧ (∀ x, x ∈ l ↔ x ∈ l1 ∨ x ∈ l2) := by
  unfold linkCompositeDefs at h
  split at h
  · rename_i hc
    cases h
    have A : ∀ cd1 cd2, cd1 ∈ l1 → cd2 ∈ l2 → cd2.name = cd1.name → cd2 = cd1 := by
      intro cd1 cd2 h1 h2 hn
      have := List.all_eq_true.mp hc cd1 h1
      have := List.all_eq_true.mp this cd2 h2
      simp only [hn, if_true, decide_eq_true_eq] at this
      exact this.symm
    refine ⟨A, rfl, ?_⟩
    intro x
    simp only [filterRedefs, List.mem_append, List.mem_filter, Bool.not_eq_true',
      decide_eq_false_iff_not]
    constructor
    · rintro (h | ⟨h, _⟩)
      · exact .inl h
      · exact .inr h
    · rintro (h | h)
      · exact .inl h
      · by_cases hn : x.name ∈ l1.map CompositeDef.name
        · obtain ⟨y, hy, hyn⟩ := List.mem_map.mp hn
          exact .inl (A y x hy h hyn.symm ▸ hy)
        · exact .inr ⟨h, hn⟩
  · cases h

instance instLinkerCompositeDefs : Linker (List CompositeDef) where
  link := linkCompositeDefs
  linkorder l1 l2 := ∀ x, x ∈ l1 → x ∈ l2
  linkorder_refl _ _ h := h
  linkorder_trans h1 h2 x hx := h2 x (h1 x hx)
  link_linkorder := by
    intro x y z h
    obtain ⟨_, _, C⟩ := link_composite_def_inv h
    exact ⟨fun a ha => (C a).mpr (.inl ha), fun a ha => (C a).mpr (.inr ha)⟩

/-- `Ctypes.add_composite_definitions_append` -/
theorem add_composite_definitions_append : ∀ (l1 l2 : List CompositeDef) (env env'' : CompositeEnv),
    addCompositeDefinitions env (l1 ++ l2) = .OK env'' ↔
    ∃ env', addCompositeDefinitions env l1 = .OK env' ∧ addCompositeDefinitions env' l2 = .OK env''
  | [], l2, env, env'' => by
    simp only [List.nil_append, addCompositeDefinitions, Res.OK.injEq]
    exact ⟨fun h => ⟨env, rfl, h⟩, fun ⟨_, e, h⟩ => e ▸ h⟩
  | .Composite id su m a :: l1, l2, env, env'' => by
    simp only [List.cons_append, addCompositeDefinitions]
    split
    · exact add_composite_definitions_append l1 l2 _ env''
    · constructor
      · intro h; cases h
      · rintro ⟨_, h, _⟩; cases h

theorem buildCompositeEnv_get_name {defs : List CompositeDef} {env : CompositeEnv}
    (h : buildCompositeEnv defs = .OK env) {id : Ident} {co : Composite} (hco : env.get id = some co) :
    id ∈ defs.map CompositeDef.name :=
  List.mem_map.mpr ⟨_, buildCompositeEnv_domain h hco, rfl⟩

/-- `Ctypes.link_add_composite_definitions` -/
theorem link_add_composite_definitions {l0 : List CompositeDef} {env0 : CompositeEnv}
    (h0 : buildCompositeEnv l0 = .OK env0) :
    ∀ (l : List CompositeDef) {env1 env1' env2 : CompositeEnv},
    addCompositeDefinitions env1 l = .OK env1' →
    EnvExtends env1 env2 → EnvExtends env0 env2 →
    (∀ id, env2.get id = if id ∈ l0.map CompositeDef.name then env0.get id else env1.get id) →
    (∀ cd1 cd2, cd1 ∈ l0 → cd2 ∈ l → cd2.name = cd1.name → cd2 = cd1) →
    ∃ env2', addCompositeDefinitions env2 (filterRedefs l0 l) = .OK env2' ∧
      EnvExtends env1' env2' ∧ EnvExtends env0 env2'
  | [], env1, env1', env2, hadd, ag1, ag0, _, _ => by
    simp only [addCompositeDefinitions, Res.OK.injEq] at hadd; subst hadd
    exact ⟨env2, rfl, ag1, ag0⟩
  | .Composite id su m a :: l, env1, env1', env2, hadd, ag1, ag0, ag2, uniq => by
    simp only [addCompositeDefinitions] at hadd
    split at hadd
    case h_2 => cases hadd
    rename_i x hx
    obtain ⟨hcx, hsu, hm, ha, hn1⟩ := compositeOfDef_consistent hx
    have uniq' : ∀ cd1 cd2, cd1 ∈ l0 → cd2 ∈ l → cd2.name = cd1.name → cd2 = cd1 :=
      fun cd1 cd2 h1 h2 => uniq cd1 cd2 h1 (List.mem_cons_of_mem _ h2)
    by_cases hin : id ∈ l0.map CompositeDef.name
    · have hf : filterRedefs l0 (.Composite id su m a :: l) = filterRedefs l0 l := by
        simp only [filterRedefs, List.filter_cons, CompositeDef.name, hin, decide_true,
          Bool.not_true, Bool.false_eq_true, if_false]
      rw [hf]
      obtain ⟨cd', hcd', hcdn⟩ := List.mem_map.mp hin
      have he := uniq cd' _ hcd' (List.mem_cons_self) hcdn.symm
      rw [← he] at hcd'
      obtain ⟨co', hco', hm', ha', hsu'⟩ := buildCompositeEnv_charact h0 hcd'
      have hco'c := compositeConsistent_stable ag0 (buildCompositeEnv_consistent h0 hco')
      have heq : co' = x :=
        compositeConsistent_unique hco'c (compositeConsistent_stable ag1 hcx)
          (hsu'.trans hsu.symm) (hm'.trans hm.symm) (ha'.trans ha.symm)
      subst heq
      refine link_add_composite_definitions h0 l hadd ?_ ag0 ?_ uniq'
      · intro id' co'' h'
        rw [PTree.gsspec] at h'
        split at h'
        · rename_i hid; subst hid; cases h'
          rw [ag2, if_pos hin]; exact hco'
        · exact ag1 id' co'' h'
      · intro id'
        rw [ag2 id', PTree.gsspec]
        by_cases hid : id' = id
        · subst hid; rw [if_pos hin, if_pos hin]
        · rw [if_neg hid]
    · have hf : filterRedefs l0 (.Composite id su m a :: l) =
          .Composite id su m a :: filterRedefs l0 l := by
        simp only [filterRedefs, List.filter_cons, CompositeDef.name, hin, decide_false,
          Bool.not_false, if_true]
      rw [hf]
      have hn2 : env2.get id = none := by rw [ag2, if_neg hin]; exact hn1
      have hx2 := compositeOfDef_stable ag1 hn2 hx
      simp only [addCompositeDefinitions, hx2]
      refine link_add_composite_definitions h0 l hadd ?_ ?_ ?_ uniq'
      · intro id' co'' h'
        rw [PTree.gsspec] at h' ⊢
        split
        · rename_i hid; rw [if_pos hid] at h'; exact h'
        · rename_i hid; rw [if_neg hid] at h'; exact ag1 id' co'' h'
      · intro id' co'' h'
        rw [PTree.gsspec]
        split
        · rename_i hid; subst hid
          exact absurd (buildCompositeEnv_get_name h0 h') hin
        · exact ag0 id' co'' h'
      · intro id'
        rw [PTree.gsspec, PTree.gsspec]
        split
        · rename_i hid; subst hid; rw [if_neg hin]
        · exact ag2 id'

/-- `Ctypes.link_build_composite_env` -/
theorem link_build_composite_env {l1 l2 l : List CompositeDef} {env1 env2 : CompositeEnv}
    (h1 : buildCompositeEnv l1 = .OK env1) (h2 : buildCompositeEnv l2 = .OK env2)
    (hl : Linker.link l1 l2 = some l) :
    ∃ env, buildCompositeEnv l = .OK env ∧ EnvExtends env1 env ∧ EnvExtends env2 env := by
  obtain ⟨A, B, _⟩ := link_composite_def_inv hl
  obtain ⟨env, P, Q, R⟩ := link_add_composite_definitions h1 l2 (env1 := PTree.empty) h2
    (fun _ _ h => by simp at h) (envExtends_refl _)
    (by
      intro id
      split
      · rfl
      · rename_i hn
        cases hg : env1.get id with
        | none => simp
        | some co => exact absurd (buildCompositeEnv_get_name h1 hg) hn) A
  refine ⟨env, ?_, R, Q⟩
  subst B
  exact (add_composite_definitions_append _ _ _ _).mpr ⟨env1, h1, P⟩

/-! ## Linking programs (`Ctypes.Linker_program`) -/

/-- `Ctypes.program`: a Clight program together with CompCert's
    `prog_comp_env_eq` — its stored composite environment is the one built from
    its composite definitions. -/
def WFProgram : Type := {p : Program // buildCompositeEnv p.prog_types = .OK p.prog_comp_env}

/-- `Ctypes.program_of_program` -/
def WFProgram.toAST (p : WFProgram) : ASTProgram FunDef Ty := p.val.toAST

/-- `Ctypes.link_program`.  The `Error` case of `build_composite_env` cannot
    happen (`link_build_composite_env`); Rocq rules it out in the type, here it
    is a dead branch. -/
def linkProgram (p1 p2 : WFProgram) : Option WFProgram :=
  match Linker.link p1.toAST p2.toAST with
  | none => none
  | some p =>
    match Linker.link p1.val.prog_types p2.val.prog_types with
    | none => none
    | some typs =>
      match he : buildCompositeEnv typs with
      | .OK env =>
        some ⟨{ prog_defs := p.prog_defs, prog_public := p.prog_public,
                prog_main := p.prog_main, prog_types := typs, prog_comp_env := env }, he⟩
      | .Error _ => none

/-- `Ctypes.linkorder_program` -/
def LinkorderProgram (p1 p2 : WFProgram) : Prop :=
  Linker.linkorder p1.toAST p2.toAST ∧ EnvExtends p1.val.prog_comp_env p2.val.prog_comp_env

theorem linkProgram_inv {p1 p2 p : WFProgram} (h : linkProgram p1 p2 = some p) :
    ∃ pp typs, Linker.link p1.toAST p2.toAST = some pp ∧
      Linker.link p1.val.prog_types p2.val.prog_types = some typs ∧
      p.toAST = pp ∧ p.val.prog_types = typs := by
  unfold linkProgram at h
  split at h
  · cases h
  · rename_i pp hpp
    split at h
    · cases h
    · rename_i typs ht
      split at h
      · cases h
        exact ⟨pp, typs, hpp, ht, rfl, rfl⟩
      · cases h

theorem linkProgram_succeeds {p1 p2 : WFProgram} {pp : ASTProgram FunDef Ty}
    {typs : List CompositeDef} (hpp : Linker.link p1.toAST p2.toAST = some pp)
    (ht : Linker.link p1.val.prog_types p2.val.prog_types = some typs) :
    ∃ p, linkProgram p1 p2 = some p ∧ p.toAST = pp ∧ p.val.prog_types = typs := by
  obtain ⟨env, hb, _, _⟩ := link_build_composite_env p1.property p2.property ht
  unfold linkProgram
  rw [hpp]
  simp only
  rw [ht]
  simp only
  split
  · exact ⟨_, rfl, rfl, rfl⟩
  · rename_i he; rw [hb] at he; cases he

theorem linkProgram_linkorder {x y z : WFProgram} (h : linkProgram x y = some z) :
    LinkorderProgram x z ∧ LinkorderProgram y z := by
  have h' := h
  unfold linkProgram at h'
  split at h'
  · cases h'
  · rename_i pp hpp
    split at h'
    · cases h'
    · rename_i typs ht
      split at h'
      · rename_i env he
        cases h'
        obtain ⟨env', hb, e1, e2⟩ := link_build_composite_env x.property y.property ht
        rw [he] at hb; cases hb
        have lo := Linker.link_linkorder hpp
        exact ⟨⟨lo.1, e1⟩, ⟨lo.2, e2⟩⟩
      · cases h'

instance instLinkerProgram : Linker WFProgram where
  link := linkProgram
  linkorder := LinkorderProgram
  linkorder_refl _ := ⟨Linker.linkorder_refl _, envExtends_refl _⟩
  linkorder_trans h1 h2 := ⟨Linker.linkorder_trans h1.1 h2.1, envExtends_trans h1.2 h2.2⟩
  link_linkorder := linkProgram_linkorder

/-! ## Commutation between linking and program transformations -/

/-- The relation of `Ctypes.LINK_MATCH_PROGRAM_GEN`: `match_program_gen` with
    the source program as context, and equal composite definitions. -/
def MatchProgramGenC (Rf : WFProgram → FunDef → FunDef → Prop) (p tp : WFProgram) : Prop :=
  Linking.MatchProgramGen Rf Eq p p.toAST tp.toAST ∧ tp.val.prog_types = p.val.prog_types

/-- `Ctypes.link_match_program_gen` -/
theorem link_match_program_gen {Rf : WFProgram → FunDef → FunDef → Prop}
    (hlf : Linking.LinkMatchFundef Rf) {p1 p2 tp1 tp2 p : WFProgram}
    (h : Linker.link p1 p2 = some p) (m1 : MatchProgramGenC Rf p1 tp1)
    (m2 : MatchProgramGenC Rf p2 tp2) :
    ∃ tp, Linker.link tp1 tp2 = some tp ∧ MatchProgramGenC Rf p tp := by
  obtain ⟨lo1, lo2⟩ := Linker.link_linkorder h
  obtain ⟨pp, typs, hpp, ht, hpa, hpt⟩ := linkProgram_inv h
  obtain ⟨tpp, htpp, hm⟩ :=
    Linking.link_match_program hlf Linking.linkMatchVarinfo_eq hpp m1.1 m2.1 lo1 lo2
  have ht' : Linker.link tp1.val.prog_types tp2.val.prog_types = some typs := by
    rw [m1.2, m2.2]; exact ht
  obtain ⟨tp, htp, htpa, htpt⟩ := linkProgram_succeeds htpp ht'
  refine ⟨tp, htp, ?_, ?_⟩
  · rw [htpa, hpa]; exact hm
  · rw [htpt, hpt]

/-- The relation of `Ctypes.LINK_MATCH_PROGRAM`: `Linking.match_program` with
    a context-free function relation, and equal composite definitions. -/
def MatchProgramC (mf : FunDef → FunDef → Prop) (p tp : WFProgram) : Prop :=
  Linking.MatchProgramCtx (fun _ f tf => mf f tf) Eq p.toAST tp.toAST ∧
    tp.val.prog_types = p.val.prog_types

/-- `Ctypes.link_match_program` -/
theorem link_match_program {mf : FunDef → FunDef → Prop}
    (hlf : ∀ f1 tf1 f2 tf2 f, Linker.link f1 f2 = some f → mf f1 tf1 → mf f2 tf2 →
      ∃ tf, Linker.link tf1 tf2 = some tf ∧ mf f tf)
    {p1 p2 tp1 tp2 p : WFProgram} (h : Linker.link p1 p2 = some p)
    (m1 : MatchProgramC mf p1 tp1) (m2 : MatchProgramC mf p2 tp2) :
    ∃ tp, Linker.link tp1 tp2 = some tp ∧ MatchProgramC mf p tp := by
  obtain ⟨pp, typs, hpp, ht, hpa, hpt⟩ := linkProgram_inv h
  obtain ⟨lo1, lo2⟩ := Linker.link_linkorder hpp
  have hlf' : Linking.LinkMatchFundef (C := ASTProgram FunDef Ty) (fun _ f tf => mf f tf) :=
    fun _ _ f1 tf1 f2 tf2 f hl e1 e2 =>
      let ⟨tf, a, b⟩ := hlf f1 tf1 f2 tf2 f hl e1 e2
      ⟨tf, a, .inl b⟩
  obtain ⟨tpp, htpp, hm⟩ :=
    Linking.link_match_program hlf' Linking.linkMatchVarinfo_eq hpp m1.1 m2.1 lo1 lo2
  have ht' : Linker.link tp1.val.prog_types tp2.val.prog_types = some typs := by
    rw [m1.2, m2.2]; exact ht
  obtain ⟨tp, htp, htpa, htpt⟩ := linkProgram_succeeds htpp ht'
  refine ⟨tp, htp, ?_, ?_⟩
  · show Linking.MatchProgramGen _ Eq p.toAST p.toAST tp.toAST
    rw [htpa, hpa]; exact hm
  · rw [htpt, hpt]

end CtypesLinking
end CC
