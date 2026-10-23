/-
  Pulling local scalar variables into temporaries: semantic preservation —
  port of `cfrontend/SimplLocalsproof.v`, part 2: allocation of local
  variables at function entry (`alloc_variables_*`, `match_alloc_variables`,
  `match_envs_alloc_variables`), temporaries (`create_undef_temps_*`),
  assignment through injections (`assign_loc_inject`), storing the
  parameters (`store_params_correct`) and freeing the local variables at
  function exit (`match_envs_free_blocks`).
-/
import CCLib.cfrontend.SimplLocalsproofEnv
import CCLib.common.MemdataTheory
import CCLib.cfrontend.CtypesTheory
import CCLib.common.MemoryBytes
namespace CC
namespace SimplLocals
open Smallstep

theorem pos_le_def {p q : Positive} : p ≤ q ↔ p.toNat ≤ q.toNat := Iff.rfl
theorem pos_lt_def {p q : Positive} : p < q ↔ p.toNat < q.toNat := Iff.rfl

theorem alloc_inv {m : Mem} {lo hi : Z} {m1 : Mem} {b1 : Block} (h : Mem.alloc m lo hi = (m1, b1)) :
    b1 = m.nextblock ∧ m1.nextblock.toNat = m.nextblock.toNat + 1 := by
  obtain ⟨rfl, rfl⟩ := Mem.alloc_eq h
  exact ⟨rfl, by simp⟩

/-! ## Allocation and initialization of parameters -/

/-- `SimplLocalsproof.alloc_variables_nextblock` -/
theorem alloc_variables_nextblock {ce : CompositeEnv} {e : Env} {m : Mem}
    {vars : List (Ident × Ty)} {e' : Env} {m' : Mem} (h : AllocVariables ce e m vars e' m') :
    m.nextblock ≤ m'.nextblock := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons e m id ty vars m1 b1 m2 e2 ha _ ih =>
    have := (alloc_inv ha).2
    rw [pos_le_def] at ih ⊢; omega

/-- `SimplLocalsproof.alloc_variables_range` -/
theorem alloc_variables_range {ce : CompositeEnv} {id : Ident} {b : Block} {ty : Ty} {e : Env}
    {m : Mem} {vars : List (Ident × Ty)} {e' : Env} {m' : Mem}
    (h : AllocVariables ce e m vars e' m') (he : e'.get id = some (b, ty)) :
    e.get id = some (b, ty) ∨ (m.nextblock ≤ b ∧ b < m'.nextblock) := by
  induction h with
  | nil => exact Or.inl he
  | cons e m id0 ty0 vars m1 b1 m2 e2 ha hrest ih =>
    obtain ⟨hb1, hn⟩ := alloc_inv ha
    have hnb := alloc_variables_nextblock hrest
    rcases ih he with A | A
    · rw [PTree.gsspec] at A
      split at A
      · cases A
        right; subst hb1
        rw [pos_le_def, pos_lt_def]; rw [pos_le_def] at hnb; omega
      · exact Or.inl A
    · right
      rw [pos_le_def, pos_lt_def] at A ⊢; omega

/-- `SimplLocalsproof.alloc_variables_injective` -/
theorem alloc_variables_injective {ce : CompositeEnv} {id1 : Ident} {b1 : Block} {ty1 : Ty}
    {id2 : Ident} {b2 : Block} {ty2 : Ty} {e : Env} {m : Mem} {vars : List (Ident × Ty)}
    {e' : Env} {m' : Mem} (h : AllocVariables ce e m vars e' m')
    (hinj : ∀ id1 b1 ty1 id2 b2 ty2, e.get id1 = some (b1, ty1) → e.get id2 = some (b2, ty2) →
      id1 ≠ id2 → b1 ≠ b2)
    (hlt : ∀ id b ty, e.get id = some (b, ty) → b < m.nextblock) :
    e'.get id1 = some (b1, ty1) → e'.get id2 = some (b2, ty2) → id1 ≠ id2 → b1 ≠ b2 := by
  induction h generalizing id1 b1 ty1 id2 b2 ty2 with
  | nil => exact hinj _ _ _ _ _ _
  | cons e m id ty vars m1 bb m2 e2 ha hrest ih =>
    obtain ⟨hbb, hn⟩ := alloc_inv ha
    apply ih
    · intro i1 c1 t1 i2 c2 t2 h1 h2 hne
      rw [PTree.gsspec] at h1 h2
      split at h1 <;> split at h2
      · rename_i e1 e2; exact absurd (e1.trans e2.symm) hne
      · cases h1; have := hlt _ _ _ h2; rw [pos_lt_def] at this
        intro hc; subst hc; subst hbb; omega
      · cases h2; have := hlt _ _ _ h1; rw [pos_lt_def] at this
        intro hc; subst hc; subst hbb; omega
      · exact hinj _ _ _ _ _ _ h1 h2 hne
    · intro i c t h1
      rw [PTree.gsspec] at h1
      rw [pos_lt_def, hn]
      split at h1
      · cases h1; subst hbb; omega
      · have := hlt _ _ _ h1; rw [pos_lt_def] at this; omega

/-- `SimplLocalsproof.alloc_variables_load` -/
theorem alloc_variables_load {ce : CompositeEnv} {e : Env} {m : Mem} {vars : List (Ident × Ty)}
    {e' : Env} {m' : Mem} (h : AllocVariables ce e m vars e' m') {chunk : Chunk} {b : Block}
    {ofs : Z} {v : Val} (hl : Mem.load chunk m b ofs = some v) :
    Mem.load chunk m' b ofs = some v := by
  induction h with
  | nil => exact hl
  | cons e m id ty vars m1 b1 m2 e2 ha _ ih =>
    apply ih
    obtain ⟨rfl, -⟩ := Mem.alloc_eq ha
    have hb : b ≠ m.nextblock := Mem.ne_nextblock_of_perm
      (Mem.validAccess_perm_nonempty (Mem.load_valid_access hl) (Int.le_refl _)
        (by have := sizeChunk_pos chunk; omega))
    rw [Mem.load_alloc_other _ _ _ _ _ hb]; exact hl


/-- `Mem.load_alloc_same'` at offset 0. -/
theorem load_alloc_same_zero (m : Mem) (hi : _root_.Int) (chunk : Chunk) (hsz : sizeChunk chunk ≤ hi) :
    Mem.load chunk (Mem.alloc m 0 hi).1 m.nextblock 0 = some .Vundef := by
  unfold Mem.load
  rw [if_pos]
  · obtain ⟨n, hn⟩ := sizeChunkNat_pos chunk
    rw [hn]
    simp only [Mem.alloc_contents, PMap.gss, Mem.getN, ZMap.gi]
    exact congrArg some (decodeVal_undef_cons _ _)
  · simp only [Mem.validAccess, Bool.and_eq_true]
    refine ⟨Mem.rangePerm_intro _ _ _ _ _ _ fun ofs h1 h2 => ?_, by simp⟩
    exact Mem.perm_implies (Mem.perm_alloc_same m 0 hi ofs _ h1
      (Int.lt_of_lt_of_le (by simpa using h2) hsz)) (by decide)

/-- `SimplLocalsproof.sizeof_by_value` -/
theorem sizeof_by_value (ce : CompositeEnv) {ty : Ty} {chunk : Chunk}
    (h : accessMode ty = .By_value chunk) : sizeChunk chunk ≤ sizeof ce ty := by
  rcases ty with _ | ⟨sz, si, a⟩ | ⟨si, a⟩ | ⟨_ | _, a⟩ | ⟨t, a⟩ | ⟨t, n, a⟩ | ⟨ta, tr, cc⟩ |
      ⟨id, a⟩ | ⟨id, a⟩ <;> (try cases sz) <;> (try cases si) <;>
    simp [accessMode] at h <;> subst h <;> simp [sizeof, sizeChunk, Mptr, Archi.ptr64]

/-- `SimplLocalsproof.env_initial_value` -/
def EnvInitialValue (e : Env) (m : Mem) : Prop :=
  ∀ id b ty chunk, e.get id = some (b, ty) → accessMode ty = .By_value chunk →
    Mem.load chunk m b 0 = some .Vundef

/-- `SimplLocalsproof.alloc_variables_initial_value` -/
theorem alloc_variables_initial_value {ce : CompositeEnv} {e : Env} {m : Mem}
    {vars : List (Ident × Ty)} {e' : Env} {m' : Mem} (h : AllocVariables ce e m vars e' m')
    (hi : EnvInitialValue e m) : EnvInitialValue e' m' := by
  induction h with
  | nil => exact hi
  | cons e m id ty vars m1 b1 m2 e2 ha _ ih =>
    apply ih
    obtain ⟨rfl, rfl⟩ := Mem.alloc_eq ha
    intro id0 b ty0 chunk he hm
    rw [PTree.gsspec] at he
    split at he
    · cases he
      exact load_alloc_same_zero m _ chunk (sizeof_by_value ce hm)
    · have hl := hi id0 b ty0 chunk he hm
      have hb : b ≠ m.nextblock := Mem.ne_nextblock_of_perm
        (Mem.validAccess_perm_nonempty (Mem.load_valid_access hl) (Int.le_refl _)
          (by have := sizeChunk_pos chunk; omega))
      rw [Mem.load_alloc_other _ _ _ _ _ hb]; exact hl

/-- `SimplLocalsproof.create_undef_temps_charact` -/
theorem create_undef_temps_charact {id : Ident} {ty : Ty} :
    ∀ {vars : List (Ident × Ty)}, (id, ty) ∈ vars → (createUndefTemps vars).get id = some .Vundef
  | [], h => by cases h
  | (id1, ty1) :: vars, h => by
    simp only [createUndefTemps]
    rw [PTree.gsspec]
    split
    · rfl
    · rcases List.mem_cons.mp h with h | h
      · cases h; contradiction
      · exact create_undef_temps_charact h

/-- `SimplLocalsproof.create_undef_temps_inv` -/
theorem create_undef_temps_inv {id : Ident} {v : Val} :
    ∀ {vars : List (Ident × Ty)}, (createUndefTemps vars).get id = some v →
    v = .Vundef ∧ id ∈ varNames vars
  | [], h => by simp [createUndefTemps] at h
  | (id1, ty1) :: vars, h => by
    simp only [createUndefTemps] at h
    rw [PTree.gsspec] at h
    split at h
    · cases h; subst_vars; exact ⟨rfl, by simp [varNames]⟩
    · obtain ⟨A, B⟩ := create_undef_temps_inv h
      exact ⟨A, by simp only [varNames, List.map_cons, List.mem_cons]; exact Or.inr B⟩

theorem create_undef_temps_none {id : Ident} :
    ∀ {vars : List (Ident × Ty)}, id ∉ varNames vars → (createUndefTemps vars).get id = none := by
  intro vars h
  cases hc : (createUndefTemps vars).get id with
  | none => rfl
  | some v => exact absurd (create_undef_temps_inv hc).2 h

/-- `SimplLocalsproof.create_undef_temps_exten` -/
theorem create_undef_temps_exten {id : Ident} {l1 l2 : List (Ident × Ty)}
    (h : id ∈ varNames l1 ↔ id ∈ varNames l2) :
    (createUndefTemps l1).get id = (createUndefTemps l2).get id := by
  have key : ∀ {l : List (Ident × Ty)}, id ∈ varNames l → (createUndefTemps l).get id = some .Vundef := by
    intro l hl
    simp only [varNames, List.mem_map] at hl
    obtain ⟨⟨id', ty⟩, hin, rfl⟩ := hl
    exact create_undef_temps_charact hin
  by_cases h1 : id ∈ varNames l1
  · rw [key h1, key (h.mp h1)]
  · rw [create_undef_temps_none h1, create_undef_temps_none (fun h2 => h1 (h.mpr h2))]

/-! ### Lists of variables -/

theorem varNames_app (vars1 vars2 : List (Ident × Ty)) :
    varNames (vars1 ++ vars2) = varNames vars1 ++ varNames vars2 := List.map_append

theorem removeLifted_cons_lifted {cenv : Compilenv} {id : Ident} {ty : Ty}
    {vars : List (Ident × Ty)} (h : VSet.mem id cenv = true) :
    removeLifted cenv ((id, ty) :: vars) = removeLifted cenv vars := by
  simp [removeLifted, h]

theorem removeLifted_cons_not_lifted {cenv : Compilenv} {id : Ident} {ty : Ty}
    {vars : List (Ident × Ty)} (h : VSet.mem id cenv = false) :
    removeLifted cenv ((id, ty) :: vars) = (id, ty) :: removeLifted cenv vars := by
  simp [removeLifted, h]

/-- `SimplLocalsproof.match_alloc_variables` -/
theorem match_alloc_variables (ce : CompositeEnv) (cenv : Compilenv) {e : Env} {m : Mem}
    {vars : List (Ident × Ty)} {e' : Env} {m' : Mem} (h : AllocVariables ce e m vars e' m') :
    ∀ {j : Val.Meminj} {tm : Mem} {te : Env}, listNorepet (varNames vars) → Mem.Inject j m tm →
    ∃ j' te' tm',
      AllocVariables ce te tm (removeLifted cenv vars) te' tm' ∧
      Mem.Inject j' m' tm' ∧
      Val.inject_incr j j' ∧
      (∀ b, Mem.validBlock m b = true → j' b = j b) ∧
      (∀ b b' delta, j' b = some (b', delta) → Mem.validBlock tm b' = true → j' b = j b) ∧
      (∀ b b' delta, j' b = some (b', delta) → Mem.validBlock tm b' = false →
        ∃ id ty, e'.get id = some (b, ty) ∧ te'.get id = some (b', ty) ∧ delta = 0) ∧
      (∀ id ty, (id, ty) ∈ vars → ∃ b, e'.get id = some (b, ty) ∧
        (if VSet.mem id cenv then te'.get id = te.get id ∧ j' b = none
         else ∃ tb, te'.get id = some (tb, ty) ∧ j' b = some (tb, 0))) ∧
      (∀ id, id ∉ varNames vars → e'.get id = e.get id ∧ te'.get id = te.get id) := by
  induction h with
  | nil e m =>
    intro j tm te _ hinj
    refine ⟨j, te, tm, .nil _ _, hinj, Val.inject_incr_refl _, fun _ _ => rfl,
      fun _ _ _ _ _ => rfl, ?_, fun _ _ h => by simp at h, fun _ _ => ⟨rfl, rfl⟩⟩
    intro b b' delta hj hv
    rw [hinj.mappedblocks _ _ _ hj] at hv; cases hv
  | cons e m id ty vars m1 b1 m2 e2 ha hrest ih =>
    intro j tm te hnr hinj
    simp only [listNorepet, varNames, List.map_cons, List.nodup_cons] at hnr
    obtain ⟨hnin, hnr⟩ := hnr
    have hm1 := Mem.alloc_eq ha
    cases hl : VSet.mem id cenv with
    | true =>
      obtain ⟨j1, A, B, C, D⟩ := Mem.alloc_left_unmapped_inject hinj ha
      obtain ⟨j', te', tm', J, K, L, M, N, Q, O, P⟩ := ih (te := te) hnr A
      refine ⟨j', te', tm', by rw [removeLifted_cons_lifted hl]; exact J, K,
        Val.inject_incr_trans B L, ?_, ?_, Q, ?_, ?_⟩
      · intro b hb
        have hb1 : b ≠ b1 := by
          rintro rfl; rw [hm1.2, Mem.fresh_block_alloc] at hb; cases hb
        rw [M b (by rw [hm1.1]; exact Mem.valid_block_alloc _ _ _ hb), D b hb1]
      · intro b b' delta hj hv
        rw [N b b' delta hj hv]
        by_cases hb1 : b = b1
        · subst hb1
          have := M b (by rw [hm1.1, hm1.2]; exact Mem.valid_new_block _ _ _)
          rw [this, C] at hj; cases hj
        · exact D b hb1
      · intro id0 ty0 hin
        by_cases hid : id0 = id
        · subst hid
          have hty : ty0 = ty := by
            rcases List.mem_cons.mp hin with h | h
            · cases h; rfl
            · exact absurd (List.mem_map_of_mem (f := Prod.fst) h) hnin
          subst hty
          obtain ⟨X, Y⟩ := P id0 hnin
          refine ⟨b1, by rw [X, PTree.gss], ?_⟩
          simp only [hl, if_true]
          exact ⟨Y, by rw [M b1 (by rw [hm1.1, hm1.2]; exact Mem.valid_new_block _ _ _), C]⟩
        · rcases List.mem_cons.mp hin with h | h
          · cases h; exact absurd rfl hid
          · exact O id0 ty0 h
      · intro id0 hn
        simp only [varNames, List.map_cons, List.mem_cons, not_or] at hn
        obtain ⟨X, Y⟩ := P id0 hn.2
        exact ⟨by rw [X, PTree.gso _ _ _ _ (Ne.symm hn.1)], Y⟩
    | false =>
      obtain ⟨j1, tm1, tb1, A0, A, B, C, D⟩ :=
        Mem.alloc_parallel_inject hinj ha (Int.le_refl 0) (Int.le_refl (sizeof ce ty))
      have htm1 := Mem.alloc_eq A0
      obtain ⟨j', te', tm', J, K, L, M, N, Q, O, P⟩ := ih (te := te.set id (tb1, ty)) hnr A
      have hvb1 : Mem.validBlock m1 b1 = true := by
        rw [hm1.1, hm1.2]; exact Mem.valid_new_block _ _ _
      have hvtb1 : Mem.validBlock tm1 tb1 = true := by
        rw [htm1.1, htm1.2]; exact Mem.valid_new_block _ _ _
      have hntb1 : Mem.validBlock tm tb1 = false := by rw [htm1.2]; exact Mem.fresh_block_alloc _
      refine ⟨j', te', tm', ?_, K, Val.inject_incr_trans B L, ?_, ?_, ?_, ?_, ?_⟩
      · rw [removeLifted_cons_not_lifted hl]; exact .cons _ _ _ _ _ _ _ _ _ A0 J
      · intro b hb
        have hb1 : b ≠ b1 := by
          rintro rfl; rw [hm1.2, Mem.fresh_block_alloc] at hb; cases hb
        rw [M b (by rw [hm1.1]; exact Mem.valid_block_alloc _ _ _ hb), D b hb1]
      · intro b b' delta hj hv
        rw [N b b' delta hj (by rw [htm1.1]; exact Mem.valid_block_alloc _ _ _ hv)]
        by_cases hb1 : b = b1
        · subst hb1
          rw [M b hvb1, C] at hj; cases hj
          rw [hntb1] at hv; cases hv
        · exact D b hb1
      · intro b b' delta hj hv
        by_cases hb' : b' = tb1
        · subst hb'
          have hjb := N b b' delta hj hvtb1
          rw [hjb] at hj
          by_cases hb1 : b = b1
          · subst hb1
            rw [C] at hj; cases hj
            obtain ⟨X, Y⟩ := P id hnin
            exact ⟨id, ty, by rw [X, PTree.gss], by rw [Y, PTree.gss], rfl⟩
          · rw [D b hb1] at hj
            rw [hinj.mappedblocks _ _ _ hj] at hv; cases hv
        · apply Q b b' delta hj
          rw [htm1.1]
          cases hc : Mem.validBlock (Mem.alloc tm 0 (sizeof ce ty)).1 b' with
          | false => rfl
          | true =>
            rcases Mem.valid_block_alloc_inv _ _ _ hc with h | h
            · rw [← htm1.2] at h; exact absurd h hb'
            · rw [hv] at h; cases h
      · intro id0 ty0 hin
        by_cases hid : id0 = id
        · subst hid
          have hty : ty0 = ty := by
            rcases List.mem_cons.mp hin with h | h
            · cases h; rfl
            · exact absurd (List.mem_map_of_mem (f := Prod.fst) h) hnin
          subst hty
          obtain ⟨X, Y⟩ := P id0 hnin
          refine ⟨b1, by rw [X, PTree.gss], ?_⟩
          simp only [hl]
          exact ⟨tb1, by rw [Y, PTree.gss], by rw [M b1 hvb1, C]⟩
        · rcases List.mem_cons.mp hin with h | h
          · cases h; exact absurd rfl hid
          · obtain ⟨b, X, Y⟩ := O id0 ty0 h
            refine ⟨b, X, ?_⟩
            split
            · rename_i hl0; simp only [hl0, if_true] at Y
              exact ⟨by rw [Y.1, PTree.gso _ _ _ _ (Ne.symm hid)], Y.2⟩
            · rename_i hl0; simp only [hl0] at Y; exact Y
      · intro id0 hn
        simp only [varNames, List.map_cons, List.mem_cons, not_or] at hn
        obtain ⟨X, Y⟩ := P id0 hn.2
        exact ⟨by rw [X, PTree.gso _ _ _ _ (Ne.symm hn.1)],
          by rw [Y, PTree.gso _ _ _ _ (Ne.symm hn.1)]⟩

/-- `SimplLocalsproof.create_undef_temps_lifted` -/
theorem create_undef_temps_lifted {id : Ident} {f : Function} (h : id ∉ varNames f.fn_params) :
    (createUndefTemps (addLifted (cenvFor f) f.fn_vars f.fn_temps)).get id =
      (createUndefTemps (addLifted (cenvFor f) (f.fn_params ++ f.fn_vars) f.fn_temps)).get id := by
  apply create_undef_temps_exten
  simp only [addLifted, List.filter_append, varNames, List.map_append, List.mem_append]
  constructor
  · rintro (h1 | h1)
    · exact Or.inl (Or.inr h1)
    · exact Or.inr h1
  · rintro ((h1 | h1) | h1)
    · exfalso; apply h
      simp only [List.mem_map, List.mem_filter] at h1
      obtain ⟨p, ⟨hp, _⟩, rfl⟩ := h1
      exact List.mem_map_of_mem hp
    · exact Or.inl h1
    · exact Or.inr h1

/-- `SimplLocalsproof.vars_and_temps_properties` -/
theorem vars_and_temps_properties {cenv : Compilenv} {params vars temps : List (Ident × Ty)}
    (h1 : listNorepet (varNames params ++ varNames vars))
    (h2 : listDisjoint (varNames params) (varNames temps)) :
    listNorepet (varNames params) ∧
      listNorepet (varNames (removeLifted cenv (params ++ vars))) ∧
      listDisjoint (varNames params) (varNames (addLifted cenv vars temps)) := by
  unfold listNorepet at *
  have hA : (varNames params).Nodup := (List.nodup_append.mp h1).1
  refine ⟨hA, ?_, ?_⟩
  · unfold removeLifted varNames
    rw [← varNames_app] at h1
    exact List.Nodup.sublist ((List.filter_sublist).map _) h1
  · intro x hx hx'
    simp only [addLifted, varNames, List.map_append, List.mem_append] at hx'
    rcases hx' with hx' | hx'
    · simp only [List.mem_map, List.mem_filter] at hx'
      obtain ⟨p, ⟨hp, _⟩, rfl⟩ := hx'
      exact (List.nodup_append.mp h1).2.2 _ hx _ (List.mem_map_of_mem hp) rfl
    · exact h2 x hx hx'

theorem mem_varNames {id : Ident} {vars : List (Ident × Ty)} (h : id ∈ varNames vars) :
    ∃ ty, (id, ty) ∈ vars := by
  simp only [varNames, List.mem_map] at h
  obtain ⟨⟨id', ty⟩, hin, rfl⟩ := h
  exact ⟨ty, hin⟩

/-- `SimplLocalsproof.match_envs_alloc_variables` -/
theorem match_envs_alloc_variables (ce : CompositeEnv) {cenv : Compilenv} {m : Mem}
    {vars : List (Ident × Ty)} {e : Env} {m' : Mem} (temps : List (Ident × Ty))
    {j : Val.Meminj} {tm : Mem}
    (h : AllocVariables ce emptyEnv m vars e m') (hnr : listNorepet (varNames vars))
    (hinj : Mem.Inject j m tm)
    (H1 : ∀ id ty, (id, ty) ∈ vars → VSet.mem id cenv = true →
      ∃ chunk, accessMode ty = .By_value chunk)
    (H2 : ∀ id, VSet.mem id cenv = true → id ∈ varNames vars) :
    ∃ j' te tm',
      AllocVariables ce emptyEnv tm (removeLifted cenv vars) te tm' ∧
      MatchEnvs j' cenv e (createUndefTemps temps) m' m.nextblock m'.nextblock
        te (createUndefTemps (addLifted cenv vars temps)) tm.nextblock tm'.nextblock ∧
      Mem.Inject j' m' tm' ∧
      Val.inject_incr j j' ∧
      (∀ b, Mem.validBlock m b = true → j' b = j b) ∧
      (∀ b b' delta, j' b = some (b', delta) → Mem.validBlock tm b' = true → j' b = j b) ∧
      (∀ id ty, (id, ty) ∈ vars → VSet.mem id cenv = false → ∃ b, te.get id = some (b, ty)) := by
  obtain ⟨j', te, tm', A, B, C, D, E, K, F, G⟩ := match_alloc_variables ce cenv h (te := emptyEnv) hnr hinj
  have hempty : ∀ id, (emptyEnv : Env).get id = none := fun id => PTree.gempty id
  have hinjE : ∀ {e0 : Env} {m0 m0' : Mem} {vs : List (Ident × Ty)},
      AllocVariables ce emptyEnv m0 vs e0 m0' →
      ∀ id1 b1 ty1 id2 b2 ty2, e0.get id1 = some (b1, ty1) → e0.get id2 = some (b2, ty2) →
        id1 ≠ id2 → b1 ≠ b2 := by
    intro e0 m0 m0' vs ha id1 b1 ty1 id2 b2 ty2
    exact alloc_variables_injective ha (fun _ _ _ _ _ _ h1 => by rw [hempty] at h1; cases h1)
      (fun _ _ _ h1 => by rw [hempty] at h1; cases h1)
  have hrange : ∀ {e0 : Env} {m0 m0' : Mem} {vs : List (Ident × Ty)},
      AllocVariables ce emptyEnv m0 vs e0 m0' →
      ∀ id b ty, e0.get id = some (b, ty) → m0.nextblock ≤ b ∧ b < m0'.nextblock := by
    intro e0 m0 m0' vs ha id b ty he
    rcases alloc_variables_range ha he with h1 | h1
    · rw [hempty] at h1; cases h1
    · exact h1
  refine ⟨j', te, tm', A, ⟨?_, ?_, hinjE h, hrange h, hrange A, ?_, ?_,
    alloc_variables_nextblock h, alloc_variables_nextblock A⟩, B, C, D, E, ?_⟩
  · -- vars
    intro id
    by_cases hin : id ∈ varNames vars
    · obtain ⟨ty, hin⟩ := mem_varNames hin
      obtain ⟨b, P, R⟩ := F id ty hin
      cases hl : VSet.mem id cenv with
      | true =>
        simp only [hl, if_true] at R
        obtain ⟨chunk, hm⟩ := H1 id ty hin hl
        refine .lifted b ty chunk .Vundef .Vundef P (by rw [R.1, hempty]) hl R.2 hm ?_ ?_ (.undef _)
        · exact alloc_variables_initial_value h (fun _ _ _ _ h1 => by rw [hempty] at h1; cases h1)
            id b ty chunk P hm
        · apply create_undef_temps_charact (ty := ty)
          simp only [addLifted, List.mem_append, List.mem_filter]
          exact Or.inl ⟨hin, hl⟩
      | false =>
        simp only [hl] at R
        obtain ⟨tb, U, V⟩ := R
        exact .not_lifted b ty tb P U hl V
    · obtain ⟨U, V⟩ := G id hin
      refine .not_local (by rw [U, hempty]) (by rw [V, hempty]) ?_
      cases hl : VSet.mem id cenv with
      | false => rfl
      | true => exact absurd (H2 id hl) hin
  · -- temps
    intro id v hv
    obtain ⟨P, Q⟩ := create_undef_temps_inv hv
    subst P
    obtain ⟨ty, hin⟩ := mem_varNames Q
    refine ⟨⟨.Vundef, ?_, .undef _⟩, fun _ => rfl⟩
    apply create_undef_temps_charact (ty := ty)
    simp only [addLifted, List.mem_append]
    exact Or.inr hin
  · -- mapped
    intro id b' ty ht
    by_cases hin : id ∈ varNames vars
    · obtain ⟨ty', hin⟩ := mem_varNames hin
      obtain ⟨b, P, R⟩ := F id ty' hin
      split at R
      · rw [R.1, hempty] at ht; cases ht
      · obtain ⟨tb, U, V⟩ := R
        rw [U] at ht; cases ht
        exact ⟨b, V, P⟩
    · rw [(G id hin).2, hempty] at ht; cases ht
  · -- flat
    intro id b' ty b delta ht hj
    have hr := hrange A id b' ty ht
    have hnv : Mem.validBlock tm b' = false := by
      simp only [Mem.validBlock, decide_eq_false_iff_not]
      rw [pos_le_def] at hr; rw [pos_lt_def]; omega
    obtain ⟨id0, ty0, U, V, W⟩ := K b b' delta hj hnv
    refine ⟨?_, W⟩
    by_cases hid : id = id0
    · subst hid; rw [V] at ht; cases ht; exact U
    · exact absurd rfl (hinjE A id b' ty id0 b' ty0 ht V hid)
  · intro id ty hin hl
    obtain ⟨b, _, R⟩ := F id ty hin
    simp only [hl] at R
    obtain ⟨tb, U, _⟩ := R
    exact ⟨tb, U⟩

/-- Loads from blocks other than `b` are unaffected by a `store` into `b`. -/
theorem load_store_other_block {chunk : Chunk} {m : Mem} {b : Block} {ofs : Z} {v : Val}
    {m' : Mem} (hs : Mem.store chunk m b ofs v = some m') {chunk' : Chunk} {b' : Block}
    {ofs' : Z} {v' : Val} (hb : b' ≠ b) (hl : Mem.load chunk' m b' ofs' = some v') :
    Mem.load chunk' m' b' ofs' = some v' :=
  (Mem.store_unchangedOn (P := fun b0 _ => b0 ≠ b) hs (fun _ _ _ h => h rfl)).load
    (fun _ _ _ => hb) hl

/-- Loads from blocks other than `b` are unaffected by a `storebytes` into `b`. -/
theorem load_storebytes_other_block {m : Mem} {b : Block} {ofs : Z} {bytes : List MemVal}
    {m' : Mem} (hs : Mem.storebytes m b ofs bytes = some m') {chunk' : Chunk} {b' : Block}
    {ofs' : Z} {v' : Val} (hb : b' ≠ b) (hl : Mem.load chunk' m b' ofs' = some v') :
    Mem.load chunk' m' b' ofs' = some v' :=
  (Mem.storebytes_unchangedOn (P := fun b0 _ => b0 ≠ b) hs (fun _ _ _ h => h rfl)).load
    (fun _ _ _ => hb) hl

theorem storev_load_other {chunk : Chunk} {m : Mem} {b : Block} {ofs : Integers.Ptrofs} {v : Val}
    {m' : Mem} (hs : Mem.storev chunk m (.Vptr b ofs) v = some m') {chunk' : Chunk} {b' : Block}
    {ofs' : Z} {v' : Val} (hb : b' ≠ b) (hl : Mem.load chunk' m b' ofs' = some v') :
    Mem.load chunk' m' b' ofs' = some v' :=
  load_store_other_block (Mem.storev_store hs) hb hl

/-- `SimplLocalsproof.assign_loc_inject` -/
theorem assign_loc_inject {ce : CompositeEnv} (hwf : CompositeEnv.WF ce) {f : Val.Meminj} {ty : Ty} {m : Mem}
    {loc : Block} {ofs : Integers.Ptrofs} {bf : Bitfield} {v : Val} {m' : Mem} {tm : Mem}
    {loc' : Block} {ofs' : Integers.Ptrofs} {v' : Val}
    (ha : AssignLoc ce ty m loc ofs bf v m') (hp : Val.Inject f (.Vptr loc ofs) (.Vptr loc' ofs'))
    (hv : Val.Inject f v v') (hm : Mem.Inject f m tm) :
    ∃ tm', AssignLoc ce ty tm loc' ofs' bf v' tm' ∧ Mem.Inject f m' tm' ∧
      (∀ b chunk v, f b = none → Mem.load chunk m b 0 = some v → Mem.load chunk m' b 0 = some v) := by
  have hfl : ∃ d, f loc = some (loc', d) := by cases hp with | ptr d hf _ => exact ⟨d, hf⟩
  obtain ⟨dd, hfd⟩ := hfl
  have hne : ∀ b, f b = none → b ≠ loc := by
    rintro b hb rfl; rw [hb] at hfd; cases hfd
  cases ha with
  | value _ chunk _ hmode hst =>
    obtain ⟨tm', A, B⟩ := Mem.storev_mapped_inject hm hst hp hv
    exact ⟨tm', .value _ _ _ hmode A, B, fun b chunk v hb hl => storev_load_other hst (hne b hb) hl⟩
  | bitfield sz sg pos width v0 _ v'' hsb =>
    cases hsb with
    | intro sz sg1 attr sg pos width m addr c n m' h1 h2 h3 h4 h5 h6 h7 =>
    obtain ⟨vc', LD', INJ⟩ := Mem.loadv_inject hm h6 hp
    cases INJ
    cases hv
    obtain ⟨tm', A, B⟩ := Mem.storev_mapped_inject hm h7 hp (.int _)
    exact ⟨tm', .bitfield _ _ _ _ _ _ _ (.intro _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 LD' A), B,
      fun b chunk v hb hl => storev_load_other h7 (hne b hb) hl⟩
  | copy bsrc osrc bytes _ hmode hal1 hal2 hdisj hlb hsb =>
    cases hv with
    | ptr ds hfs hos =>
    rename_i bsrc' osrc'
    subst hos
    cases hp with
    | ptr dd' hfd' hod =>
    rw [hfd] at hfd'; cases hfd'
    subst hod
    have hsz0 := sizeof_pos hwf ty
    have hloads : ∀ b chunk v, f b = none → Mem.load chunk m b 0 = some v →
        Mem.load chunk m' b 0 = some v :=
      fun b chunk v hb hl => load_storebytes_other_block hsb (hne b hb) hl
    by_cases hsz : sizeof ce ty > 0
    · -- general case
      have LEN := Mem.loadbytes_length hlb
      have RPSRC : Mem.rangePerm m bsrc (Integers.Ptrofs.unsigned osrc)
          (Integers.Ptrofs.unsigned osrc + sizeof ce ty) .Cur .Nonempty = true :=
        Mem.rangePerm_implies (Mem.loadbytes_range_perm hlb) (by decide)
      have RPDST : Mem.rangePerm m loc (Integers.Ptrofs.unsigned ofs)
          (Integers.Ptrofs.unsigned ofs + sizeof ce ty) .Cur .Nonempty = true := by
        have := Mem.rangePerm_implies (Mem.storebytes_rangePerm hsb) (q := .Nonempty) (by decide)
        rw [LEN] at this
        have hz : ((sizeof ce ty).toNat : _root_.Int) = sizeof ce ty := Int.toNat_of_nonneg hsz0
        rw [hz] at this; exact this
      have PSRC := Mem.rangePerm_perm _ _ _ _ _ _ RPSRC _ (Int.le_refl _)
        (by have : (0 : _root_.Int) < sizeof ce ty := hsz; omega)
      have PDST := Mem.rangePerm_perm _ _ _ _ _ _ RPDST _ (Int.le_refl _)
        (by have : (0 : _root_.Int) < sizeof ce ty := hsz; omega)
      have EQ1 := Mem.address_inject hm PSRC hfs
      have EQ2 := Mem.address_inject hm PDST hfd
      obtain ⟨bytes2, A, B⟩ := Mem.loadbytes_inject hm hlb hfs
      obtain ⟨tm', C, D⟩ := Mem.storebytes_mapped_inject hm hsb hfd B
      refine ⟨tm', .copy _ _ _ _ hmode ?_ ?_ ?_ (by rw [EQ1]; exact A) (by rw [EQ2]; exact C), D,
        hloads⟩
      · intro _
        rw [EQ1]
        exact Int.emod_eq_zero_of_dvd (Mem.aligned_area_inject hm (alignofBlockcopy_1248 hwf ty) hsz
          (sizeof_alignof_blockcopy_compat hwf ty) RPSRC (Int.dvd_of_emod_eq_zero (hal1 hsz)) hfs)
      · intro _
        rw [EQ2]
        exact Int.emod_eq_zero_of_dvd (Mem.aligned_area_inject hm (alignofBlockcopy_1248 hwf ty) hsz
          (sizeof_alignof_blockcopy_compat hwf ty) RPDST (Int.dvd_of_emod_eq_zero (hal2 hsz)) hfd)
      · rw [EQ1, EQ2]
        exact Mem.disjoint_or_equal_inject hm hfs hfd (Mem.rangePerm_max RPSRC)
          (Mem.rangePerm_max RPDST) hsz hdisj
    · -- size zero
      have hsz' : sizeof ce ty ≤ 0 := Int.not_lt.mp hsz
      have hb : bytes = [] := by
        rw [Mem.loadbytes_empty _ _ _ hsz'] at hlb; cases hlb; rfl
      subst hb
      obtain ⟨tm', SB⟩ := EventsInject.storebytes_nil_exists tm loc'
        (Integers.Ptrofs.unsigned (Integers.Ptrofs.add ofs (Integers.Ptrofs.repr dd)))
      refine ⟨tm', .copy _ _ _ _ hmode (fun h => absurd h hsz) (fun h => absurd h hsz) ?_
        (Mem.loadbytes_empty _ _ _ hsz') SB, Mem.storebytes_empty_inject hm hsb SB, hloads⟩
      right; right
      have key : ∀ (x y s : _root_.Int), s ≤ 0 → x + s ≤ y ∨ y + s ≤ x := by intros; omega
      exact key _ _ _ hsz'

/-- `PTree.gsident`, structurally: setting a key to the value it already has
    returns the same tree. -/
theorem ptree_set_same {A : Type} : ∀ (i : Positive) (v : A) (m : PTree A),
    m.get i = some v → m.set i v = m
  | .xH, v, .Leaf, h => by simp at h
  | .xO _, v, .Leaf, h => by simp at h
  | .xI _, v, .Leaf, h => by simp at h
  | .xH, v, .Node l o r, h => by simp only [PTree.get] at h; subst h; rfl
  | .xO ii, v, .Node l o r, h => by
    simp only [PTree.get] at h; simp only [PTree.set, ptree_set_same ii v l h]
  | .xI ii, v, .Node l o r, h => by
    simp only [PTree.get] at h; simp only [PTree.set, ptree_set_same ii v r h]

/-- `SimplLocalsproof.assign_loc_nextblock` -/
theorem assign_loc_nextblock {ce : CompositeEnv} {ty : Ty} {m : Mem} {b : Block}
    {ofs : Integers.Ptrofs} {bf : Bitfield} {v : Val} {m' : Mem}
    (h : AssignLoc ce ty m b ofs bf v m') : m'.nextblock = m.nextblock := by
  cases h with
  | value _ _ _ _ hs => exact Mem.storev_nextblock hs
  | copy _ _ _ _ _ _ _ _ _ hs => exact Mem.storebytes_nextblock hs
  | bitfield _ _ _ _ _ _ _ hs => cases hs with
    | intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs => exact Mem.storev_nextblock hs

/-- `SimplLocalsproof.store_params_correct` -/
theorem store_params_correct (opts : Options) {ce : CompositeEnv} (hwf : CompositeEnv.WF ce)
    {tge : CGenv} (hce : tge.genv_cenv = ce) {j : Val.Meminj} {f : Function} {k : Cont}
    {cenv : Compilenv} {le : TempEnv} {lo hi : Block} {te : Env} {tlo thi : Block} {e : Env}
    {m : Mem} {params : List (Ident × Ty)} {args : List Val} {m' : Mem}
    (hbind : BindParameters ce e m params args m') :
    ∀ {s : Stmt} {tm : Mem} {tle1 tle2 : TempEnv} {targs : List Val},
    listNorepet (varNames params) → ValCastedList args (typeOfParams params) →
    Val.InjectList j args targs → MatchEnvs j cenv e le m lo hi te tle1 tlo thi →
    Mem.Inject j m tm → (∀ id, id ∉ varNames params → tle2.get id = tle1.get id) →
    (∀ id, id ∈ varNames params → le.get id = none) →
    ∃ tle tm',
      Smallstep.Star (Step2 tge) (.State f (storeParams opts cenv params s) k te tle tm) E0
        (.State f s k te tle tm') ∧
      bindParameterTemps params targs tle2 = some tle ∧
      Mem.Inject j m' tm' ∧
      MatchEnvs j cenv e le m' lo hi te tle tlo thi ∧
      tm'.nextblock = tm.nextblock := by
  induction hbind with
  | nil m =>
    intro s tm tle1 tle2 targs _ _ VINJ MENV MINJ TLE _
    cases VINJ
    exact ⟨tle2, tm, .refl _, rfl, MINJ, match_envs_temps_exten MENV (fun id => TLE id (by simp [varNames])), rfl⟩
  | cons m id ty params v1 vl b m1 m2 he ha hrest ih =>
    intro s tm tle1 tle2 targs NOREPET CASTED VINJ MENV MINJ TLE LE
    simp only [listNorepet, varNames, List.map_cons, List.nodup_cons] at NOREPET
    obtain ⟨hnin, NOREPET⟩ := NOREPET
    cases CASTED with
    | cons hc CASTED =>
    cases VINJ with
    | @cons _ v' _ targs hvi VINJ =>
    have TLE' : ∀ id0, id0 ∉ varNames params →
        (tle2.set id v').get id0 = (tle1.set id v').get id0 := by
      intro id0 hn
      rw [PTree.gsspec, PTree.gsspec]
      split
      · rfl
      · rename_i hne
        exact TLE id0 (by simp only [varNames, List.map_cons, List.mem_cons, not_or]; exact ⟨hne, hn⟩)
    have LE' : ∀ id0, id0 ∈ varNames params → le.get id0 = none :=
      fun id0 h => LE id0 (by simp only [varNames, List.map_cons, List.mem_cons]; exact Or.inr h)
    cases hl : VSet.mem id cenv with
    | true =>
      -- lifted to a temporary
      have MV := MENV.me_vars id
      have MINJ1 : Mem.Inject j m1 tm := by
        cases MV with
        | lifted b0 ty0 chunk v0 tv0 ENV _ _ MAPPED MODE _ _ _ =>
          rw [he] at ENV; cases ENV
          cases ha with
          | value _ chunk' _ hmode hst =>
            exact Mem.store_unmapped_inject MINJ (Mem.storev_store hst) MAPPED
          | copy => rename_i h _ _ _ _ _; rw [MODE] at h; cases h
        | not_lifted _ _ _ _ _ h3 _ => rw [hl] at h3; cases h3
        | not_local h1 _ _ => rw [he] at h1; cases h1
      obtain ⟨tle, tm', U, V, X, Y, Z⟩ := ih (s := s) NOREPET CASTED VINJ
        (match_envs_assign_lifted MENV he hc hvi ha hl) MINJ1 TLE' LE'
      refine ⟨tle, tm', ?_, V, X, Y, Z⟩
      simp only [storeParams, hl, if_true]
      split
      · have A : tle.get id = some v' := by rw [bind_parameter_temps_inv V hnin, PTree.gss]
        have EV : EvalExpr tge te tle tm (makeCast (.Etempvar id ty) ty) v' :=
          make_cast_correct (.Etempvar _ _ _ A)
            (Cop.cast_val_casted tm (val_casted_inject hvi hc))
        have H := Step.set (functionEntry := FunctionEntry2 tge) f id _ (.Kseq (storeParams opts cenv params s) k) te tle tm v' EV
        rw [ptree_set_same _ _ _ A] at H
        exact star_left (Step.seq _ _ _ _ _ _ _) (star_left H
          (star_left (Step.skip_seq _ _ _ _ _ _) U rfl) rfl) rfl
      · exact U
    | false =>
      -- still in memory
      have MV := MENV.me_vars id
      cases MV with
      | lifted _ _ _ _ _ _ _ h3 _ _ _ _ _ => rw [hl] at h3; cases h3
      | not_local h1 _ _ => rw [he] at h1; cases h1
      | not_lifted b0 ty0 b' ENV TENV _ MAPPED =>
      rw [he] at ENV; cases ENV
      obtain ⟨tm1, A, B, C⟩ := assign_loc_inject hwf ha
        (.ptr 0 MAPPED (EventsInject.ptrofs_add_repr_zero _).symm) hvi MINJ
      have ME1 := match_envs_change_temp (v := v')
        (match_envs_invariant MENV (fun b chunk v hb _ hl => C b chunk v hb hl)
          (Val.inject_incr_refl _) (fun _ _ => rfl) (fun _ _ _ _ _ => rfl))
        (LE id (by simp [varNames])) hl
      obtain ⟨tle, tm', U, V, X, Y, Z⟩ := ih (s := s) NOREPET CASTED VINJ ME1 B TLE' LE'
      refine ⟨tle, tm', ?_, V, X, Y, by rw [Z, assign_loc_nextblock A]⟩
      simp only [storeParams, hl]
      have A' : tle.get id = some v' := by rw [bind_parameter_temps_inv V hnin, PTree.gss]
      have H := Step.assign (functionEntry := FunctionEntry2 tge) f (.Evar id ty) (.Etempvar id ty)
        (.Kseq (storeParams opts cenv params s) k) te tle tm b' Integers.Ptrofs.zero .Full v' v' tm1
        (.Evar_local _ _ _ TENV) (.Etempvar _ _ _ A')
        (Cop.cast_val_casted tm (val_casted_inject hvi hc)) (by rw [hce]; exact A)
      exact star_left (Step.seq _ _ _ _ _ _ _) (star_left H
        (star_left (Step.skip_seq _ _ _ _ _ _) U rfl) rfl) rfl

/-! ### Freeing of local variables -/

/-- `Mem.perm_free_list` -/
theorem perm_freeList : ∀ {l : List (Block × Z × Z)} {m m' : Mem} {b : Block} {ofs : Z}
    {k : PermKind} {p : Permission}, Mem.freeList m l = some m' → Mem.perm m' b ofs k p = true →
    Mem.perm m b ofs k p = true ∧ ∀ lo hi, (b, lo, hi) ∈ l → ¬ (lo ≤ ofs ∧ ofs < hi)
  | [], m, m', b, ofs, k, p, h, hp => by
    simp only [Mem.freeList, Option.some.injEq] at h; subst h
    exact ⟨hp, fun _ _ h => by simp at h⟩
  | (b1, lo1, hi1) :: l, m, m', b, ofs, k, p, h, hp => by
    simp only [Mem.freeList] at h
    split at h
    · cases h
    · rename_i m1 hfr
      obtain ⟨A, B⟩ := perm_freeList h hp
      rw [Mem.free_result hfr] at A
      have A' := Mem.perm_free_3 A
      refine ⟨A', ?_⟩
      intro lo hi hin
      rcases List.mem_cons.mp hin with heq | hin
      · cases heq
        intro ⟨h1, h2⟩
        rw [Mem.perm_free_inside _ _ _ _ _ _ _ h1 h2] at A; cases A
      · exact B lo hi hin

/-- `SimplLocalsproof.free_list_perm'` -/
theorem freeList_perm' : ∀ {l : List (Block × Z × Z)} {m m' : Mem} {b : Block} {lo hi : Z},
    Mem.freeList m l = some m' → (b, lo, hi) ∈ l → Mem.rangePerm m b lo hi .Cur .Freeable = true
  | [], _, _, _, _, _, _, h => by simp at h
  | (b1, lo1, hi1) :: l, m, m', b, lo, hi, h, hin => by
    simp only [Mem.freeList] at h
    split at h
    · cases h
    · rename_i m1 hfr
      rcases List.mem_cons.mp hin with heq | hin
      · cases heq; exact Mem.free_range_perm hfr
      · have := freeList_perm' h hin
        rw [Mem.free_result hfr] at this
        exact Mem.rangePerm_intro _ _ _ _ _ _ fun ofs h1 h2 =>
          Mem.perm_free_3 (Mem.rangePerm_perm _ _ _ _ _ _ this ofs h1 h2)

/-- `SimplLocalsproof.can_free_list`, for lists of pairwise distinct blocks. -/
theorem can_free_list : ∀ (l : List (Block × Z × Z)) (m : Mem),
    (∀ x ∈ l, Mem.rangePerm m x.1 x.2.1 x.2.2 .Cur .Freeable = true) →
    l.Pairwise (fun a b => a.1 ≠ b.1) → ∃ m', Mem.freeList m l = some m'
  | [], m, _, _ => ⟨m, rfl⟩
  | (b, lo, hi) :: l, m, hp, hpw => by
    obtain ⟨m1, A⟩ := Mem.range_perm_free (hp _ (List.mem_cons_self ..))
    simp only [Mem.freeList, A]
    rw [List.pairwise_cons] at hpw
    apply can_free_list l m1 _ hpw.2
    intro x hx
    rw [Mem.free_result A]
    exact Mem.rangePerm_intro _ _ _ _ _ _ fun ofs h1 h2 => Mem.perm_free_1 (Or.inl (hpw.1 x hx).symm)
      (Mem.rangePerm_perm _ _ _ _ _ _ (hp x (List.mem_cons_of_mem _ hx)) ofs h1 h2)

/-- `SimplLocalsproof.free_list_right_inject` -/
theorem freeList_right_inject {j : Val.Meminj} {m1 : Mem} : ∀ {l : List (Block × Z × Z)} {m2 m2' : Mem},
    Mem.Inject j m1 m2 → Mem.freeList m2 l = some m2' →
    (∀ b1 b2 delta lo hi ofs k p, j b1 = some (b2, delta) → (b2, lo, hi) ∈ l →
      Mem.perm m1 b1 ofs k p = true → lo ≤ ofs + delta → ofs + delta < hi → False) →
    Mem.Inject j m1 m2'
  | [], m2, m2', hi, h, _ => by
    simp only [Mem.freeList, Option.some.injEq] at h; subst h; exact hi
  | (b, lo, hi) :: l, m2, m2', hinj, h, H => by
    simp only [Mem.freeList] at h
    split at h
    · cases h
    · rename_i m21 hfr
      refine freeList_right_inject (Mem.free_right_inject hinj hfr ?_) h ?_
      · intro b1 delta ofs k p hj hp h1 h2
        exact H b1 b delta lo hi ofs k p hj (List.mem_cons_self ..) hp h1 h2
      · intro b1 b2 delta lo hi ofs k p hj hin hp h1 h2
        exact H b1 b2 delta lo hi ofs k p hj (List.mem_cons_of_mem _ hin) hp h1 h2

theorem mem_blocksOfEnv {ce : CompositeEnv} {e : Env} {b : Block} {lo hi : Z}
    (h : (b, lo, hi) ∈ blocksOfEnv ce e) : ∃ id ty, e.get id = some (b, ty) ∧ lo = 0 ∧ hi = sizeof ce ty := by
  simp only [blocksOfEnv, List.mem_map] at h
  obtain ⟨⟨id, b', ty⟩, hin, heq⟩ := h
  simp only [blockOfBinding, Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  exact ⟨id, ty, PTree.elements_complete _ _ _ hin, rfl, rfl⟩

theorem blocksOfEnv_mem {ce : CompositeEnv} {e : Env} {id : Ident} {b : Block} {ty : Ty}
    (h : e.get id = some (b, ty)) : (b, 0, sizeof ce ty) ∈ blocksOfEnv ce e :=
  List.mem_map.mpr ⟨(id, b, ty), PTree.elements_correct _ _ _ h, rfl⟩

/-- In matching environments, the target environment binds distinct
    variables to distinct blocks. -/
theorem match_envs_te_inj {j : Val.Meminj} {cenv : Compilenv} {e : Env} {le : TempEnv} {m : Mem}
    {lo hi : Block} {te : Env} {tle : TempEnv} {tlo thi : Block}
    (ME : MatchEnvs j cenv e le m lo hi te tle tlo thi) {id1 id2 : Ident} {b : Block} {ty1 ty2 : Ty}
    (h1 : te.get id1 = some (b, ty1)) (h2 : te.get id2 = some (b, ty2)) : id1 = id2 := by
  obtain ⟨b1, A1, B1⟩ := ME.me_mapped id1 b ty1 h1
  obtain ⟨b2, A2, B2⟩ := ME.me_mapped id2 b ty2 h2
  obtain ⟨C, _⟩ := ME.me_flat id1 b ty1 b2 0 h1 A2
  rw [B1] at C; cases C
  exact Classical.byContradiction fun hne => ME.me_inj id1 b1 ty1 id2 b1 ty2 B1 B2 hne rfl

theorem blocksOfEnv_pairwise {j : Val.Meminj} {cenv : Compilenv} {e : Env} {le : TempEnv} {m : Mem}
    {lo hi : Block} {te : Env} {tle : TempEnv} {tlo thi : Block}
    (ME : MatchEnvs j cenv e le m lo hi te tle tlo thi) (ce : CompositeEnv) :
    (blocksOfEnv ce te).Pairwise (fun a b => a.1 ≠ b.1) := by
  unfold blocksOfEnv
  rw [List.pairwise_map]
  have hk := PTree.elements_keys_norepet te
  rw [List.Nodup, List.pairwise_map] at hk
  refine hk.imp_of_mem ?_
  intro a b ha hb hne
  obtain ⟨ida, ba, ta⟩ := a
  obtain ⟨idb, bb, tb⟩ := b
  simp only [blockOfBinding]
  intro heq
  subst heq
  exact hne (match_envs_te_inj ME (PTree.elements_complete _ _ _ ha) (PTree.elements_complete _ _ _ hb))

/-- `SimplLocalsproof.match_envs_free_blocks` -/
theorem match_envs_free_blocks {ce : CompositeEnv} {j : Val.Meminj} {cenv : Compilenv} {e : Env}
    {le : TempEnv} {m : Mem} {lo hi : Block} {te : Env} {tle : TempEnv} {tlo thi : Block}
    {m' tm : Mem} (ME : MatchEnvs j cenv e le m lo hi te tle tlo thi) (MINJ : Mem.Inject j m tm)
    (hfr : Mem.freeList m (blocksOfEnv ce e) = some m') :
    ∃ tm', Mem.freeList tm (blocksOfEnv ce te) = some tm' ∧ Mem.Inject j m' tm' := by
  obtain ⟨tm', FREE⟩ : ∃ tm', Mem.freeList tm (blocksOfEnv ce te) = some tm' := by
    apply can_free_list _ _ _ (blocksOfEnv_pairwise ME ce)
    intro x hx
    obtain ⟨b', lo', hi'⟩ := x
    obtain ⟨id, ty, hte, rfl, rfl⟩ := mem_blocksOfEnv hx
    obtain ⟨b, A, B⟩ := ME.me_mapped id b' ty hte
    have := Mem.rangePerm_inject A MINJ (freeList_perm' hfr (blocksOfEnv_mem B))
    simpa using this
  refine ⟨tm', FREE, freeList_right_inject (Mem.freeList_left_inject _ MINJ hfr) FREE ?_⟩
  intro b1 b2 delta lo' hi' ofs k p hj hin hp h1 h2
  obtain ⟨id, ty, hte, rfl, rfl⟩ := mem_blocksOfEnv hin
  obtain ⟨P, rfl⟩ := ME.me_flat id b2 ty b1 delta hte hj
  exact (perm_freeList hfr hp).2 0 (sizeof ce ty) (blocksOfEnv_mem P) ⟨by simpa using h1, by simpa using h2⟩

/-- `SimplLocalsproof.bind_parameters_nextblock` -/
theorem bind_parameters_nextblock {ce : CompositeEnv} {e : Env} {m : Mem}
    {params : List (Ident × Ty)} {args : List Val} {m' : Mem}
    (h : BindParameters ce e m params args m') : m'.nextblock = m.nextblock := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ _ _ _ _ _ _ ha _ ih => rw [ih, assign_loc_nextblock ha]

/-- `SimplLocalsproof.bind_parameters_load` (in the direction used by the
    proof: loads from blocks that are not local variables are preserved). -/
theorem bind_parameters_load {ce : CompositeEnv} {e : Env} {chunk : Chunk} {b : Block} {ofs : Z}
    {v : Val} (hb : ∀ id b' ty, e.get id = some (b', ty) → b ≠ b') {m : Mem}
    {params : List (Ident × Ty)} {args : List Val} {m' : Mem}
    (h : BindParameters ce e m params args m') (hl : Mem.load chunk m b ofs = some v) :
    Mem.load chunk m' b ofs = some v := by
  induction h with
  | nil => exact hl
  | cons m id ty params v1 vl b0 m1 m2 he ha _ ih =>
    apply ih
    have hne := hb id b0 ty he
    cases ha with
    | value _ _ _ _ hs => exact storev_load_other hs hne hl
    | copy _ _ _ _ _ _ _ _ _ hs => exact load_storebytes_other_block hs hne hl

end SimplLocals
end CC
