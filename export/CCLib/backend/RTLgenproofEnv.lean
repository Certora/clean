/-
  Correctness of RTL generation — port of `backend/RTLgenproof.v`, part 1:
  well-formedness of compile-time mappings (`map_wf`, `init_mapping_wf`,
  `add_var_wf`, `add_vars_wf`, `add_letvar_wf`) and the matching between
  CminorSel and RTL environments (`match_env` and its lemmas, up to
  `match_init_env_init_reg`).
-/
import CCLib.backend.RTLgenspecStmt
import CCLib.backend.CminorSel

namespace CC
namespace RTLgen

open Op CminorSel RTL

/-- `RTLgenproof.map_wf` -/
structure MapWf (m : Mapping) : Prop where
  inj : ∀ id1 id2 r, m.map_vars.get id1 = some r → m.map_vars.get id2 = some r → id1 = id2
  disj : ∀ id r, m.map_vars.get id = some r → r ∈ m.map_letvars → False

/-- `RTLgenproof.init_mapping_wf` -/
theorem init_mapping_wf : MapWf initMapping :=
  ⟨fun _ _ _ h => by simp [initMapping] at h, fun _ _ h => by simp [initMapping] at h⟩

/-- `RTLgenproof.add_var_wf` -/
theorem add_var_wf {s1 s2 : State} {map : Mapping} {name : Ident} {r : Reg} {map' : Mapping}
    {i : StateIncr s1 s2} (h : addVar map name s1 = .OK (r, map') s2 i) (hw : MapWf map)
    (hv : MapValid map s1) : MapWf map' := by
  obtain ⟨i', h1, rfl⟩ := add_var_inv h
  have FR := new_reg_fresh h1
  constructor
  · intro id1 id2 r0 A B
    simp only at A B
    rw [PTree.gsspec] at A B
    by_cases e1 : id1 = name <;> by_cases e2 : id2 = name <;> simp only [e1, e2, ↓reduceIte] at A B
    · subst e1; subst e2; rfl
    · cases A
      exact absurd (hv _ (.inl ⟨id2, B⟩)) FR
    · cases B
      exact absurd (hv _ (.inl ⟨id1, A⟩)) FR
    · exact hw.inj _ _ _ A B
  · intro id _ A B
    simp only at A B
    rw [PTree.gsspec] at A
    split at A
    · cases A
      exact FR (hv _ (.inr B))
    · exact hw.disj _ _ A B

/-- `RTLgenproof.add_vars_wf` -/
theorem add_vars_wf :
    ∀ (names : List Ident) {s1 s2 : State} {map map' : Mapping} {rl : List Reg}
      {i : StateIncr s1 s2}, addVars map names s1 = .OK (rl, map') s2 i →
      MapWf map → MapValid map s1 → MapWf map'
  | [], _, _, _, _, _, _, h, hw, _ => by cases h; exact hw
  | n1 :: nl, _, _, _, _, _, _, h, hw, hv => by
    unfold addVars at h
    obtain ⟨rl1, map1, s, i1, i2, h1, h⟩ := bind2_inv h
    obtain ⟨r1, map2, s', i3, i4, h2, h⟩ := bind2_inv h
    cases h
    exact add_var_wf h2 (add_vars_wf nl h1 hw hv) (add_vars_valid nl h1 hv).2

/-- `RTLgenproof.add_letvar_wf` -/
theorem add_letvar_wf {map : Mapping} {r : Reg} (hw : MapWf map) (hr : ¬ RegInMap map r) :
    MapWf (addLetvar map r) := by
  refine ⟨hw.inj, fun id r0 A B => ?_⟩
  cases B with
  | head => exact hr (.inl ⟨id, A⟩)
  | tail _ B => exact hw.disj _ _ A B

/-! ## Matching between environments -/

/-- `RTLgenproof.match_env` -/
structure MatchEnv (map : Mapping) (e : Cminor.Env) (le : Letenv) (rs : Regset) : Prop where
  vars : ∀ id v, e.get id = some v → ∃ r, map.map_vars.get id = some r ∧ Val.Lessdef v (rs.get r)
  letvars : Val.LessdefList le (rs.getList map.map_letvars)

/-- `RTLgenproof.match_env_find_var` -/
theorem match_env_find_var {map : Mapping} {e : Cminor.Env} {le : Letenv} {rs : Regset}
    {id : Ident} {v : Val} {r : Reg} (hm : MatchEnv map e le rs) (he : e.get id = some v)
    (hr : map.map_vars.get id = some r) : Val.Lessdef v (rs.get r) := by
  obtain ⟨r', A, B⟩ := hm.vars _ _ he
  rw [hr] at A; cases A; exact B

theorem lessdefList_nth {rs : Regset} :
    ∀ {l : List Reg} {le : Letenv} {idx : Nat} {v : Val} {r : Reg},
    Val.LessdefList le (rs.getList l) → le[idx]? = some v → l[idx]? = some r →
    Val.Lessdef v (rs.get r)
  | [], _, _, _, _, _, _, h => by simp at h
  | r1 :: l, le, idx, v, r, hl, h1, h2 => by
    cases hl with
    | cons hv hl' =>
      cases idx with
      | zero => simp at h1 h2; subst h1; subst h2; exact hv
      | succ n => simp at h1 h2; exact lessdefList_nth hl' h1 h2

/-- `RTLgenproof.match_env_find_letvar` -/
theorem match_env_find_letvar {map : Mapping} {e : Cminor.Env} {le : Letenv} {rs : Regset}
    {idx : Nat} {v : Val} {r : Reg} (hm : MatchEnv map e le rs) (h1 : le[idx]? = some v)
    (h2 : map.map_letvars[idx]? = some r) : Val.Lessdef v (rs.get r) :=
  lessdefList_nth hm.letvars h1 h2

theorem getList_exten {rs rs' : Regset} :
    ∀ (l : List Reg), (∀ r, r ∈ l → rs'.get r = rs.get r) → rs'.getList l = rs.getList l
  | [], _ => rfl
  | r :: l, h => by
    show rs'.get r :: rs'.getList l = rs.get r :: rs.getList l
    rw [h r (.head _), getList_exten l (fun r' hr => h r' (.tail _ hr))]

/-- `RTLgenproof.match_env_invariant` -/
theorem match_env_invariant {map : Mapping} {e : Cminor.Env} {le : Letenv} {rs rs' : Regset}
    (hm : MatchEnv map e le rs) (h : ∀ r, RegInMap map r → rs'.get r = rs.get r) :
    MatchEnv map e le rs' := by
  refine ⟨fun id v hv => ?_, ?_⟩
  · obtain ⟨r, A, B⟩ := hm.vars _ _ hv
    exact ⟨r, A, by rw [h r (.inl ⟨id, A⟩)]; exact B⟩
  · rw [getList_exten _ (fun r hr => h r (.inr hr))]
    exact hm.letvars

/-- `RTLgenproof.match_env_update_temp` -/
theorem match_env_update_temp {map : Mapping} {e : Cminor.Env} {le : Letenv} {rs : Regset}
    {r : Reg} {v : Val} (hm : MatchEnv map e le rs) (hr : ¬ RegInMap map r) :
    MatchEnv map e le (rs.set r v) :=
  match_env_invariant hm (fun _ h0 => PMap.gso _ _ _ _ (fun he => hr (he ▸ h0)))

/-- `RTLgenproof.match_env_update_var` -/
theorem match_env_update_var {map : Mapping} {e : Cminor.Env} {le : Letenv} {rs : Regset}
    {id : Ident} {r : Reg} {v tv : Val} (hv : Val.Lessdef v tv) (hw : MapWf map)
    (hr : map.map_vars.get id = some r) (hm : MatchEnv map e le rs) :
    MatchEnv map (PTree.set id v e) le (rs.set r tv) := by
  refine ⟨fun id' v' h => ?_, ?_⟩
  · rw [PTree.gsspec] at h
    split at h
    · next he => subst he; cases h; exact ⟨r, hr, by rw [PMap.gss]; exact hv⟩
    · next hne =>
      obtain ⟨r', A, B⟩ := hm.vars _ _ h
      refine ⟨r', A, ?_⟩
      rw [PMap.gso]
      · exact B
      · rintro rfl; exact hne (hw.inj _ _ _ A hr)
  · rw [getList_exten _ (fun r' hr' => PMap.gso _ _ _ _ (fun he => hw.disj _ _ hr (by subst he; exact hr')))]
    exact hm.letvars

/-- `RTLgenproof.match_env_update_dest` -/
theorem match_env_update_dest {map : Mapping} {e : Cminor.Env} {le : Letenv} {rs : Regset}
    {dst : Option Ident} {r : Reg} {v tv : Val} (hv : Val.Lessdef v tv) (hw : MapWf map)
    (hd : RegMapOk map r dst) (hm : MatchEnv map e le rs) :
    MatchEnv map (Cminor.setOptvar dst v e) le (rs.set r tv) := by
  cases hd with
  | novar h => exact match_env_update_temp hm h
  | somevar _ h => exact match_env_update_var hv hw h hm

/-- `RTLgenproof.match_env_update_res` -/
theorem match_env_update_res {map : Mapping} {res : BuiltinRes Ident} {v : Val} {e : Cminor.Env}
    {le : Letenv} {tres : BuiltinRes Reg} {tv : Val} {rs : Regset} (hv : Val.Lessdef v tv)
    (hw : MapWf map) (ht : TrBuiltinRes map res tres) (hm : MatchEnv map e le rs) :
    MatchEnv map (setBuiltinRes res v e) le (regmapSetres tres tv rs) := by
  cases ht with
  | var id r h => exact match_env_update_var hv hw h hm
  | none => exact hm
  | fresh r h => exact match_env_update_temp hm h

/-- `RTLgenproof.match_env_bind_letvar` -/
theorem match_env_bind_letvar {map : Mapping} {e : Cminor.Env} {le : Letenv} {rs : Regset}
    {r : Reg} {v : Val} (hm : MatchEnv map e le rs) (hv : Val.Lessdef v (rs.get r)) :
    MatchEnv (addLetvar map r) e (v :: le) rs :=
  ⟨hm.vars, .cons hv hm.letvars⟩

/-- `RTLgenproof.match_env_unbind_letvar` -/
theorem match_env_unbind_letvar {map : Mapping} {e : Cminor.Env} {le : Letenv} {rs : Regset}
    {r : Reg} {v : Val} (hm : MatchEnv (addLetvar map r) e (v :: le) rs) : MatchEnv map e le rs := by
  refine ⟨hm.vars, ?_⟩
  have := hm.letvars
  cases this with
  | cons _ h => exact h

/-- `RTLgenproof.match_env_empty` -/
theorem match_env_empty {map : Mapping} (h : map.map_letvars = []) :
    MatchEnv map PTree.empty [] (PMap.init .Vundef) := by
  refine ⟨fun id v hv => by simp at hv, ?_⟩
  rw [h]; exact .nil

theorem initRegs_nil (rl : List Reg) : initRegs [] rl = PMap.init .Vundef := by
  cases rl <;> rfl

theorem initRegs_nilr (vl : List Val) : initRegs vl [] = PMap.init .Vundef := by
  cases vl <;> rfl

/-- `RTLgenproof.match_set_params_init_regs` -/
theorem match_set_params_init_regs :
    ∀ (il : List Ident) {rl : List Reg} {s1 : State} {map2 : Mapping} {s2 : State}
      {vl tvl : List Val} {i : StateIncr s1 s2},
    addVars initMapping il s1 = .OK (rl, map2) s2 i → Val.LessdefList vl tvl →
    MatchEnv map2 (Cminor.setParams vl il) [] (initRegs tvl rl) ∧
      (∀ r, RegFresh r s2 → (initRegs tvl rl).get r = .Vundef)
  | [], _, _, _, _, vl, tvl, _, h, hl => by
    cases h
    refine ⟨?_, fun r _ => by rw [initRegs_nilr]; exact PMap.gi _ _⟩
    have : Cminor.setParams vl [] = PTree.empty := by cases vl <;> rfl
    rw [this, initRegs_nilr]
    exact match_env_empty rfl
  | a :: il, _, _, _, _, vl, tvl, _, h, hl => by
    unfold addVars at h
    obtain ⟨rl', map1, s, i1, i2, EQ, h⟩ := bind2_inv h
    obtain ⟨x1, map2', s', i3, i4, EQ1, h⟩ := bind2_inv h
    cases h
    obtain ⟨_, B⟩ := add_vars_valid il EQ (init_mapping_valid _)
    obtain ⟨i', hnr, rfl⟩ := add_var_inv EQ1
    have FR := new_reg_fresh hnr
    have RV := new_reg_valid hnr
    cases hl with
    | nil =>
      obtain ⟨ME, UNDEF⟩ := match_set_params_init_regs il EQ .nil
      rw [initRegs_nil] at ME ⊢
      refine ⟨⟨fun id v hv => ?_, ME.letvars⟩, fun r _ => PMap.gi _ _⟩
      replace hv : (PTree.set a .Vundef (Cminor.setParams [] il)).get id = some v := hv
      rw [PTree.gsspec] at hv
      split at hv
      · next he => subst he; cases hv; exact ⟨x1, PTree.gss _ _ _, .undef _⟩
      · next hne =>
        obtain ⟨r, A, B⟩ := ME.vars _ _ hv
        exact ⟨r, by show (PTree.set a x1 map1.map_vars).get id = _; rw [PTree.gso _ _ _ _ (Ne.symm hne)]; exact A, B⟩
    | cons hv1 hl' =>
      rename_i v1 tv1 vs tvs
      obtain ⟨ME, UNDEF⟩ := match_set_params_init_regs il EQ hl'
      refine ⟨⟨fun id v hv => ?_, ?_⟩, fun r hr => ?_⟩
      · replace hv : (PTree.set a v1 (Cminor.setParams vs il)).get id = some v := hv
        rw [PTree.gsspec] at hv
        split at hv
        · next he =>
          subst he; cases hv
          exact ⟨x1, PTree.gss _ _ _, by show Val.Lessdef v1 (((initRegs tvs rl').set x1 tv1).get x1); rw [PMap.gss]; exact hv1⟩
        · next hne =>
          obtain ⟨r', C, D⟩ := ME.vars _ _ hv
          refine ⟨r', by show (PTree.set a x1 map1.map_vars).get id = _; rw [PTree.gso _ _ _ _ (Ne.symm hne)]; exact C, ?_⟩
          show Val.Lessdef v (((initRegs tvs rl').set x1 tv1).get r')
          rw [PMap.gso]
          · exact D
          · exact (valid_fresh_different (B r' (.inl ⟨id, C⟩)) FR).symm
      · have hlv := ME.letvars
        show Val.LessdefList [] (Regmap.getList ((initRegs tvs rl').set x1 tv1) map1.map_letvars)
        cases hml : map1.map_letvars with
        | nil => exact .nil
        | cons r0 l0 => rw [hml] at hlv; cases hlv
      · show ((initRegs tvs rl').set x1 tv1).get r = .Vundef
        rw [PMap.gso]
        · exact UNDEF r (reg_fresh_decr i' hr)
        · exact valid_fresh_different RV hr

/-- `RTLgenproof.match_set_locals` -/
theorem match_set_locals {map1 : Mapping} {s1 : State} (hw : MapWf map1) :
    ∀ (il : List Ident) {rl : List Reg} {map2 : Mapping} {s2 : State} {e : Cminor.Env}
      {le : Letenv} {rs : Regset} {i : StateIncr s1 s2},
    MatchEnv map1 e le rs → (∀ r, RegFresh r s1 → rs.get r = .Vundef) →
    addVars map1 il s1 = .OK (rl, map2) s2 i → MatchEnv map2 (Cminor.setLocals il e) le rs
  | [], _, _, _, _, _, _, _, hm, _, h => by cases h; exact hm
  | a :: il, _, _, _, e, le, rs, _, hm, hu, h => by
    unfold addVars at h
    obtain ⟨rl', map1', s, i1, i2, EQ, h⟩ := bind2_inv h
    obtain ⟨x1, map2', s', i3, i4, EQ1, h⟩ := bind2_inv h
    cases h
    have ME := match_set_locals hw il hm hu EQ
    obtain ⟨i', hnr, rfl⟩ := add_var_inv EQ1
    refine ⟨fun id v hv => ?_, ME.letvars⟩
    replace hv : (PTree.set a .Vundef (Cminor.setLocals il e)).get id = some v := hv
    rw [PTree.gsspec] at hv
    split at hv
    · next he =>
      subst he; cases hv
      exact ⟨x1, PTree.gss _ _ _, by rw [hu x1 (reg_fresh_decr i1 (new_reg_fresh hnr))]; exact .refl _⟩
    · next hne =>
      obtain ⟨r, A, B⟩ := ME.vars _ _ hv
      exact ⟨r, by show (PTree.set a x1 map1'.map_vars).get id = _; rw [PTree.gso _ _ _ _ (Ne.symm hne)]; exact A, B⟩

/-- `RTLgenproof.match_init_env_init_reg` -/
theorem match_init_env_init_reg {params : List Ident} {s0 : State} {rparams : List Reg}
    {map1 : Mapping} {s1 : State} {i1 : StateIncr s0 s1} {vars : List Ident} {rvars : List Reg}
    {map2 : Mapping} {s2 : State} {i2 : StateIncr s1 s2} {vparams tvparams : List Val}
    (h1 : addVars initMapping params s0 = .OK (rparams, map1) s1 i1)
    (h2 : addVars map1 vars s1 = .OK (rvars, map2) s2 i2)
    (hl : Val.LessdefList vparams tvparams) :
    MatchEnv map2 (Cminor.setLocals vars (Cminor.setParams vparams params)) []
      (initRegs tvparams rparams) := by
  obtain ⟨A, B⟩ := match_set_params_init_regs params h1 hl
  exact match_set_locals (add_vars_wf params h1 init_mapping_wf (init_mapping_valid _)) vars A B h2

end RTLgen
end CC
