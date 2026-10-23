/-
  Correctness of Cminor generation — port of `cfrontend/Cminorgenproof.v`,
  part 2: correctness of the stack allocation of local variables
  (`cenv_remove`, `cenv_compat`, `cenv_separated`, `cenv_mem_separated`,
  `match_callstack_alloc_variables_rec`, `match_callstack_alloc_variables`),
  properties of the compilation environment produced by `build_compilenv`
  (`assign_variable(s)_sound`, `build_compilenv_sound`,
  `build_compilenv_domain`), initialization of temporaries and local
  variables (`set_params'`, `bind_parameters_agree`) and the main result
  `match_callstack_function_entry`.

  Differences from Rocq: `Mem.inj_offset_aligned ofs sz` is replaced by the
  equivalent `minSafeAlignment sz ∣ ofs`, which is the form taken by the
  port's `Mem.alloc_left_mapped_inject`.
-/
import CCLib.cfrontend.CminorgenproofEnv

namespace CC
namespace Cminorgen

open Smallstep

local macro "blk_omega" : tactic =>
  `(tactic| (simp only [Positive.lt_iff, pos_le_iff, Positive.toNat_succ] at *; omega))

local macro "zomega" : tactic => `(tactic| ((try dsimp only [CC.Z] at *) <;> omega))

variable {ge : Csharpminor.CGenv}

/-! ## Compilation environments -/

/-- `Cminorgenproof.cenv_remove` -/
def cenvRemove (cenv : Compilenv) (vars : List (Ident × Z)) : Compilenv :=
  vars.foldr (fun idlv ce => PTree.remove idlv.1 ce) cenv

/-- `Cminorgenproof.cenv_remove_gso` -/
theorem cenv_remove_gso {id : Ident} : ∀ {vars : List (Ident × Z)} {cenv : Compilenv},
    id ∉ vars.map Prod.fst → (cenvRemove cenv vars).get id = cenv.get id
  | [], _, _ => rfl
  | (id', sz) :: vars, cenv, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [cenvRemove, List.foldr_cons]
    rw [PTree.gro _ _ _ (Ne.symm h.1)]
    exact cenv_remove_gso h.2

/-- `Cminorgenproof.cenv_remove_gss` -/
theorem cenv_remove_gss {id : Ident} : ∀ {vars : List (Ident × Z)} {cenv : Compilenv},
    id ∈ vars.map Prod.fst → (cenvRemove cenv vars).get id = none
  | [], _, h => by simp at h
  | (id', sz) :: vars, cenv, h => by
    simp only [cenvRemove, List.foldr_cons]
    rw [PTree.grspec]
    split
    · rfl
    · rename_i hne
      simp only [List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · exact absurd h hne
      · exact cenv_remove_gss h

/-- `Cminorgenproof.cenv_compat` (with `Mem.inj_offset_aligned ofs sz`
    expressed as `minSafeAlignment sz ∣ ofs`). -/
def CenvCompat (cenv : Compilenv) (vars : List (Ident × Z)) (tsz : Z) : Prop :=
  ∀ id sz, (id, sz) ∈ vars → ∃ ofs, cenv.get id = some ofs ∧ minSafeAlignment sz ∣ ofs ∧
    0 ≤ ofs ∧ ofs + max 0 sz ≤ tsz

/-- `Cminorgenproof.cenv_separated` -/
def CenvSeparated (cenv : Compilenv) (vars : List (Ident × Z)) : Prop :=
  ∀ id1 sz1 ofs1 id2 sz2 ofs2, (id1, sz1) ∈ vars → (id2, sz2) ∈ vars →
    cenv.get id1 = some ofs1 → cenv.get id2 = some ofs2 → id1 ≠ id2 →
    ofs1 + sz1 ≤ ofs2 ∨ ofs2 + sz2 ≤ ofs1

/-- `Cminorgenproof.cenv_mem_separated` -/
def CenvMemSeparated (cenv : Compilenv) (vars : List (Ident × Z)) (f : Val.Meminj) (sp : Block)
    (m : Mem) : Prop :=
  ∀ id sz ofs b delta ofs' k p, (id, sz) ∈ vars → cenv.get id = some ofs →
    f b = some (sp, delta) → Mem.perm m b ofs' k p = true →
    ofs ≤ ofs' + delta → ofs' + delta < sz + ofs → False

/-- `Cminorgenproof.match_callstack_alloc_variables_rec` -/
theorem match_callstack_alloc_variables_rec {tm : Mem} {sp : Block} {tf : Cminor.Function}
    {cenv : Compilenv} {le : Csharpminor.TempEnv} {te : Cminor.Env} {lo : Block} {cs : Callstack}
    (VALID : Mem.validBlock tm sp = true)
    (REPRES : tf.fn_stackspace ≤ Integers.Ptrofs.max_unsigned)
    (STKSIZE : ∀ ofs k p, Mem.perm tm sp ofs k p = true → 0 ≤ ofs ∧ ofs < tf.fn_stackspace)
    (STKPERMS : ∀ ofs k p, 0 ≤ ofs → ofs < tf.fn_stackspace → Mem.perm tm sp ofs k p = true) :
    ∀ {e1 m1 vars e2 m2}, Csharpminor.AllocVariables e1 m1 vars e2 m2 → ∀ (f1 : Val.Meminj),
    (vars.map Prod.fst).Nodup →
    CenvCompat cenv vars tf.fn_stackspace →
    CenvSeparated cenv vars →
    CenvMemSeparated cenv vars f1 sp m1 →
    (∀ id sz, (id, sz) ∈ vars → e1.get id = none) →
    MatchCallstack ge f1 m1 tm
      (⟨cenvRemove cenv vars, tf, e1, le, te, sp, lo, m1.nextblock⟩ :: cs) m1.nextblock tm.nextblock →
    Mem.Inject f1 m1 tm →
    ∃ f2, MatchCallstack ge f2 m2 tm (⟨cenv, tf, e2, le, te, sp, lo, m2.nextblock⟩ :: cs)
        m2.nextblock tm.nextblock ∧ Mem.Inject f2 m2 tm := by
  intro e1 m1 vars e2 m2 hav
  induction hav with
  | nil e m =>
    intro f1 _ _ _ _ _ MCS MINJ
    exact ⟨f1, MCS, MINJ⟩
  | cons e m id sz vars m1 b1 m2 e2 ha _ ih =>
    intro f1 NOREPET COMPAT SEP1 SEP2 UNBOUND MCS MINJ
    simp only [List.map_cons, List.nodup_cons] at NOREPET
    obtain ⟨NOTIN, NOREPET⟩ := NOREPET
    obtain ⟨ofs, CENV, ALIGNED, LOB, HIB⟩ := COMPAT id sz (List.mem_cons_self ..)
    have hmax1 : sz ≤ max 0 sz := Int.le_max_right 0 sz
    have hmax2 : 0 ≤ max 0 sz := Int.le_max_left 0 sz
    obtain ⟨f2, A, B, C, D⟩ := Mem.alloc_left_mapped_inject (delta := ofs) MINJ ha VALID
      ⟨LOB, by zomega⟩ (.inr (Int.le_refl 0))
      (fun ofs' k p hp => .inr (by have := STKSIZE ofs' k p hp; zomega))
      (fun ofs' k p h1 h2 => STKPERMS _ k p (by zomega) (by zomega))
      (by rw [Int.sub_zero]; exact ALIGNED)
      (fun b delta' ofs' k p hf hp h1 h2 =>
        SEP2 id sz ofs b delta' ofs' k p (List.mem_cons_self ..) CENV hf hp (by zomega) (by zomega))
    obtain ⟨rfl, rfl⟩ := Mem.alloc_eq ha
    refine ih f2 NOREPET (fun id' sz' h => COMPAT id' sz' (List.mem_cons_of_mem _ h))
      (fun id1 sz1 ofs1 id2 sz2 ofs2 h1 h2 => SEP1 id1 sz1 ofs1 id2 sz2 ofs2
        (List.mem_cons_of_mem _ h1) (List.mem_cons_of_mem _ h2)) ?_ ?_ ?_ A
    · intro id0 sz0 ofs0 b delta ofs' k p hin hc hf hp h1 h2
      have P := Mem.perm_alloc_inv hp
      split at P
      · rename_i hb; subst hb
        rw [C] at hf; cases hf
        have hne : id ≠ id0 := by
          intro he; subst he
          exact NOTIN (List.mem_map_of_mem (f := Prod.fst) hin)
        rcases SEP1 id sz ofs id0 sz0 ofs0 (List.mem_cons_self ..) (List.mem_cons_of_mem _ hin)
          CENV hc hne with h | h <;> zomega
      · rename_i hb
        rw [D b hb] at hf
        exact SEP2 id0 sz0 ofs0 b delta ofs' k p (List.mem_cons_of_mem _ hin) hc hf P h1 h2
    · intro id0 sz0 hin
      rw [PTree.gso]
      · exact UNBOUND id0 sz0 (List.mem_cons_of_mem _ hin)
      · intro he; subst he; exact NOTIN (List.mem_map_of_mem (f := Prod.fst) hin)
    · refine match_callstack_alloc_left (cenv := cenvRemove cenv vars) MCS ha ?_ B C D
        (UNBOUND id sz (List.mem_cons_self ..))
      rw [cenv_remove_gso NOTIN]; exact CENV

/-- `Cminorgenproof.match_callstack_alloc_variables` -/
theorem match_callstack_alloc_variables {tm1 : Mem} {sp : Block} {tm2 m1 : Mem}
    {vars : List (Ident × Z)} {e : Csharpminor.Env} {m2 : Mem} {cenv : Compilenv}
    {f1 : Val.Meminj} {cs : Callstack} {fn : Cminor.Function} {le : Csharpminor.TempEnv}
    {te : Cminor.Env}
    (ALLOC : Mem.alloc tm1 0 fn.fn_stackspace = (tm2, sp))
    (REPRES : fn.fn_stackspace ≤ Integers.Ptrofs.max_unsigned)
    (AV : Csharpminor.AllocVariables Csharpminor.emptyEnv m1 vars e m2)
    (NOREPET : (vars.map Prod.fst).Nodup)
    (COMPAT : CenvCompat cenv vars fn.fn_stackspace) (SEP : CenvSeparated cenv vars)
    (DOM : ∀ id ofs, cenv.get id = some ofs → id ∈ vars.map Prod.fst)
    (MINJ : Mem.Inject f1 m1 tm1)
    (MCS : MatchCallstack ge f1 m1 tm1 cs m1.nextblock tm1.nextblock)
    (MTMP : MatchTemps f1 le te) :
    ∃ f2, MatchCallstack ge f2 m2 tm2 (⟨cenv, fn, e, le, te, sp, m1.nextblock, m2.nextblock⟩ :: cs)
        m2.nextblock tm2.nextblock ∧ Mem.Inject f2 m2 tm2 := by
  have MCS' := match_callstack_alloc_right (cenv := cenvRemove cenv vars) MCS ALLOC MINJ MTMP ?_
  · have MINJ' := Mem.alloc_right_inject MINJ ALLOC
    obtain ⟨rfl, rfl⟩ := Mem.alloc_eq ALLOC
    refine match_callstack_alloc_variables_rec
      (by have := Mem.valid_new_block tm1 0 fn.fn_stackspace; simpa using this) REPRES ?_ ?_ AV f1
      NOREPET COMPAT SEP ?_ (fun _ _ _ => by simp [Csharpminor.emptyEnv]) MCS' MINJ'
    · intro ofs k p hp
      have := Mem.perm_alloc_inv hp
      rw [if_pos rfl] at this
      exact this
    · intro ofs k p h1 h2
      exact Mem.perm_implies (Mem.perm_alloc_same _ _ _ _ _ h1 h2) (by cases p <;> rfl)
    · intro id sz ofs b delta ofs' k p _ _ hf _ _ _
      have := Mem.validBlock_inject_2 hf MINJ
      rw [Mem.fresh_block_alloc] at this; cases this
  · intro id
    by_cases hin : id ∈ vars.map Prod.fst
    · exact cenv_remove_gss hin
    · rw [cenv_remove_gso hin]
      cases hc : cenv.get id with
      | none => rfl
      | some ofs => exact absurd (DOM id ofs hc) hin

/-! ## Properties of the compilation environment produced by `build_compilenv` -/

/-- `Cminorgenproof.assign_variable_incr` -/
theorem assign_variable_incr {id : Ident} {sz : Z} {cenv : Compilenv} {stksz : Z}
    {cenv' : Compilenv} {stksz' : Z} (h : assignVariable (cenv, stksz) (id, sz) = (cenv', stksz')) :
    stksz ≤ stksz' := by
  simp only [assignVariable, Prod.mk.injEq] at h
  obtain ⟨_, rfl⟩ := h
  have h1 := align_le stksz (minSafeAlignment sz) (minSafeAlignment_pos sz)
  have h2 : 0 ≤ max 0 sz := Int.le_max_left 0 sz
  zomega

/-- `Cminorgenproof.assign_variables_incr` -/
theorem assign_variables_incr : ∀ {vars : List (Ident × Z)} {cenv : Compilenv} {sz : Z}
    {cenv' : Compilenv} {sz' : Z}, assignVariables (cenv, sz) vars = (cenv', sz') → sz ≤ sz'
  | [], _, _, _, _, h => by
    simp only [assignVariables, List.foldl_nil, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h; exact Int.le_refl _
  | (id, s) :: vars, cenv, sz, cenv', sz', h => by
    change assignVariables (assignVariable (cenv, sz) (id, s)) vars = _ at h
    rcases h1 : assignVariable (cenv, sz) (id, s) with ⟨cenv1, sz1⟩
    rw [h1] at h
    exact Int.le_trans (assign_variable_incr h1) (assign_variables_incr h)

/-- `Cminorgenproof.assign_variable_sound` -/
theorem assign_variable_sound {cenv1 : Compilenv} {sz1 : Z} {id : Ident} {sz : Z}
    {cenv2 : Compilenv} {sz2 : Z} {vars : List (Ident × Z)}
    (ASV : assignVariable (cenv1, sz1) (id, sz) = (cenv2, sz2))
    (NOREPET : id ∉ vars.map Prod.fst) (POS : 0 ≤ sz1)
    (COMPAT : CenvCompat cenv1 vars sz1) (SEP : CenvSeparated cenv1 vars) :
    CenvCompat cenv2 (vars ++ [(id, sz)]) sz2 ∧ CenvSeparated cenv2 (vars ++ [(id, sz)]) := by
  simp only [assignVariable, Prod.mk.injEq] at ASV
  obtain ⟨rfl, rfl⟩ := ASV
  have LE := align_le sz1 (minSafeAlignment sz) (minSafeAlignment_pos sz)
  have hmax1 : sz ≤ max 0 sz := Int.le_max_right 0 sz
  have hmax2 : 0 ≤ max 0 sz := Int.le_max_left 0 sz
  have EITHER : ∀ id' sz', (id', sz') ∈ vars ++ [(id, sz)] →
      ((id', sz') ∈ vars ∧ id' ≠ id) ∨ (id', sz') = (id, sz) := by
    intro id' sz' h
    rcases List.mem_append.mp h with h1 | h1
    · refine .inl ⟨h1, ?_⟩
      intro he; apply NOREPET; rw [← he]; exact List.mem_map_of_mem (f := Prod.fst) h1
    · simp only [List.mem_singleton] at h1; exact .inr h1
  constructor
  · intro id' sz' h
    rcases EITHER id' sz' h with ⟨P, Q⟩ | P
    · obtain ⟨ofs, A, B, C, D⟩ := COMPAT id' sz' P
      refine ⟨ofs, ?_, B, C, ?_⟩
      · rw [PTree.gso _ _ _ _ (Ne.symm Q)]; exact A
      · have := Int.le_max_left 0 sz'; zomega
    · simp only [Prod.mk.injEq] at P; obtain ⟨rfl, rfl⟩ := P
      exact ⟨_, PTree.gss _ _ _, align_divides _ _, by zomega, by zomega⟩
  · intro i1 s1 o1 i2 s2 o2 h1 h2 g1 g2 hne
    rcases EITHER i1 s1 h1 with ⟨P, Q⟩ | P <;> rcases EITHER i2 s2 h2 with ⟨R, S⟩ | R
    · rw [PTree.gso _ _ _ _ (Ne.symm Q)] at g1
      rw [PTree.gso _ _ _ _ (Ne.symm S)] at g2
      exact SEP i1 s1 o1 i2 s2 o2 P R g1 g2 hne
    · simp only [Prod.mk.injEq] at R; obtain ⟨rfl, rfl⟩ := R
      rw [PTree.gso _ _ _ _ (Ne.symm Q)] at g1
      rw [PTree.gss] at g2; cases g2
      obtain ⟨ofs, A, _, _, D⟩ := COMPAT i1 s1 P
      rw [A] at g1; cases g1
      have := Int.le_max_right 0 s1
      exact .inl (by zomega)
    · simp only [Prod.mk.injEq] at P; obtain ⟨rfl, rfl⟩ := P
      rw [PTree.gso _ _ _ _ (Ne.symm S)] at g2
      rw [PTree.gss] at g1; cases g1
      obtain ⟨ofs, A, _, _, D⟩ := COMPAT i2 s2 R
      rw [A] at g2; cases g2
      have := Int.le_max_right 0 s2
      exact .inr (by zomega)
    · simp only [Prod.mk.injEq] at P R
      exact absurd (P.1.trans R.1.symm) hne

/-- `Cminorgenproof.assign_variables_sound` -/
theorem assign_variables_sound : ∀ {vars' : List (Ident × Z)} {cenv1 : Compilenv} {sz1 : Z}
    {cenv2 : Compilenv} {sz2 : Z} {vars : List (Ident × Z)},
    assignVariables (cenv1, sz1) vars' = (cenv2, sz2) →
    (vars'.map Prod.fst ++ vars.map Prod.fst).Nodup → 0 ≤ sz1 →
    CenvCompat cenv1 vars sz1 → CenvSeparated cenv1 vars →
    CenvCompat cenv2 (vars ++ vars') sz2 ∧ CenvSeparated cenv2 (vars ++ vars')
  | [], cenv1, sz1, cenv2, sz2, vars, h, _, _, C, S => by
    simp only [assignVariables, List.foldl_nil, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [List.append_nil]; exact ⟨C, S⟩
  | (id, sz) :: vars', cenv1, sz1, cenv2, sz2, vars, h, NR, POS, C, S => by
    change assignVariables (assignVariable (cenv1, sz1) (id, sz)) vars' = _ at h
    rcases h1 : assignVariable (cenv1, sz1) (id, sz) with ⟨cenv', sz'⟩
    rw [h1] at h
    simp only [List.map_cons, List.cons_append, List.nodup_cons, List.mem_append, not_or] at NR
    obtain ⟨⟨N1, N2⟩, NR⟩ := NR
    obtain ⟨A, B⟩ := assign_variable_sound h1 N2 POS C S
    have := assign_variables_sound (vars := vars ++ [(id, sz)]) h ?_
      (Int.le_trans POS (assign_variable_incr h1)) A B
    · rw [List.append_assoc] at this; exact this
    · rw [List.nodup_append] at NR ⊢
      obtain ⟨P, Q, R⟩ := NR
      refine ⟨P, ?_, ?_⟩
      · rw [List.map_append, List.nodup_append]
        refine ⟨Q, by simp, ?_⟩
        intro a ha b hb
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
        subst hb; intro he; subst he; exact N2 ha
      · intro a ha b hb
        rw [List.map_append, List.mem_append] at hb
        rcases hb with hb | hb
        · exact R a ha b hb
        · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
          subst hb; intro he; subst he; exact N1 ha

/-- `Cminorgenproof.build_compilenv_sound` -/
theorem build_compilenv_sound {f : Csharpminor.Function} {cenv : Compilenv} {sz : Z}
    (h : buildCompilenv f = (cenv, sz)) (NR : (f.fn_vars.map Prod.fst).Nodup) :
    CenvCompat cenv f.fn_vars sz ∧ CenvSeparated cenv f.fn_vars := by
  have P := varSort_perm f.fn_vars
  have hNR : ((varSort f.fn_vars).map Prod.fst ++ ([] : List (Ident × Z)).map Prod.fst).Nodup := by
    rw [List.map_nil, List.append_nil]
    exact ((P.map Prod.fst).nodup_iff).mpr NR
  obtain ⟨A, B⟩ := assign_variables_sound (vars := []) h hNR (Int.le_refl 0)
    (fun _ _ h => by simp at h) (fun _ _ _ _ _ _ h => by simp at h)
  rw [List.nil_append] at A B
  exact ⟨fun id sz' hin => A id sz' (P.mem_iff.mpr hin),
    fun i1 s1 o1 i2 s2 o2 h1 h2 => B i1 s1 o1 i2 s2 o2 (P.mem_iff.mpr h1) (P.mem_iff.mpr h2)⟩

/-- `Cminorgenproof.assign_variables_domain` -/
theorem assign_variables_domain {id : Ident} : ∀ {vars : List (Ident × Z)} {cesz : Compilenv × Z},
    (assignVariables cesz vars).1.get id ≠ none → cesz.1.get id ≠ none ∨ id ∈ vars.map Prod.fst
  | [], _, h => .inl h
  | (id1, sz1) :: vars, (cenv, stksz), h => by
    change (assignVariables (assignVariable (cenv, stksz) (id1, sz1)) vars).1.get id ≠ none at h
    rcases assign_variables_domain h with h' | h'
    · simp only [assignVariable] at h'
      rw [PTree.gsspec] at h'
      split at h'
      · rename_i he; subst he; exact .inr (List.mem_cons_self ..)
      · exact .inl h'
    · exact .inr (List.mem_cons_of_mem _ h')

/-- `Cminorgenproof.build_compilenv_domain` -/
theorem build_compilenv_domain {f : Csharpminor.Function} {cenv : Compilenv} {sz : Z} {id : Ident}
    {ofs : Z} (h : buildCompilenv f = (cenv, sz)) (hc : cenv.get id = some ofs) :
    id ∈ f.fn_vars.map Prod.fst := by
  have P := varSort_perm f.fn_vars
  have := assign_variables_domain (id := id) (vars := varSort f.fn_vars) (cesz := (PTree.empty, 0))
  simp only [buildCompilenv] at h
  rw [h] at this
  rcases this (by rw [hc]; simp) with h' | h'
  · simp at h'
  · exact (P.map Prod.fst).mem_iff.mp h'

/-! ## Initialization of Csharpminor temporaries and Cminor local variables -/

/-- `Cminorgenproof.create_undef_temps_val` -/
theorem create_undef_temps_val {id : Ident} {v : Val} : ∀ {temps : List Ident},
    (Csharpminor.createUndefTemps temps).get id = some v → id ∈ temps ∧ v = .Vundef
  | [], h => by simp [Csharpminor.createUndefTemps] at h
  | a :: temps, h => by
    simp only [Csharpminor.createUndefTemps] at h
    rw [PTree.gsspec] at h
    split at h
    · rename_i he; subst he; cases h; exact ⟨List.mem_cons_self .., rfl⟩
    · obtain ⟨A, B⟩ := create_undef_temps_val h
      exact ⟨List.mem_cons_of_mem _ A, B⟩

/-- `Cminorgenproof.set_params'` -/
def setParams' : List Val → List Ident → Cminor.Env → Cminor.Env
  | v1 :: vl, i1 :: il, te => setParams' vl il (te.set i1 v1)
  | [], i1 :: il, te => setParams' [] il (te.set i1 .Vundef)
  | _, [], te => te

/-- `Cminorgenproof.bind_parameters_agree_rec` -/
theorem bind_parameters_agree_rec {f : Val.Meminj} : ∀ {vars : List Ident} {vals tvals : List Val}
    {le1 le2 : Csharpminor.TempEnv} {te : Cminor.Env},
    Csharpminor.bindParameters vars vals le1 = some le2 → Val.InjectList f vals tvals →
    MatchTemps f le1 te → MatchTemps f le2 (setParams' tvals vars te)
  | [], vals, tvals, le1, le2, te, h, hi, hm => by
    cases vals with
    | nil => cases hi; simp only [Csharpminor.bindParameters, Option.some.injEq] at h; subst h
             exact hm
    | cons => simp [Csharpminor.bindParameters] at h
  | a :: vars, vals, tvals, le1, le2, te, h, hi, hm => by
    cases vals with
    | nil => simp [Csharpminor.bindParameters] at h
    | cons v vl =>
      cases hi with
      | cons hv hvl =>
        simp only [Csharpminor.bindParameters] at h
        simp only [setParams']
        exact bind_parameters_agree_rec h hvl (match_temps_assign hm hv)

/-- `Cminorgenproof.set_params'_outside` -/
theorem setParams'_outside {id : Ident} : ∀ {il : List Ident} {vl : List Val} {te : Cminor.Env},
    id ∉ il → (setParams' vl il te).get id = te.get id
  | [], vl, te, _ => by cases vl <;> rfl
  | a :: il, vl, te, h => by
    simp only [List.mem_cons, not_or] at h
    cases vl with
    | nil => simp only [setParams']; rw [setParams'_outside h.2, PTree.gso _ _ _ _ (Ne.symm h.1)]
    | cons v vl => simp only [setParams']; rw [setParams'_outside h.2, PTree.gso _ _ _ _ (Ne.symm h.1)]

/-- `Cminorgenproof.set_params'_inside` -/
theorem setParams'_inside {id : Ident} : ∀ {il : List Ident} {vl : List Val} {te1 te2 : Cminor.Env},
    id ∈ il → (setParams' vl il te1).get id = (setParams' vl il te2).get id
  | [], _, _, _, h => by simp at h
  | a :: il, vl, te1, te2, h => by
    by_cases hin : id ∈ il
    · cases vl <;> simp only [setParams'] <;> exact setParams'_inside hin
    · have ha : a = id := by
        rcases List.mem_cons.mp h with h | h
        · exact h.symm
        · exact absurd h hin
      subst ha
      cases vl <;> simp only [setParams'] <;> rw [setParams'_outside hin, setParams'_outside hin,
        PTree.gss, PTree.gss]

/-- `Cminorgenproof.set_params_set_params'` -/
theorem setParams_setParams' : ∀ {il : List Ident} {vl : List Val} {id : Ident},
    il.Nodup → (Cminor.setParams vl il).get id = (setParams' vl il PTree.empty).get id
  | [], vl, id, _ => by cases vl <;> simp [Cminor.setParams, setParams']
  | a :: il, vl, id, h => by
    rw [List.nodup_cons] at h
    have key : ∀ v, (PTree.set a v (Cminor.setParams (vl.drop 1) il)).get id =
        (setParams' (vl.drop 1) il (PTree.set a v PTree.empty)).get id := by
      intro v
      rw [PTree.gsspec]
      split
      · rename_i he; subst he; rw [setParams'_outside h.1, PTree.gss]
      · rename_i hne
        rw [setParams_setParams' h.2]
        by_cases hin : id ∈ il
        · exact setParams'_inside hin
        · rw [setParams'_outside hin, setParams'_outside hin, PTree.gso _ _ _ _ (Ne.symm hne)]
    cases vl with
    | nil => exact key .Vundef
    | cons v vl => exact key v

/-- `Cminorgenproof.set_locals_outside` -/
theorem setLocals_outside {e : Cminor.Env} {id : Ident} : ∀ {il : List Ident},
    id ∉ il → (Cminor.setLocals il e).get id = e.get id
  | [], _ => rfl
  | a :: il, h => by
    simp only [List.mem_cons, not_or] at h
    simp only [Cminor.setLocals]
    rw [PTree.gso _ _ _ _ (Ne.symm h.1), setLocals_outside h.2]

/-- `Cminorgenproof.set_locals_inside` -/
theorem setLocals_inside {e : Cminor.Env} {id : Ident} : ∀ {il : List Ident},
    id ∈ il → (Cminor.setLocals il e).get id = some .Vundef
  | [], h => by simp at h
  | a :: il, h => by
    simp only [Cminor.setLocals]
    rw [PTree.gsspec]
    split
    · rfl
    · rename_i hne
      rcases List.mem_cons.mp h with h | h
      · exact absurd h hne
      · exact setLocals_inside h

/-- `Cminorgenproof.set_locals_set_params'` -/
theorem setLocals_setParams' {vars : List Ident} {vals : List Val} {params : List Ident}
    {id : Ident} (h1 : params.Nodup) (h2 : listDisjoint params vars) :
    (Cminor.setLocals vars (Cminor.setParams vals params)).get id =
      (setParams' vals params (Cminor.setLocals vars PTree.empty)).get id := by
  by_cases hv : id ∈ vars
  · have hp : id ∉ params := fun h => h2 id h hv
    rw [setLocals_inside hv, setParams'_outside hp, setLocals_inside hv]
  · rw [setLocals_outside hv, setParams_setParams' h1]
    by_cases hp : id ∈ params
    · exact setParams'_inside hp
    · rw [setParams'_outside hp, setParams'_outside hp, setLocals_outside hv]

/-- `Cminorgenproof.bind_parameters_agree` -/
theorem bind_parameters_agree {f : Val.Meminj} {params temps : List Ident} {vals tvals : List Val}
    {le : Csharpminor.TempEnv}
    (h : Csharpminor.bindParameters params vals (Csharpminor.createUndefTemps temps) = some le)
    (hi : Val.InjectList f vals tvals) (h1 : params.Nodup) (h2 : listDisjoint params temps) :
    MatchTemps f le (Cminor.setLocals temps (Cminor.setParams tvals params)) := by
  intro id v hv
  have := bind_parameters_agree_rec (te := Cminor.setLocals temps PTree.empty) h hi (by
    intro id' v' hv'
    obtain ⟨A, B⟩ := create_undef_temps_val hv'
    subst B
    exact ⟨.Vundef, setLocals_inside A, .undef _⟩) id v hv
  obtain ⟨v', A, B⟩ := this
  exact ⟨v', by rw [setLocals_setParams' h1 h2]; exact A, B⟩

/-! ## The main result of this section -/

/-- `Cminorgenproof.match_callstack_function_entry` -/
theorem match_callstack_function_entry {fn : Csharpminor.Function} {cenv : Compilenv}
    {tf : Cminor.Function} {m : Mem} {e : Csharpminor.Env} {m' tm tm' : Mem} {sp : Block}
    {f : Val.Meminj} {cs : Callstack} {args targs : List Val} {le : Csharpminor.TempEnv}
    (BC : buildCompilenv fn = (cenv, tf.fn_stackspace))
    (REPRES : tf.fn_stackspace ≤ Integers.Ptrofs.max_unsigned)
    (NR1 : (fn.fn_vars.map Prod.fst).Nodup) (NR2 : fn.fn_params.Nodup)
    (DISJ : listDisjoint fn.fn_params fn.fn_temps)
    (AV : Csharpminor.AllocVariables Csharpminor.emptyEnv m fn.fn_vars e m')
    (BP : Csharpminor.bindParameters fn.fn_params args (Csharpminor.createUndefTemps fn.fn_temps) =
      some le)
    (ARGS : Val.InjectList f args targs)
    (ALLOC : Mem.alloc tm 0 tf.fn_stackspace = (tm', sp))
    (MCS : MatchCallstack ge f m tm cs m.nextblock tm.nextblock)
    (MINJ : Mem.Inject f m tm) :
    ∃ f', MatchCallstack ge f' m' tm'
        (⟨cenv, tf, e, le, Cminor.setLocals fn.fn_temps (Cminor.setParams targs fn.fn_params), sp,
          m.nextblock, m'.nextblock⟩ :: cs) m'.nextblock tm'.nextblock ∧ Mem.Inject f' m' tm' := by
  obtain ⟨C1, C2⟩ := build_compilenv_sound BC NR1
  exact match_callstack_alloc_variables ALLOC REPRES AV NR1 C1 C2
    (fun id ofs h => build_compilenv_domain BC h) MINJ MCS (bind_parameters_agree BP ARGS NR2 DISJ)

end Cminorgen
end CC
