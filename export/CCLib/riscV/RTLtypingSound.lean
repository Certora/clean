/-
  [RISC-V instance of `CCLib/backend/RTLtypingSound.lean`: the same development, in
  namespace `CC.RiscV`, over the RISC-V operators, registers and conventions.]

  Typing of RTL — port of the relational part of `backend/RTLtyping.v` and of
  the soundness of type inference: `valid_successor`, `wt_instr`,
  `wt_function`, `wt_fundef`, `wt_program`, and `type_ros_sound`,
  `check_successor(s)_sound`, `type_expect_sound`, `type_builtin_arg(s)_sound`,
  `type_builtin_res_sound`, the `*_incr` lemmas, `type_instr_sound`,
  `type_code_sound` and **`type_function_correct`**.

  Differences from Rocq: `Archi.abi` (used by `tailcall_possible`) is an
  explicit argument `abi`; the `ty` argument of `wt_Ireturn_some` (always
  equal to `env arg`) is dropped.
-/
import CCLib.riscV.RTLtyping
import CCLib.common.UnitypingSound

namespace CC
namespace RiscV
namespace RTLtyping

open RTL Op

private theorem rbind_OK {A B : Type} {x : Res A} {f : A → Res B} {b : B} :
    (bind x f = Res.OK b) ↔ ∃ a, x = .OK a ∧ f a = .OK b := by
  cases x <;> simp [bind, Res.bind]

/-! ## Relational typing -/

section WT_INSTR
variable (funct : RTL.Function) (env : Regenv)

/-- `RTLtyping.valid_successor` -/
def ValidSuccessor (s : Node) : Prop := ∃ i, funct.fn_code.get s = some i

/-- The typing constraint on the function position of a call. -/
def RosTyped : Sum Reg Ident → Prop
  | .inl r => env r = Tptr
  | .inr _ => True

/-- The typing constraint on the arguments of a builtin. -/
def BuiltinArgsTyped (ef : ExtFun) (args : List (BuiltinArg Reg)) : Prop :=
  match ef with
  | .EF_annot _ _ _ | .EF_debug _ _ _ => True
  | _ => args.map (typeOfBuiltinArg env) = projSigArgs ef.sig

/-- `RTLtyping.wt_instr` -/
inductive WtInstr : Instruction → Prop where
  | Inop (s : Node) : ValidSuccessor funct s → WtInstr (.Inop s)
  | Iopmove (r1 r : Reg) (s : Node) :
      env r = env r1 → ValidSuccessor funct s → WtInstr (.Iop .Omove [r1] r s)
  | Iop (op : Operation) (args : List Reg) (res : Reg) (s : Node) :
      op ≠ .Omove → args.map env = (typeOfOperation op).1 → env res = (typeOfOperation op).2 →
      ValidSuccessor funct s → WtInstr (.Iop op args res s)
  | Iload (chunk : Chunk) (addr : Addressing) (args : List Reg) (dst : Reg) (s : Node) :
      args.map env = typeOfAddressing addr → env dst = chunk.typ → ValidSuccessor funct s →
      WtInstr (.Iload chunk addr args dst s)
  | Istore (chunk : Chunk) (addr : Addressing) (args : List Reg) (src : Reg) (s : Node) :
      args.map env = typeOfAddressing addr → env src = chunk.typ → ValidSuccessor funct s →
      WtInstr (.Istore chunk addr args src s)
  | Icall (sig : Signature) (ros : Sum Reg Ident) (args : List Reg) (res : Reg) (s : Node) :
      RosTyped env ros → args.map env = projSigArgs sig → env res = projSigRes sig →
      ValidSuccessor funct s → WtInstr (.Icall sig ros args res s)
  | Itailcall (sig : Signature) (ros : Sum Reg Ident) (args : List Reg) :
      RosTyped env ros → args.map env = projSigArgs sig →
      sig.sig_res = funct.fn_sig.sig_res → Conventions.TailcallPossible  sig →
      WtInstr (.Itailcall sig ros args)
  | Ibuiltin (ef : ExtFun) (args : List (BuiltinArg Reg)) (res : BuiltinRes Reg) (s : Node) :
      BuiltinArgsTyped env ef args → typeOfBuiltinRes env res = projSigRes ef.sig →
      ValidSuccessor funct s → WtInstr (.Ibuiltin ef args res s)
  | Icond (cond : Condition) (args : List Reg) (s1 s2 : Node) :
      args.map env = typeOfCondition cond → ValidSuccessor funct s1 →
      ValidSuccessor funct s2 → WtInstr (.Icond cond args s1 s2)
  | Ijumptable (arg : Reg) (tbl : List Node) :
      env arg = .Tint → (∀ s ∈ tbl, ValidSuccessor funct s) →
      (tbl.length : Z) * 4 ≤ Integers.Int.max_unsigned → WtInstr (.Ijumptable arg tbl)
  | Ireturn_none : funct.fn_sig.sig_res = .Xvoid → WtInstr (.Ireturn none)
  | Ireturn_some (arg : Reg) :
      funct.fn_sig.sig_res ≠ .Xvoid → env arg = projSigRes funct.fn_sig →
      WtInstr (.Ireturn (some arg))

end WT_INSTR

/-- `RTLtyping.wt_function` -/
structure WtFunction (f : RTL.Function) (env : Regenv) : Prop where
  wt_params : f.fn_params.map env = projSigArgs f.fn_sig
  wt_norepet : f.fn_params.Nodup
  wt_instrs : ∀ pc i, f.fn_code.get pc = some i → WtInstr  f env i
  wt_entrypoint : ValidSuccessor f f.fn_entrypoint

/-- `RTLtyping.wt_fundef` -/
inductive WtFundef : RTL.Fundef → Prop where
  | external (ef : ExtFun) : WtFundef  (.External ef)
  | internal (f : RTL.Function) (env : Regenv) : WtFunction  f env → WtFundef  (.Internal f)

/-- `RTLtyping.wt_program` -/
def WtProgram (p : RTL.Program) : Prop :=
  ∀ i f, (i, GlobDef.Gfun f) ∈ p.prog_defs → WtFundef  f

/-! ## Soundness of type inference -/

section SOUNDNESS
variable {f : RTL.Function}

open UniSolver

/-- `RTLtyping.type_ros_incr` -/
theorem type_ros_incr {e e' : STypenv} {ros : Sum Reg Ident} {te : Regenv}
    (h : typeRos e ros = .OK e') (hs : Satisf te e') : Satisf te e := by
  cases ros with
  | inl r => exact set_incr h hs
  | inr _ => cases h; exact hs

/-- `RTLtyping.type_ros_sound` -/
theorem type_ros_sound {e e' : STypenv} {ros : Sum Reg Ident} {te : Regenv}
    (h : typeRos e ros = .OK e') (hs : Satisf te e') : RosTyped te ros := by
  cases ros with
  | inl r => exact set_sound h hs
  | inr _ => trivial

/-- `RTLtyping.check_successor_sound` -/
theorem check_successor_sound {s : Node} {x : Unit} (h : checkSuccessor f s = .OK x) :
    ValidSuccessor f s := by
  unfold checkSuccessor at h
  split at h
  · cases h
  · next i hi => exact ⟨i, hi⟩

/-- `RTLtyping.check_successors_sound` -/
theorem check_successors_sound :
    ∀ {sl : List Node} {x : Unit}, checkSuccessors f sl = .OK x → ∀ s ∈ sl, ValidSuccessor f s
  | [], _, _, _, hs => by cases hs
  | a :: sl, _, h, s, hs => by
    simp only [checkSuccessors, rbind_OK] at h
    obtain ⟨_, h1, h2⟩ := h
    rcases List.mem_cons.mp hs with rfl | hs
    · exact check_successor_sound h1
    · exact check_successors_sound h2 s hs

/-- `RTLtyping.type_expect_incr` -/
theorem type_expect_incr {e e' : STypenv} {t1 t2 : ATyp} {te : Regenv}
    (h : typeExpect e t1 t2 = .OK e') (hs : Satisf te e') : Satisf te e := by
  unfold typeExpect at h; split at h
  · cases h; exact hs
  · cases h

/-- `RTLtyping.type_expect_sound` -/
theorem type_expect_sound {e e' : STypenv} {t1 t2 : ATyp} (h : typeExpect e t1 t2 = .OK e') :
    t1 = t2 := by
  unfold typeExpect at h; split at h
  · assumption
  · cases h

/-- `RTLtyping.type_builtin_arg_incr` -/
theorem type_builtin_arg_incr {e e' : STypenv} {a : BuiltinArg Reg} {ty : ATyp} {te : Regenv}
    (h : typeBuiltinArg e a ty = .OK e') (hs : Satisf te e') : Satisf te e := by
  cases a <;> simp only [typeBuiltinArg] at h <;>
    first | exact set_incr h hs | exact type_expect_incr h hs

/-- `RTLtyping.type_builtin_args_incr` -/
theorem type_builtin_args_incr {te : Regenv} :
    ∀ {a : List (BuiltinArg Reg)} {ty : List ATyp} {e e' : STypenv},
    typeBuiltinArgs e a ty = .OK e' → Satisf te e' → Satisf te e
  | [], [], _, _, h, hs => by cases h; exact hs
  | [], _ :: _, _, _, h, _ => by cases h
  | _ :: _, [], _, _, h, _ => by cases h
  | _ :: _, _ :: _, _, _, h, hs => by
    simp only [typeBuiltinArgs, rbind_OK] at h
    obtain ⟨_, h1, h2⟩ := h
    exact type_builtin_arg_incr h1 (type_builtin_args_incr h2 hs)

/-- `RTLtyping.type_builtin_res_incr` -/
theorem type_builtin_res_incr {e e' : STypenv} {a : BuiltinRes Reg} {ty : ATyp} {te : Regenv}
    (h : typeBuiltinRes e a ty = .OK e') (hs : Satisf te e') : Satisf te e := by
  cases a <;> simp only [typeBuiltinRes] at h <;>
    first | exact set_incr h hs | exact type_expect_incr h hs

/-- `RTLtyping.type_builtin_arg_sound` -/
theorem type_builtin_arg_sound {e e' : STypenv} {a : BuiltinArg Reg} {ty : ATyp} {te : Regenv}
    (h : typeBuiltinArg e a ty = .OK e') (hs : Satisf te e') : typeOfBuiltinArg te a = ty := by
  cases a <;> simp only [typeBuiltinArg] at h <;> simp only [typeOfBuiltinArg] <;>
    first | exact set_sound h hs | exact (type_expect_sound h).symm

/-- `RTLtyping.type_builtin_args_sound` -/
theorem type_builtin_args_sound {te : Regenv} :
    ∀ {al : List (BuiltinArg Reg)} {tyl : List ATyp} {e e' : STypenv},
    typeBuiltinArgs e al tyl = .OK e' → Satisf te e' → al.map (typeOfBuiltinArg te) = tyl
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, h, _ => by cases h
  | _ :: _, [], _, _, h, _ => by cases h
  | _ :: _, _ :: _, _, _, h, hs => by
    simp only [typeBuiltinArgs, rbind_OK] at h
    obtain ⟨_, h1, h2⟩ := h
    simp only [List.map_cons]
    rw [type_builtin_arg_sound h1 (type_builtin_args_incr h2 hs), type_builtin_args_sound h2 hs]

/-- `RTLtyping.type_builtin_res_sound` -/
theorem type_builtin_res_sound {e e' : STypenv} {a : BuiltinRes Reg} {ty : ATyp} {te : Regenv}
    (h : typeBuiltinRes e a ty = .OK e') (hs : Satisf te e') : typeOfBuiltinRes te a = ty := by
  cases a <;> simp only [typeBuiltinRes] at h <;> simp only [typeOfBuiltinRes] <;>
    first | exact set_sound h hs | exact (type_expect_sound h).symm

/-- `RTLtyping.type_instr_incr` -/
theorem type_instr_incr {e e' : STypenv} {i : Instruction} {te : Regenv}
    (h : typeInstr  f e i = .OK e') (hs : Satisf te e') : Satisf te e := by
  cases i with
  | Inop s =>
    simp only [typeInstr, rbind_OK] at h
    obtain ⟨_, _, h⟩ := h; cases h; exact hs
  | Iop op args res s =>
    simp only [typeInstr, rbind_OK] at h
    obtain ⟨_, _, h⟩ := h
    split at h
    · split at h
      · simp only [rbind_OK] at h
        obtain ⟨⟨_, e1⟩, h1, h2⟩ := h
        cases h2
        exact move_incr h1 hs
      · cases h
    · simp only [rbind_OK] at h
      obtain ⟨_, h1, h2⟩ := h
      exact set_list_incr h1 (set_incr h2 hs)
  | Iload chunk addr args dst s =>
    simp only [typeInstr, rbind_OK] at h
    obtain ⟨_, _, _, h1, h2⟩ := h
    exact set_list_incr h1 (set_incr h2 hs)
  | Istore chunk addr args src s =>
    simp only [typeInstr, rbind_OK] at h
    obtain ⟨_, _, _, h1, h2⟩ := h
    exact set_list_incr h1 (set_incr h2 hs)
  | Icall sig ros args res s =>
    simp only [typeInstr, rbind_OK] at h
    obtain ⟨_, _, _, h1, _, h2, h3⟩ := h
    exact type_ros_incr h1 (set_list_incr h2 (set_incr h3 hs))
  | Itailcall sig ros args =>
    simp only [typeInstr, rbind_OK] at h
    obtain ⟨_, h1, _, h2, h3⟩ := h
    split at h3
    · split at h3
      · cases h3; exact type_ros_incr h1 (set_list_incr h2 hs)
      · cases h3
    · cases h3
  | Ibuiltin ef args res s =>
    simp only [typeInstr, rbind_OK] at h
    obtain ⟨_, _, h⟩ := h
    split at h
    · exact type_builtin_res_incr h hs
    · exact type_builtin_res_incr h hs
    · simp only [rbind_OK] at h
      obtain ⟨_, h1, h2⟩ := h
      exact type_builtin_args_incr h1 (type_builtin_res_incr h2 hs)
  | Icond cond args s1 s2 =>
    simp only [typeInstr, rbind_OK] at h
    obtain ⟨_, _, _, _, h⟩ := h
    exact set_list_incr h hs
  | Ijumptable arg tbl =>
    simp only [typeInstr, rbind_OK] at h
    obtain ⟨_, _, _, h1, h2⟩ := h
    split at h2
    · cases h2; exact set_incr h1 hs
    · cases h2
  | Ireturn optres =>
    simp only [typeInstr] at h
    split at h
    · cases h; exact hs
    · exact set_incr h hs
    · cases h

/-- `RTLtyping.type_instr_sound` -/
theorem type_instr_sound {e e' : STypenv} {i : Instruction} {te : Regenv}
    (h : typeInstr  f e i = .OK e') (hs : Satisf te e') : WtInstr  f te i := by
  cases i with
  | Inop s =>
    simp only [typeInstr, rbind_OK] at h
    obtain ⟨_, h1, _⟩ := h
    exact .Inop _ (check_successor_sound h1)
  | Iop op args res s =>
    simp only [typeInstr, rbind_OK] at h
    obtain ⟨_, hs1, h⟩ := h
    split at h
    · next hmove =>
      have : op = .Omove := by cases op <;> first | rfl | cases hmove
      subst this
      split at h
      · simp only [rbind_OK] at h
        obtain ⟨⟨_, e1⟩, h1, h2⟩ := h
        cases h2
        exact .Iopmove _ _ _ (move_sound h1 hs) (check_successor_sound hs1)
      · cases h
    · next hmove =>
      simp only [rbind_OK] at h
      obtain ⟨_, h1, h2⟩ := h
      exact .Iop _ _ _ _ (by rintro rfl; exact hmove rfl)
        (set_list_sound h1 (set_incr h2 hs)) (set_sound h2 hs) (check_successor_sound hs1)
  | Iload chunk addr args dst s =>
    simp only [typeInstr, rbind_OK] at h
    obtain ⟨_, hs1, _, h1, h2⟩ := h
    exact .Iload _ _ _ _ _ (set_list_sound h1 (set_incr h2 hs)) (set_sound h2 hs)
      (check_successor_sound hs1)
  | Istore chunk addr args src s =>
    simp only [typeInstr, rbind_OK] at h
    obtain ⟨_, hs1, _, h1, h2⟩ := h
    exact .Istore _ _ _ _ _ (set_list_sound h1 (set_incr h2 hs)) (set_sound h2 hs)
      (check_successor_sound hs1)
  | Icall sig ros args res s =>
    simp only [typeInstr, rbind_OK] at h
    obtain ⟨_, hs1, _, h1, _, h2, h3⟩ := h
    exact .Icall _ _ _ _ _ (type_ros_sound h1 (set_list_incr h2 (set_incr h3 hs)))
      (set_list_sound h2 (set_incr h3 hs)) (set_sound h3 hs) (check_successor_sound hs1)
  | Itailcall sig ros args =>
    simp only [typeInstr, rbind_OK] at h
    obtain ⟨_, h1, _, h2, h3⟩ := h
    split at h3
    · next hres =>
      split at h3
      · next htc =>
        cases h3
        exact .Itailcall _ _ _ (type_ros_sound h1 (set_list_incr h2 hs)) (set_list_sound h2 hs)
          hres (Conventions.tailcallIsPossible_correct htc)
      · cases h3
    · cases h3
  | Ibuiltin ef args res s =>
    simp only [typeInstr, rbind_OK] at h
    obtain ⟨_, hs1, h⟩ := h
    split at h
    · exact .Ibuiltin _ _ _ _ trivial (type_builtin_res_sound h hs) (check_successor_sound hs1)
    · exact .Ibuiltin _ _ _ _ trivial (type_builtin_res_sound h hs) (check_successor_sound hs1)
    · next hne1 hne2 =>
      simp only [rbind_OK] at h
      obtain ⟨_, h1, h2⟩ := h
      refine .Ibuiltin _ _ _ _ ?_ (type_builtin_res_sound h2 hs) (check_successor_sound hs1)
      unfold BuiltinArgsTyped
      split
      · exact absurd rfl (hne1 _ _ _)
      · exact absurd rfl (hne2 _ _ _)
      · exact type_builtin_args_sound h1 (type_builtin_res_incr h2 hs)
  | Icond cond args s1 s2 =>
    simp only [typeInstr, rbind_OK] at h
    obtain ⟨_, hs1, _, hs2, h⟩ := h
    exact .Icond _ _ _ _ (set_list_sound h hs) (check_successor_sound hs1)
      (check_successor_sound hs2)
  | Ijumptable arg tbl =>
    simp only [typeInstr, rbind_OK] at h
    obtain ⟨_, hs1, _, h1, h2⟩ := h
    split at h2
    · next hle =>
      cases h2
      exact .Ijumptable _ _ (set_sound h1 hs) (check_successors_sound hs1) hle
    · cases h2
  | Ireturn optres =>
    simp only [typeInstr] at h
    split at h
    · next hv => exact .Ireturn_none (of_decide_eq_true hv)
    · next r hv => exact .Ireturn_some _ (of_decide_eq_false hv) (set_sound h hs)
    · cases h

/-- Invariant of the fold in `type_code`. -/
private theorem type_code_fold_sound {te : Regenv} {pc : Node} {i : Instruction} :
    ∀ (l : List (Positive × Instruction)) (r : Res STypenv) (e' : STypenv),
    l.foldl (fun re p =>
      match re with
      | .Error _ => re
      | .OK e =>
          match typeInstr  f e p.2 with
          | .Error msg => .Error ("At PC: " ++ msg)
          | .OK e' => .OK e') r = .OK e' →
    Satisf te e' →
    (∀ e0, r = .OK e0 → Satisf te e0 → (pc, i) ∈ l → WtInstr  f te i) ∧
    (∀ e0, r = .OK e0 → Satisf te e0) ∧
    ((pc, i) ∈ l → WtInstr  f te i)
  | [], r, e', h, hs => by
    simp only [List.foldl_nil] at h
    subst h
    exact ⟨(fun _ _ _ hm => by cases hm), (fun e0 he => by cases he; exact hs),
      (fun hm => by cases hm)⟩
  | p :: l, r, e', h, hs => by
    simp only [List.foldl_cons] at h
    cases r with
    | Error m =>
      exfalso
      have : ∀ l : List (Positive × Instruction), l.foldl (fun re p =>
          match re with
          | .Error _ => re
          | .OK e =>
              match typeInstr  f e p.2 with
              | .Error msg => .Error ("At PC: " ++ msg)
              | .OK e' => .OK e') (Res.Error m) = .Error m := by
        intro l; induction l with
        | nil => rfl
        | cons _ _ ih => exact ih
      simp only at h
      rw [this] at h; cases h
    | OK e0 =>
      simp only at h
      cases hti : typeInstr  f e0 p.2 with
      | Error msg =>
        exfalso
        rw [hti] at h
        simp only at h
        have : ∀ (m : String) (l : List (Positive × Instruction)), l.foldl (fun re p =>
            match re with
            | .Error _ => re
            | .OK e =>
                match typeInstr  f e p.2 with
                | .Error msg => .Error ("At PC: " ++ msg)
                | .OK e' => .OK e') (Res.Error m) = .Error m := by
          intro m l; induction l with
          | nil => rfl
          | cons _ _ ih => exact ih
        rw [this] at h; cases h
      | OK e1 =>
        rw [hti] at h
        simp only at h
        obtain ⟨A, B, C⟩ := type_code_fold_sound l (.OK e1) e' h hs
        have S1 : Satisf te e1 := B e1 rfl
        have S0 : Satisf te e0 := type_instr_incr hti S1
        have W : (pc, i) ∈ p :: l → WtInstr  f te i := by
          intro hm
          rcases List.mem_cons.mp hm with heq | hm
          · subst heq; exact type_instr_sound hti S1
          · exact C hm
        exact ⟨(fun _ _ _ hm => W hm), (fun e2 he => by cases he; exact S0), W⟩

/-- `RTLtyping.type_code_sound` -/
theorem type_code_sound {pc : Node} {i : Instruction} {e e' : STypenv} {te : Regenv}
    (h : typeCode  f e = .OK e') (hpc : f.fn_code.get pc = some i) (hs : Satisf te e') :
    WtInstr  f te i := by
  unfold typeCode at h
  rw [PTree.fold_spec] at h
  exact (type_code_fold_sound _ _ _ h hs).2.2 (PTree.elements_correct _ _ _ hpc)

/-- The fold in `type_code` returns a satisfiable environment only if its
    initial environment is satisfiable. -/
theorem type_code_incr {e e' : STypenv} {te : Regenv}
    (h : typeCode  f e = .OK e') (hs : Satisf te e') : Satisf te e := by
  unfold typeCode at h
  rw [PTree.fold_spec] at h
  exact (type_code_fold_sound (pc := f.fn_entrypoint) (i := .Inop f.fn_entrypoint) _ _ _ h hs).2.1 e rfl

/-- `RTLtyping.type_function_correct` -/
theorem type_function_correct {env : Regenv} (h : typeFunction  f = .OK env) :
    WtFunction  f env := by
  simp only [typeFunction, rbind_OK] at h
  obtain ⟨e1, h1, e2, h2, te, h3, _, h4, _, h5, h6⟩ := h
  cases h6
  have SAT0 : Satisf env e2 := solve_sound h3
  have SAT1 : Satisf env e1 := set_list_incr h2 SAT0
  refine ⟨set_list_sound h2 SAT0, ?_, fun pc i hpc => type_code_sound h1 hpc SAT1,
    check_successor_sound h5⟩
  unfold checkParamsNorepet at h4
  split at h4
  · assumption
  · cases h4

end SOUNDNESS

end RTLtyping
end RiscV
end CC
