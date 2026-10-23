/-
  [x86-64 instance of `CCLib/backend/RTLgenproofBuiltin.lean`: the same development, in
  namespace `CC.X86`, over the x86-64 operators, registers and conventions.]

  Correctness of RTL generation — port of `backend/RTLgenproof.v`, part 3:
  evaluation of builtin arguments (`eval_exprlist_append`,
  `invert_eval_builtin_arg(s)`, `transl_eval_builtin_arg(s)`).
-/
import CCLib.x86.RTLgenproofExpr

namespace CC
namespace X86
namespace RTLgen

open Op CminorSel

theorem convertBuiltinArg_splitlong {A : Type} (hi lo : BuiltinArg CminorSel.Expr) (rl : List A) :
    convertBuiltinArg (.BA_splitlong hi lo) rl =
      (.BA_splitlong (convertBuiltinArg hi rl).1
        (convertBuiltinArg lo (convertBuiltinArg hi rl).2).1,
       (convertBuiltinArg lo (convertBuiltinArg hi rl).2).2) := rfl

theorem convertBuiltinArg_addptr {A : Type} (a1 a2 : BuiltinArg CminorSel.Expr) (rl : List A) :
    convertBuiltinArg (.BA_addptr a1 a2) rl =
      (.BA_addptr (convertBuiltinArg a1 rl).1
        (convertBuiltinArg a2 (convertBuiltinArg a1 rl).2).1,
       (convertBuiltinArg a2 (convertBuiltinArg a1 rl).2).2) := rfl

theorem convertBuiltinArgs_cons {A : Type} (a : BuiltinArg CminorSel.Expr)
    (al : List (BuiltinArg CminorSel.Expr)) (rl : List A) :
    convertBuiltinArgs (a :: al) rl =
      (convertBuiltinArg a rl).1 :: convertBuiltinArgs al (convertBuiltinArg a rl).2 := rfl

section BUILTIN
variable {ge : CminorSel.CGenv} (sp : Val) (e : Cminor.Env) (m : Mem)

/-- `RTLgenproof.eval_exprlist_append` -/
theorem eval_exprlist_append {le : Letenv} :
    ∀ {al1 : List CminorSel.Expr} {vl1 : List Val} {al2 : List CminorSel.Expr} {vl2 : List Val},
    CminorSel.EvalExprlist ge sp e m le (exprlistOfExprList al1) vl1 →
    CminorSel.EvalExprlist ge sp e m le (exprlistOfExprList al2) vl2 →
    CminorSel.EvalExprlist ge sp e m le (exprlistOfExprList (al1 ++ al2)) (vl1 ++ vl2)
  | [], _, _, _, h1, h2 => by cases h1; exact h2
  | a :: al1, _, _, _, h1, h2 => by
    cases h1 with
    | Econs _ _ _ v1 vl1 ha hl =>
      exact .Econs _ _ _ _ _ ha (eval_exprlist_append hl h2)


/-- `RTLgenproof.invert_eval_builtin_arg` -/
theorem invert_eval_builtin_arg {a : BuiltinArg CminorSel.Expr} {v : Val}
    (h : CminorSel.EvalBuiltinArg ge sp e m a v) :
    ∃ vl, CminorSel.EvalExprlist ge sp e m [] (exprlistOfExprList (BuiltinArg.params a)) vl ∧
      EvalBuiltinArg ge.toSenv (fun v => v) sp m (convertBuiltinArg a vl).1 v ∧
      (∀ vl', convertBuiltinArg a (vl ++ vl') = ((convertBuiltinArg a vl).1, vl')) := by
  induction h with
  | BA a v ha =>
    exact ⟨[v], .Econs _ _ _ _ _ ha (.Enil _), .BA _, fun _ => rfl⟩
  | BA_int n => exact ⟨[], .Enil _, .BA_int n, fun _ => rfl⟩
  | BA_long n => exact ⟨[], .Enil _, .BA_long n, fun _ => rfl⟩
  | BA_float n => exact ⟨[], .Enil _, .BA_float n, fun _ => rfl⟩
  | BA_single n => exact ⟨[], .Enil _, .BA_single n, fun _ => rfl⟩
  | BA_loadstack chunk ofs v hl => exact ⟨[], .Enil _, .BA_loadstack _ _ _ hl, fun _ => rfl⟩
  | BA_addrstack ofs => exact ⟨[], .Enil _, .BA_addrstack ofs, fun _ => rfl⟩
  | BA_loadglobal chunk id ofs v hl => exact ⟨[], .Enil _, .BA_loadglobal _ _ _ _ hl, fun _ => rfl⟩
  | BA_addrglobal id ofs => exact ⟨[], .Enil _, .BA_addrglobal id ofs, fun _ => rfl⟩
  | BA_splitlong a1 a2 v1 v2 h1 h2 =>
    exact ⟨[v1, v2], .Econs _ _ _ _ _ h1 (.Econs _ _ _ _ _ h2 (.Enil _)),
      .BA_splitlong _ _ _ _ (.BA _) (.BA _), fun _ => rfl⟩
  | BA_addptr a1 v1 a2 v2 _ _ ih1 ih2 =>
    obtain ⟨vl1, A1, B1, C1⟩ := ih1
    obtain ⟨vl2, A2, B2, C2⟩ := ih2
    refine ⟨vl1 ++ vl2, eval_exprlist_append sp e m A1 A2, ?_, fun vl' => ?_⟩
    · rw [convertBuiltinArg_addptr, C1]
      exact .BA_addptr _ _ _ _ B1 B2
    · rw [convertBuiltinArg_addptr, convertBuiltinArg_addptr, List.append_assoc, C1, C1, C2]

/-- `RTLgenproof.invert_eval_builtin_args` -/
theorem invert_eval_builtin_args :
    ∀ {al : List (BuiltinArg CminorSel.Expr)} {vl : List Val},
    ListForall2 (CminorSel.EvalBuiltinArg ge sp e m) al vl →
    ∃ vl', CminorSel.EvalExprlist ge sp e m [] (exprlistOfExprList (BuiltinArg.paramsList al)) vl' ∧
      EvalBuiltinArgs ge.toSenv (fun v => v) sp m (convertBuiltinArgs al vl') vl
  | [], [], .nil => ⟨[], .Enil _, .nil⟩
  | _ :: _, _ :: _, .cons h hl => by
    obtain ⟨vl1, A, B, C⟩ := invert_eval_builtin_arg sp e m h
    obtain ⟨vl2, D, E⟩ := invert_eval_builtin_args hl
    refine ⟨vl1 ++ vl2, eval_exprlist_append sp e m A D, ?_⟩
    rw [convertBuiltinArgs_cons, C]
    exact .cons B E

/-- `RTLgenproof.transl_eval_builtin_arg` -/
theorem transl_eval_builtin_arg (rs : RTL.Regset) :
    ∀ (a : BuiltinArg CminorSel.Expr) {vl : List Val} {rl : List Reg} {v : Val},
    Val.LessdefList vl (rs.getList rl) →
    EvalBuiltinArg ge.toSenv (fun v => v) sp m (convertBuiltinArg a vl).1 v →
    ∃ v', EvalBuiltinArg ge.toSenv (fun r => rs.get r) sp m (convertBuiltinArg a rl).1 v' ∧
      Val.Lessdef v v' ∧
      Val.LessdefList (convertBuiltinArg a vl).2 (rs.getList (convertBuiltinArg a rl).2)
  | .BA x, vl, rl, v, LD, EV => by
    cases rl with
    | nil =>
      cases LD
      cases EV
      exact ⟨_, .BA_int _, .refl _, .nil⟩
    | cons r rl =>
      cases LD with
      | cons h1 h2 =>
        cases EV
        exact ⟨_, .BA _, h1, h2⟩
  | .BA_int n, vl, rl, v, LD, EV => by cases EV; exact ⟨_, .BA_int n, .refl _, LD⟩
  | .BA_long n, vl, rl, v, LD, EV => by cases EV; exact ⟨_, .BA_long n, .refl _, LD⟩
  | .BA_float n, vl, rl, v, LD, EV => by cases EV; exact ⟨_, .BA_float n, .refl _, LD⟩
  | .BA_single n, vl, rl, v, LD, EV => by cases EV; exact ⟨_, .BA_single n, .refl _, LD⟩
  | .BA_loadstack chunk ofs, vl, rl, v, LD, EV => by
    cases EV with | BA_loadstack _ _ _ hl => exact ⟨_, .BA_loadstack _ _ _ hl, .refl _, LD⟩
  | .BA_addrstack ofs, vl, rl, v, LD, EV => by cases EV; exact ⟨_, .BA_addrstack ofs, .refl _, LD⟩
  | .BA_loadglobal chunk id ofs, vl, rl, v, LD, EV => by
    cases EV with | BA_loadglobal _ _ _ _ hl => exact ⟨_, .BA_loadglobal _ _ _ _ hl, .refl _, LD⟩
  | .BA_addrglobal id ofs, vl, rl, v, LD, EV => by
    cases EV; exact ⟨_, .BA_addrglobal id ofs, .refl _, LD⟩
  | .BA_splitlong a1 a2, vl, rl, v, LD, EV => by
    rw [convertBuiltinArg_splitlong] at EV ⊢
    cases EV with
    | BA_splitlong _ _ v1 v2 E1 E2 =>
      obtain ⟨v1', A1, B1, C1⟩ := transl_eval_builtin_arg rs a1 LD E1
      obtain ⟨v2', A2, B2, C2⟩ := transl_eval_builtin_arg rs a2 C1 E2
      exact ⟨_, .BA_splitlong _ _ _ _ A1 A2, Val.longofwords_lessdef B1 B2, C2⟩
  | .BA_addptr a1 a2, vl, rl, v, LD, EV => by
    rw [convertBuiltinArg_addptr] at EV ⊢
    cases EV with
    | BA_addptr _ _ v1 v2 E1 E2 =>
      obtain ⟨v1', A1, B1, C1⟩ := transl_eval_builtin_arg rs a1 LD E1
      obtain ⟨v2', A2, B2, C2⟩ := transl_eval_builtin_arg rs a2 C1 E2
      refine ⟨_, .BA_addptr _ _ _ _ A1 A2, ?_, C2⟩
      cases Archi.ptr64
      · exact Val.add_lessdef B1 B2
      · exact Val.addl_lessdef B1 B2

/-- `RTLgenproof.transl_eval_builtin_args` -/
theorem transl_eval_builtin_args (rs : RTL.Regset) :
    ∀ (al : List (BuiltinArg CminorSel.Expr)) {vl1 : List Val} {rl : List Reg} {vl : List Val},
    Val.LessdefList vl1 (rs.getList rl) →
    EvalBuiltinArgs ge.toSenv (fun v => v) sp m (convertBuiltinArgs al vl1) vl →
    ∃ vl', EvalBuiltinArgs ge.toSenv (fun r => rs.get r) sp m (convertBuiltinArgs al rl) vl' ∧
      Val.LessdefList vl vl'
  | [], _, _, _, _, EV => by cases EV; exact ⟨[], .nil, .nil⟩
  | a :: al, vl1, rl, vl, LD, EV => by
    rw [convertBuiltinArgs_cons] at EV ⊢
    cases EV with
    | cons E1 E2 =>
      obtain ⟨v1', A1, B1, C1⟩ := transl_eval_builtin_arg sp m rs a LD E1
      obtain ⟨vl', A2, B2⟩ := transl_eval_builtin_args rs al C1 E2
      exact ⟨v1' :: vl', .cons A1 A2, .cons B1 B2⟩

end BUILTIN

end RTLgen
end X86
end CC
