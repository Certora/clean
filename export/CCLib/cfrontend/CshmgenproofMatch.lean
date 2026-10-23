/-
  Translation from Clight to Csharpminor: semantic preservation — port of
  `cfrontend/Cshmgenproof.v`, part 5: the simulation invariant
  (`match_transl`, `match_cont`, `match_states`), the commutation of label
  resolution with the translation (`transl_find_label`) and the properties
  of call continuations (`match_cont_call_cont`, `match_cont_is_call_cont`).

  Whole-program statement: the composite environment `ce` is the program's,
  so it is a parameter of the relations rather than an index of `match_cont`.
-/
import CCLib.cfrontend.CshmgenproofExpr

namespace CC
namespace Cshmgen

open Conventions1 (AbiKind)
open Smallstep

section MATCH
variable (rvNorm : XType → Bool) (ce : CompositeEnv) (tge : Csharpminor.CGenv)

/-- `Cshmgenproof.match_transl` -/
inductive MatchTransl : Csharpminor.Stmt → Csharpminor.Cont → Csharpminor.Stmt →
    Csharpminor.Cont → Prop where
  | zero (ts tk) : MatchTransl ts tk ts tk
  | one (ts tk) : MatchTransl (.Sblock ts) tk ts (.Kblock tk)

/-- `Cshmgenproof.match_cont` -/
inductive MatchCont : Ty → Nat → Nat → Cont → Csharpminor.Cont → Prop where
  | Kstop (tyret nbrk ncnt) : MatchCont tyret nbrk ncnt .Kstop .Kstop
  | Kseq (tyret nbrk ncnt s k ts tk) :
      translStatement rvNorm ce tyret nbrk ncnt s = .OK ts →
      MatchCont tyret nbrk ncnt k tk →
      MatchCont tyret nbrk ncnt (.Kseq s k) (.Kseq ts tk)
  | Kloop1 (tyret s1 s2 k ts1 ts2 nbrk ncnt tk) :
      translStatement rvNorm ce tyret 1 0 s1 = .OK ts1 →
      translStatement rvNorm ce tyret 0 (ncnt + 1) s2 = .OK ts2 →
      MatchCont tyret nbrk ncnt k tk →
      MatchCont tyret 1 0 (.Kloop1 s1 s2 k)
        (.Kblock (.Kseq ts2 (.Kseq (.Sloop (.Sseq (.Sblock ts1) ts2)) (.Kblock tk))))
  | Kloop2 (tyret s1 s2 k ts1 ts2 nbrk ncnt tk) :
      translStatement rvNorm ce tyret 1 0 s1 = .OK ts1 →
      translStatement rvNorm ce tyret 0 (ncnt + 1) s2 = .OK ts2 →
      MatchCont tyret nbrk ncnt k tk →
      MatchCont tyret 0 (ncnt + 1) (.Kloop2 s1 s2 k)
        (.Kseq (.Sloop (.Sseq (.Sblock ts1) ts2)) (.Kblock tk))
  | Kswitch (tyret nbrk ncnt k tk) :
      MatchCont tyret nbrk ncnt k tk →
      MatchCont tyret 0 (ncnt + 1) (.Kswitch k) (.Kblock tk)
  | Kcall (tyret nbrk ncnt nbrk' ncnt' f e k id tf te le tk) :
      translFunction rvNorm ce f = .OK tf →
      MatchEnv ce e te →
      MatchCont f.fn_return nbrk' ncnt' k tk →
      MatchCont tyret nbrk ncnt (.Kcall id f e le k) (.Kcall id tf te le tk)
  | Kcall_normalize (tyret nbrk ncnt nbrk' ncnt' f e k id a tf te le tk) :
      translFunction rvNorm ce f = .OK tf →
      MatchEnv ce e te →
      MatchCont f.fn_return nbrk' ncnt' k tk →
      (∀ v e le m, Ctyping.WtVal v tyret → PTree.get id le = some v →
        Csharpminor.EvalExpr tge e le m a v) →
      MatchCont tyret nbrk ncnt (.Kcall (some id) f e le k)
        (.Kcall (some id) tf te le (.Kseq (.Sset id a) tk))

/-- `Cshmgenproof.match_states` -/
inductive MatchStates : State → Csharpminor.State → Prop where
  | state (f nbrk ncnt s k e le m tf ts tk te ts' tk') :
      translFunction rvNorm ce f = .OK tf →
      translStatement rvNorm ce f.fn_return nbrk ncnt s = .OK ts →
      MatchTransl ts tk ts' tk' →
      MatchEnv ce e te →
      MatchCont rvNorm ce tge f.fn_return nbrk ncnt k tk →
      MatchStates (.State f s k e le m) (.State tf ts' tk' te le m)
  | callstate (fd args k m tfd tk targs tres cconv) :
      MatchFundef rvNorm ce fd tfd →
      MatchCont rvNorm ce tge tres 0 0 k tk →
      isCallCont k = true →
      typeOfFundef fd = .Tfunction targs tres cconv →
      Val.HasArgtypeList args (targs.map argtypeOfType) →
      MatchStates (.Callstate fd args k m) (.Callstate tfd args tk m)
  | returnstate (res tres k m tk) :
      MatchCont rvNorm ce tge tres 0 0 k tk →
      Ctyping.WtVal res tres →
      MatchStates (.Returnstate res k m) (.Returnstate res tk m)

/-- `Cshmgenproof.match_transl_step` -/
theorem match_transl_step {ts ts' : Csharpminor.Stmt} {tk tk' : Csharpminor.Cont}
    {f : Csharpminor.Function} {te : Csharpminor.Env} {le : Csharpminor.TempEnv} {m : Mem}
    (h : MatchTransl (.Sblock ts) tk ts' tk') :
    Smallstep.Star (Csharpminor.Step tge) (.State f ts' tk' te le m) E0
      (.State f ts (.Kblock tk) te le m) := by
  cases h with
  | zero => exact star_one (.block _ _ _ _ _ _)
  | one => exact .refl _

/-- `Cshmgenproof.match_states_skip` -/
theorem match_states_skip {f : Function} {e : Env} {le : TempEnv} {te : Csharpminor.Env}
    {nbrk ncnt : Nat} {k : Cont} {tf : Csharpminor.Function} {tk : Csharpminor.Cont} {m : Mem}
    (htf : translFunction rvNorm ce f = .OK tf) (hme : MatchEnv ce e te)
    (hk : MatchCont rvNorm ce tge f.fn_return nbrk ncnt k tk) :
    MatchStates rvNorm ce tge (.State f .Sskip k e le m) (.State tf .Sskip tk te le m) :=
  .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ htf rfl (.zero _ _) hme hk

/-! ## Commutation between label resolution and compilation -/

section FINDLABEL_EQNS
variable (lbl : Ident)

theorem cl_findLabel_seq (s1 s2 : Stmt) (k : Cont) :
    findLabel lbl (.Ssequence s1 s2) k =
      (findLabel lbl s1 (.Kseq s2 k)).orElse (fun _ => findLabel lbl s2 k) := by
  rw [findLabel]; split <;> simp_all [Option.orElse]
theorem cl_findLabel_ite (a : Expr) (s1 s2 : Stmt) (k : Cont) :
    findLabel lbl (.Sifthenelse a s1 s2) k =
      (findLabel lbl s1 k).orElse (fun _ => findLabel lbl s2 k) := by
  rw [findLabel]; split <;> simp_all [Option.orElse]
theorem cl_findLabel_loop (s1 s2 : Stmt) (k : Cont) :
    findLabel lbl (.Sloop s1 s2) k =
      (findLabel lbl s1 (.Kloop1 s1 s2 k)).orElse (fun _ => findLabel lbl s2 (.Kloop2 s1 s2 k)) := by
  rw [findLabel]; split <;> simp_all [Option.orElse]
theorem cl_findLabelLs_cons (o : Option Int) (s : Stmt) (sl : LStmts) (k : Cont) :
    findLabelLs lbl (.LScons o s sl) k =
      (findLabel lbl s (.Kseq (seqOfLabeledStatement sl) k)).orElse
        (fun _ => findLabelLs lbl sl k) := by
  rw [findLabelLs]; split <;> simp_all [Option.orElse]
theorem cs_findLabel_seq (s1 s2 : Csharpminor.Stmt) (k : Csharpminor.Cont) :
    Csharpminor.findLabel lbl (.Sseq s1 s2) k =
      (Csharpminor.findLabel lbl s1 (.Kseq s2 k)).orElse (fun _ => Csharpminor.findLabel lbl s2 k) := by
  rw [Csharpminor.findLabel]; split <;> simp_all [Option.orElse]
theorem cs_findLabel_ite (a : Csharpminor.Expr) (s1 s2 : Csharpminor.Stmt) (k : Csharpminor.Cont) :
    Csharpminor.findLabel lbl (.Sifthenelse a s1 s2) k =
      (Csharpminor.findLabel lbl s1 k).orElse (fun _ => Csharpminor.findLabel lbl s2 k) := by
  rw [Csharpminor.findLabel]; split <;> simp_all [Option.orElse]
theorem cs_findLabel_block (s : Csharpminor.Stmt) (k : Csharpminor.Cont) :
    Csharpminor.findLabel lbl (.Sblock s) k = Csharpminor.findLabel lbl s (.Kblock k) := by
  rw [Csharpminor.findLabel]
theorem cs_findLabel_loop (s : Csharpminor.Stmt) (k : Csharpminor.Cont) :
    Csharpminor.findLabel lbl (.Sloop s) k = Csharpminor.findLabel lbl s (.Kseq (.Sloop s) k) := by
  rw [Csharpminor.findLabel]
theorem cs_findLabelLs_cons (o : Option Z) (s : Csharpminor.Stmt) (sl : Csharpminor.LblStmt)
    (k : Csharpminor.Cont) :
    Csharpminor.findLabelLs lbl (.LScons o s sl) k =
      (Csharpminor.findLabel lbl s (.Kseq (Csharpminor.seqOfLblStmt sl) k)).orElse
        (fun _ => Csharpminor.findLabelLs lbl sl k) := by
  rw [Csharpminor.findLabelLs]; split <;> simp_all [Option.orElse]

end FINDLABEL_EQNS

/-- The conclusion of `Cshmgenproof.transl_find_label`. -/
def FindLabelSpec (tyret : Ty) : Option (Stmt × Cont) →
    Option (Csharpminor.Stmt × Csharpminor.Cont) → Prop
  | none, r => r = none
  | some (s', k'), r => ∃ ts' tk' nbrk' ncnt', r = some (ts', tk') ∧
      translStatement rvNorm ce tyret nbrk' ncnt' s' = .OK ts' ∧
      MatchCont rvNorm ce tge tyret nbrk' ncnt' k' tk'

theorem findLabelSpec_seq {tyret : Ty} {o1 o2 : Option (Stmt × Cont)}
    {r1 r2 : Option (Csharpminor.Stmt × Csharpminor.Cont)}
    (h1 : FindLabelSpec rvNorm ce tge tyret o1 r1) (h2 : o1 = none → FindLabelSpec rvNorm ce tge tyret o2 r2) :
    FindLabelSpec rvNorm ce tge tyret (o1.orElse fun _ => o2) (r1.orElse fun _ => r2) := by
  cases o1 with
  | none => simp only [FindLabelSpec] at h1; subst h1; exact h2 rfl
  | some p =>
    obtain ⟨s', k'⟩ := p
    obtain ⟨ts', tk', nbrk', ncnt', hr, A, B⟩ := h1
    subst hr
    exact ⟨ts', tk', nbrk', ncnt', rfl, A, B⟩

theorem makeStore_findLabel {addr rhs : Csharpminor.Expr} {ty : Ty} {bf : Bitfield}
    {s : Csharpminor.Stmt} (lbl : Ident) (k : Csharpminor.Cont) (h : makeStore ce addr ty bf rhs = .OK s) :
    Csharpminor.findLabel lbl s k = none := by
  unfold makeStore at h
  split at h
  · split at h
    · cases h; simp [Csharpminor.findLabel]
    · simp only [makeMemcpy, res_bind_eq_OK] at h
      obtain ⟨_, _, h⟩ := h; cases h; simp [Csharpminor.findLabel]
    · cases h
  · unfold makeStoreBitfield at h
    split at h
    · cases h; simp [Csharpminor.findLabel]
    · cases h

theorem makeFuncall_findLabel {x : Option Ident} {tres : Ty} {sg : Signature}
    {fn : Csharpminor.Expr} {args : List Csharpminor.Expr} (lbl : Ident) (k : Csharpminor.Cont) :
    Csharpminor.findLabel lbl (makeFuncall rvNorm x tres sg fn args) k = none := by
  unfold makeFuncall
  split <;> simp [Csharpminor.findLabel]

mutual
/-- `Cshmgenproof.transl_find_label` -/
theorem transl_find_label (lbl : Ident) (tyret : Ty) :
    ∀ (s : Stmt) {nbrk ncnt : Nat} {k : Cont} {ts : Csharpminor.Stmt} {tk : Csharpminor.Cont},
    translStatement rvNorm ce tyret nbrk ncnt s = .OK ts →
    MatchCont rvNorm ce tge tyret nbrk ncnt k tk →
    FindLabelSpec rvNorm ce tge tyret (findLabel lbl s k) (Csharpminor.findLabel lbl ts tk)
  | .Sskip, _, _, _, _, _, htr, _ => by
    cases htr; simp [findLabel, Csharpminor.findLabel, FindLabelSpec]
  | .Sassign b c, _, _, _, _, _, htr, _ => by
    simp only [translStatement, res_bind_eq_OK] at htr
    obtain ⟨⟨tb, bf⟩, _, tc, _, tc', _, htr⟩ := htr
    simp only [findLabel, FindLabelSpec]
    exact makeStore_findLabel ce lbl _ htr
  | .Sset x b, _, _, _, _, _, htr, _ => by
    simp only [translStatement, res_bind_eq_OK] at htr
    obtain ⟨_, _, htr⟩ := htr
    cases htr; simp [findLabel, Csharpminor.findLabel, FindLabelSpec]
  | .Scall x b cl, _, _, _, _, _, htr, _ => by
    simp only [translStatement] at htr
    split at htr
    · simp only [res_bind_eq_OK] at htr
      obtain ⟨_, _, _, _, htr⟩ := htr
      cases htr
      simp only [findLabel, FindLabelSpec]
      exact makeFuncall_findLabel rvNorm lbl _
    · cases htr
  | .Sbuiltin x ef tyargs bl, _, _, _, _, _, htr, _ => by
    simp only [translStatement, res_bind_eq_OK] at htr
    obtain ⟨_, _, htr⟩ := htr
    cases htr; simp [findLabel, Csharpminor.findLabel, FindLabelSpec]
  | .Ssequence s1 s2, _, _, _, _, _, htr, hk => by
    simp only [translStatement, res_bind_eq_OK] at htr
    obtain ⟨ts1, h1, ts2, h2, htr⟩ := htr
    cases htr
    rw [cl_findLabel_seq, cs_findLabel_seq]
    exact findLabelSpec_seq rvNorm ce tge
      (transl_find_label lbl tyret s1 h1 (.Kseq _ _ _ _ _ _ _ h2 hk))
      (fun _ => transl_find_label lbl tyret s2 h2 hk)
  | .Sifthenelse a s1 s2, _, _, _, _, _, htr, hk => by
    simp only [translStatement, res_bind_eq_OK] at htr
    obtain ⟨_, _, ts1, h1, ts2, h2, htr⟩ := htr
    cases htr
    rw [cl_findLabel_ite, cs_findLabel_ite]
    exact findLabelSpec_seq rvNorm ce tge (transl_find_label lbl tyret s1 h1 hk)
      (fun _ => transl_find_label lbl tyret s2 h2 hk)
  | .Sloop s1 s2, _, _, _, _, _, htr, hk => by
    simp only [translStatement, res_bind_eq_OK] at htr
    obtain ⟨ts1, h1, ts2, h2, htr⟩ := htr
    cases htr
    rw [cl_findLabel_loop, cs_findLabel_block, cs_findLabel_loop, cs_findLabel_seq,
      cs_findLabel_block]
    exact findLabelSpec_seq rvNorm ce tge
      (transl_find_label lbl tyret s1 h1 (.Kloop1 _ _ _ _ _ _ _ _ _ h1 h2 hk))
      (fun _ => transl_find_label lbl tyret s2 h2 (.Kloop2 _ _ _ _ _ _ _ _ _ h1 h2 hk))
  | .Sbreak, _, _, _, _, _, htr, _ => by
    cases htr; simp [findLabel, Csharpminor.findLabel, FindLabelSpec]
  | .Scontinue, _, _, _, _, _, htr, _ => by
    cases htr; simp [findLabel, Csharpminor.findLabel, FindLabelSpec]
  | .Sreturn none, _, _, _, _, _, htr, _ => by
    cases htr; simp [findLabel, Csharpminor.findLabel, FindLabelSpec]
  | .Sreturn (some a), _, _, _, _, _, htr, _ => by
    simp only [translStatement, res_bind_eq_OK] at htr
    obtain ⟨_, _, _, _, htr⟩ := htr
    cases htr; simp [findLabel, Csharpminor.findLabel, FindLabelSpec]
  | .Sswitch a sl, _, _, _, ts, _, htr, hk => by
    simp only [translStatement, res_bind_eq_OK] at htr
    obtain ⟨ta, _, tsl, hsl, htr⟩ := htr
    have hts : ∃ b, ts = Csharpminor.Stmt.Sblock (.Sswitch b ta tsl) := by
      split at htr <;> cases htr <;> exact ⟨_, rfl⟩
    obtain ⟨b, hb⟩ := hts
    subst hb
    rw [cs_findLabel_block]
    simp only [findLabel, Csharpminor.findLabel]
    exact transl_find_label_ls lbl tyret sl hsl (.Kswitch _ _ _ _ _ hk)
  | .Slabel l s, _, _, _, _, _, htr, hk => by
    simp only [translStatement, res_bind_eq_OK] at htr
    obtain ⟨ts, h, htr⟩ := htr
    cases htr
    simp only [findLabel, Csharpminor.findLabel]
    split
    · exact ⟨_, _, _, _, rfl, h, hk⟩
    · exact transl_find_label lbl tyret s h hk
  | .Sgoto l, _, _, _, _, _, htr, _ => by
    cases htr; simp [findLabel, Csharpminor.findLabel, FindLabelSpec]

/-- `Cshmgenproof.transl_find_label_ls` -/
theorem transl_find_label_ls (lbl : Ident) (tyret : Ty) :
    ∀ (ls : LStmts) {nbrk ncnt : Nat} {k : Cont} {tls : Csharpminor.LblStmt}
      {tk : Csharpminor.Cont},
    translLblStmt rvNorm ce tyret nbrk ncnt ls = .OK tls →
    MatchCont rvNorm ce tge tyret nbrk ncnt k tk →
    FindLabelSpec rvNorm ce tge tyret (findLabelLs lbl ls k) (Csharpminor.findLabelLs lbl tls tk)
  | .LSnil, _, _, _, _, _, htr, _ => by
    cases htr; simp [findLabelLs, Csharpminor.findLabelLs, FindLabelSpec]
  | .LScons o s ls, _, _, _, _, _, htr, hk => by
    simp only [translLblStmt, res_bind_eq_OK] at htr
    obtain ⟨ts, h1, tls', h2, htr⟩ := htr
    cases htr
    rw [cl_findLabelLs_cons, cs_findLabelLs_cons]
    exact findLabelSpec_seq rvNorm ce tge
      (transl_find_label lbl tyret s h1 (.Kseq _ _ _ _ _ _ _ (transl_lbl_stmt_2 h2) hk))
      (fun _ => transl_find_label_ls lbl tyret ls h2 hk)
end

/-! ## Properties of call continuations -/

/-- `Cshmgenproof.match_cont_call_cont` -/
theorem match_cont_call_cont {tyret : Ty} {nbrk ncnt : Nat} {k : Cont} {tk : Csharpminor.Cont}
    (h : MatchCont rvNorm ce tge tyret nbrk ncnt k tk) (nbrk' ncnt' : Nat) :
    MatchCont rvNorm ce tge tyret nbrk' ncnt' (callCont k) (Csharpminor.callCont tk) := by
  induction h with
  | Kstop => exact .Kstop _ _ _
  | Kseq _ _ _ _ _ _ _ _ _ ih => exact ih
  | Kloop1 _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | Kloop2 _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | Kswitch _ _ _ _ _ _ ih => exact ih
  | Kcall _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 => exact .Kcall _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3
  | Kcall_normalize _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 =>
    exact .Kcall_normalize _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4

/-- `Cshmgenproof.match_cont_is_call_cont` -/
theorem match_cont_is_call_cont {tyret : Ty} {nbrk ncnt : Nat} {k : Cont} {tk : Csharpminor.Cont}
    (h : MatchCont rvNorm ce tge tyret nbrk ncnt k tk) (hk : isCallCont k = true) (nbrk' ncnt' : Nat) :
    MatchCont rvNorm ce tge tyret nbrk' ncnt' k tk ∧ Csharpminor.isCallCont tk = true := by
  cases h with
  | Kstop => exact ⟨.Kstop _ _ _, rfl⟩
  | Kcall _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 => exact ⟨.Kcall _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3, rfl⟩
  | Kcall_normalize _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 =>
    exact ⟨.Kcall_normalize _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4, rfl⟩
  | _ => simp [isCallCont] at hk

end MATCH

end Cshmgen
end CC
