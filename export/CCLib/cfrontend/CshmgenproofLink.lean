/-
  Translation from Clight to Csharpminor: separate compilation — the linking
  part of `cfrontend/Cshmgenproof.v` (`match_prog`, `transf_program_match`,
  `TransfCshmgenLink`) and the semantic preservation theorem stated for
  `match_prog`.

  Difference from Rocq: CompCert proves the simulation directly for
  `match_prog`, where each function is translated with the composite
  environment of its own compilation unit.  Here the simulation proof of
  `CshmgenproofStep` is reused: every use of the composite environment by the
  translation is guarded (`Cshmgen.sizeof`/`alignof` check completeness,
  `make_field_access` checks that the composite is defined), so a function
  translated in a compilation unit translates to the same code in the whole
  linked program, whose composite environment extends the unit's
  (`translFunction_stable`).
-/
import CCLib.cfrontend.CshmgenproofStep
import CCLib.cfrontend.CtypesLinking
import CCLib.common.LinkingFundef

namespace CC
namespace Cshmgen

open CtypesLinking Smallstep

/-! ## Stability of the translation under extension of the composite environment -/

/-- `x'` succeeds with the same result as `x` whenever `x` succeeds. -/
def Stab {A : Type} (x x' : Res A) : Prop := ∀ a, x = .OK a → x' = .OK a

theorem Stab.refl {A : Type} (x : Res A) : Stab x x := fun _ h => h

theorem Stab.bind {A B : Type} {x x' : Res A} {f g : A → Res B} (h : Stab x x')
    (hf : ∀ a, Stab (f a) (g a)) : Stab (x >>= f) (x' >>= g) := by
  intro b hb
  cases hx : x with
  | Error => rw [hx] at hb; cases hb
  | OK a =>
    rw [hx] at hb
    rw [h a hx]
    exact hf a b hb

section STABLE
variable {ce ce' : CompositeEnv} (hext : EnvExtends ce ce') (hcons : EnvConsistent ce)
include hext

theorem sizeof_stab (t : Ty) : Stab (sizeof ce t) (sizeof ce' t) := by
  intro z h
  unfold sizeof at h ⊢
  split at h
  · rename_i hc
    cases h
    rw [if_pos (completeType_stable hext t hc), CtypesLinking.sizeof_stable hext t hc]
  · cases h

theorem alignof_stab (t : Ty) : Stab (alignof ce t) (alignof ce' t) := by
  intro z h
  unfold alignof at h ⊢
  split at h
  · rename_i hc
    cases h
    rw [if_pos (completeType_stable hext t hc), CtypesLinking.alignof_stable hext t hc]
  · cases h

theorem alignofBlockcopy_stable : ∀ (t : Ty), completeType ce t = true →
    alignofBlockcopy ce' t = alignofBlockcopy ce t
  | .Tvoid, _ => rfl
  | .Tint sz _ _, _ => by cases sz <;> rfl
  | .Tlong _ _, _ => rfl
  | .Tfloat sz _, _ => by cases sz <;> rfl
  | .Tpointer _ _, _ => rfl
  | .Tarray t _ _, h => by simp only [alignofBlockcopy]; exact alignofBlockcopy_stable t h
  | .Tfunction _ _ _, _ => rfl
  | .Tstruct _ _, h => by simp only [alignofBlockcopy]; rw [get_stable hext h]
  | .Tunion _ _, h => by simp only [alignofBlockcopy]; rw [get_stable hext h]

theorem layoutField_stable {pos : Z} {m : Member} (h : completeType ce m.type = true) :
    layoutField ce' pos m = layoutField ce pos m := by
  cases m with
  | Member_plain id t =>
    simp only [Member.type] at h
    simp only [layoutField, bitalignof]
    rw [CtypesLinking.alignof_stable hext t h]
  | Member_bitfield => rfl

theorem fieldOffsetRec_stable (id : Ident) : ∀ (ms : List Member) (pos : Z),
    completeMembers ce ms = true → fieldOffsetRec ce' id pos ms = fieldOffsetRec ce id pos ms
  | [], _, _ => rfl
  | m :: ms, pos, h => by
    simp only [completeMembers, Bool.and_eq_true] at h
    simp only [fieldOffsetRec]
    rw [layoutField_stable hext h.1, nextField_stable hext h.1,
      fieldOffsetRec_stable id ms _ h.2]

theorem unionFieldOffset_stable (id : Ident) : ∀ (ms : List Member),
    completeMembers ce ms = true → unionFieldOffset ce' id ms = unionFieldOffset ce id ms
  | [], _ => rfl
  | m :: ms, h => by
    simp only [completeMembers, Bool.and_eq_true] at h
    simp only [unionFieldOffset]
    rw [layoutField_stable hext h.1, unionFieldOffset_stable id ms h.2]

include hcons in
theorem makeFieldAccess_stab (ty : Ty) (f : Ident) (a : Csharpminor.Expr) :
    Stab (makeFieldAccess ce ty f a) (makeFieldAccess ce' ty f a) := by
  intro r h
  cases ty with
  | Tstruct id att =>
    simp only [makeFieldAccess] at h ⊢
    cases hco : PTree.get id ce with
    | none => simp [hco, bind, Res.bind] at h
    | some co =>
      rw [hext id co hco]
      simp only [hco] at h
      simp only [fieldOffset] at h ⊢
      rw [fieldOffsetRec_stable hext f _ _ (hcons id co hco).complete]
      exact h
  | Tunion id att =>
    simp only [makeFieldAccess] at h ⊢
    cases hco : PTree.get id ce with
    | none => simp [hco, bind, Res.bind] at h
    | some co =>
      rw [hext id co hco]
      simp only [hco] at h
      simp only
      rw [unionFieldOffset_stable hext f _ (hcons id co hco).complete]
      exact h
  | _ => simp [makeFieldAccess, bind, Res.bind] at h

theorem makeAddPtrInt_stab (ty : Ty) (si : Signedness) (e1 e2 : Csharpminor.Expr) :
    Stab (makeAddPtrInt ce ty si e1 e2) (makeAddPtrInt ce' ty si e1 e2) :=
  Stab.bind (sizeof_stab hext ty) (fun _ => Stab.refl _)

theorem makeAddPtrLong_stab (ty : Ty) (e1 e2 : Csharpminor.Expr) :
    Stab (makeAddPtrLong ce ty e1 e2) (makeAddPtrLong ce' ty e1 e2) :=
  Stab.bind (sizeof_stab hext ty) (fun _ => Stab.refl _)

theorem translBinop_stab (op : Binop) (a : Csharpminor.Expr) (ta : Ty) (b : Csharpminor.Expr)
    (tb : Ty) : Stab (translBinop ce op a ta b tb) (translBinop ce' op a ta b tb) := by
  cases op <;> simp only [translBinop] <;> try exact Stab.refl _
  · unfold makeAdd
    split
    · exact makeAddPtrInt_stab hext _ _ _ _
    · exact makeAddPtrLong_stab hext _ _ _
    · exact makeAddPtrInt_stab hext _ _ _ _
    · exact makeAddPtrLong_stab hext _ _ _
    · exact Stab.refl _
  · unfold makeSub
    split
    · exact Stab.bind (sizeof_stab hext _) (fun _ => Stab.refl _)
    · exact Stab.bind (sizeof_stab hext _) (fun _ => Stab.refl _)
    · exact Stab.bind (sizeof_stab hext _) (fun _ => Stab.refl _)
    · exact Stab.refl _

theorem makeStore_stab (addr : Csharpminor.Expr) (ty : Ty) (bf : Bitfield)
    (rhs : Csharpminor.Expr) : Stab (makeStore ce addr ty bf rhs) (makeStore ce' addr ty bf rhs) := by
  unfold makeStore
  split
  · split
    · exact Stab.refl _
    · unfold makeMemcpy
      intro r h
      unfold sizeof at h ⊢
      by_cases hc : completeType ce ty = true
      · rw [if_pos hc] at h
        rw [if_pos (completeType_stable hext ty hc), CtypesLinking.sizeof_stable hext ty hc,
          alignofBlockcopy_stable hext ty hc]
        exact h
      · rw [if_neg hc] at h
        simp [bind, Res.bind] at h
    · exact Stab.refl _
  · exact Stab.refl _

include hcons in
mutual
theorem translExpr_stab : ∀ (a : Expr), Stab (translExpr ce a) (translExpr ce' a)
  | .Econst_int .. => Stab.refl _
  | .Econst_float .. => Stab.refl _
  | .Econst_single .. => Stab.refl _
  | .Econst_long .. => Stab.refl _
  | .Evar .. => Stab.refl _
  | .Etempvar .. => Stab.refl _
  | .Ederef b _ => by
    simp only [translExpr]
    exact Stab.bind (translExpr_stab b) (fun _ => Stab.refl _)
  | .Eaddrof b _ => by
    simp only [translExpr]
    exact Stab.bind (translLvalue_stab b) (fun _ => Stab.refl _)
  | .Eunop _ b _ => by
    simp only [translExpr]
    exact Stab.bind (translExpr_stab b) (fun _ => Stab.refl _)
  | .Ebinop _ b c _ => by
    simp only [translExpr]
    exact Stab.bind (translExpr_stab b) (fun _ => Stab.bind (translExpr_stab c)
      (fun _ => translBinop_stab hext _ _ _ _ _))
  | .Ecast b _ => by
    simp only [translExpr]
    exact Stab.bind (translExpr_stab b) (fun _ => Stab.refl _)
  | .Efield b _ _ => by
    simp only [translExpr]
    exact Stab.bind (translExpr_stab b) (fun _ => Stab.bind (makeFieldAccess_stab hext hcons _ _ _)
      (fun _ => Stab.refl _))
  | .Esizeof ty _ => by
    simp only [translExpr]
    exact Stab.bind (sizeof_stab hext ty) (fun _ => Stab.refl _)
  | .Ealignof ty _ => by
    simp only [translExpr]
    exact Stab.bind (alignof_stab hext ty) (fun _ => Stab.refl _)

theorem translLvalue_stab : ∀ (a : Expr), Stab (translLvalue ce a) (translLvalue ce' a)
  | .Evar .. => Stab.refl _
  | .Ederef b _ => by
    simp only [translLvalue]
    exact Stab.bind (translExpr_stab b) (fun _ => Stab.refl _)
  | .Efield b _ _ => by
    simp only [translLvalue]
    exact Stab.bind (translExpr_stab b) (fun _ => makeFieldAccess_stab hext hcons _ _ _)
  | .Econst_int .. => Stab.refl _
  | .Econst_float .. => Stab.refl _
  | .Econst_single .. => Stab.refl _
  | .Econst_long .. => Stab.refl _
  | .Etempvar .. => Stab.refl _
  | .Eaddrof .. => Stab.refl _
  | .Eunop .. => Stab.refl _
  | .Ebinop .. => Stab.refl _
  | .Ecast .. => Stab.refl _
  | .Esizeof .. => Stab.refl _
  | .Ealignof .. => Stab.refl _
end

include hcons in
theorem translArglist_stab : ∀ (al : List Expr) (tyl : List Ty),
    Stab (translArglist ce al tyl) (translArglist ce' al tyl)
  | [], [] => Stab.refl _
  | [], _ :: _ => Stab.refl _
  | a :: al, ty :: tyl => by
    simp only [translArglist]
    exact Stab.bind (translExpr_stab hext hcons a) (fun _ => Stab.bind (Stab.refl _)
      (fun _ => Stab.bind (translArglist_stab al tyl) (fun _ => Stab.refl _)))
  | a :: al, [] => by
    simp only [translArglist]
    exact Stab.bind (translExpr_stab hext hcons a) (fun _ => Stab.bind (Stab.refl _)
      (fun _ => Stab.bind (translArglist_stab al []) (fun _ => Stab.refl _)))

variable (rvNorm : XType → Bool)

include hcons in
mutual
theorem translStatement_stab (tyret : Ty) : ∀ (nbrk ncnt : Nat) (s : Stmt),
    Stab (translStatement rvNorm ce tyret nbrk ncnt s) (translStatement rvNorm ce' tyret nbrk ncnt s)
  | _, _, .Sskip => Stab.refl _
  | _, _, .Sassign b c => by
    simp only [translStatement]
    exact Stab.bind (translLvalue_stab hext hcons b) (fun _ =>
      Stab.bind (translExpr_stab hext hcons c) (fun _ => Stab.bind (Stab.refl _)
        (fun _ => makeStore_stab hext _ _ _ _)))
  | _, _, .Sset _ b => by
    simp only [translStatement]
    exact Stab.bind (translExpr_stab hext hcons b) (fun _ => Stab.refl _)
  | _, _, .Scall _ b cl => by
    simp only [translStatement]
    split
    · exact Stab.bind (translExpr_stab hext hcons b) (fun _ =>
        Stab.bind (translArglist_stab hext hcons cl _) (fun _ => Stab.refl _))
    · exact Stab.refl _
  | _, _, .Sbuiltin _ _ _ bl => by
    simp only [translStatement]
    exact Stab.bind (translArglist_stab hext hcons bl _) (fun _ => Stab.refl _)
  | nbrk, ncnt, .Ssequence s1 s2 => by
    simp only [translStatement]
    exact Stab.bind (translStatement_stab tyret nbrk ncnt s1) (fun _ =>
      Stab.bind (translStatement_stab tyret nbrk ncnt s2) (fun _ => Stab.refl _))
  | nbrk, ncnt, .Sifthenelse e s1 s2 => by
    simp only [translStatement]
    exact Stab.bind (translExpr_stab hext hcons e) (fun _ =>
      Stab.bind (translStatement_stab tyret nbrk ncnt s1) (fun _ =>
        Stab.bind (translStatement_stab tyret nbrk ncnt s2) (fun _ => Stab.refl _)))
  | _, ncnt, .Sloop s1 s2 => by
    simp only [translStatement]
    exact Stab.bind (translStatement_stab tyret 1 0 s1) (fun _ =>
      Stab.bind (translStatement_stab tyret 0 (ncnt + 1) s2) (fun _ => Stab.refl _))
  | _, _, .Sbreak => Stab.refl _
  | _, _, .Scontinue => Stab.refl _
  | _, _, .Sreturn (some e) => by
    simp only [translStatement]
    exact Stab.bind (translExpr_stab hext hcons e) (fun _ => Stab.bind (Stab.refl _)
      (fun _ => Stab.refl _))
  | _, _, .Sreturn none => Stab.refl _
  | _, ncnt, .Sswitch a sl => by
    simp only [translStatement]
    exact Stab.bind (translExpr_stab hext hcons a) (fun _ =>
      Stab.bind (translLblStmt_stab tyret 0 (ncnt + 1) sl) (fun _ => Stab.refl _))
  | nbrk, ncnt, .Slabel _ s => by
    simp only [translStatement]
    exact Stab.bind (translStatement_stab tyret nbrk ncnt s) (fun _ => Stab.refl _)
  | _, _, .Sgoto _ => Stab.refl _

theorem translLblStmt_stab (tyret : Ty) : ∀ (nbrk ncnt : Nat) (sl : LStmts),
    Stab (translLblStmt rvNorm ce tyret nbrk ncnt sl) (translLblStmt rvNorm ce' tyret nbrk ncnt sl)
  | _, _, .LSnil => Stab.refl _
  | nbrk, ncnt, .LScons _ s sl => by
    simp only [translLblStmt]
    exact Stab.bind (translStatement_stab tyret nbrk ncnt s) (fun _ =>
      Stab.bind (translLblStmt_stab tyret nbrk ncnt sl) (fun _ => Stab.refl _))
end

omit hext in
theorem mmap_stab {A B : Type} {f g : A → Res B} (h : ∀ a, Stab (f a) (g a)) :
    ∀ (l : List A), Stab (mmap f l) (mmap g l)
  | [] => Stab.refl _
  | a :: l => by
    simp only [mmap]
    exact Stab.bind (h a) (fun _ => Stab.bind (mmap_stab h l) (fun _ => Stab.refl _))

include hcons in
/-- A function translated with the composite environment `ce` is translated
    identically with any consistent extension `ce'`. -/
theorem translFunction_stable (f : Function) :
    Stab (translFunction rvNorm ce f) (translFunction rvNorm ce' f) := by
  unfold translFunction
  exact Stab.bind (translStatement_stab hext hcons rvNorm _ _ _ _) (fun _ =>
    Stab.bind (mmap_stab (fun (v : Ident × Ty) => Stab.bind (sizeof_stab hext v.2) (fun _ => Stab.refl _)) _)
      (fun _ => Stab.refl _))

include hcons in
theorem matchFundef_stable {f : FunDef} {tf : Csharpminor.Fundef}
    (h : MatchFundef rvNorm ce f tf) : MatchFundef rvNorm ce' f tf := by
  cases h with
  | internal f tf htr => exact .internal _ _ (translFunction_stable hext hcons rvNorm f tf htr)
  | external ef args res cc hsig => exact .external _ _ _ _ hsig

end STABLE

/-! ## `match_prog` and linking -/

/-- `Cshmgenproof.match_prog`: every function is translated with the
    composite environment of a compilation unit of the program. -/
def MatchProgLink (rvNorm : XType → Bool) (p : WFProgram) (tp : Csharpminor.Program) : Prop :=
  Linking.MatchProgramGen (fun (cu : WFProgram) f tf => MatchFundef rvNorm cu.val.prog_comp_env f tf)
    (fun (_ : Ty) (_ : Unit) => True) p p.toAST tp

/-- `Cshmgenproof.transf_program_match` -/
theorem transf_program_match_link {rvNorm : XType → Bool} {p : WFProgram}
    {tp : Csharpminor.Program} (h : translProgram rvNorm p.val = .OK tp) :
    MatchProgLink rvNorm p tp :=
  Linking.match_transform_partial_program2 p h (fun _ _ _ e => translFundef_match e)
    (fun _ _ _ _ => trivial)

/-- `Linking.link_match_fundef` for `Cshmgenproof.match_fundef`. -/
theorem link_matchFundef (rvNorm : XType → Bool) :
    Linking.LinkMatchFundef
      (fun (cu : WFProgram) f tf => MatchFundef rvNorm cu.val.prog_comp_env f tf) := by
  intro c1 c2 f1 tf1 f2 tf2 f h m1 m2
  change linkFundef f1 f2 = some f at h
  cases m1 with
  | internal g1 tg1 e1 =>
    cases m2 with
    | internal => simp [linkFundef] at h
    | external ef args res cc hsig =>
      cases ef <;> simp [linkFundef] at h
      subst h
      exact ⟨.Internal tg1, rfl, .inl (.internal _ _ e1)⟩
  | external ef args res cc hsig =>
    cases m2 with
    | internal g2 tg2 e2 =>
      cases ef <;> simp [linkFundef] at h
      subst h
      exact ⟨.Internal tg2, rfl, .inr (.internal _ _ e2)⟩
    | external ef2 args2 res2 cc2 hsig2 =>
      simp only [linkFundef] at h
      split at h
      · rename_i hc
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hc
        cases h
        refine ⟨.External ef, ?_, .inl (.external _ _ _ _ hsig)⟩
        change Linking.linkASTFundef _ _ = _
        simp [Linking.linkASTFundef]
      · cases h

/-- `Ctypes.link_match_program_gen`, for a translation to a language whose
    programs are `AST.program`s. -/
theorem link_match_program_gen_ast {F2 V2 : Type} [Linker F2] [Linker V2]
    {Rf : WFProgram → FunDef → F2 → Prop} {Rv : Ty → V2 → Prop}
    (hlf : Linking.LinkMatchFundef Rf) (hlv : Linking.LinkMatchVarinfo Rv)
    {p1 p2 p : WFProgram} {tp1 tp2 : ASTProgram F2 V2} (h : Linker.link p1 p2 = some p)
    (m1 : Linking.MatchProgramGen Rf Rv p1 p1.toAST tp1)
    (m2 : Linking.MatchProgramGen Rf Rv p2 p2.toAST tp2) :
    ∃ tp, Linker.link tp1 tp2 = some tp ∧ Linking.MatchProgramGen Rf Rv p p.toAST tp := by
  obtain ⟨lo1, lo2⟩ := Linker.link_linkorder h
  obtain ⟨pp, typs, hpp, _, hpa, _⟩ := linkProgram_inv h
  rw [hpa]
  exact Linking.link_match_program hlf hlv hpp m1 m2 lo1 lo2

/-- `Cshmgenproof.TransfCshmgenLink` -/
instance transfCshmgenLink (rvNorm : XType → Bool) : Linking.TransfLink (MatchProgLink rvNorm) where
  transf_link h m1 m2 :=
    link_match_program_gen_ast (link_matchFundef rvNorm)
      (fun _ _ _ _ _ _ _ _ => ⟨(), rfl, trivial⟩) h m1 m2

/-- `match_prog` implies the whole-program relation used by the simulation
    proof: every function is translated with the composite environment of the
    linked program. -/
theorem matchProgram_of_link {rvNorm : XType → Bool} {p : WFProgram} {tp : Csharpminor.Program}
    (h : MatchProgLink rvNorm p tp) :
    MatchProgram (MatchFundef rvNorm p.val.prog_comp_env) (fun _ _ => True) p.val.toAST tp := by
  have h' := Linking.MatchProgramGen.toMatchProgram h
  refine ⟨Genv.MatchDefs.imp (fun f tf ⟨cu, hl, e⟩ => ?_) (fun _ _ e => e) h'.defs,
    h'.main_eq, h'.public_eq⟩
  exact matchFundef_stable hl.2 (fun id co hco => buildCompositeEnv_consistent cu.property hco)
    rvNorm e

/-- `Cshmgenproof.transl_program_correct`, for `match_prog`. -/
theorem transl_program_correct_match (rvNorm : XType → Bool) {p : WFProgram}
    {tp : Csharpminor.Program} (h : MatchProgLink rvNorm p tp)
    (hextw : ∀ name sg, ExtcallWellTyped (externalFunctionsSem name sg) sg)
    (hasmw : ∀ name sg, ExtcallWellTyped (inlineAssemblySem name sg) sg) :
    ForwardSimulation (Clight.semantics2 p.val) (Csharpminor.semantics tp) :=
  transl_program_correct_gen rvNorm p.val tp (matchProgram_of_link h)
    (buildCompositeEnv_wf p.property) hextw hasmw

end Cshmgen
end CC
