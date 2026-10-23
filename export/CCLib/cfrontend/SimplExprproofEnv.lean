/-
  Expression simplification: semantic preservation — port of
  `cfrontend/SimplExprproof.v`, part 1: global environments, properties of
  the smart constructors (`Ederef'`, `Eaddrof'`, `make_normalize`), the
  translation of `deref_loc`/`assign_loc`, bitfield accesses, and the
  evaluation of simple expressions and of their translation (`tr_simple`).

  Differences from Rocq:
  * whole-program statement: the hypothesis is `translProgram fu prog = .OK
    tprog` rather than CompCert's linking-aware `match_prog`, so the
    "compilation unit" is `prog` itself and `linkorder` hypotheses disappear
    (the composite environment used by the translation is
    `prog.prog_comp_env`, which is also the one of both global environments);
  * the mutual inductions on `tr_expr`/`eval_simple_*` are mutual structural
    recursions.
-/
import CCLib.cfrontend.SimplExprspecMain
import CCLib.cfrontend.Cstrategy
import CCLib.common.GlobalenvsTransf
import CCLib.cfrontend.ClightBehaviors
import CCLib.common.EventsProps

namespace CC
namespace SimplExpr

open Destination SetDestination Cstrategy

local macro "zomega" : tactic => `(tactic| ((try dsimp only [CC.Z] at *) <;> omega))

/-! ## Global environments -/

section GENV
variable {fu : Ident} {prog : Csyntax.Program} {tprog : Program}
  (TRANSL : translProgram fu prog = .OK tprog)
include TRANSL

/-- `SimplExprproof.transf_program_match` (whole-program form). -/
theorem transf_program_match :
    MatchProgram (fun f tf => translFundef prog.prog_comp_env fu f = .OK tf) Eq
      prog.toAST tprog.toAST := by
  unfold translProgram at TRANSL
  split at TRANSL
  · cases TRANSL
  · rename_i p1 hp1
    cases TRANSL
    exact match_transform_partial_program hp1

/-- `SimplExprproof.comp_env_preserved` -/
theorem comp_env_preserved : tprog.prog_comp_env = prog.prog_comp_env := by
  unfold translProgram at TRANSL
  split at TRANSL
  · cases TRANSL
  · cases TRANSL; rfl

theorem genv_cenv_preserved :
    tprog.globalenv.genv_cenv = (Csem.globalenv prog).genv_cenv :=
  comp_env_preserved TRANSL

/-- `SimplExprproof.symbols_preserved` -/
theorem symbols_preserved (s : Ident) :
    Genv.findSymbol tprog.globalenv.genv_genv s = Genv.findSymbol (Csem.globalenv prog).genv_genv s :=
  (transf_program_match TRANSL).find_symbol s

/-- `SimplExprproof.senv_preserved` (an equality of symbol environments). -/
theorem senv_preserved :
    Genv.toSenv tprog.globalenv.genv_genv = Genv.toSenv (Csem.globalenv prog).genv_genv :=
  (transf_program_match TRANSL).senv

/-- `SimplExprproof.functions_translated` -/
theorem functions_translated {v : Val} {f : Csyntax.FunDef}
    (h : Genv.findFunct (Csem.globalenv prog).genv_genv v = some f) :
    ∃ tf, Genv.findFunct tprog.globalenv.genv_genv v = some tf ∧ TrFundef prog f tf := by
  obtain ⟨tf, h1, h2⟩ := (transf_program_match TRANSL).find_funct h
  exact ⟨tf, h1, transl_fundef_spec h2⟩

/-- `SimplExprproof.function_ptr_translated` -/
theorem function_ptr_translated {b : Block} {f : Csyntax.FunDef}
    (h : Genv.findFunctPtr (Csem.globalenv prog).genv_genv b = some f) :
    ∃ tf, Genv.findFunctPtr tprog.globalenv.genv_genv b = some tf ∧ TrFundef prog f tf := by
  obtain ⟨tf, h1, h2⟩ := (transf_program_match TRANSL).find_funct_ptr h
  exact ⟨tf, h1, transl_fundef_spec h2⟩

end GENV

/-- `SimplExprproof.type_of_fundef_preserved` -/
theorem type_of_fundef_preserved {p : Csyntax.Program} {f : Csyntax.FunDef} {tf : FunDef}
    (h : TrFundef p f tf) : typeOfFundef tf = Csyntax.typeOfFundef f := by
  cases h with
  | tr_internal f tf h =>
    cases h with
    | tr_function_intro _ h1 h2 h3 _ =>
      simp only [typeOfFundef, Csyntax.typeOfFundef, typeOfFunction, Csyntax.typeOfFunction,
        h1, h2, h3]
  | tr_external => rfl

/-- `SimplExprproof.function_return_preserved` -/
theorem function_return_preserved {ce : CompositeEnv} {f : Csyntax.Function} {tf : Function}
    (h : TrFunction ce f tf) : tf.fn_return = f.fn_return := by
  cases h with
  | tr_function_intro _ h1 => exact h1

/-! ## Properties of smart constructors -/

/-- `SimplExprproof.eval_Ederef'` -/
theorem eval_Ederef' {ge : CGenv} {e le m a t l ofs}
    (h : EvalExpr ge e le m a (.Vptr l ofs)) : EvalLvalue ge e le m (Ederef' a t) l ofs .Full := by
  unfold Ederef'
  split
  · rename_i a' ty'
    split
    · cases h with
      | Eaddrof _ _ _ _ h => exact h
      | Elvalue _ _ _ _ _ hl _ => cases hl
    · exact .Ederef _ _ _ _ h
  · exact .Ederef _ _ _ _ h

/-- `SimplExprproof.typeof_Ederef'` -/
theorem typeof_Ederef' (a : Expr) (t : Ty) : typeof (Ederef' a t) = t := by
  unfold Ederef'
  split
  · split
    · rename_i h; exact h.symm
    · rfl
  · rfl

/-- `SimplExprproof.eval_Eaddrof'` -/
theorem eval_Eaddrof' {ge : CGenv} {e le m a t l ofs}
    (h : EvalLvalue ge e le m a l ofs .Full) : EvalExpr ge e le m (Eaddrof' a t) (.Vptr l ofs) := by
  unfold Eaddrof'
  split
  · split
    · cases h with
      | Ederef _ _ _ _ h => exact h
    · exact .Eaddrof _ _ _ _ h
  · exact .Eaddrof _ _ _ _ h

/-- `SimplExprproof.typeof_Eaddrof'` -/
theorem typeof_Eaddrof' (a : Expr) (t : Ty) : typeof (Eaddrof' a t) = t := by
  unfold Eaddrof'
  split
  · split
    · rename_i h; exact h.symm
    · rfl
  · rfl

/-- `SimplExprproof.eval_make_normalize` -/
theorem eval_make_normalize {ge : CGenv} {e le m a n sz sg sg1 attr} {width : Z}
    (hw0 : 0 < width) (hw1 : width ≤ bitsizeIntsize sz)
    (hty : typeof a = .Tint sz sg1 attr) (hev : EvalExpr ge e le m a (.Vint n)) :
    EvalExpr ge e le m (makeNormalize sz sg width a)
      (.Vint (Cop.bitfieldNormalize sz sg width n)) := by
  have hb : bitsizeIntsize sz ≤ 32 := by cases sz <;> decide
  obtain ⟨k, rfl⟩ : ∃ k : Nat, width = (k : Z) := ⟨width.toNat, by zomega⟩
  have hk : (k : Z).toNat = k := by zomega
  have hk1 : 1 ≤ k := by zomega
  have hk2 : k ≤ 32 := by zomega
  unfold makeNormalize Cop.bitfieldNormalize
  by_cases hc : sz = .IBool ∨ sg = .Unsigned
  · have hc' : (sz = .IBool || sg = .Unsigned) = true := by
      rcases hc with h | h <;> simp [h]
    rw [if_pos hc, if_pos hc', Integers.Int.zero_ext_and, hk]
    refine .Ebinop _ _ _ _ _ _ _ hev (.Econst_int _ _) ?_
    have : twoP (k : Z) - 1 = 2 ^ k - 1 := by
      simp only [twoP]; rw [if_pos (by zomega), hk]
    rw [hty, this]; cases sz <;> cases sg1 <;> rfl
  · have hc' : (sz = .IBool || sg = .Unsigned) = false := by
      simp only [not_or] at hc; simp [hc.1, hc.2]
    rw [if_neg hc]
    simp only [hc', hk, Bool.false_eq_true, if_false]
    have hamt : (Integers.Int.repr (Integers.Int.zwordsize - (k : Z))).toNat = 32 - k := by
      simp only [Integers.Int.repr, Integers.MI.repr, Integers.Int.zwordsize]
      rw [BitVec.toNat_ofInt]
      have : ((32 : Z) - (k : Z)) = ((32 - k : Nat) : Z) := by zomega
      rw [this]; zomega
    have hlt : Integers.Int.ltu (Integers.Int.repr (Integers.Int.zwordsize - (k : Z)))
        Integers.Int.iwordsize = true := by
      simp only [Integers.Int.ltu, Integers.MI.ltu, BitVec.ult, hamt, Integers.Int.iwordsize,
        Integers.MI.iwordsize, BitVec.toNat_ofNat]
      simp only [decide_eq_true_eq]; zomega
    refine .Ebinop _ _ _ _ _ _ _ (.Ebinop _ _ _ _ _ _
      (.Vint (Integers.Int.shl n (Integers.Int.repr (Integers.Int.zwordsize - (k : Z)))))
      hev (.Econst_int _ _) ?_) (.Econst_int _ _) ?_
    · rw [hty]
      show Cop.semShl _ _ _ _ = _
      cases sz <;> cases sg1 <;> simp [Cop.semShl, Cop.semShift, Cop.classifyShift, hlt] <;> rfl
    · show Cop.semShr _ _ _ _ = _
      have hse : Integers.Int.sign_ext k n = Integers.Int.shr
          (Integers.Int.shl n (Integers.Int.repr (Integers.Int.zwordsize - (k : Z))))
          (Integers.Int.repr (Integers.Int.zwordsize - (k : Z))) := by
        simp only [Integers.Int.sign_ext, Integers.MI.sign_ext, Integers.Int.shr, Integers.MI.shr,
          Integers.Int.shl, Integers.MI.shl, hamt]
        rw [if_neg (by omega)]
        by_cases h32 : k = 32
        · subst h32; simp
        · rw [if_neg (by omega)]
      rw [hse]
      simp [Cop.semShr, Cop.semShift, typeof, type_int32s, Cop.classifyShift, typeconv, hlt]
      rfl


/-! ## Translation of `deref_loc` and `assign_loc` -/

theorem chunkForVolatileType_eq_some {ty : Ty} {bf : Bitfield} {chunk : Chunk} :
    chunkForVolatileType ty bf = some chunk ↔
      typeIsVolatile ty = true ∧ accessMode ty = .By_value chunk ∧ bf = .Full := by
  unfold chunkForVolatileType
  cases hv : typeIsVolatile ty
  · simp
  · cases accessMode ty <;> cases bf <;> simp

theorem chunkForVolatileType_eq_none {ty : Ty} {bf : Bitfield} :
    chunkForVolatileType ty bf = none ↔
      ¬ (typeIsVolatile ty = true ∧ ∃ chunk, accessMode ty = .By_value chunk ∧ bf = .Full) := by
  constructor
  · rintro h ⟨h1, chunk, h2, h3⟩
    have := chunkForVolatileType_eq_some.2 ⟨h1, h2, h3⟩
    rw [h] at this; cases this
  · intro h
    cases hc : chunkForVolatileType ty bf with
    | none => rfl
    | some chunk =>
      obtain ⟨h1, h2, h3⟩ := chunkForVolatileType_eq_some.1 hc
      exact absurd ⟨h1, chunk, h2, h3⟩ h

section DEREF_ASSIGN
variable {ge : Csem.CGenv} {tge : CGenv}
  (hse : Genv.toSenv tge.genv_genv = Genv.toSenv ge.genv_genv)
  (hce : tge.genv_cenv = ge.genv_cenv)

include hse in
/-- `SimplExprproof.deref_loc_translated` -/
theorem deref_loc_translated {ty m b ofs bf t v} (h : Csem.DerefLoc ge ty m b ofs bf t v) :
    match chunkForVolatileType ty bf with
    | none => t = E0 ∧ DerefLoc ty m b ofs bf v
    | some chunk => bf = .Full ∧ VolatileLoad (Genv.toSenv tge.genv_genv) chunk m b ofs t v := by
  cases h with
  | value chunk v ham hvol hld =>
    rw [chunkForVolatileType_eq_none.2 (by simp [hvol])]
    exact ⟨rfl, .value _ _ ham hld⟩
  | volatile chunk t v ham hvol hv =>
    rw [chunkForVolatileType_eq_some.2 ⟨hvol, ham, rfl⟩]
    exact ⟨rfl, hse ▸ hv⟩
  | reference ham =>
    rw [chunkForVolatileType_eq_none.2 (by simp [ham])]
    exact ⟨rfl, .reference ham⟩
  | copy ham =>
    rw [chunkForVolatileType_eq_none.2 (by simp [ham])]
    exact ⟨rfl, .copy ham⟩
  | bitfield sz sg pos width v hl =>
    rw [chunkForVolatileType_eq_none.2 (by simp)]
    exact ⟨rfl, .bitfield _ _ _ _ _ hl⟩

include hse hce in
/-- `SimplExprproof.assign_loc_translated` -/
theorem assign_loc_translated {ty m b ofs bf v t m' v'}
    (h : Csem.AssignLoc ge ty m b ofs bf v t m' v') :
    match chunkForVolatileType ty bf with
    | none => t = E0 ∧ AssignLoc tge.genv_cenv ty m b ofs bf v m'
    | some chunk => bf = .Full ∧ VolatileStore (Genv.toSenv tge.genv_genv) chunk m b ofs v t m' := by
  cases h with
  | value v chunk m' ham hvol hst =>
    rw [chunkForVolatileType_eq_none.2 (by simp [hvol])]
    exact ⟨rfl, .value _ _ _ ham hst⟩
  | volatile v chunk t m' ham hvol hv =>
    rw [chunkForVolatileType_eq_some.2 ⟨hvol, ham, rfl⟩]
    exact ⟨rfl, hse ▸ hv⟩
  | copy b' ofs' bytes m' ham h1 h2 h3 h4 h5 =>
    rw [chunkForVolatileType_eq_none.2 (by simp [ham])]
    rw [hce]
    exact ⟨rfl, .copy _ _ _ _ ham (fun _ => Int.emod_eq_zero_of_dvd h1)
      (fun _ => Int.emod_eq_zero_of_dvd h2) h3 h4 h5⟩
  | bitfield sz sg pos width v m' v' hs =>
    rw [chunkForVolatileType_eq_none.2 (by simp)]
    exact ⟨rfl, .bitfield _ _ _ _ _ _ _ hs⟩

end DEREF_ASSIGN

/-! ## Bitfield accesses -/

/-- `SimplExprproof.is_bitfield_access_sound` (the composite environment of
    the target global environment is the one used by the translation). -/
theorem is_bitfield_access_sound {tge : CGenv} {ce : CompositeEnv} (hce : tge.genv_cenv = ce)
    {e le m a b ofs bf bf'} (h : EvalLvalue tge e le m a b ofs bf)
    (htr : TrIsBitfieldAccess ce a bf') : bf' = bf := by
  subst hce
  cases h with
  | Evar_local => exact htr
  | Evar_global => exact htr
  | Ederef => exact htr
  | Efield_struct a i ty l ofs id co att delta bf _ hty hco hfo =>
    obtain ⟨co', ofs', h1⟩ := htr
    rw [hty] at h1
    obtain ⟨h1, h2⟩ := h1
    rw [hco] at h1; cases h1
    rw [hfo] at h2; cases h2; rfl
  | Efield_union a i ty l ofs id co att delta bf _ hty hco hfo =>
    obtain ⟨co', ofs', h1⟩ := htr
    rw [hty] at h1
    obtain ⟨h1, h2⟩ := h1
    rw [hco] at h1; cases h1
    rw [hfo] at h2; cases h2; rfl

/-- `SimplExprproof.make_assign_value_sound` -/
theorem make_assign_value_sound {ge : Csem.CGenv} {ty m b ofs bf v t m' v'}
    (h : Csem.AssignLoc ge ty m b ofs bf v t m' v') {tge : CGenv} {e le m'' r}
    (hty : typeof r = ty) (hev : EvalExpr tge e le m'' r v) :
    EvalExpr tge e le m'' (makeAssignValue bf r) v' := by
  cases h with
  | value => exact hev
  | volatile => exact hev
  | copy => exact hev
  | bitfield sz sg pos width v m' v' hs =>
    cases hs with
    | intro sz sg1 attr sg pos width m addr c n m' _ hw0 hw1 =>
      exact eval_make_normalize hw0 hw1 hty hev

/-- `SimplExprproof.typeof_make_assign_value` -/
theorem typeof_make_assign_value (bf : Bitfield) (r : Expr) :
    typeof (makeAssignValue bf r) = typeof r := by
  cases bf with
  | Full => rfl
  | Bits sz sg pos width =>
    simp only [makeAssignValue, makeNormalize]
    split <;> rfl

/-! ## Translation of simple expressions -/

section TRANSLATION
variable (ce : CompositeEnv)

theorem final_nil {dst : Destination} (a : Expr) (hd : dst = For_val ∨ dst = For_effects) :
    final dst a = [] := by
  rcases hd with rfl | rfl <;> rfl

mutual
/-- `SimplExprproof.tr_simple_nil` (expressions) -/
theorem tr_simple_expr_nil {le dst r sl a tmps} (h : TrExpr ce le dst r sl a tmps)
    (hd : dst = For_val ∨ dst = For_effects) (hs : simple r = true) : sl = [] := by
  cases h
  case tr_var => exact final_nil _ hd
  case tr_deref h1 =>
    rw [tr_simple_expr_nil h1 (.inl rfl) hs, final_nil _ hd]; rfl
  case tr_field h1 =>
    rw [tr_simple_expr_nil h1 (.inl rfl) hs, final_nil _ hd]; rfl
  case tr_val_effect => rfl
  case tr_val_value => rfl
  case tr_val_set => simp at hd
  case tr_sizeof => exact final_nil _ hd
  case tr_alignof => exact final_nil _ hd
  case tr_valof h1 _ h2 _ _ =>
    simp only [simple, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hs
    cases h2 with
    | tr_rvalof_nonvol =>
      rw [tr_simple_expr_nil h1 (.inl rfl) hs.1, final_nil _ hd]; rfl
    | tr_rvalof_vol => simp_all
  case tr_addrof h1 =>
    rw [tr_simple_expr_nil h1 (.inl rfl) hs, final_nil _ hd]; rfl
  case tr_unop h1 =>
    rw [tr_simple_expr_nil h1 (.inl rfl) hs, final_nil _ hd]; rfl
  case tr_binop h1 h2 _ _ _ =>
    simp only [simple, Bool.and_eq_true] at hs
    rw [tr_simple_expr_nil h1 (.inl rfl) hs.1, tr_simple_expr_nil h2 (.inl rfl) hs.2,
      final_nil _ hd]; rfl
  case tr_cast_effects h1 => exact tr_simple_expr_nil h1 (.inr rfl) hs
  case tr_cast_val h1 =>
    rw [tr_simple_expr_nil h1 (.inl rfl) hs, final_nil _ hd]; rfl
  all_goals simp [simple] at hs

/-- `SimplExprproof.tr_simple_nil` (expression lists) -/
theorem tr_simple_exprlist_nil {le rl sl al tmps} (h : TrExprlist ce le rl sl al tmps)
    (hs : simplelist rl = true) : sl = [] := by
  cases h with
  | tr_nil => rfl
  | tr_cons _ _ _ _ _ _ _ _ _ h1 h2 =>
    simp only [simplelist, Bool.and_eq_true] at hs
    rw [tr_simple_expr_nil h1 (.inl rfl) hs.1, tr_simple_exprlist_nil h2 hs.2]; rfl
end

/-! ## Evaluation of simple expressions and of their translation -/

/-- The relations between the source and target global environments used by
    the simulation proof. -/
structure GenvRel (ge : Csem.CGenv) (tge : CGenv) : Prop where
  symb : ∀ s, Genv.findSymbol tge.genv_genv s = Genv.findSymbol ge.genv_genv s
  senv : Genv.toSenv tge.genv_genv = Genv.toSenv ge.genv_genv
  cenv : tge.genv_cenv = ge.genv_cenv

theorem genvRel_of_transl {fu : Ident} {prog : Csyntax.Program} {tprog : Program}
    (TRANSL : translProgram fu prog = .OK tprog) :
    GenvRel (Csem.globalenv prog) tprog.globalenv :=
  ⟨symbols_preserved TRANSL, senv_preserved TRANSL, genv_cenv_preserved TRANSL⟩

section SIMPLE
variable {ge : Csem.CGenv} {tge : CGenv} (GR : GenvRel ge tge)

/-- The conclusion of `SimplExprproof.tr_simple_rvalue`, by destination. -/
def TrSimpleRes (tge : CGenv) (e : Env) (le : TempEnv) (m : Mem) (r : Csyntax.Expr) (v : Val) :
    Destination → List Stmt → Expr → Prop
  | .For_val, sl, a => sl = [] ∧ Csyntax.typeof r = typeof a ∧ EvalExpr tge e le m a v
  | .For_effects, sl, _ => sl = []
  | .For_set sd, sl, _ =>
    ∃ b, sl = doSet sd b ∧ Csyntax.typeof r = typeof b ∧ EvalExpr tge e le m b v

theorem trSimpleRes_final {tge e le m r v} (dst : Destination) {a : Expr}
    (hty : Csyntax.typeof r = typeof a) (hev : EvalExpr tge e le m a v) :
    TrSimpleRes tge e le m r v dst (final dst a) a := by
  cases dst with
  | For_val => exact ⟨rfl, hty, hev⟩
  | For_effects => rfl
  | For_set sd => exact ⟨a, rfl, hty, hev⟩

include GR

mutual
/-- `SimplExprproof.tr_simple_rvalue` -/
theorem tr_simple_rvalue {e m r v} (h : EvalSimpleRvalue ge e m r v) :
    ∀ {le dst sl a tmps}, TrExpr ce le dst r sl a tmps → TrSimpleRes tge e le m r v dst sl a := by
  intro le dst sl a tmps htr
  cases h with
  | val v ty =>
    cases htr with
    | tr_val_effect => rfl
    | tr_val_value =>
      rename_i hty hev; exact ⟨rfl, hty.symm, hev _ _ _ _ fun _ _ => rfl⟩
    | tr_val_set =>
      rename_i hty hev; exact ⟨_, rfl, hty.symm, hev _ _ _ _ fun _ _ => rfl⟩
  | rvalof b ofs bf l ty v hl hty hvol hd =>
    cases htr with
    | tr_valof =>
      have h1 := ‹TrExpr ce le For_val l _ _ _›
      cases ‹TrRvalof _ _ _ _ _ _› with
      | tr_rvalof_vol => simp_all
      | tr_rvalof_nonvol =>
        obtain ⟨hsl, hty1, hev1⟩ := tr_simple_lvalue hl h1
        subst hsl hty
        have hd' := deref_loc_translated GR.senv hd
        rw [chunkForVolatileType_eq_none.2 (by simp [hvol])] at hd'
        rw [hty1] at hd'
        exact trSimpleRes_final _ hty1 (.Elvalue _ _ _ _ _ hev1 hd'.2)
  | addrof b ofs l ty hl =>
    cases htr with
    | tr_addrof =>
      have h1 := ‹TrExpr ce le For_val l _ _ _›
      obtain ⟨hsl, _, hev1⟩ := tr_simple_lvalue hl h1
      subst hsl
      exact trSimpleRes_final _ (typeof_Eaddrof' _ _).symm (eval_Eaddrof' hev1)
  | unop op r1 ty v1 v hr hop =>
    cases htr with
    | tr_unop =>
      have h1 := ‹TrExpr ce le For_val r1 _ _ _›
      obtain ⟨hsl, hty1, hev1⟩ := tr_simple_rvalue hr h1
      subst hsl
      exact trSimpleRes_final _ rfl (.Eunop _ _ _ _ _ hev1 (hty1 ▸ hop))
  | binop op r1 r2 ty v1 v2 v hr1 hr2 hop =>
    cases htr with
    | tr_binop =>
      have h1 := ‹TrExpr ce le For_val r1 _ _ _›
      have h2 := ‹TrExpr ce le For_val r2 _ _ _›
      obtain ⟨hsl1, hty1, hev1⟩ := tr_simple_rvalue hr1 h1
      obtain ⟨hsl2, hty2, hev2⟩ := tr_simple_rvalue hr2 h2
      subst hsl1 hsl2
      refine trSimpleRes_final _ rfl (.Ebinop _ _ _ _ _ _ _ hev1 hev2 ?_)
      rw [GR.cenv, ← hty1, ← hty2]; exact hop
  | cast ty r1 v1 v hr hop =>
    cases htr with
    | tr_cast_effects => exact tr_simple_rvalue hr ‹TrExpr ce le For_effects r1 _ _ _›
    | tr_cast_val =>
      have h1 := ‹TrExpr ce le For_val r1 _ _ _›
      obtain ⟨hsl, hty1, hev1⟩ := tr_simple_rvalue hr h1
      subst hsl
      exact trSimpleRes_final _ rfl (.Ecast _ _ _ _ hev1 (hty1 ▸ hop))
  | sizeof ty1 ty =>
    cases htr with
    | tr_sizeof =>
      have := EvalExpr.Esizeof (ge := tge) (e := e) (le := le) (m := m) ty1 ty
      rw [GR.cenv] at this
      exact trSimpleRes_final _ rfl this
  | alignof ty1 ty =>
    cases htr with
    | tr_alignof =>
      have := EvalExpr.Ealignof (ge := tge) (e := e) (le := le) (m := m) ty1 ty
      rw [GR.cenv] at this
      exact trSimpleRes_final _ rfl this

/-- `SimplExprproof.tr_simple_lvalue` -/
theorem tr_simple_lvalue {e m l b ofs bf} (h : EvalSimpleLvalue ge e m l b ofs bf) :
    ∀ {le sl a tmps}, TrExpr ce le For_val l sl a tmps →
      sl = [] ∧ Csyntax.typeof l = typeof a ∧ EvalLvalue tge e le m a b ofs bf := by
  intro le sl a tmps htr
  cases h with
  | loc => cases htr
  | var_local x ty b hx =>
    cases htr with
    | tr_var => exact ⟨rfl, rfl, .Evar_local _ _ _ hx⟩
  | var_global x ty b hx hs =>
    cases htr with
    | tr_var => exact ⟨rfl, rfl, .Evar_global _ _ _ hx ((GR.symb _).trans hs)⟩
  | deref r ty b ofs hr =>
    cases htr with
    | tr_deref =>
      have h1 := ‹TrExpr ce le For_val r _ _ _›
      obtain ⟨hsl, _, hev1⟩ := tr_simple_rvalue hr h1
      subst hsl
      exact ⟨rfl, (typeof_Ederef' _ _).symm, eval_Ederef' hev1⟩
  | field_struct r f ty b ofs id co att delta bf hr hty hco hfo =>
    cases htr with
    | tr_field =>
      have h1 := ‹TrExpr ce le For_val r _ _ _›
      obtain ⟨hsl, hty1, hev1⟩ := tr_simple_rvalue hr h1
      subst hsl
      refine ⟨rfl, rfl, .Efield_struct _ _ _ _ _ _ co _ _ _ hev1 (hty1 ▸ hty) ?_ ?_⟩
      · rw [GR.cenv]; exact hco
      · rw [GR.cenv]; exact hfo
  | field_union r f ty b ofs id co att delta bf hr hty hfo hco =>
    cases htr with
    | tr_field =>
      have h1 := ‹TrExpr ce le For_val r _ _ _›
      obtain ⟨hsl, hty1, hev1⟩ := tr_simple_rvalue hr h1
      subst hsl
      refine ⟨rfl, rfl, .Efield_union _ _ _ _ _ _ co _ _ _ hev1 (hty1 ▸ hty) ?_ ?_⟩
      · rw [GR.cenv]; exact hco
      · rw [GR.cenv]; exact hfo
end

/-- `SimplExprproof.tr_simple_exprlist` -/
theorem tr_simple_exprlist {le rl sl al tmps} (htr : TrExprlist ce le rl sl al tmps) :
    ∀ {e m tyl vl}, EvalSimpleList ge e m rl tyl vl →
      sl = [] ∧ EvalExprlist tge e le m al tyl vl := by
  intro e m tyl vl h
  cases htr with
  | tr_nil => cases h; exact ⟨rfl, .nil⟩
  | tr_cons =>
    have h1 := ‹TrExpr ce le For_val _ _ _ _›
    have h2 := ‹TrExprlist ce le _ _ _ _›
    cases h with
    | cons _ _ ty tyl v vl v' hr hc hl =>
      obtain ⟨hsl1, hty1, hev1⟩ := tr_simple_rvalue ce GR hr h1
      obtain ⟨hsl2, hev2⟩ := tr_simple_exprlist h2 hl
      subst hsl1 hsl2
      exact ⟨rfl, .cons _ _ _ _ _ _ _ hev1 (hty1 ▸ hc) hev2⟩

end SIMPLE

end TRANSLATION

end SimplExpr
end CC
