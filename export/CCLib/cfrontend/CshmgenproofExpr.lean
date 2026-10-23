/-
  Translation from Clight to Csharpminor: semantic preservation — port of
  `cfrontend/Cshmgenproof.v`, part 4 (section `EXPR`): the translation of
  expressions, l-values and argument lists preserves their values
  (`transl_expr_correct`, `transl_lvalue_correct`, `transl_arglist_correct`).

  Whole-program statement: the composite environment of the translation is
  the one of the program (`prog.prog_comp_env`), which is also the one of the
  Clight global environment.
-/
import CCLib.cfrontend.CshmgenproofEnv
import CCLib.cfrontend.CopArith
import CCLib.cfrontend.CopTheory
import CCLib.cfrontend.CtypingPreservation

namespace CC
namespace Cshmgen

open Conventions1 (AbiKind)
open Cminor.BinaryOperation

section EXPR
variable {rvNorm : XType → Bool} {prog : Program} {tprog : Csharpminor.Program}
  (TRANSL : MatchProgram (MatchFundef rvNorm prog.prog_comp_env) (fun _ _ => True) prog.toAST tprog)
  {e : Env} {le : TempEnv} {m : Mem} {te : Csharpminor.Env}
  (MENV : MatchEnv prog.prog_comp_env e te)

local notation "TEV" => Csharpminor.EvalExpr tprog.globalenv te le m

theorem makeFieldAccess_struct {ce : CompositeEnv} {ty : Ty} {i : Ident} {tb a' : Csharpminor.Expr}
    {bf bf' : Bitfield} {id : Ident} {att : Attr} {co : Composite} {delta : Z}
    (hty : ty = .Tstruct id att) (hco : ce.get id = some co)
    (hfo : fieldOffset ce i co.co_members = .OK (delta, bf))
    (h : makeFieldAccess ce ty i tb = .OK (a', bf')) :
    bf' = bf ∧ a' = .Ebinop Oaddl tb (makeLongconst (Integers.Int64.repr delta)) := by
  subst hty
  simp only [makeFieldAccess, hco, hfo, Archi.ptr64, if_true] at h
  cases h; exact ⟨rfl, rfl⟩

theorem makeFieldAccess_union {ce : CompositeEnv} {ty : Ty} {i : Ident} {tb a' : Csharpminor.Expr}
    {bf bf' : Bitfield} {id : Ident} {att : Attr} {co : Composite} {delta : Z}
    (hty : ty = .Tunion id att) (hco : ce.get id = some co)
    (hfo : unionFieldOffset ce i co.co_members = .OK (delta, bf))
    (h : makeFieldAccess ce ty i tb = .OK (a', bf')) :
    bf' = bf ∧ a' = .Ebinop Oaddl tb (makeLongconst (Integers.Int64.repr delta)) := by
  subst hty
  simp only [makeFieldAccess, hco, hfo, Archi.ptr64, if_true] at h
  cases h; exact ⟨rfl, rfl⟩

/-- `Cshmgenproof.transl_expr_lvalue` -/
theorem transl_expr_lvalue {a : Expr} {loc : Block} {ofs : Integers.Ptrofs} {bf : Bitfield}
    {ta : Csharpminor.Expr} (hev : EvalLvalue prog.globalenv e le m a loc ofs bf)
    (htr : translExpr prog.prog_comp_env a = .OK ta) :
    ∃ tb, translLvalue prog.prog_comp_env a = .OK (tb, bf) ∧ makeLoad tb (typeof a) bf = .OK ta := by
  cases hev with
  | Evar_local id l ty _ => exact ⟨_, rfl, htr⟩
  | Evar_global id l ty _ _ => exact ⟨_, rfl, htr⟩
  | Ederef a ty l ofs _ =>
    simp only [translExpr, res_bind_eq_OK] at htr
    obtain ⟨tb, htb, htr⟩ := htr
    exact ⟨tb, by simp only [translLvalue, htb]; rfl, htr⟩
  | Efield_struct a i ty l ofs id co att delta bf _ hty hco hfo =>
    simp only [translExpr, res_bind_eq_OK] at htr
    obtain ⟨tb, htb, ⟨a', bf'⟩, hfa, htr⟩ := htr
    obtain ⟨rfl, -⟩ := makeFieldAccess_struct hty hco hfo hfa
    exact ⟨a', by simp only [translLvalue, htb]; exact hfa, htr⟩
  | Efield_union a i ty l ofs id co att delta bf _ hty hco hfo =>
    simp only [translExpr, res_bind_eq_OK] at htr
    obtain ⟨tb, htb, ⟨a', bf'⟩, hfa, htr⟩ := htr
    obtain ⟨rfl, -⟩ := makeFieldAccess_union hty hco hfo hfa
    exact ⟨a', by simp only [translLvalue, htb]; exact hfa, htr⟩

theorem ptrofs_add_repr (ofs : Integers.Ptrofs) (delta : Z) :
    Integers.Ptrofs.add ofs (Integers.Ptrofs.of_int64 (Integers.Int64.repr delta)) =
      Integers.Ptrofs.add ofs (Integers.Ptrofs.repr delta) := by
  rw [of_int64_id]; rfl

include TRANSL MENV in
mutual
/-- `Cshmgenproof.transl_expr_correct` -/
theorem transl_expr_correct {a : Expr} {v : Val} :
    EvalExpr prog.globalenv e le m a v →
    ∀ {ta}, translExpr prog.prog_comp_env a = .OK ta → TEV ta v
  | .Econst_int _ _, _, htr => by cases htr; exact make_intconst_correct _
  | .Econst_float _ _, _, htr => by cases htr; exact make_floatconst_correct _
  | .Econst_single _ _, _, htr => by cases htr; exact make_singleconst_correct _
  | .Econst_long _ _, _, htr => by cases htr; exact make_longconst_correct _
  | .Etempvar _ _ _ h, _, htr => by cases htr; exact .Evar _ _ h
  | .Eaddrof _ _ _ _ hl, _, htr => by
    simp only [translExpr, res_bind_eq_OK] at htr
    obtain ⟨⟨tb, bf⟩, htb, htr⟩ := htr
    obtain ⟨rfl, hev⟩ := transl_lvalue_correct hl htb
    cases htr; exact hev
  | .Eunop _ _ _ _ _ h hs, _, htr => by
    simp only [translExpr, res_bind_eq_OK] at htr
    obtain ⟨tb, htb, htr⟩ := htr
    exact transl_unop_correct htr hs (transl_expr_correct h htb)
  | .Ebinop _ _ _ _ _ _ _ h1 h2 hs, _, htr => by
    simp only [translExpr, res_bind_eq_OK] at htr
    obtain ⟨tb, htb, tc, htc, htr⟩ := htr
    exact transl_binop_correct htr hs (transl_expr_correct h1 htb) (transl_expr_correct h2 htc)
  | .Ecast _ _ _ _ h hs, _, htr => by
    simp only [translExpr, res_bind_eq_OK] at htr
    obtain ⟨tb, htb, htr⟩ := htr
    exact make_cast_correct htr (transl_expr_correct h htb) hs
  | .Esizeof _ _, _, htr => by
    simp only [translExpr, res_bind_eq_OK] at htr
    obtain ⟨sz, hsz, htr⟩ := htr
    cases htr; rw [transl_sizeof hsz]; exact make_ptrofsconst_correct _
  | .Ealignof _ _, _, htr => by
    simp only [translExpr, res_bind_eq_OK] at htr
    obtain ⟨al, hal, htr⟩ := htr
    cases htr; rw [transl_alignof hal]; exact make_ptrofsconst_correct _
  | .Elvalue _ _ _ _ _ hl hd, _, htr => by
    obtain ⟨tb, htl, hmk⟩ := transl_expr_lvalue hl htr
    obtain ⟨-, hev⟩ := transl_lvalue_correct hl htl
    exact make_load_correct hmk hev hd

/-- `Cshmgenproof.transl_lvalue_correct` -/
theorem transl_lvalue_correct {a : Expr} {b : Block} {ofs : Integers.Ptrofs} {bf : Bitfield} :
    EvalLvalue prog.globalenv e le m a b ofs bf →
    ∀ {ta bf'}, translLvalue prog.prog_comp_env a = .OK (ta, bf') → bf = bf' ∧ TEV ta (.Vptr b ofs)
  | .Evar_local _ _ _ h, _, _, htr => by
    cases htr
    exact ⟨rfl, .Eaddrof _ _ (.local _ _ _ _ (MENV.me_local _ _ _ h))⟩
  | .Evar_global _ _ _ h hs, _, _, htr => by
    cases htr
    exact ⟨rfl, .Eaddrof _ _ (.global _ _ _ (match_env_globals MENV h)
      (by rw [symbols_preserved TRANSL]; exact hs))⟩
  | .Ederef _ _ _ _ h, _, _, htr => by
    simp only [translLvalue, res_bind_eq_OK] at htr
    obtain ⟨tb, htb, htr⟩ := htr
    cases htr
    exact ⟨rfl, transl_expr_correct h htb⟩
  | .Efield_struct _ _ _ _ _ _ _ _ _ _ h hty hco hfo, _, _, htr => by
    simp only [translLvalue, res_bind_eq_OK] at htr
    obtain ⟨tb, htb, htr⟩ := htr
    obtain ⟨rfl, rfl⟩ := makeFieldAccess_struct hty hco hfo htr
    refine ⟨rfl, make_binop_correct (transl_expr_correct h htb) (make_longconst_correct _) ?_⟩
    simp only [Cminor.evalBinop, Val.addl, Archi.ptr64, if_true, ptrofs_add_repr]
  | .Efield_union _ _ _ _ _ _ _ _ _ _ h hty hco hfo, _, _, htr => by
    simp only [translLvalue, res_bind_eq_OK] at htr
    obtain ⟨tb, htb, htr⟩ := htr
    obtain ⟨rfl, rfl⟩ := makeFieldAccess_union hty hco hfo htr
    refine ⟨rfl, make_binop_correct (transl_expr_correct h htb) (make_longconst_correct _) ?_⟩
    simp only [Cminor.evalBinop, Val.addl, Archi.ptr64, if_true, ptrofs_add_repr]
end

include TRANSL MENV in
/-- `Cshmgenproof.transl_arglist_correct` -/
theorem transl_arglist_correct {al : List Expr} {tyl : List Ty} {vl : List Val}
    (h : EvalExprlist prog.globalenv e le m al tyl vl) :
    ∀ {tal}, translArglist prog.prog_comp_env al tyl = .OK tal →
    Csharpminor.EvalExprlist tprog.globalenv te le m tal vl := by
  induction h with
  | nil => intro tal htr; simp only [translArglist] at htr; cases htr; exact .nil
  | cons a bl ty tyl v1 v2 vl ha hc _ ih =>
    intro tal htr
    simp only [translArglist, res_bind_eq_OK] at htr
    obtain ⟨ta1, h1, ta1', h1', ta2, h2, htr⟩ := htr
    cases htr
    exact .cons _ _ _ _ (make_cast_correct h1' (transl_expr_correct TRANSL MENV ha h1) hc) (ih h2)

omit TRANSL in
/-- `Cshmgenproof.transl_arglist_typed` -/
theorem transl_arglist_typed {al : List Expr} {tyl : List Ty} {vl : List Val}
    (h : EvalExprlist prog.globalenv e le m al tyl vl) :
    Val.HasArgtypeList vl (tyl.map argtypeOfType) := by
  induction h with
  | nil => trivial
  | cons a bl ty tyl v1 v2 vl ha hc _ ih =>
    exact ⟨Cop.val_casted_has_argtype (Cop.cast_val_is_casted hc), ih⟩

omit TRANSL in
/-- `Cshmgenproof.typlist_of_arglist_eq` -/
theorem typlist_of_arglist_eq {al : List Expr} {tyl : List Ty} {vl : List Val}
    (h : EvalExprlist prog.globalenv e le m al tyl vl) :
    typlistOfArglist al tyl = tyl.map argtypeOfType := by
  induction h with
  | nil => rfl
  | cons a bl ty tyl v1 v2 vl ha hc _ ih => simp only [typlistOfArglist, List.map_cons, ih]

end EXPR

end Cshmgen
end CC
