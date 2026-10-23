/-
  Correctness of the parts of `backend/SplitLong.vp` used by instruction
  selection on x86-64 (see `CCLib/x86/SplitLong.lean`) — port of the
  corresponding lemmas of `backend/SplitLongproof.v`: `eval_helper`,
  `eval_helper_1`, `eval_longuoffloat`, `eval_floatoflongu`,
  `eval_longuofsingle`, `eval_singleoflongu`.

  Differences from Rocq: Rocq states these lemmas for the global environment
  of a program `prog` with `helper_functions_declared prog hf`.  Here they
  hold for any CminorSel global environment `ge` in which the three runtime
  helpers used on x86-64 are bound to the expected external functions
  (`HelpersDeclaredGe ge hf`); `helpersDeclaredGe_of_program` derives this
  from Rocq's `helper_functions_declared` (shared with
  `CCLib/backend/SplitLongproof.lean`).
-/
import CCLib.x86.SplitLong
import CCLib.x86.SelectOpproof3
import CCLib.backend.SplitLongproof

namespace CC
namespace X86
namespace SplitLongproof

open Op CminorSel SelectOp SplitLong SelectOpproof
open CC.SplitLong (HelperFunctions sigFL sigLF sigLS)
open CC.SplitLongproof (helper_declared helper_functions_declared)

local infixr:67 " ::: " => CminorSel.Exprlist.Econs

/-- The global `id` of the environment `ge` is the runtime function `name`
with signature `sg` (the global-environment form of Rocq's
`helper_declared`). -/
def HelperDeclaredGe (ge : CminorSel.CGenv) (id : Ident) (name : String) (sg : Signature) :
    Prop :=
  ∃ b, Genv.findSymbol ge id = some b ∧
    Genv.findFunctPtr ge b = some (.External (.EF_runtime name sg))

/-- The runtime helpers used by x86-64 instruction selection are declared in
`ge` with their expected names and signatures. -/
def HelpersDeclaredGe (ge : CminorSel.CGenv) (hf : HelperFunctions) : Prop :=
  HelperDeclaredGe ge hf.i64_dtou "__compcert_i64_dtou" sigFL ∧
  HelperDeclaredGe ge hf.i64_utod "__compcert_i64_utod" sigLF ∧
  HelperDeclaredGe ge hf.i64_utof "__compcert_i64_utof" sigLS

theorem helperDeclaredGe_of_program {p : CminorSel.Program} {id : Ident} {name : String}
    {sg : Signature} (hd : helper_declared p id name sg) :
    HelperDeclaredGe p.globalenv id name sg := by
  unfold helper_declared at hd
  rw [ASTProgram.defmap_eq, Genv.find_def_symbol] at hd
  obtain ⟨b, P, Q⟩ := hd
  exact ⟨b, P, (Genv.findFunctPtr_iff _ _ _).2 Q⟩

/-- `helper_functions_declared p hf` implies `HelpersDeclaredGe` for the
global environment of `p`. -/
theorem helpersDeclaredGe_of_program {p : CminorSel.Program} {hf : HelperFunctions}
    (h : helper_functions_declared p hf) : HelpersDeclaredGe p.globalenv hf :=
  ⟨helperDeclaredGe_of_program h.2.1, helperDeclaredGe_of_program h.2.2.2.1,
    helperDeclaredGe_of_program h.2.2.2.2.2.1⟩

section HELPERS

variable {ge : CminorSel.CGenv} {hf : HelperFunctions} {sp : Val} {e : Cminor.Env} {m : Mem}

/-- `eval_helper` -/
theorem eval_helper {bf : Builtins.BuiltinFunction} {le : Letenv} {id : Ident} {name : String}
    {sg : Signature} {args : SplitLong.Exprlist} {vargs : List Val} {vres : Val}
    (hargs : CminorSel.EvalExprlist ge sp e m le args vargs)
    (hd : HelperDeclaredGe ge id name sg)
    (hl : Builtins.lookupBuiltinFunction name sg = some bf)
    (hs : (Builtins.builtinFunctionSem bf).sem vargs = some vres) :
    CminorSel.EvalExpr ge sp e m le (.Eexternal id sg args) vres := by
  obtain ⟨b, P, Q⟩ := hd
  refine .Eexternal _ _ _ _ b (.EF_runtime name sg) _ _ P Q rfl hargs ?_
  show builtinOrExternalSem name sg _ _ _ _ _ _
  unfold builtinOrExternalSem
  rw [hl]
  exact .intro _ _ _ _ hs

/-- `eval_helper_1` -/
theorem eval_helper_1 {bf : Builtins.BuiltinFunction} {le : Letenv} {id : Ident} {name : String}
    {sg : Signature} {arg1 : SplitLong.Expr} {varg1 vres : Val}
    (h1 : CminorSel.EvalExpr ge sp e m le arg1 varg1)
    (hd : HelperDeclaredGe ge id name sg)
    (hl : Builtins.lookupBuiltinFunction name sg = some bf)
    (hs : (Builtins.builtinFunctionSem bf).sem [varg1] = some vres) :
    CminorSel.EvalExpr ge sp e m le (.Eexternal id sg (arg1 ::: .Enil)) vres :=
  eval_helper (.Econs _ _ _ _ _ h1 (.Enil _)) hd hl hs

variable (HELPERS : HelpersDeclaredGe ge hf)
include HELPERS

/-- `eval_longuoffloat` -/
theorem eval_longuoffloat {le : Letenv} {a : SplitLong.Expr} {x y : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (h : Val.longuoffloat x = some y) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (longuoffloat hf a) v ∧ Val.Lessdef y v :=
  ⟨y, eval_helper_1 (bf := .BI_standard .BI_i64_dtou) ha HELPERS.1 (by decide)
    (by rw [← h]; cases x <;> rfl), .refl _⟩

/-- `eval_longuofsingle` -/
theorem eval_longuofsingle {le : Letenv} {a : SplitLong.Expr} {x y : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (h : Val.longuofsingle x = some y) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (longuofsingle hf a) v ∧ Val.Lessdef y v := by
  cases x <;> simp only [Val.longuofsingle, reduceCtorEq] at h
  rename_i f
  obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨v, hv, hl⟩ := eval_floatofsingle _ _ _ ha
  cases hl
  have hd : Floats.Float.toLongu (Floats.Float.ofSingle f) = some n :=
    Floats.Float32.to_longu_double f n hn
  exact eval_longuoffloat HELPERS hv (by simp [Val.floatofsingle, Val.longuoffloat, hd])

/-- `eval_floatoflongu` -/
theorem eval_floatoflongu {le : Letenv} {a : SplitLong.Expr} {x y : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (h : Val.floatoflongu x = some y) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (floatoflongu hf a) v ∧ Val.Lessdef y v :=
  ⟨y, eval_helper_1 (bf := .BI_standard .BI_i64_utod) ha HELPERS.2.1 (by decide)
    (by cases x <;> first | (rw [← h]; rfl) | cases h), .refl _⟩

/-- `eval_singleoflongu` -/
theorem eval_singleoflongu {le : Letenv} {a : SplitLong.Expr} {x y : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (h : Val.singleoflongu x = some y) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (singleoflongu hf a) v ∧ Val.Lessdef y v :=
  ⟨y, eval_helper_1 (bf := .BI_standard .BI_i64_utof) ha HELPERS.2.2 (by decide)
    (by cases x <;> first | (rw [← h]; rfl) | cases h), .refl _⟩

end HELPERS

end SplitLongproof
end X86
end CC
