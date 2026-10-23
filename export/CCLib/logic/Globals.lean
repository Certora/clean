/-
  Reading a global variable in the separation logic.

  A global `g` of scalar type is the lvalue `Evar g ty`: when `g` is not
  shadowed by a local (`e.get g = none`) it denotes offset `0` of the block
  `Genv.find_symbol ge g` (`EvalLvalue.Evar_global`).  Owning that cell
  (VST's `data_at sh ty v (gv _g)`) makes the read evaluate to its contents
  (`eval_global_mapsto`), as `eval_deref_mapsto` does for `*p`.
-/
import CCLib.logic.SepHoareCore

namespace CC

open HProp

/-- Evaluating a global variable `g` whose cell the fragment owns. -/
theorem eval_global_mapsto {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem}
    {id : Ident} {ty : Ty} {chunk : Chunk} {p : Permission} {b : Block} {v : Val} {h : Heap}
    (hloc : e.get id = none)
    (hsym : Genv.findSymbol ge.genv_genv id = some b)
    (hacc : accessMode ty = .By_value chunk)
    (hpr : permOrder p .Readable = true)
    (hm : mapsto chunk p b 0 v h)
    (hag : Heap.Agrees h m) :
    EvalExpr ge e le m (.Evar id ty) (Val.loadResult chunk v) := by
  refine EvalExpr.Elvalue _ b Integers.Ptrofs.zero .Full _
    (EvalLvalue.Evar_global id b ty hloc hsym) (DerefLoc.value chunk _ hacc ?_)
  rw [Mem.loadv_ptr _ _ _ _ (Or.inr (by cases chunk <;> decide))]
  exact mapsto_load hpr hm hag

/-- A global variable `g` (not shadowed by a local) as an l-value: offset `0`
    of its block. -/
theorem lvalue_global {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {id : Ident} {ty : Ty}
    {b : Block} (hloc : e.get id = none) (hsym : Genv.findSymbol ge.genv_genv id = some b) :
    EvalLvalue ge e le m (.Evar id ty) b Integers.Ptrofs.zero .Full :=
  EvalLvalue.Evar_global id b ty hloc hsym

/-- A field `g.fld` of a global `struct` `g`: offset `delta` of `g`'s block. -/
theorem lvalue_global_field {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {id sid fld : Ident}
    {att : Attr} {ty : Ty} {b : Block} {co : Composite} {delta : Z}
    (hloc : e.get id = none) (hsym : Genv.findSymbol ge.genv_genv id = some b)
    (hco : ge.genv_cenv.get sid = some co)
    (hoff : fieldOffset ge.genv_cenv fld co.co_members = .OK (delta, .Full)) :
    EvalLvalue ge e le m (.Efield (.Evar id (.Tstruct sid att)) fld ty) b
      (Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.repr delta)) .Full :=
  EvalLvalue.Efield_struct _ fld ty b Integers.Ptrofs.zero sid co att delta .Full
    (EvalExpr.Elvalue _ b _ .Full _ (lvalue_global hloc hsym) (DerefLoc.copy rfl)) rfl hco hoff

end CC
