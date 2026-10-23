/-
  Evaluation of the arguments of builtin functions — port of the
  `EVAL_BUILTIN_ARG` sections of `common/Events.v`
  (`eval_builtin_arg`, `eval_builtin_args`, determinism,
  `builtin_arg_depends_on_memory`, preservation under symbol-preserving
  environment changes).
-/
import CCLib.common.Events
import CCLib.common.ASTTheory
import CCLib.common.LinkingTheory

namespace CC

/-- `Senv.symbol_address` -/
def Senv.symbolAddress (ge : Senv) (id : Ident) (ofs : Integers.Ptrofs) : Val :=
  match ge.find_symbol id with
  | some b => .Vptr b ofs
  | none => .Vundef

theorem Genv.toSenv_symbolAddress {F V : Type} (ge : Genv F V) (id ofs) :
    (Genv.toSenv ge).symbolAddress id ofs = Genv.symbolAddress ge id ofs := rfl

section EVAL_BUILTIN_ARG
variable {A : Type} (ge : Senv) (e : A → Val) (sp : Val) (m : Mem)

/-- `Events.eval_builtin_arg` -/
inductive EvalBuiltinArg : BuiltinArg A → Val → Prop where
  | BA (x) : EvalBuiltinArg (.BA x) (e x)
  | BA_int (n) : EvalBuiltinArg (.BA_int n) (.Vint n)
  | BA_long (n) : EvalBuiltinArg (.BA_long n) (.Vlong n)
  | BA_float (n) : EvalBuiltinArg (.BA_float n) (.Vfloat n)
  | BA_single (n) : EvalBuiltinArg (.BA_single n) (.Vsingle n)
  | BA_loadstack (chunk ofs v) :
      Mem.loadv chunk m (Val.offsetPtr sp ofs) = some v →
      EvalBuiltinArg (.BA_loadstack chunk ofs) v
  | BA_addrstack (ofs) : EvalBuiltinArg (.BA_addrstack ofs) (Val.offsetPtr sp ofs)
  | BA_loadglobal (chunk id ofs v) :
      Mem.loadv chunk m (ge.symbolAddress id ofs) = some v →
      EvalBuiltinArg (.BA_loadglobal chunk id ofs) v
  | BA_addrglobal (id ofs) : EvalBuiltinArg (.BA_addrglobal id ofs) (ge.symbolAddress id ofs)
  | BA_splitlong (hi lo vhi vlo) :
      EvalBuiltinArg hi vhi → EvalBuiltinArg lo vlo →
      EvalBuiltinArg (.BA_splitlong hi lo) (Val.longofwords vhi vlo)
  | BA_addptr (a1 a2 v1 v2) :
      EvalBuiltinArg a1 v1 → EvalBuiltinArg a2 v2 →
      EvalBuiltinArg (.BA_addptr a1 a2) (if Archi.ptr64 then Val.addl v1 v2 else Val.add v1 v2)

/-- `Events.eval_builtin_args` -/
def EvalBuiltinArgs (al : List (BuiltinArg A)) (vl : List Val) : Prop :=
  ListForall2 (EvalBuiltinArg ge e sp m) al vl

end EVAL_BUILTIN_ARG

/-- `Events.eval_builtin_arg_determ` -/
theorem evalBuiltinArg_determ {A : Type} {ge : Senv} {e : A → Val} {sp m a v}
    (h : EvalBuiltinArg ge e sp m a v) : ∀ {v'}, EvalBuiltinArg ge e sp m a v' → v' = v := by
  induction h with
  | BA_splitlong _ _ _ _ _ _ ih1 ih2 =>
    intro v' h'; cases h' with
    | BA_splitlong _ _ _ _ h1 h2 => rw [ih1 h1, ih2 h2]
  | BA_addptr _ _ _ _ _ _ ih1 ih2 =>
    intro v' h'; cases h' with
    | BA_addptr _ _ _ _ h1 h2 => rw [ih1 h1, ih2 h2]
  | BA_loadstack _ _ _ h1 => intro v' h'; cases h'; simp_all
  | BA_loadglobal _ _ _ _ h1 => intro v' h'; cases h'; simp_all
  | _ => intro v' h'; cases h'; rfl

/-- `Events.eval_builtin_args_determ` -/
theorem evalBuiltinArgs_determ {A : Type} {ge : Senv} {e : A → Val} {sp m al vl}
    (h : EvalBuiltinArgs ge e sp m al vl) :
    ∀ {vl'}, EvalBuiltinArgs ge e sp m al vl' → vl' = vl := by
  induction h with
  | nil => intro vl' h'; cases h'; rfl
  | cons ha _ ih =>
    intro vl' h'; cases h' with
    | cons ha' hl' => rw [evalBuiltinArg_determ ha ha', ih hl']

/-- `Events.builtin_arg_depends_on_memory` -/
def builtinArgDependsOnMemory {A : Type} : BuiltinArg A → Bool
  | .BA_loadstack _ _ | .BA_loadglobal _ _ _ => true
  | .BA_splitlong a1 a2 | .BA_addptr a1 a2 =>
      builtinArgDependsOnMemory a1 || builtinArgDependsOnMemory a2
  | _ => false

/-- `Events.builtin_arg_depends_on_memory_correct` -/
theorem builtinArgDependsOnMemory_correct {A : Type} (m' : Mem) {ge : Senv} {e : A → Val}
    {sp m ba v} (h : EvalBuiltinArg ge e sp m ba v) (hd : builtinArgDependsOnMemory ba = false) :
    EvalBuiltinArg ge e sp m' ba v := by
  induction h with
  | BA_loadstack => simp [builtinArgDependsOnMemory] at hd
  | BA_loadglobal => simp [builtinArgDependsOnMemory] at hd
  | BA_splitlong _ _ _ _ _ _ ih1 ih2 =>
    simp only [builtinArgDependsOnMemory, Bool.or_eq_false_iff] at hd
    exact .BA_splitlong _ _ _ _ (ih1 hd.1) (ih2 hd.2)
  | BA_addptr _ _ _ _ _ _ ih1 ih2 =>
    simp only [builtinArgDependsOnMemory, Bool.or_eq_false_iff] at hd
    exact .BA_addptr _ _ _ _ (ih1 hd.1) (ih2 hd.2)
  | BA x => exact .BA x
  | BA_int n => exact .BA_int n
  | BA_long n => exact .BA_long n
  | BA_float n => exact .BA_float n
  | BA_single n => exact .BA_single n
  | BA_addrstack ofs => exact .BA_addrstack ofs
  | BA_addrglobal id ofs => exact .BA_addrglobal id ofs

/-- `Events.eval_builtin_arg_preserved` -/
theorem evalBuiltinArg_preserved {A : Type} {ge1 ge2 : Senv} {e : A → Val} {sp m a v}
    (hsym : ∀ id, ge2.find_symbol id = ge1.find_symbol id)
    (h : EvalBuiltinArg ge1 e sp m a v) : EvalBuiltinArg ge2 e sp m a v := by
  have EQ : ∀ id ofs, ge2.symbolAddress id ofs = ge1.symbolAddress id ofs := by
    intro id ofs; simp [Senv.symbolAddress, hsym]
  induction h with
  | BA x => exact .BA x
  | BA_int n => exact .BA_int n
  | BA_long n => exact .BA_long n
  | BA_float n => exact .BA_float n
  | BA_single n => exact .BA_single n
  | BA_loadstack _ _ _ h1 => exact .BA_loadstack _ _ _ h1
  | BA_addrstack ofs => exact .BA_addrstack ofs
  | BA_loadglobal _ _ _ _ h1 => exact .BA_loadglobal _ _ _ _ (by rw [EQ]; exact h1)
  | BA_addrglobal id ofs => rw [← EQ]; exact .BA_addrglobal id ofs
  | BA_splitlong _ _ _ _ _ _ ih1 ih2 => exact .BA_splitlong _ _ _ _ ih1 ih2
  | BA_addptr _ _ _ _ _ _ ih1 ih2 => exact .BA_addptr _ _ _ _ ih1 ih2

/-- `Events.eval_builtin_args_preserved` -/
theorem evalBuiltinArgs_preserved {A : Type} {ge1 ge2 : Senv} {e : A → Val} {sp m al vl}
    (hsym : ∀ id, ge2.find_symbol id = ge1.find_symbol id)
    (h : EvalBuiltinArgs ge1 e sp m al vl) : EvalBuiltinArgs ge2 e sp m al vl := by
  induction h with
  | nil => exact .nil
  | cons ha _ ih => exact .cons (evalBuiltinArg_preserved hsym ha) ih

end CC
