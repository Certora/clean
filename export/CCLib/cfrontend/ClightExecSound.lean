/-
  Soundness of the executable Clight semantics against the relational one.

  The theorems all have the shape "if the interpreter takes a step, the relation
  permits that step".  This is the direction that matters: it says the
  interpreter never invents behaviour, so anything observed by running a program
  is genuinely a behaviour of the Clight semantics.

  (The converse — completeness — would say the interpreter finds *every* step the
  relation allows.  It is false as stated for the external-call rules, since
  `externalCall` is uninterpreted for unknown functions and event-producing for
  volatiles, which is exactly why `doExternalCall` stops there.  For the
  deterministic fragment it should hold; it is not proved here.)
-/
import CCLib.cfrontend.ClightExec

namespace CC

set_option linter.unusedVariables false

/-! ## Locations -/

theorem doDerefLoc_sound (ty : Ty) (m : Mem) (b : Block) (ofs : Integers.Ptrofs)
    (bf : Bitfield) (v : Val) (h : doDerefLoc ty m b ofs bf = some v) :
    DerefLoc ty m b ofs bf v := by
  cases bf with
  | Full =>
      simp only [doDerefLoc] at h
      split at h
      · next chunk hm => exact DerefLoc.value chunk v hm h
      · next hm => cases h; exact DerefLoc.reference hm
      · next hm => cases h; exact DerefLoc.copy hm
      · next => exact absurd h (by simp)
  | Bits sz sg pos width =>
      simp only [doDerefLoc] at h
      split at h
      · next sz' sg1 att =>
          split at h
          · next hok =>
              obtain ⟨hsz, hpos, hw0, hwle, hcar, hsg⟩ := hok
              subst hsz
              split at h
              · next c hload =>
                  injection h with hv
                  subst hv
                  exact DerefLoc.bitfield _ _ _ _ _
                    (Cop.LoadBitfield.intro sz' sg1 att sg pos width m (.Vptr b ofs) c
                      hpos hw0 hwle hcar hsg hload)
              · exact absurd h (by simp)
          · exact absurd h (by simp)
      · exact absurd h (by simp)

theorem doAssignLoc_sound (ce : CompositeEnv) (ty : Ty) (m : Mem) (b : Block)
    (ofs : Integers.Ptrofs) (bf : Bitfield) (v : Val) (m' : Mem)
    (h : doAssignLoc ce ty m b ofs bf v = some m') :
    AssignLoc ce ty m b ofs bf v m' := by
  cases bf with
  | Full =>
      simp only [doAssignLoc] at h
      split at h
      · next chunk hm => exact AssignLoc.value v chunk m' hm h
      · next hm =>
          -- By_copy: a block copy, with alignment and non-overlap side conditions
          split at h
          · next b' ofs' =>
              split at h
              · next hcond =>
                  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
                  obtain ⟨⟨hal1, hal2⟩, hno⟩ := hcond
                  split at h
                  · next bytes hlb =>
                      exact AssignLoc.copy b' ofs' bytes m' hm hal1 hal2 hno hlb h
                  · exact absurd h (by simp)
              · exact absurd h (by simp)
          · exact absurd h (by simp)
      · next hm => exact absurd h (by simp)
  | Bits sz sg pos width =>
      simp only [doAssignLoc] at h
      split at h
      · next sz' sg1 att n =>
          split at h
          · next hok =>
              obtain ⟨hsz, hpos, hw0, hwle, hcar, hsg⟩ := hok
              subst hsz
              split at h
              · next c hload =>
                  exact AssignLoc.bitfield _ _ _ _ _ _ _
                    (Cop.StoreBitfield.intro sz' sg1 att sg pos width m (.Vptr b ofs) c n m'
                      hpos hw0 hwle hcar hsg hload h)
              · exact absurd h (by simp)
          · exact absurd h (by simp)
      · exact absurd h (by simp)

/-! ## L-value helpers -/

theorem lvalOfVar_sound (ge : CGenv) (e : Env) (le : TempEnv) (m : Mem)
    (id : Ident) (ty : Ty) (loc : Block) (ofs : Integers.Ptrofs) (bf : Bitfield)
    (h : lvalOfVar ge e id ty = some (loc, ofs, bf)) :
    EvalLvalue ge e le m (.Evar id ty) loc ofs bf := by
  simp only [lvalOfVar] at h
  split at h
  · next l ty' hget =>
      split at h
      · next hty => cases h; subst hty; exact EvalLvalue.Evar_local _ _ _ hget
      · exact absurd h (by simp)
  · next hget =>
      split at h
      · next l hsym => cases h; exact EvalLvalue.Evar_global _ _ _ hget hsym
      · exact absurd h (by simp)

theorem lvalOfField_sound (ge : CGenv) (e : Env) (le : TempEnv) (m : Mem)
    (a : Expr) (i : Ident) (ty : Ty) (v : Val)
    (loc : Block) (ofs : Integers.Ptrofs) (bf : Bitfield)
    (hev : EvalExpr ge e le m a v)
    (h : lvalOfField ge (typeof a) i v = some (loc, ofs, bf)) :
    EvalLvalue ge e le m (.Efield a i ty) loc ofs bf := by
  simp only [lvalOfField] at h
  split at h
  · next l o =>
      split at h
      · next id att hta =>
          split at h
          · next co hco =>
              split at h
              · next delta bf' hfo =>
                  cases h
                  exact EvalLvalue.Efield_struct _ _ _ _ _ _ _ _ _ _ hev hta hco hfo
              · exact absurd h (by simp)
          · exact absurd h (by simp)
      · next id att hta =>
          split at h
          · next co hco =>
              split at h
              · next delta bf' hfo =>
                  cases h
                  exact EvalLvalue.Efield_union _ _ _ _ _ _ _ _ _ _ hev hta hco hfo
              · exact absurd h (by simp)
          · exact absurd h (by simp)
      · exact absurd h (by simp)
  · exact absurd h (by simp)

/-! ## Expressions

The centrepiece: whatever value the interpreter computes for an expression, the
relation agrees it is a possible value. -/

mutual
theorem doEvalExpr_sound (ge : CGenv) (e : Env) (le : TempEnv) (m : Mem) :
    ∀ (a : Expr) (v : Val), doEvalExpr ge e le m a = some v → EvalExpr ge e le m a v
  | .Econst_int i ty, v, h => by
      simp only [doEvalExpr] at h; cases h; exact .Econst_int i ty
  | .Econst_float f ty, v, h => by
      simp only [doEvalExpr] at h; cases h; exact .Econst_float f ty
  | .Econst_single f ty, v, h => by
      simp only [doEvalExpr] at h; cases h; exact .Econst_single f ty
  | .Econst_long i ty, v, h => by
      simp only [doEvalExpr] at h; cases h; exact .Econst_long i ty
  | .Etempvar id ty, v, h => by
      simp only [doEvalExpr] at h; exact .Etempvar id ty v h
  | .Esizeof ty1 ty, v, h => by
      simp only [doEvalExpr] at h; cases h; exact .Esizeof ty1 ty
  | .Ealignof ty1 ty, v, h => by
      simp only [doEvalExpr] at h; cases h; exact .Ealignof ty1 ty
  | .Eaddrof a ty, v, h => by
      simp only [doEvalExpr] at h
      split at h
      · next loc ofs hlv =>
          cases h
          exact .Eaddrof a ty loc ofs (doEvalLvalue_sound ge e le m a loc ofs .Full hlv)
      · exact absurd h (by simp)
  | .Eunop op a ty, v, h => by
      simp only [doEvalExpr] at h
      split at h
      · next v1 hv1 =>
          exact .Eunop op a ty v1 v (doEvalExpr_sound ge e le m a v1 hv1) h
      · exact absurd h (by simp)
  | .Ebinop op a1 a2 ty, v, h => by
      simp only [doEvalExpr] at h
      split at h
      · next v1 v2 hv1 hv2 =>
          exact .Ebinop op a1 a2 ty v1 v2 v
            (doEvalExpr_sound ge e le m a1 v1 hv1)
            (doEvalExpr_sound ge e le m a2 v2 hv2) h
      · exact absurd h (by simp)
  | .Ecast a ty, v, h => by
      simp only [doEvalExpr] at h
      split at h
      · next v1 hv1 => exact .Ecast a ty v1 v (doEvalExpr_sound ge e le m a v1 hv1) h
      · exact absurd h (by simp)
  | .Evar id ty, v, h => by
      simp only [doEvalExpr] at h
      split at h
      · next loc ofs bf hlv =>
          exact .Elvalue (.Evar id ty) loc ofs bf v
            (lvalOfVar_sound ge e le m id ty loc ofs bf hlv)
            (doDerefLoc_sound ty m loc ofs bf v h)
      · exact absurd h (by simp)
  | .Ederef a ty, v, h => by
      simp only [doEvalExpr] at h
      split at h
      · next l ofs hv =>
          exact .Elvalue (.Ederef a ty) l ofs .Full v
            (.Ederef a ty l ofs (doEvalExpr_sound ge e le m a (.Vptr l ofs) hv))
            (doDerefLoc_sound ty m l ofs .Full v h)
      · exact absurd h (by simp)
  | .Efield a i ty, v, h => by
      simp only [doEvalExpr] at h
      split at h
      · next v0 hv0 =>
          split at h
          · next loc ofs bf hlf =>
              exact .Elvalue (.Efield a i ty) loc ofs bf v
                (lvalOfField_sound ge e le m a i ty v0 loc ofs bf
                  (doEvalExpr_sound ge e le m a v0 hv0) hlf)
                (doDerefLoc_sound ty m loc ofs bf v h)
          · exact absurd h (by simp)
      · exact absurd h (by simp)

theorem doEvalLvalue_sound (ge : CGenv) (e : Env) (le : TempEnv) (m : Mem) :
    ∀ (a : Expr) (loc : Block) (ofs : Integers.Ptrofs) (bf : Bitfield),
      doEvalLvalue ge e le m a = some (loc, ofs, bf) →
      EvalLvalue ge e le m a loc ofs bf
  | .Evar id ty, loc, ofs, bf, h => by
      simp only [doEvalLvalue] at h
      exact lvalOfVar_sound ge e le m id ty loc ofs bf h
  | .Ederef a ty, loc, ofs, bf, h => by
      simp only [doEvalLvalue] at h
      split at h
      · next l o hv =>
          cases h
          exact .Ederef a ty _ _ (doEvalExpr_sound ge e le m a _ hv)
      · exact absurd h (by simp)
  | .Efield a i ty, loc, ofs, bf, h => by
      simp only [doEvalLvalue] at h
      split at h
      · next v0 hv0 =>
          exact lvalOfField_sound ge e le m a i ty v0 loc ofs bf
            (doEvalExpr_sound ge e le m a v0 hv0) h
      · exact absurd h (by simp)
  | .Econst_int _ _, _, _, _, h => by simp only [doEvalLvalue] at h; exact absurd h (by simp)
  | .Econst_float _ _, _, _, _, h => by simp only [doEvalLvalue] at h; exact absurd h (by simp)
  | .Econst_single _ _, _, _, _, h => by simp only [doEvalLvalue] at h; exact absurd h (by simp)
  | .Econst_long _ _, _, _, _, h => by simp only [doEvalLvalue] at h; exact absurd h (by simp)
  | .Etempvar _ _, _, _, _, h => by simp only [doEvalLvalue] at h; exact absurd h (by simp)
  | .Eaddrof _ _, _, _, _, h => by simp only [doEvalLvalue] at h; exact absurd h (by simp)
  | .Eunop _ _ _, _, _, _, h => by simp only [doEvalLvalue] at h; exact absurd h (by simp)
  | .Ebinop _ _ _ _, _, _, _, h => by simp only [doEvalLvalue] at h; exact absurd h (by simp)
  | .Ecast _ _, _, _, _, h => by simp only [doEvalLvalue] at h; exact absurd h (by simp)
  | .Esizeof _ _, _, _, _, h => by simp only [doEvalLvalue] at h; exact absurd h (by simp)
  | .Ealignof _ _, _, _, _, h => by simp only [doEvalLvalue] at h; exact absurd h (by simp)
end

/-- Soundness for argument lists. -/
theorem doEvalExprlist_sound (ge : CGenv) (e : Env) (le : TempEnv) (m : Mem) :
    ∀ (al : List Expr) (tyl : List Ty) (vl : List Val),
      doEvalExprlist ge e le m al tyl = some vl → EvalExprlist ge e le m al tyl vl
  | [], [], vl, h => by simp only [doEvalExprlist] at h; cases h; exact .nil
  | a :: bl, ty :: tyl, vl, h => by
      simp only [doEvalExprlist] at h
      split at h
      · next v1 hv1 =>
          split at h
          · next v2 hv2 =>
              split at h
              · next vl' hvl =>
                  cases h
                  exact .cons a bl ty tyl v1 v2 vl'
                    (doEvalExpr_sound ge e le m a v1 hv1) hv2
                    (doEvalExprlist_sound ge e le m bl tyl vl' hvl)
              · exact absurd h (by simp)
          · exact absurd h (by simp)
      · exact absurd h (by simp)
  | [], _ :: _, _, h => by simp only [doEvalExprlist] at h; exact absurd h (by simp)
  | _ :: _, [], _, h => by simp only [doEvalExprlist] at h; exact absurd h (by simp)


/-! ## Function entry -/

theorem doAllocVariables_sound (ce : CompositeEnv) :
    ∀ (vars : List (Ident × Ty)) (e : Env) (m : Mem) (e' : Env) (m' : Mem),
      doAllocVariables ce e m vars = (e', m') → AllocVariables ce e m vars e' m'
  | [], e, m, e', m', h => by
      simp only [doAllocVariables] at h; cases h; exact .nil _ _
  | (id, ty) :: vars, e, m, e', m', h => by
      simp only [doAllocVariables] at h
      exact .cons e m id ty vars _ _ m' e' rfl
        (doAllocVariables_sound ce vars _ _ e' m' h)

theorem doBindParameters_sound (ce : CompositeEnv) (e : Env) :
    ∀ (params : List (Ident × Ty)) (vl : List Val) (m m' : Mem),
      doBindParameters ce e m params vl = some m' →
      BindParameters ce e m params vl m'
  | [], [], m, m', h => by simp only [doBindParameters] at h; cases h; exact .nil _
  | (id, ty) :: params, v1 :: vl, m, m', h => by
      simp only [doBindParameters] at h
      split at h
      · next b ty' hget =>
          split at h
          · next hty =>
              subst hty
              split at h
              · next m1 hass =>
                  exact .cons m id ty' params v1 vl b m1 m' hget
                    (doAssignLoc_sound ce ty' m b Integers.Ptrofs.zero .Full v1 m1 hass)
                    (doBindParameters_sound ce e params vl m1 m' h)
              · exact absurd h (by simp)
          · exact absurd h (by simp)
      · exact absurd h (by simp)
  | [], _ :: _, _, _, h => by simp only [doBindParameters] at h; exact absurd h (by simp)
  | _ :: _, [], _, _, h => by simp only [doBindParameters] at h; exact absurd h (by simp)

theorem doFunctionEntry2_sound (ge : CGenv) (f : Function) (vargs : List Val)
    (m : Mem) (e : Env) (le : TempEnv) (m1 : Mem)
    (h : doFunctionEntry2 ge f vargs m = some (e, le, m1)) :
    FunctionEntry2 ge f vargs m e le m1 := by
  simp only [doFunctionEntry2] at h
  split at h
  · next hcond =>
      obtain ⟨hnv, hnp, hdisj⟩ := hcond
      split at h
      · next le' hbind =>
          cases h
          exact FunctionEntry2.intro hnv hnp hdisj
            (doAllocVariables_sound ge.genv_cenv f.fn_vars emptyEnv m _ _ rfl) hbind
      · exact absurd h (by simp)
  · exact absurd h (by simp)

/-! ## External calls

Only the builtins the interpreter actually executes need covering; for everything
else `doExternalCall` returns `none` and there is nothing to prove. -/

theorem ptrofsOfVal_sound (v : Val) (sz : Integers.Ptrofs)
    (h : ptrofsOfVal v = some sz) : v = Val.Vptrofs sz := by
  cases v with
  | Vlong n =>
      simp only [ptrofsOfVal, Archi.ptr64, if_true] at h
      cases h
      simp [Val.Vptrofs, Archi.ptr64, Integers.Ptrofs.to_int64,
            Integers.Ptrofs.of_int64, Integers.MI.repr, Integers.MI.unsigned]
  | Vint n => simp only [ptrofsOfVal, Archi.ptr64, if_true] at h; exact absurd h (by simp)
  | _ => simp only [ptrofsOfVal] at h; exact absurd h (by simp)

theorem doExternalCall_sound (ge : Senv) (ef : ExtFun) (vargs : List Val) (m : Mem)
    (t : Trace) (vres : Val) (m' : Mem)
    (h : doExternalCall ef vargs m = some (t, vres, m')) :
    externalCall ef ge vargs m t vres m' := by
  simp only [doExternalCall] at h
  split at h
  -- malloc
  · next v =>
      split at h
      · next sz hsz =>
          split at h
          · next m'' hst =>
              cases h
              rw [ptrofsOfVal_sound v sz hsz]
              exact ExtcallMallocSem.intro ge sz m _ _ _ rfl hst
          · exact absurd h (by simp)
      · exact absurd h (by simp)
  -- free
  · next b lo =>
      split at h
      · next vsz hload =>
          split at h
          · next sz hsz =>
              split at h
              · next mf hfree =>
                  cases h
                  exact ExtcallFreeSem.ptr ge b lo sz m _
                    (by rw [hload, ptrofsOfVal_sound vsz sz hsz]) hfree
              · exact absurd h (by simp)
          · exact absurd h (by simp)
      · exact absurd h (by simp)
  -- memcpy
  · next sz al bdst odst bsrc osrc =>
      split at h
      · next hcond =>
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
          obtain ⟨⟨⟨⟨⟨hal, hsz0⟩, hdvd⟩, hsrc⟩, hdst⟩, hno⟩ := hcond
          split at h
          · next bytes hlb =>
              split at h
              · next mc hsb =>
                  cases h
                  exact ExtcallMemcpySem.intro ge bdst odst bsrc osrc m bytes _
                    hal hsz0 hdvd hsrc hdst hno hlb hsb
              · exact absurd h (by simp)
          · exact absurd h (by simp)
      · exact absurd h (by simp)
  -- debug
  · next => cases h; exact ExtcallDebugSem.intro ge vargs m
  · exact absurd h (by simp)


/-! ## The interpreter is sound

Every transition `doStep` takes is one the relation permits.  Combined with the
fact that `doStep` is a function, this says a run of the interpreter exhibits a
genuine behaviour of the Clight semantics — nothing is invented. -/

theorem doStep_sound (ge : CGenv) :
    ∀ (s : State) (t : Trace) (s' : State),
      doStep ge s = some (t, s') → Step ge (FunctionEntry2 ge) s t s'
  | .State f (.Sassign a1 a2) k e le m, t, s', h => by
      simp only [doStep] at h
      split at h
      · next loc ofs bf v2 hlv hv2 =>
          split at h
          · next v hcast =>
              split at h
              · next m' hass =>
                  cases h
                  exact .assign f a1 a2 k e le m loc ofs bf v2 v m'
                    (doEvalLvalue_sound ge e le m a1 loc ofs bf hlv)
                    (doEvalExpr_sound ge e le m a2 v2 hv2) hcast
                    (doAssignLoc_sound _ _ _ _ _ _ _ _ hass)
              · exact absurd h (by simp)
          · exact absurd h (by simp)
      · exact absurd h (by simp)
  | .State f (.Sset id a) k e le m, t, s', h => by
      simp only [doStep] at h
      split at h
      · next v hv =>
          cases h
          exact .set f id a k e le m v (doEvalExpr_sound ge e le m a v hv)
      · exact absurd h (by simp)
  | .State f (.Scall optid a al) k e le m, t, s', h => by
      simp only [doStep] at h
      split at h
      · next tyargs tyres cconv hcf =>
          split at h
          · next vf hvf =>
              split at h
              · next vargs hargs =>
                  split at h
                  · next fd hfd =>
                      split at h
                      · next hty =>
                          cases h
                          exact .call f optid a al k e le m tyargs tyres cconv vf vargs fd
                            hcf (doEvalExpr_sound ge e le m a vf hvf)
                            (doEvalExprlist_sound ge e le m al tyargs vargs hargs)
                            hfd hty
                      · exact absurd h (by simp)
                  · exact absurd h (by simp)
              · exact absurd h (by simp)
          · exact absurd h (by simp)
      · exact absurd h (by simp)
  | .State f (.Sbuiltin optid ef tyargs al) k e le m, t, s', h => by
      simp only [doStep] at h
      split at h
      · next vargs hargs =>
          split at h
          · next t0 vres m' hext =>
              cases h
              exact .builtin f optid ef tyargs al k e le m vargs _ vres m'
                (doEvalExprlist_sound ge e le m al tyargs vargs hargs)
                (doExternalCall_sound _ ef vargs m _ vres m' hext)
          · exact absurd h (by simp)
      · exact absurd h (by simp)
  | .State f (.Ssequence s1 s2) k e le m, t, s', h => by
      simp only [doStep] at h; cases h; exact .seq f s1 s2 k e le m
  | .State f (.Sifthenelse a s1 s2) k e le m, t, s', h => by
      simp only [doStep] at h
      split at h
      · next v1 hv1 =>
          split at h
          · next b hb =>
              cases h
              exact .ifthenelse f a s1 s2 k e le m v1 b
                (doEvalExpr_sound ge e le m a v1 hv1) hb
          · exact absurd h (by simp)
      · exact absurd h (by simp)
  | .State f (.Sloop s1 s2) k e le m, t, s', h => by
      simp only [doStep] at h; cases h; exact .loop f s1 s2 k e le m
  | .State f (.Sreturn none) k e le m, t, s', h => by
      simp only [doStep] at h
      split at h
      · next m' hfree => cases h; exact .return_0 f k e le m m' hfree
      · exact absurd h (by simp)
  | .State f (.Sreturn (some a)) k e le m, t, s', h => by
      simp only [doStep] at h
      split at h
      · next v hv =>
          split at h
          · next v' hcast =>
              split at h
              · next m' hfree =>
                  cases h
                  exact .return_1 f a k e le m v v' m'
                    (doEvalExpr_sound ge e le m a v hv) hcast hfree
              · exact absurd h (by simp)
          · exact absurd h (by simp)
      · exact absurd h (by simp)
  | .State f (.Sswitch a sl) k e le m, t, s', h => by
      simp only [doStep] at h
      split at h
      · next v hv =>
          split at h
          · next n hn =>
              cases h
              exact .switch f a sl k e le m v n (doEvalExpr_sound ge e le m a v hv) hn
          · exact absurd h (by simp)
      · exact absurd h (by simp)
  | .State f (.Slabel lbl s) k e le m, t, s', h => by
      simp only [doStep] at h; cases h; exact .label f lbl s k e le m
  | .State f (.Sgoto lbl) k e le m, t, s', h => by
      simp only [doStep] at h
      split at h
      · next s0 k0 hfl => cases h; exact .goto f lbl k e le m s0 k0 hfl
      · exact absurd h (by simp)
  | .State f .Sskip k e le m, t, s', h => by
      simp only [doStep] at h
      split at h
      · next s0 k0 => cases h; exact .skip_seq f s0 k0 e le m
      · next s1 s2 k0 => cases h; exact .skip_or_continue_loop1 f s1 s2 k0 e le m .Sskip (.inl rfl)
      · next s1 s2 k0 => cases h; exact .skip_loop2 f s1 s2 k0 e le m
      · next k0 => cases h; exact .skip_break_switch f .Sskip k0 e le m (.inl rfl)
      · next =>
          split at h
          · next m' hfree => cases h; exact .skip_call f .Kstop e le m m' rfl hfree
          · exact absurd h (by simp)
      · next optid f' e' le' k0 =>
          split at h
          · next m' hfree =>
              cases h
              exact .skip_call f (.Kcall optid f' e' le' k0) e le m m' rfl hfree
          · exact absurd h (by simp)
  | .State f .Sbreak k e le m, t, s', h => by
      simp only [doStep] at h
      split at h
      · next s0 k0 => cases h; exact .break_seq f s0 k0 e le m
      · next s1 s2 k0 => cases h; exact .break_loop1 f s1 s2 k0 e le m
      · next s1 s2 k0 => cases h; exact .break_loop2 f s1 s2 k0 e le m
      · next k0 => cases h; exact .skip_break_switch f .Sbreak k0 e le m (.inr rfl)
      · exact absurd h (by simp)
  | .State f .Scontinue k e le m, t, s', h => by
      simp only [doStep] at h
      split at h
      · next s0 k0 => cases h; exact .continue_seq f s0 k0 e le m
      · next s1 s2 k0 =>
          cases h
          exact .skip_or_continue_loop1 f s1 s2 k0 e le m .Scontinue (.inr rfl)
      · next k0 => cases h; exact .continue_switch f k0 e le m
      · exact absurd h (by simp)
  | .Callstate (.Internal f) vargs k m, t, s', h => by
      simp only [doStep] at h
      split at h
      · next e le m1 hfe =>
          cases h
          exact .internal_function f vargs k m e le m1
            (doFunctionEntry2_sound ge f vargs m e le m1 hfe)
      · exact absurd h (by simp)
  | .Callstate (.External ef targs tres cc) vargs k m, t, s', h => by
      simp only [doStep] at h
      split at h
      · next t0 vres m' hext =>
          cases h
          exact .external_function ef targs tres cc vargs k m vres _ m'
            (doExternalCall_sound _ ef vargs m _ vres m' hext)
      · exact absurd h (by simp)
  | .Returnstate v (.Kcall optid f e le k) m, t, s', h => by
      simp only [doStep] at h; cases h; exact .returnstate v optid f e le k m
  | .Returnstate v .Kstop m, t, s', h => by
      simp only [doStep] at h; exact absurd h (by simp)
  | .Returnstate v (.Kseq _ _) m, t, s', h => by
      simp only [doStep] at h; exact absurd h (by simp)
  | .Returnstate v (.Kloop1 _ _ _) m, t, s', h => by
      simp only [doStep] at h; exact absurd h (by simp)
  | .Returnstate v (.Kloop2 _ _ _) m, t, s', h => by
      simp only [doStep] at h; exact absurd h (by simp)
  | .Returnstate v (.Kswitch _) m, t, s', h => by
      simp only [doStep] at h; exact absurd h (by simp)

end CC
