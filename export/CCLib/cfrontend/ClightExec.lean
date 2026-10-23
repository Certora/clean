/-
  An EXECUTABLE Clight semantics, and its agreement with the relation.

  CompCert has no executable Clight semantics: `cfrontend/Cexec.v` is built on
  `Csyntax`/`Csem` (the source language with unspecified evaluation order), and
  `ccomp -interp` runs that.  So this file has no Rocq original to transliterate.
  It is, however, much simpler than `Cexec`: Clight expressions are deterministic
  and side-effect-free, so `Cexec`'s 211-line `step_expr` reduct machinery
  collapses into a plain recursive `doEvalExpr : Expr → Option Val`.

  Structure, mirroring `Cexec`'s: a `do*` function for each relation, then
  soundness theorems saying every step the interpreter takes is a step the
  relation allows.  Soundness is the direction that matters — it says the
  interpreter never invents behaviour.

  External calls: the interpreter implements the builtins with real, deterministic
  semantics (`malloc`, `free`, `memcpy`, `debug`) and gets stuck on everything
  else (volatile accesses, `annot`, unknown externals), because those are either
  event-producing or uninterpreted and so have no single executable answer.
-/
import CCLib.cfrontend.Clight

namespace CC

/-! ## Reading and writing a datum -/

/-- The side conditions shared by `Cop.load_bitfield` and `store_bitfield`,
    stated as a decidable *Prop* rather than a `Bool`.  That way the interpreter's
    `if h : …` hands the soundness proof exactly the conjunction it needs, with no
    `decide`/`&&` plumbing in between. -/
def bitfieldOk (tysz : IntSize) (tysg : Signedness) (sz : IntSize)
    (sg : Signedness) (pos width : Z) : Prop :=
  tysz = sz ∧ 0 ≤ pos ∧ 0 < width ∧ width ≤ bitsizeIntsize sz
    ∧ pos + width ≤ Cop.bitsizeCarrier sz
    ∧ tysg = (if width < bitsizeIntsize sz then Signedness.Signed else sg)

instance (tysz : IntSize) (tysg : Signedness) (sz : IntSize) (sg : Signedness)
    (pos width : Z) : Decidable (bitfieldOk tysz tysg sz sg pos width) := by
  unfold bitfieldOk; infer_instance

/-- Executable `deref_loc`. -/
def doDerefLoc (ty : Ty) (m : Mem) (b : Block) (ofs : Integers.Ptrofs)
    (bf : Bitfield) : Option Val :=
  match bf with
  | .Full =>
      match accessMode ty with
      | .By_value chunk => Mem.loadv chunk m (.Vptr b ofs)
      | .By_reference => some (.Vptr b ofs)
      | .By_copy => some (.Vptr b ofs)
      | .By_nothing => none
  | .Bits sz sg pos width =>
      -- the side conditions of `Cop.load_bitfield`, checked
      match ty with
      | .Tint sz' sg1 _ =>
          if bitfieldOk sz' sg1 sz sg pos width then
            match Mem.loadv (Cop.chunkForCarrier sz) m (.Vptr b ofs) with
            | some (.Vint c) => some (.Vint (Cop.bitfieldExtract sz sg pos width c))
            | _ => none
          else none
      | _ => none

/-- Executable `assign_loc`. -/
def doAssignLoc (ce : CompositeEnv) (ty : Ty) (m : Mem) (b : Block)
    (ofs : Integers.Ptrofs) (bf : Bitfield) (v : Val) : Option Mem :=
  match bf with
  | .Full =>
      match accessMode ty with
      | .By_value chunk => Mem.storev chunk m (.Vptr b ofs) v
      | .By_copy =>
          match v with
          | .Vptr b' ofs' =>
              let sz := sizeof ce ty
              let al := alignofBlockcopy ce ty
              if (sz > 0 → Integers.Ptrofs.unsigned ofs' % al = 0)
                 && (sz > 0 → Integers.Ptrofs.unsigned ofs % al = 0)
                 && (b' ≠ b
                     ∨ Integers.Ptrofs.unsigned ofs' = Integers.Ptrofs.unsigned ofs
                     ∨ Integers.Ptrofs.unsigned ofs' + sz ≤ Integers.Ptrofs.unsigned ofs
                     ∨ Integers.Ptrofs.unsigned ofs + sz ≤ Integers.Ptrofs.unsigned ofs')
              then
                match Mem.loadbytes m b' (Integers.Ptrofs.unsigned ofs') sz with
                | some bytes => Mem.storebytes m b (Integers.Ptrofs.unsigned ofs) bytes
                | none => none
              else none
          | _ => none
      | _ => none
  | .Bits sz sg pos width =>
      match ty, v with
      | .Tint sz' sg1 _, .Vint n =>
          if bitfieldOk sz' sg1 sz sg pos width then
            match Mem.loadv (Cop.chunkForCarrier sz) m (.Vptr b ofs) with
            | some (.Vint c) =>
                Mem.storev (Cop.chunkForCarrier sz) m (.Vptr b ofs)
                  (.Vint (Integers.Int.bitfield_insert
                    (Cop.firstBit sz pos width).toNat width.toNat c n))
            | _ => none
          else none
      | _, _ => none

/-! ## Expression evaluation

`Evar`/`Ederef`/`Efield` are l-values; as r-values they go through
`doEvalLvalue` and then `doDerefLoc`, which is exactly what the relation's
`Elvalue` rule says. -/

/-- The l-value of a variable: local if bound (with a matching type
    annotation, as the relation demands), otherwise a global symbol. -/
def lvalOfVar (ge : CGenv) (e : Env) (id : Ident) (ty : Ty) :
    Option (Block × Integers.Ptrofs × Bitfield) :=
  match e.get id with
  | some (l, ty') => if ty' = ty then some (l, Integers.Ptrofs.zero, .Full) else none
  | none =>
      match Genv.findSymbol ge.genv_genv id with
      | some l => some (l, Integers.Ptrofs.zero, .Full)
      | none => none

/-- The l-value of `a.i`, given the already-evaluated address of `a` and its
    type.  Split out (and non-recursive) so that expression evaluation stays
    structural. -/
def lvalOfField (ge : CGenv) (ta : Ty) (i : Ident) (v : Val) :
    Option (Block × Integers.Ptrofs × Bitfield) :=
  match v with
  | .Vptr l ofs =>
      let fromOffset : Res (Z × Bitfield) → Option (Block × Integers.Ptrofs × Bitfield)
        | .OK (delta, bf) =>
            some (l, Integers.Ptrofs.add ofs (Integers.Ptrofs.repr delta), bf)
        | .Error _ => none
      match ta with
      | .Tstruct id _ =>
          match ge.genv_cenv.get id with
          | some co => fromOffset (fieldOffset ge.genv_cenv i co.co_members)
          | none => none
      | .Tunion id _ =>
          match ge.genv_cenv.get id with
          | some co => fromOffset (unionFieldOffset ge.genv_cenv i co.co_members)
          | none => none
      | _ => none
  | _ => none

/-! Note on structure: the relation's `Elvalue` rule turns an l-value into an
r-value using the *same* expression, so a literal transcription would not be
structurally recursive.  Instead the l-value logic that does not recurse
(`lvalOfVar`, `lvalOfField`) is factored out above, and both `doEvalExpr` and
`doEvalLvalue` recurse only into strict subterms. -/

mutual
def doEvalExpr (ge : CGenv) (e : Env) (le : TempEnv) (m : Mem) :
    Expr → Option Val
  | .Econst_int i _ => some (.Vint i)
  | .Econst_float f _ => some (.Vfloat f)
  | .Econst_single f _ => some (.Vsingle f)
  | .Econst_long i _ => some (.Vlong i)
  | .Etempvar id _ => le.get id
  | .Esizeof ty1 _ =>
      some (Val.Vptrofs (Integers.Ptrofs.repr (sizeof ge.genv_cenv ty1)))
  | .Ealignof ty1 _ =>
      some (Val.Vptrofs (Integers.Ptrofs.repr (alignof ge.genv_cenv ty1)))
  | .Eaddrof a _ =>
      match doEvalLvalue ge e le m a with
      | some (loc, ofs, .Full) => some (.Vptr loc ofs)
      | _ => none
  | .Eunop op a _ =>
      match doEvalExpr ge e le m a with
      | some v1 => Cop.semUnaryOperation op v1 (typeof a) m
      | none => none
  | .Ebinop op a1 a2 _ =>
      match doEvalExpr ge e le m a1, doEvalExpr ge e le m a2 with
      | some v1, some v2 =>
          Cop.semBinaryOperation ge.genv_cenv op v1 (typeof a1) v2 (typeof a2) m
      | _, _ => none
  | .Ecast a ty =>
      match doEvalExpr ge e le m a with
      | some v1 => Cop.semCast v1 (typeof a) ty m
      | none => none
  -- the three l-value forms, read as r-values (the `Elvalue` rule)
  | .Evar id ty =>
      match lvalOfVar ge e id ty with
      | some (loc, ofs, bf) => doDerefLoc ty m loc ofs bf
      | none => none
  | .Ederef a ty =>
      match doEvalExpr ge e le m a with
      | some (.Vptr l ofs) => doDerefLoc ty m l ofs .Full
      | _ => none
  | .Efield a i ty =>
      match doEvalExpr ge e le m a with
      | some v =>
          match lvalOfField ge (typeof a) i v with
          | some (loc, ofs, bf) => doDerefLoc ty m loc ofs bf
          | none => none
      | none => none

def doEvalLvalue (ge : CGenv) (e : Env) (le : TempEnv) (m : Mem) :
    Expr → Option (Block × Integers.Ptrofs × Bitfield)
  | .Evar id ty => lvalOfVar ge e id ty
  | .Ederef a _ =>
      match doEvalExpr ge e le m a with
      | some (.Vptr l ofs) => some (l, ofs, .Full)
      | _ => none
  | .Efield a i _ =>
      match doEvalExpr ge e le m a with
      | some v => lvalOfField ge (typeof a) i v
      | none => none
  | _ => none
end

/-- Executable `eval_exprlist`. -/
def doEvalExprlist (ge : CGenv) (e : Env) (le : TempEnv) (m : Mem) :
    List Expr → List Ty → Option (List Val)
  | [], [] => some []
  | a :: bl, ty :: tyl =>
      match doEvalExpr ge e le m a with
      | some v1 =>
          match Cop.semCast v1 (typeof a) ty m with
          | some v2 =>
              match doEvalExprlist ge e le m bl tyl with
              | some vl => some (v2 :: vl)
              | none => none
          | none => none
      | none => none
  | _, _ => none

/-! ## Function entry -/

/-- Executable `alloc_variables`. -/
def doAllocVariables (ce : CompositeEnv) (e : Env) (m : Mem) :
    List (Ident × Ty) → Env × Mem
  | [] => (e, m)
  | (id, ty) :: vars =>
      -- written with projections rather than a pattern-`let` so that the
      -- `Mem.alloc … = (m1, b1)` equation the relation needs holds by `rfl`
      doAllocVariables ce (e.set id ((Mem.alloc m 0 (sizeof ce ty)).2, ty))
        (Mem.alloc m 0 (sizeof ce ty)).1 vars

/-- Executable `bind_parameters`. -/
def doBindParameters (ce : CompositeEnv) (e : Env) (m : Mem) :
    List (Ident × Ty) → List Val → Option Mem
  | [], [] => some m
  | (id, ty) :: params, v1 :: vl =>
      match e.get id with
      | some (b, ty') =>
          if ty' = ty then
            match doAssignLoc ce ty m b Integers.Ptrofs.zero .Full v1 with
            | some m1 => doBindParameters ce e m1 params vl
            | none => none
          else none
      | none => none
  | _, _ => none

/-- Executable `function_entry1` (parameters as stack variables). -/
def doFunctionEntry1 (ge : CGenv) (f : Function) (vargs : List Val) (m : Mem) :
    Option (Env × TempEnv × Mem) :=
  if listNorepet (varNames f.fn_params ++ varNames f.fn_vars) then
    let (e, m1) := doAllocVariables ge.genv_cenv emptyEnv m (f.fn_params ++ f.fn_vars)
    match doBindParameters ge.genv_cenv e m1 f.fn_params vargs with
    | some m' => some (e, createUndefTemps f.fn_temps, m')
    | none => none
  else none

/-- Executable `function_entry2` (parameters as temporaries). -/
def doFunctionEntry2 (ge : CGenv) (f : Function) (vargs : List Val) (m : Mem) :
    Option (Env × TempEnv × Mem) :=
  -- stated as decidable *Props* (not `Bool`s) so that the soundness proof gets
  -- exactly the hypotheses `FunctionEntry2` asks for
  if listNorepet (varNames f.fn_vars) ∧ listNorepet (varNames f.fn_params)
     ∧ listDisjoint (varNames f.fn_params) (varNames f.fn_temps) then
    let (e, m') := doAllocVariables ge.genv_cenv emptyEnv m f.fn_vars
    match bindParameterTemps f.fn_params vargs (createUndefTemps f.fn_temps) with
    | some le => some (e, le, m')
    | none => none
  else none

/-! ## External calls

Only the deterministic, event-free builtins are executable.  Everything else —
volatile accesses, `annot` (which emits an event whose value must satisfy
`eventval_match`), and unknown externals (uninterpreted in Rocq too) — has no
single answer, so the interpreter stops. -/

/-- Recover the `ptrofs` from a value that `Val.Vptrofs` would have produced.
    `Vptrofs` is a *definition* (it picks `Vlong` or `Vint` by `Archi.ptr64`), so
    it cannot appear as a pattern; this is its inverse on the relevant shapes. -/
def ptrofsOfVal : Val → Option Integers.Ptrofs
  | .Vlong n => if Archi.ptr64 then some (Integers.Ptrofs.of_int64 n) else none
  | .Vint n => if Archi.ptr64 then none else some (Integers.Ptrofs.of_intu n)
  | _ => none

def doExternalCall (ef : ExtFun) (vargs : List Val) (m : Mem) :
    Option (Trace × Val × Mem) :=
  match ef, vargs with
  | .EF_malloc, [v] =>
      match ptrofsOfVal v with
      | some sz =>
          let (m', b) := Mem.alloc m (- sizeChunk Mptr) (Integers.Ptrofs.unsigned sz)
          match Mem.store Mptr m' b (- sizeChunk Mptr) (Val.Vptrofs sz) with
          | some m'' => some (E0, .Vptr b Integers.Ptrofs.zero, m'')
          | none => none
      | none => none
  | .EF_free, [.Vptr b lo] =>
      match Mem.load Mptr m b (Integers.Ptrofs.unsigned lo - sizeChunk Mptr) with
      | some vsz =>
          match ptrofsOfVal vsz with
          | some sz =>
              match Mem.free m b (Integers.Ptrofs.unsigned lo - sizeChunk Mptr)
                      (Integers.Ptrofs.unsigned lo + Integers.Ptrofs.unsigned sz) with
              | some m' => some (E0, .Vundef, m')
              | none => none
          | none => none
      | _ => none
  | .EF_memcpy sz al, [.Vptr bdst odst, .Vptr bsrc osrc] =>
      if (al = 1 ∨ al = 2 ∨ al = 4 ∨ al = 8) && (sz ≥ 0) && (sz % al = 0)
         && (sz > 0 → Integers.Ptrofs.unsigned osrc % al = 0)
         && (sz > 0 → Integers.Ptrofs.unsigned odst % al = 0)
         && (bsrc ≠ bdst
             ∨ Integers.Ptrofs.unsigned osrc = Integers.Ptrofs.unsigned odst
             ∨ Integers.Ptrofs.unsigned osrc + sz ≤ Integers.Ptrofs.unsigned odst
             ∨ Integers.Ptrofs.unsigned odst + sz ≤ Integers.Ptrofs.unsigned osrc)
      then
        match Mem.loadbytes m bsrc (Integers.Ptrofs.unsigned osrc) sz with
        | some bytes =>
            match Mem.storebytes m bdst (Integers.Ptrofs.unsigned odst) bytes with
            | some m' => some (E0, .Vundef, m')
            | none => none
        | none => none
      else none
  | .EF_debug _ _ _, _ => some (E0, .Vundef, m)
  | _, _ => none

/-! ## The interpreter -/

/-- Executable one-step transition, using `function_entry2`.  `none` means the
    state is stuck *for this interpreter* (genuinely stuck, or an external call
    it cannot execute). -/
def doStep (ge : CGenv) : State → Option (Trace × State)
  | .State f (.Sassign a1 a2) k e le m =>
      match doEvalLvalue ge e le m a1, doEvalExpr ge e le m a2 with
      | some (loc, ofs, bf), some v2 =>
          match Cop.semCast v2 (typeof a2) (typeof a1) m with
          | some v =>
              match doAssignLoc ge.genv_cenv (typeof a1) m loc ofs bf v with
              | some m' => some (E0, .State f .Sskip k e le m')
              | none => none
          | none => none
      | _, _ => none
  | .State f (.Sset id a) k e le m =>
      match doEvalExpr ge e le m a with
      | some v => some (E0, .State f .Sskip k e (le.set id v) m)
      | none => none
  | .State f (.Scall optid a al) k e le m =>
      match Cop.classifyFun (typeof a) with
      | .f tyargs tyres cconv =>
          match doEvalExpr ge e le m a with
          | some vf =>
              match doEvalExprlist ge e le m al tyargs with
              | some vargs =>
                  match Genv.findFunct ge.genv_genv vf with
                  | some fd =>
                      if typeOfFundef fd = .Tfunction tyargs tyres cconv
                      then some (E0, .Callstate fd vargs (.Kcall optid f e le k) m)
                      else none
                  | none => none
              | none => none
          | none => none
      | .default => none
  | .State f (.Sbuiltin optid ef tyargs al) k e le m =>
      match doEvalExprlist ge e le m al tyargs with
      | some vargs =>
          match doExternalCall ef vargs m with
          | some (t, vres, m') =>
              some (t, .State f .Sskip k e (setOpttemp optid vres le) m')
          | none => none
      | none => none
  | .State f (.Ssequence s1 s2) k e le m =>
      some (E0, .State f s1 (.Kseq s2 k) e le m)
  | .State f (.Sifthenelse a s1 s2) k e le m =>
      match doEvalExpr ge e le m a with
      | some v1 =>
          match Cop.boolVal v1 (typeof a) m with
          | some b => some (E0, .State f (if b then s1 else s2) k e le m)
          | none => none
      | none => none
  | .State f (.Sloop s1 s2) k e le m =>
      some (E0, .State f s1 (.Kloop1 s1 s2 k) e le m)
  | .State _ (.Sreturn none) k e _ m =>
      match Mem.freeList m (blocksOfEnv ge.genv_cenv e) with
      | some m' => some (E0, .Returnstate .Vundef (callCont k) m')
      | none => none
  | .State f (.Sreturn (some a)) k e le m =>
      match doEvalExpr ge e le m a with
      | some v =>
          match Cop.semCast v (typeof a) f.fn_return m with
          | some v' =>
              match Mem.freeList m (blocksOfEnv ge.genv_cenv e) with
              | some m' => some (E0, .Returnstate v' (callCont k) m')
              | none => none
          | none => none
      | none => none
  | .State f (.Sswitch a sl) k e le m =>
      match doEvalExpr ge e le m a with
      | some v =>
          match Cop.semSwitchArg v (typeof a) with
          | some n =>
              some (E0, .State f (seqOfLabeledStatement (selectSwitch n sl))
                          (.Kswitch k) e le m)
          | none => none
      | none => none
  | .State f (.Slabel _ s) k e le m => some (E0, .State f s k e le m)
  | .State f (.Sgoto lbl) k e le m =>
      match findLabel lbl f.fn_body (callCont k) with
      | some (s', k') => some (E0, .State f s' k' e le m)
      | none => none
  -- `Sskip`, `Sbreak` and `Scontinue` dispatch on the continuation
  | .State f .Sskip k e le m =>
      match k with
      | .Kseq s k' => some (E0, .State f s k' e le m)
      | .Kloop1 s1 s2 k' => some (E0, .State f s2 (.Kloop2 s1 s2 k') e le m)
      | .Kloop2 s1 s2 k' => some (E0, .State f (.Sloop s1 s2) k' e le m)
      | .Kswitch k' => some (E0, .State f .Sskip k' e le m)
      -- Kstop and Kcall are `is_call_cont`s: falling off the end returns.
      -- They are listed separately (rather than as a catch-all) so that the
      -- soundness proof can discharge `isCallCont k = true` by computation.
      | .Kstop =>
          match Mem.freeList m (blocksOfEnv ge.genv_cenv e) with
          | some m' => some (E0, .Returnstate .Vundef .Kstop m')
          | none => none
      | .Kcall optid f' e' le' k' =>
          match Mem.freeList m (blocksOfEnv ge.genv_cenv e) with
          | some m' => some (E0, .Returnstate .Vundef (.Kcall optid f' e' le' k') m')
          | none => none
  | .State f .Sbreak k e le m =>
      match k with
      | .Kseq _ k' => some (E0, .State f .Sbreak k' e le m)
      | .Kloop1 _ _ k' => some (E0, .State f .Sskip k' e le m)
      | .Kloop2 _ _ k' => some (E0, .State f .Sskip k' e le m)
      | .Kswitch k' => some (E0, .State f .Sskip k' e le m)
      | _ => none
  | .State f .Scontinue k e le m =>
      match k with
      | .Kseq _ k' => some (E0, .State f .Scontinue k' e le m)
      | .Kloop1 s1 s2 k' => some (E0, .State f s2 (.Kloop2 s1 s2 k') e le m)
      | .Kswitch k' => some (E0, .State f .Scontinue k' e le m)
      | _ => none
  | .Callstate (.Internal f) vargs k m =>
      match doFunctionEntry2 ge f vargs m with
      | some (e, le, m1) => some (E0, .State f f.fn_body k e le m1)
      | none => none
  | .Callstate (.External ef _ _ _) vargs k m =>
      match doExternalCall ef vargs m with
      | some (t, vres, m') => some (t, .Returnstate vres k m')
      | none => none
  | .Returnstate v (.Kcall optid f e le k) m =>
      some (E0, .State f .Sskip k e (setOpttemp optid v le) m)
  | .Returnstate _ _ _ => none

/-- How a bounded run ended. -/
inductive RunResult where
  | done (r : Integers.Int) (t : Trace)   -- reached a final state
  | stuck (s : State) (t : Trace)         -- no step applies
  | outOfFuel (t : Trace)
  deriving Inhabited

/-- Run at most `fuel` steps from a state, accumulating the trace. -/
def run (ge : CGenv) (s : State) (acc : Trace) : Nat → RunResult
  | 0 => .outOfFuel acc
  | n + 1 =>
      match s with
      | .Returnstate (.Vint r) .Kstop _ => .done r acc
      | _ =>
          match doStep ge s with
          | some (t, s') => run ge s' (Eapp acc t) n
          | none => .stuck s acc

/-- Build the initial state of a program and run it. -/
def runProgram (p : Program) (fuel : Nat) : Option RunResult :=
  let ge := p.globalenv
  match p.initMem with
  | none => none
  | some m0 =>
      match Genv.findSymbol ge.genv_genv p.prog_main with
      | none => none
      | some b =>
          match Genv.findFunctPtr ge.genv_genv b with
          | none => none
          | some f =>
              if typeOfFundef f = .Tfunction [] type_int32s cc_default
              then some (run ge (.Callstate f [] .Kstop m0) E0 fuel)
              else none

end CC
