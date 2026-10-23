/-
  Correctness of Cminor generation — port of `cfrontend/Cminorgenproof.v`,
  part 1: global environments, derived properties of memory operations, the
  correspondence between Csharpminor environments and the Cminor stack frame
  (`match_temps`, `match_var`, `match_env`, `match_bounds`,
  `padding_freeable`), matching of global environments
  (`match_globalenvs`) and the invariant on call stacks
  (`match_callstack`) with its preservation lemmas (invariance, assignment of
  temporaries, freeing at function exit, external calls, allocation).

  Differences from Rocq:
  * whole-program statement: the hypothesis is `translProgram prog = .OK
    tprog` rather than CompCert's linking-aware `match_prog`;
  * `is_reachable_from_env_dec` is not needed: excluded middle is used
    directly;
  * `match_globalenvs` is parameterized by the source global environment.
-/
import CCLib.cfrontend.Cminorgen
import CCLib.cfrontend.CsharpminorSem
import CCLib.cfrontend.SimplLocalsproofMatch

namespace CC
namespace Cminorgen

open Smallstep

theorem pos_le_iff (p q : Positive) : p ≤ q ↔ p.toNat ≤ q.toNat := Iff.rfl

/-- Turn every comparison of blocks into a comparison of natural numbers and
    call `omega`. -/
local macro "blk_omega" : tactic =>
  `(tactic| (simp only [Positive.lt_iff, pos_le_iff, Positive.toNat_succ] at *; omega))

local macro "zomega" : tactic => `(tactic| ((try dsimp only [CC.Z] at *) <;> omega))

/-! ## Global environments -/

section GENV
variable {prog : Csharpminor.Program} {tprog : Cminor.Program}
  (TRANSL : translProgram prog = .OK tprog)
include TRANSL

/-- `Cminorgenproof.symbols_preserved` -/
theorem symbols_preserved (id : Ident) :
    Genv.findSymbol tprog.globalenv id = Genv.findSymbol prog.globalenv id :=
  find_symbol_transf_partial TRANSL id

/-- `Cminorgenproof.senv_preserved` (an equality of symbol environments). -/
theorem senv_preserved : Genv.toSenv tprog.globalenv = Genv.toSenv prog.globalenv :=
  senv_transf_partial TRANSL

/-- `Cminorgenproof.function_ptr_translated` -/
theorem function_ptr_translated {b : Block} {f : Csharpminor.Fundef}
    (h : Genv.findFunctPtr prog.globalenv b = some f) :
    ∃ tf, Genv.findFunctPtr tprog.globalenv b = some tf ∧ translFundef f = .OK tf :=
  find_funct_ptr_transf_partial TRANSL h

/-- `Cminorgenproof.functions_translated` -/
theorem functions_translated {v : Val} {f : Csharpminor.Fundef}
    (h : Genv.findFunct prog.globalenv v = some f) :
    ∃ tf, Genv.findFunct tprog.globalenv v = some tf ∧ translFundef f = .OK tf :=
  find_funct_transf_partial TRANSL h

end GENV

/-- `Cminorgenproof.sig_preserved_body` -/
theorem sig_preserved_body {f : Csharpminor.Function} {tf : Cminor.Function} {cenv : Compilenv}
    {size : Z} (h : translFunbody cenv size f = .OK tf) : tf.fn_sig = f.fn_sig := by
  simp only [translFunbody] at h
  cases h1 : translStmt cenv [] f.fn_body with
  | Error _ => rw [h1] at h; cases h
  | OK tb => rw [h1] at h; cases h; rfl

theorem translFunction_inv {f : Csharpminor.Function} {tf : Cminor.Function}
    (h : translFunction f = .OK tf) :
    ∃ cenv, buildCompilenv f = (cenv, tf.fn_stackspace) ∧
      tf.fn_stackspace ≤ Integers.Ptrofs.max_unsigned ∧ translFunbody cenv tf.fn_stackspace f = .OK tf := by
  simp only [translFunction] at h
  rcases hb : buildCompilenv f with ⟨cenv, sz⟩
  rw [hb] at h
  simp only at h
  split at h
  · rename_i hle
    have hsz : tf.fn_stackspace = sz := by
      simp only [translFunbody] at h
      cases h1 : translStmt cenv [] f.fn_body with
      | Error _ => rw [h1] at h; cases h
      | OK tb => rw [h1] at h; cases h; rfl
    subst hsz
    exact ⟨cenv, rfl, hle, h⟩
  · cases h

/-- `Cminorgenproof.sig_preserved` -/
theorem sig_preserved {f : Csharpminor.Fundef} {tf : Cminor.Fundef} (h : translFundef f = .OK tf) :
    Cminor.funsig tf = Csharpminor.funsig f := by
  cases f with
  | Internal f =>
    simp only [translFundef, ASTFundef.transfPartial] at h
    split at h
    · rename_i tf' htf
      cases h
      obtain ⟨_, _, _, hb⟩ := translFunction_inv htf
      exact sig_preserved_body hb
    · cases h
  | External ef => cases h; rfl

/-! ## Derived properties of memory operations -/

/-- `Cminorgenproof.load_freelist` -/
theorem load_freelist {chunk : Chunk} {b : Block} {ofs : Z} :
    ∀ {fbl : List (Block × Z × Z)} {m m' : Mem}, (∀ b' lo hi, (b', lo, hi) ∈ fbl → b' ≠ b) →
      Mem.freeList m fbl = some m' → Mem.load chunk m' b ofs = Mem.load chunk m b ofs
  | [], m, m', _, h => by simp only [Mem.freeList, Option.some.injEq] at h; subst h; rfl
  | (b', lo, hi) :: fbl, m, m', H, h => by
    simp only [Mem.freeList] at h
    split at h
    · cases h
    · rename_i m1 hfr
      rw [load_freelist (fun b'' lo' hi' hin => H b'' lo' hi' (List.mem_cons_of_mem _ hin)) h,
        Mem.free_result hfr]
      exact Mem.load_free_other _ _ _ _ _ _ (H b' lo hi (List.mem_cons_self ..)).symm _

/-- `Cminorgenproof.perm_freelist` -/
theorem perm_freelist {fbl : List (Block × Z × Z)} {m m' : Mem} {b : Block} {ofs : Z}
    {k : PermKind} {p : Permission} (h : Mem.freeList m fbl = some m')
    (hp : Mem.perm m' b ofs k p = true) : Mem.perm m b ofs k p = true :=
  (SimplLocals.perm_freeList h hp).1

/-- `Cminorgenproof.nextblock_freelist` -/
theorem nextblock_freelist {fbl : List (Block × Z × Z)} {m m' : Mem}
    (h : Mem.freeList m fbl = some m') : m'.nextblock = m.nextblock :=
  Mem.nextblock_freeList h

/-- `Cminorgenproof.free_list_freeable` -/
theorem free_list_freeable {l : List (Block × Z × Z)} {m m' : Mem} (h : Mem.freeList m l = some m')
    {b : Block} {lo hi : Z} (hin : (b, lo, hi) ∈ l) : Mem.rangePerm m b lo hi .Cur .Freeable = true :=
  SimplLocals.freeList_perm' h hin

/-- `Mem.free_inject`: freeing a list of blocks in the source and one block in
    the target preserves the injection, provided every source location that
    maps into the freed target range is itself freed. -/
theorem free_inject {f : Val.Meminj} {m1 m2 : Mem} {l : List (Block × Z × Z)} {m1' m2' : Mem}
    {b : Block} {lo hi : Z} (hinj : Mem.Inject f m1 m2) (hfl : Mem.freeList m1 l = some m1')
    (hfr : Mem.free m2 b lo hi = some m2')
    (H : ∀ b1 delta ofs k p, f b1 = some (b, delta) → Mem.perm m1 b1 ofs k p = true →
      lo ≤ ofs + delta → ofs + delta < hi → ∃ lo1 hi1, (b1, lo1, hi1) ∈ l ∧ lo1 ≤ ofs ∧ ofs < hi1) :
    Mem.Inject f m1' m2' := by
  refine Mem.free_right_inject (Mem.freeList_left_inject l hinj hfl) hfr ?_
  intro b1 delta ofs k p hf hp h1 h2
  obtain ⟨A, B⟩ := SimplLocals.perm_freeList hfl hp
  obtain ⟨lo1, hi1, hin, h3, h4⟩ := H b1 delta ofs k p hf A h1 h2
  exact B lo1 hi1 hin ⟨h3, h4⟩

/-- `Cminorgenproof.nextblock_storev` -/
theorem nextblock_storev {chunk : Chunk} {m : Mem} {addr v : Val} {m' : Mem}
    (h : Mem.storev chunk m addr v = some m') : m'.nextblock = m.nextblock :=
  Mem.storev_nextblock h

/-! ## Matching between Csharpminor's temporaries and Cminor's variables -/

/-- `Cminorgenproof.match_temps` -/
def MatchTemps (f : Val.Meminj) (le : Csharpminor.TempEnv) (te : Cminor.Env) : Prop :=
  ∀ id v, le.get id = some v → ∃ v', te.get id = some v' ∧ Val.Inject f v v'

/-- `Cminorgenproof.match_temps_invariant` -/
theorem match_temps_invariant {f f' : Val.Meminj} {le : Csharpminor.TempEnv} {te : Cminor.Env}
    (h : MatchTemps f le te) (hi : Val.inject_incr f f') : MatchTemps f' le te := by
  intro id v hv
  obtain ⟨v', A, B⟩ := h id v hv
  exact ⟨v', A, Val.inject_incr_inject hi B⟩

/-- `Cminorgenproof.match_temps_assign` -/
theorem match_temps_assign {f : Val.Meminj} {le : Csharpminor.TempEnv} {te : Cminor.Env}
    {id : Ident} {v tv : Val} (h : MatchTemps f le te) (hv : Val.Inject f v tv) :
    MatchTemps f (le.set id v) (te.set id tv) := by
  intro id' v' hv'
  by_cases hid : id' = id
  · subst hid; rw [PTree.gss] at hv' ⊢; cases hv'; exact ⟨tv, rfl, hv⟩
  · rw [PTree.gso _ _ _ _ (Ne.symm hid)] at hv' ⊢; exact h id' v' hv'

/-! ## Matching between Csharpminor's variable environment and Cminor's stack pointer -/

/-- `Cminorgenproof.match_var` -/
inductive MatchVar (f : Val.Meminj) (sp : Block) : Option (Block × Z) → Option Z → Prop where
  | «local» (b sz ofs) : Val.Inject f (.Vptr b Integers.Ptrofs.zero) (.Vptr sp (Integers.Ptrofs.repr ofs)) →
      MatchVar f sp (some (b, sz)) (some ofs)
  | global : MatchVar f sp none none

theorem MatchVar.mono {f f' : Val.Meminj} {sp : Block} {x : Option (Block × Z)} {y : Option Z}
    (h : MatchVar f sp x y) (INCR : Val.inject_incr f f') : MatchVar f' sp x y := by
  cases h with
  | «local» b sz ofs h => exact .«local» b sz ofs (Val.inject_incr_inject INCR h)
  | global => exact .global

/-- `Cminorgenproof.match_env` -/
structure MatchEnv (f : Val.Meminj) (cenv : Compilenv) (e : Csharpminor.Env) (sp : Block)
    (lo hi : Block) : Prop where
  me_vars : ∀ id, MatchVar f sp (e.get id) (cenv.get id)
  me_low_high : lo ≤ hi
  me_bounded : ∀ id b sz, e.get id = some (b, sz) → lo ≤ b ∧ b < hi
  me_inv : ∀ b delta, f b = some (sp, delta) → ∃ id sz, e.get id = some (b, sz)
  me_incr : ∀ b tb delta, f b = some (tb, delta) → b < lo → tb < sp

/-- `Cminorgenproof.match_env_invariant` -/
theorem match_env_invariant {f1 f2 : Val.Meminj} {cenv : Compilenv} {e : Csharpminor.Env}
    {sp lo hi : Block} (ME : MatchEnv f1 cenv e sp lo hi) (INCR : Val.inject_incr f1 f2)
    (H1 : ∀ b delta, f2 b = some (sp, delta) → f1 b = some (sp, delta))
    (H2 : ∀ b, b < lo → f2 b = f1 b) : MatchEnv f2 cenv e sp lo hi where
  me_vars id := (ME.me_vars id).mono INCR
  me_low_high := ME.me_low_high
  me_bounded := ME.me_bounded
  me_inv b delta h := ME.me_inv b delta (H1 b delta h)
  me_incr b tb delta h hb := by rw [H2 b hb] at h; exact ME.me_incr b tb delta h hb

/-- `Cminorgenproof.inject_incr_separated_same` -/
theorem inject_incr_separated_same {f1 f2 : Val.Meminj} {m1 m1' : Mem}
    (INCR : Val.inject_incr f1 f2) (SEP : InjectSeparated f1 f2 m1 m1') {b : Block}
    (hb : Mem.validBlock m1 b = true) : f2 b = f1 b := by
  cases h1 : f1 b with
  | some p => obtain ⟨b', d⟩ := p; exact INCR _ _ _ h1
  | none =>
    cases h2 : f2 b with
    | none => rfl
    | some p =>
      obtain ⟨b', d⟩ := p
      have := (SEP b b' d h1 h2).1
      rw [hb] at this; cases this

/-- `Cminorgenproof.inject_incr_separated_same'` -/
theorem inject_incr_separated_same' {f1 f2 : Val.Meminj} {m1 m1' : Mem}
    (INCR : Val.inject_incr f1 f2) (SEP : InjectSeparated f1 f2 m1 m1') {b b' : Block} {delta : Z}
    (h : f2 b = some (b', delta)) (hb : Mem.validBlock m1' b' = true) : f1 b = some (b', delta) := by
  cases h1 : f1 b with
  | some p =>
    obtain ⟨b'', d⟩ := p
    rw [INCR _ _ _ h1] at h; rw [← h]
  | none =>
    have := (SEP b b' delta h1 h).2
    rw [hb] at this; cases this

/-- `Cminorgenproof.match_env_external_call` -/
theorem match_env_external_call {f1 f2 : Val.Meminj} {cenv : Compilenv} {e : Csharpminor.Env}
    {sp lo hi : Block} {m1 m1' : Mem} (ME : MatchEnv f1 cenv e sp lo hi)
    (INCR : Val.inject_incr f1 f2) (SEP : InjectSeparated f1 f2 m1 m1')
    (HB : hi ≤ m1.nextblock) (SPB : sp < m1'.nextblock) : MatchEnv f2 cenv e sp lo hi :=
  match_env_invariant ME INCR
    (fun _ _ h => inject_incr_separated_same' INCR SEP h (by simp [Mem.validBlock]; exact SPB))
    (fun b hb => inject_incr_separated_same INCR SEP (by
      have := ME.me_low_high
      simp only [Mem.validBlock, decide_eq_true_eq]; blk_omega))

/-- `Cminorgenproof.match_env_alloc` -/
theorem match_env_alloc {f1 f2 : Val.Meminj} {id : Ident} {cenv : Compilenv}
    {e : Csharpminor.Env} {sp lo : Block} {m1 m2 : Mem} {sz : Z} {b : Block} {ofs : Z}
    (ME : MatchEnv f1 (PTree.remove id cenv) e sp lo m1.nextblock)
    (ALLOC : Mem.alloc m1 0 sz = (m2, b)) (CENV : cenv.get id = some ofs)
    (SAME : f2 b = some (sp, ofs))
    (OTHER : ∀ b', b' ≠ b → f2 b' = f1 b') (ENV : e.get id = none) :
    MatchEnv f2 cenv (e.set id (b, sz)) sp lo m2.nextblock := by
  obtain ⟨rfl, rfl⟩ := Mem.alloc_eq ALLOC
  have NB : (Mem.alloc m1 0 sz).1.nextblock = m1.nextblock.succ := Mem.nextblock_alloc m1 0 sz
  have LH := ME.me_low_high
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro id0
    rw [PTree.gsspec]
    split
    · rename_i h; subst h
      rw [CENV]
      exact .«local» _ _ _ (.ptr ofs SAME (by
        rw [Integers.Ptrofs.add_commut, Integers.Ptrofs.add_zero]))
    · rename_i hne
      have := ME.me_vars id0
      rw [PTree.gro _ _ _ (Ne.symm hne)] at this
      have hbd : ∀ b' sz', e.get id0 = some (b', sz') → b' ≠ m1.nextblock := by
        intro b' sz' h he; subst he
        have := (ME.me_bounded id0 _ sz' h).2
        blk_omega
      revert this hbd
      generalize e.get id0 = x
      generalize cenv.get id0 = y
      intro this hbd
      cases this with
      | «local» b' sz' ofs' h =>
        refine .«local» _ _ _ ?_
        cases h with
        | ptr delta hf ho =>
          refine .ptr delta ?_ ho
          rw [OTHER _ (hbd b' sz' rfl)]; exact hf
      | global => exact .global
  · rw [NB]; blk_omega
  · intro id0 b0 sz0 h
    rw [PTree.gsspec] at h
    split at h
    · cases h; rw [NB]; constructor <;> blk_omega
    · have := ME.me_bounded id0 b0 sz0 h
      rw [NB]; constructor <;> blk_omega
  · intro b0 delta h
    by_cases hb : b0 = m1.nextblock
    · subst hb; exact ⟨id, sz, PTree.gss _ _ _⟩
    · rw [OTHER _ hb] at h
      obtain ⟨id1, sz1, EQ⟩ := ME.me_inv b0 delta h
      refine ⟨id1, sz1, ?_⟩
      rw [PTree.gso]
      · exact EQ
      · intro he; subst he; rw [ENV] at EQ; cases EQ
  · intro b0 tb delta h hlt
    have hb : b0 ≠ m1.nextblock := by intro he; subst he; blk_omega
    rw [OTHER _ hb] at h
    exact ME.me_incr b0 tb delta h hlt

/-- `Cminorgenproof.match_bounds` -/
def MatchBounds (e : Csharpminor.Env) (m : Mem) : Prop :=
  ∀ id b sz ofs p, e.get id = some (b, sz) → Mem.perm m b ofs .Max p = true → 0 ≤ ofs ∧ ofs < sz

/-- `Cminorgenproof.match_bounds_invariant` -/
theorem match_bounds_invariant {e : Csharpminor.Env} {m1 m2 : Mem} (h : MatchBounds e m1)
    (H : ∀ id b sz ofs p, e.get id = some (b, sz) → Mem.perm m2 b ofs .Max p = true →
      Mem.perm m1 b ofs .Max p = true) : MatchBounds e m2 :=
  fun id b sz ofs p he hp => h id b sz ofs p he (H id b sz ofs p he hp)

/-! ## Permissions on the Cminor stack block -/

/-- `Cminorgenproof.is_reachable_from_env` -/
inductive IsReachableFromEnv (f : Val.Meminj) (e : Csharpminor.Env) (sp : Block) (ofs : Z) : Prop where
  | intro (id b sz delta) : e.get id = some (b, sz) → f b = some (sp, delta) →
      delta ≤ ofs → ofs < delta + sz → IsReachableFromEnv f e sp ofs

/-- `Cminorgenproof.padding_freeable` -/
def PaddingFreeable (f : Val.Meminj) (e : Csharpminor.Env) (tm : Mem) (sp : Block) (sz : Z) : Prop :=
  ∀ ofs, 0 ≤ ofs → ofs < sz → Mem.perm tm sp ofs .Cur .Freeable = true ∨ IsReachableFromEnv f e sp ofs

/-- `Cminorgenproof.padding_freeable_invariant` -/
theorem padding_freeable_invariant {f1 f2 : Val.Meminj} {e : Csharpminor.Env} {tm1 tm2 : Mem}
    {sp : Block} {sz : Z} {cenv : Compilenv} {lo hi : Block} (h : PaddingFreeable f1 e tm1 sp sz)
    (ME : MatchEnv f1 cenv e sp lo hi)
    (H1 : ∀ ofs, Mem.perm tm1 sp ofs .Cur .Freeable = true → Mem.perm tm2 sp ofs .Cur .Freeable = true)
    (H2 : ∀ b, b < hi → f2 b = f1 b) : PaddingFreeable f2 e tm2 sp sz := by
  intro ofs h1 h2
  rcases h ofs h1 h2 with A | ⟨id, b, sz', delta, he, hf, h3, h4⟩
  · exact .inl (H1 ofs A)
  · exact .inr ⟨id, b, sz', delta, he, by rw [H2 b (ME.me_bounded id b sz' he).2]; exact hf, h3, h4⟩

/-! ## Correspondence between global environments -/

/-- `Cminorgenproof.match_globalenvs` -/
structure MatchGlobalenvs (ge : Csharpminor.CGenv) (f : Val.Meminj) (bound : Block) : Prop where
  domain : ∀ b, b < bound → f b = some (b, 0)
  image : ∀ b1 b2 delta, f b1 = some (b2, delta) → b2 < bound → b1 = b2
  symbols : ∀ id b, Genv.findSymbol ge id = some b → b < bound
  functions : ∀ b fd, Genv.findFunctPtr ge b = some fd → b < bound
  varinfos : ∀ b gv, Genv.findVarInfo ge b = some gv → b < bound

/-- `Cminorgenproof.inj_preserves_globals`, in the form used by the
    injection property of external calls. -/
theorem match_globalenvs_symbols_inject {ge : Csharpminor.CGenv} {f : Val.Meminj} {bound : Block}
    (MG : MatchGlobalenvs ge f bound) : SymbolsInject f (Genv.toSenv ge) (Genv.toSenv ge) := by
  refine ⟨fun _ => rfl, ?_, ?_, ?_⟩
  · intro id b1 b2 delta hf hfs
    rw [MG.domain b1 (MG.symbols id b1 hfs)] at hf
    cases hf
    exact ⟨rfl, hfs⟩
  · intro id b1 _ hfs
    exact ⟨b1, MG.domain b1 (MG.symbols id b1 hfs), hfs⟩
  · intro b1 b2 delta hf
    show Genv.blockIsVolatile ge b2 = Genv.blockIsVolatile ge b1
    by_cases hb1 : b1 < bound
    · rw [MG.domain b1 hb1] at hf; cases hf; rfl
    · by_cases hb2 : b2 < bound
      · rw [MG.image b1 b2 delta hf hb2]
      · have none_of : ∀ b, ¬ b < bound → Genv.blockIsVolatile ge b = false := by
          intro b hb
          unfold Genv.blockIsVolatile
          cases hv : Genv.findVarInfo ge b with
          | none => rfl
          | some gv => exact absurd (MG.varinfos b gv hv) hb
        rw [none_of b1 hb1, none_of b2 hb2]

/-! ## Invariant on abstract call stacks -/

/-- `Cminorgenproof.frame` -/
structure Frame where
  cenv : Compilenv
  tf : Cminor.Function
  e : Csharpminor.Env
  le : Csharpminor.TempEnv
  te : Cminor.Env
  sp : Block
  lo : Block
  hi : Block

/-- `Cminorgenproof.callstack` -/
abbrev Callstack := List Frame

section CALLSTACK
variable (ge : Csharpminor.CGenv)

/-- `Cminorgenproof.match_callstack` -/
inductive MatchCallstack (f : Val.Meminj) (m tm : Mem) : Callstack → Block → Block → Prop where
  | nil (hi bound tbound) : MatchGlobalenvs ge f hi → hi ≤ bound → hi ≤ tbound →
      MatchCallstack f m tm [] bound tbound
  | cons (cenv tf e le te sp lo hi cs bound tbound) :
      hi ≤ bound → sp < tbound →
      MatchTemps f le te →
      MatchEnv f cenv e sp lo hi →
      MatchBounds e m →
      PaddingFreeable f e tm sp tf.fn_stackspace →
      MatchCallstack f m tm cs lo sp →
      MatchCallstack f m tm (⟨cenv, tf, e, le, te, sp, lo, hi⟩ :: cs) bound tbound

end CALLSTACK

variable {ge : Csharpminor.CGenv}

/-- `Cminorgenproof.match_callstack_match_globalenvs` -/
theorem match_callstack_match_globalenvs {f : Val.Meminj} {m tm : Mem} {cs : Callstack}
    {bound tbound : Block} (h : MatchCallstack ge f m tm cs bound tbound) :
    ∃ hi, MatchGlobalenvs ge f hi := by
  induction h with
  | nil hi _ _ MG _ _ => exact ⟨hi, MG⟩
  | cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih

/-- `Cminorgenproof.match_callstack_invariant` -/
theorem match_callstack_invariant {f1 : Val.Meminj} {m1 tm1 : Mem} {cs : Callstack}
    {bound tbound : Block} (h : MatchCallstack ge f1 m1 tm1 cs bound tbound) :
    ∀ {f2 : Val.Meminj} {m2 tm2 : Mem},
    Val.inject_incr f1 f2 →
    (∀ b ofs p, b < bound → Mem.perm m2 b ofs .Max p = true → Mem.perm m1 b ofs .Max p = true) →
    (∀ sp ofs, sp < tbound → Mem.perm tm1 sp ofs .Cur .Freeable = true →
      Mem.perm tm2 sp ofs .Cur .Freeable = true) →
    (∀ b, b < bound → f2 b = f1 b) →
    (∀ b b' delta, f2 b = some (b', delta) → b' < tbound → f1 b = some (b', delta)) →
    MatchCallstack ge f2 m2 tm2 cs bound tbound := by
  induction h with
  | nil hi bound tbound MG h1 h2 =>
    intro f2 m2 tm2 INCR _ _ H3 H4
    refine .nil hi bound tbound ⟨?_, ?_, MG.symbols, MG.functions, MG.varinfos⟩ h1 h2
    · intro b hb; rw [H3 b (by blk_omega)]; exact MG.domain b hb
    · intro b1 b2 delta hf hb2
      exact MG.image b1 b2 delta (H4 b1 b2 delta hf (by blk_omega)) hb2
  | cons cenv tf e le te sp lo hi cs bound tbound HB TB MTMP MENV MB PERM MCS ih =>
    intro f2 m2 tm2 INCR H1 H2 H3 H4
    have LH := MENV.me_low_high
    refine .cons cenv tf e le te sp lo hi cs bound tbound HB TB (match_temps_invariant MTMP INCR)
      (match_env_invariant MENV INCR (fun b delta hf => H4 b sp delta hf TB)
        (fun b hb => H3 b (by blk_omega)))
      (match_bounds_invariant MB fun id b sz ofs p he hp =>
        H1 b ofs p (by have := (MENV.me_bounded id b sz he).2; blk_omega) hp)
      (padding_freeable_invariant PERM MENV (fun ofs hp => H2 sp ofs TB hp)
        (fun b hb => H3 b (by blk_omega)))
      (ih INCR (fun b ofs p hb hp => H1 b ofs p (by blk_omega) hp)
        (fun sp' ofs hsp hp => H2 sp' ofs (by blk_omega) hp)
        (fun b hb => H3 b (by blk_omega))
        (fun b b' delta hf hb => H4 b b' delta hf (by blk_omega)))

/-- `Cminorgenproof.match_callstack_incr_bound` -/
theorem match_callstack_incr_bound {f : Val.Meminj} {m tm : Mem} {cs : Callstack}
    {bound tbound bound' tbound' : Block} (h : MatchCallstack ge f m tm cs bound tbound)
    (h1 : bound ≤ bound') (h2 : tbound ≤ tbound') : MatchCallstack ge f m tm cs bound' tbound' := by
  cases h with
  | nil hi _ _ MG a b => exact .nil hi _ _ MG (by blk_omega) (by blk_omega)
  | cons cenv tf e le te sp lo hi cs _ _ HB TB a b c d e' =>
    exact .cons cenv tf e le te sp lo hi cs _ _ (by blk_omega) (by blk_omega) a b c d e'

/-- `Cminorgenproof.match_callstack_set_temp` -/
theorem match_callstack_set_temp {f : Val.Meminj} {cenv : Compilenv} {e : Csharpminor.Env}
    {le : Csharpminor.TempEnv} {te : Cminor.Env} {sp lo hi : Block} {cs : Callstack}
    {bound tbound : Block} {m tm : Mem} {tf : Cminor.Function} {id : Ident} {v tv : Val}
    (hv : Val.Inject f v tv)
    (h : MatchCallstack ge f m tm (⟨cenv, tf, e, le, te, sp, lo, hi⟩ :: cs) bound tbound) :
    MatchCallstack ge f m tm (⟨cenv, tf, e, le.set id v, te.set id tv, sp, lo, hi⟩ :: cs)
      bound tbound := by
  cases h with
  | cons _ _ _ _ _ _ _ _ _ _ _ HB TB MTMP MENV MB PERM MCS =>
    exact .cons _ _ _ _ _ _ _ _ _ _ _ HB TB (match_temps_assign MTMP hv) MENV MB PERM MCS

/-- `Cminorgenproof.in_blocks_of_env` -/
theorem in_blocks_of_env {e : Csharpminor.Env} {id : Ident} {b : Block} {sz : Z}
    (h : e.get id = some (b, sz)) : (b, 0, sz) ∈ Csharpminor.blocksOfEnv e :=
  List.mem_map.mpr ⟨(id, b, sz), PTree.elements_correct _ _ _ h, rfl⟩

/-- `Cminorgenproof.in_blocks_of_env_inv` -/
theorem in_blocks_of_env_inv {b : Block} {lo hi : Z} {e : Csharpminor.Env}
    (h : (b, lo, hi) ∈ Csharpminor.blocksOfEnv e) : ∃ id, e.get id = some (b, hi) ∧ lo = 0 := by
  simp only [Csharpminor.blocksOfEnv, List.mem_map] at h
  obtain ⟨⟨id, b', sz⟩, hin, heq⟩ := h
  simp only [Csharpminor.blockOfBinding, Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  exact ⟨id, PTree.elements_complete _ _ _ hin, rfl⟩

/-- `Cminorgenproof.match_callstack_freelist` -/
theorem match_callstack_freelist {f : Val.Meminj} {cenv : Compilenv} {tf : Cminor.Function}
    {e : Csharpminor.Env} {le : Csharpminor.TempEnv} {te : Cminor.Env} {sp lo hi : Block}
    {cs : Callstack} {m m' tm : Mem} (INJ : Mem.Inject f m tm)
    (FREELIST : Mem.freeList m (Csharpminor.blocksOfEnv e) = some m')
    (MCS : MatchCallstack ge f m tm (⟨cenv, tf, e, le, te, sp, lo, hi⟩ :: cs) m.nextblock tm.nextblock) :
    ∃ tm', Mem.free tm sp 0 tf.fn_stackspace = some tm' ∧
      MatchCallstack ge f m' tm' cs m'.nextblock tm'.nextblock ∧ Mem.Inject f m' tm' := by
  cases MCS with
  | cons _ _ _ _ _ _ _ _ _ _ _ HB TB MTMP MENV MB PERM MCS =>
  have hrange : Mem.rangePerm tm sp 0 tf.fn_stackspace .Cur .Freeable = true := by
    refine Mem.rangePerm_intro _ _ _ _ _ _ fun ofs h1 h2 => ?_
    rcases PERM ofs h1 h2 with A | ⟨id, b, sz, delta, he, hf, h3, h4⟩
    · exact A
    · have hr := free_list_freeable FREELIST (in_blocks_of_env he)
      have := Mem.perm_inject hf INJ
        (Mem.rangePerm_perm _ _ _ _ _ _ hr (ofs - delta) (by zomega) (by zomega))
      rwa [show ofs - delta + delta = ofs by zomega] at this
  obtain ⟨tm', FREE⟩ := Mem.range_perm_free hrange
  have NEXT := nextblock_freelist FREELIST
  have NEXT' := Mem.nextblock_free FREE
  refine ⟨tm', FREE, ?_, ?_⟩
  · rw [NEXT, NEXT']
    have LH := MENV.me_low_high
    refine match_callstack_incr_bound (match_callstack_invariant MCS (Val.inject_incr_refl f)
      (fun b ofs p _ hp => perm_freelist FREELIST hp) ?_ (fun _ _ => rfl)
      (fun _ _ _ h _ => h)) (by blk_omega) (by blk_omega)
    intro sp' ofs hsp hp
    rw [Mem.free_result FREE]
    exact Mem.perm_free_1 (Or.inl (fun he => by subst he; blk_omega)) hp
  · refine free_inject INJ FREELIST FREE ?_
    intro b1 delta ofs k p hf hp _ _
    obtain ⟨id, sz, A⟩ := MENV.me_inv b1 delta hf
    exact ⟨0, sz, in_blocks_of_env A, MB id b1 sz ofs p A (Mem.perm_max hp)⟩

/-- `Cminorgenproof.match_callstack_external_call` -/
theorem match_callstack_external_call {f1 f2 : Val.Meminj} {m1 m2 m1' m2' : Mem}
    (OUTOFREACH : Mem.UnchangedOn (locOutOfReach f1 m1) m1' m2')
    (INCR : Val.inject_incr f1 f2) (SEPARATED : InjectSeparated f1 f2 m1 m1')
    (MAXPERMS : ∀ b ofs p, Mem.validBlock m1 b = true → Mem.perm m2 b ofs .Max p = true →
      Mem.perm m1 b ofs .Max p = true) {cs : Callstack} {bound tbound : Block}
    (h : MatchCallstack ge f1 m1 m1' cs bound tbound) :
    bound ≤ m1.nextblock → tbound ≤ m1'.nextblock → MatchCallstack ge f2 m2 m2' cs bound tbound := by
  induction h with
  | nil hi bound tbound MG h1 h2 =>
    intro hb htb
    refine .nil hi bound tbound ⟨fun b hb' => INCR _ _ _ (MG.domain b hb'), ?_, MG.symbols,
      MG.functions, MG.varinfos⟩ h1 h2
    intro b1 b2 delta hf hb2
    cases h1' : f1 b1 with
    | some p =>
      obtain ⟨b2', delta'⟩ := p
      rw [INCR _ _ _ h1'] at hf; cases hf
      exact MG.image _ _ _ h1' hb2
    | none =>
      have := (SEPARATED b1 b2 delta h1' hf).2
      simp only [Mem.validBlock, decide_eq_false_iff_not] at this
      exact absurd (by blk_omega) this
  | cons cenv tf e le te sp lo hi cs bound tbound HB TB MTMP MENV MB PERM MCS ih =>
    intro hb htb
    have LH := MENV.me_low_high
    refine .cons cenv tf e le te sp lo hi cs bound tbound HB TB (match_temps_invariant MTMP INCR)
      (match_env_invariant MENV INCR ?_ ?_) ?_ ?_ (ih (by blk_omega) (by blk_omega))
    · intro b delta hf
      cases h1 : f1 b with
      | some p => obtain ⟨b', d⟩ := p; rw [INCR _ _ _ h1] at hf; rw [← hf]
      | none =>
        have := (SEPARATED b sp delta h1 hf).2
        simp only [Mem.validBlock, decide_eq_false_iff_not] at this
        exact absurd (by blk_omega) this
    · intro b hb'
      exact inject_incr_separated_same INCR SEPARATED (by
        simp only [Mem.validBlock, decide_eq_true_eq]; blk_omega)
    · refine match_bounds_invariant MB fun id b sz ofs p he hp => MAXPERMS b ofs p ?_ hp
      have := (MENV.me_bounded id b sz he).2
      simp only [Mem.validBlock, decide_eq_true_eq]; blk_omega
    · intro ofs h1 h2
      by_cases hr : IsReachableFromEnv f1 e sp ofs
      · obtain ⟨id, b, sz, delta, he, hf, h3, h4⟩ := hr
        exact .inr ⟨id, b, sz, delta, he, INCR _ _ _ hf, h3, h4⟩
      · rcases PERM ofs h1 h2 with A | A
        · refine .inl (OUTOFREACH.perm_1 ?_ A)
          intro b0 delta hf hp
          obtain ⟨id, lv, B⟩ := MENV.me_inv b0 delta hf
          have C := MB id b0 lv _ _ B hp
          exact hr ⟨id, b0, lv, delta, B, hf, by zomega, by zomega⟩
        · exact absurd A hr

/-- `Cminorgenproof.match_callstack_alloc_right` -/
theorem match_callstack_alloc_right {f : Val.Meminj} {m tm : Mem} {cs : Callstack}
    {tf : Cminor.Function} {tm' : Mem} {sp : Block} {le : Csharpminor.TempEnv} {te : Cminor.Env}
    {cenv : Compilenv} (MCS : MatchCallstack ge f m tm cs m.nextblock tm.nextblock)
    (ALLOC : Mem.alloc tm 0 tf.fn_stackspace = (tm', sp)) (INJ : Mem.Inject f m tm)
    (MTMP : MatchTemps f le te) (CENV : ∀ id, cenv.get id = none) :
    MatchCallstack ge f m tm'
      (⟨cenv, tf, Csharpminor.emptyEnv, le, te, sp, m.nextblock, m.nextblock⟩ :: cs)
      m.nextblock tm'.nextblock := by
  obtain ⟨rfl, rfl⟩ := Mem.alloc_eq ALLOC
  have NB := Mem.nextblock_alloc tm 0 tf.fn_stackspace
  refine .cons _ _ _ _ _ _ _ _ _ _ _ (by blk_omega) (by rw [NB]; blk_omega) MTMP ?_ ?_ ?_ ?_
  · refine ⟨fun id => by rw [CENV]; simp [Csharpminor.emptyEnv]; exact .global,
      by blk_omega, fun id b sz h => by simp [Csharpminor.emptyEnv] at h, ?_, ?_⟩
    · intro b delta hf
      have := Mem.validBlock_inject_2 hf INJ
      rw [Mem.fresh_block_alloc] at this; cases this
    · intro b tb delta hf _
      have := Mem.validBlock_inject_2 hf INJ
      simp only [Mem.validBlock, decide_eq_true_eq] at this
      exact this
  · intro id b sz ofs p h; simp [Csharpminor.emptyEnv] at h
  · intro ofs h1 h2
    exact .inl (Mem.perm_alloc_same _ _ _ _ _ h1 h2)
  · refine match_callstack_invariant MCS (Val.inject_incr_refl f) (fun _ _ _ _ hp => hp) ?_
      (fun _ _ => rfl) (fun _ _ _ h _ => h)
    intro sp' ofs _ hp
    exact Mem.perm_alloc_1 hp

/-- `Cminorgenproof.match_callstack_alloc_left` -/
theorem match_callstack_alloc_left {f1 f2 : Val.Meminj} {m1 m2 tm : Mem} {id : Ident}
    {cenv : Compilenv} {tf : Cminor.Function} {e : Csharpminor.Env} {le : Csharpminor.TempEnv}
    {te : Cminor.Env} {sp lo : Block} {cs : Callstack} {sz : Z} {b : Block} {ofs : Z}
    (MCS : MatchCallstack ge f1 m1 tm
      (⟨PTree.remove id cenv, tf, e, le, te, sp, lo, m1.nextblock⟩ :: cs) m1.nextblock tm.nextblock)
    (ALLOC : Mem.alloc m1 0 sz = (m2, b)) (CENV : cenv.get id = some ofs)
    (INCR : Val.inject_incr f1 f2) (SAME : f2 b = some (sp, ofs))
    (OTHER : ∀ b', b' ≠ b → f2 b' = f1 b') (ENV : e.get id = none) :
    MatchCallstack ge f2 m2 tm
      (⟨cenv, tf, e.set id (b, sz), le, te, sp, lo, m2.nextblock⟩ :: cs)
      m2.nextblock tm.nextblock := by
  cases MCS with
  | cons _ _ _ _ _ _ _ _ _ _ _ HB TB MTMP MENV MB PERM MCS =>
  have MENV' := match_env_alloc MENV ALLOC CENV SAME OTHER ENV
  obtain ⟨rfl, rfl⟩ := Mem.alloc_eq ALLOC
  have NB := Mem.nextblock_alloc m1 0 sz
  have LO := MENV.me_low_high
  refine .cons _ _ _ _ _ _ _ _ _ _ _ (by blk_omega) TB (match_temps_invariant MTMP INCR) MENV' ?_ ?_ ?_
  · intro id0 b0 sz0 ofs0 p h hp
    rw [PTree.gsspec] at h
    split at h
    · cases h
      have := Mem.perm_alloc_inv hp
      rw [if_pos rfl] at this
      exact this
    · have hb := (MENV.me_bounded id0 b0 sz0 h).2
      have hne : b0 ≠ m1.nextblock := by intro he; subst he; blk_omega
      rw [Mem.perm_alloc_other _ _ _ _ hne] at hp
      exact MB id0 b0 sz0 ofs0 p h hp
  · intro ofs0 h1 h2
    rcases PERM ofs0 h1 h2 with A | ⟨id0, b0, sz0, delta, he, hf, h3, h4⟩
    · exact .inl A
    · refine .inr ⟨id0, b0, sz0, delta, ?_, ?_, h3, h4⟩
      · rw [PTree.gso]; exact he
        intro heq; subst heq; rw [ENV] at he; cases he
      · have hb := (MENV.me_bounded id0 b0 sz0 he).2
        have hne : b0 ≠ m1.nextblock := by intro he; subst he; blk_omega
        rw [OTHER _ hne]; exact hf
  · refine match_callstack_invariant MCS INCR ?_ (fun _ _ _ hp => hp) ?_ ?_
    · intro b0 ofs0 p hb hp
      have hne : b0 ≠ m1.nextblock := by intro he; subst he; blk_omega
      rwa [Mem.perm_alloc_other _ _ _ _ hne] at hp
    · intro b0 hb
      exact OTHER b0 (by intro he; subst he; blk_omega)
    · intro b0 b' delta hf hb'
      by_cases hb : b0 = m1.nextblock
      · subst hb; rw [SAME] at hf; cases hf; blk_omega
      · rw [OTHER _ hb] at hf; exact hf

end Cminorgen
end CC
