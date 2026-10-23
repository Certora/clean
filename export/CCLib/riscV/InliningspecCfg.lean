/-
  [RISC-V instance of `CCLib/backend/InliningspecCfg.lean`: the same development, in
  namespace `CC.RiscV`, over the RISC-V operators, registers and conventions.]

  RTL function inlining: relational specification — port of
  `backend/Inliningspec.v`, part 2: the relational specification of CFG
  expansion (`tr_instr`, `tr_funbody`), and the facts that expansion leaves
  older code unchanged (`expand_instr_unchanged`, `expand_cfg_rec_unchanged`).

  Rocq's `expand_cfg` recurses on the size of the environment; the port
  recurses on a counter (`expandCfgFuel`).  The section variable `rec` of
  `EXPAND_INSTR` is a `Recursor` (an optional function), assumed to satisfy
  the hypotheses `rec_unchanged`/`rec_spec` of Rocq for every smaller
  environment, plus monotonicity of the state (`rec_incr`), which Rocq gets
  from its monad.
-/
import CCLib.riscV.InliningspecBasic

namespace CC
namespace RiscV
namespace Inlining

open Op RTL

theorem minSafeAlignment_pos (sz : Z) : 0 < minSafeAlignment sz := by
  unfold minSafeAlignment; split <;> (try split) <;> (try split) <;> omega

/-- `Inliningspec.context_below` -/
def ContextBelow (ctx1 ctx2 : Context) : Prop :=
  Positive.add ctx1.dreg ctx1.mreg ≤ ctx2.dreg

/-- `Inliningspec.context_stack_call` -/
def ContextStackCall (ctx1 ctx2 : Context) : Prop :=
  ctx1.mstk ≥ 0 ∧ ctx1.dstk + ctx1.mstk ≤ ctx2.dstk

/-- `Inliningspec.context_stack_tailcall` -/
def ContextStackTailcall (ctx1 : Context) (f : RTL.Function) (ctx2 : Context) : Prop :=
  ctx2.dstk = align ctx1.dstk (minSafeAlignment f.fn_stacksize)

section INLINING_SPEC
variable (fenv : Funenv) (stacksize : Z)

mutual
/-- `Inliningspec.tr_instr` -/
inductive TrInstr : Context → Node → Instruction → Code → Prop where
  | nop (ctx pc c s) :
      c.get (spc ctx pc) = some (.Inop (spc ctx s)) →
      TrInstr ctx pc (.Inop s) c
  | op (ctx pc c op args res s) :
      res ≤ ctx.mreg →
      c.get (spc ctx pc) = some (.Iop (sop ctx op) (sregs ctx args) (sreg ctx res) (spc ctx s)) →
      TrInstr ctx pc (.Iop op args res s) c
  | load (ctx pc c chunk addr args res s) :
      res ≤ ctx.mreg →
      c.get (spc ctx pc) =
        some (.Iload chunk (saddr ctx addr) (sregs ctx args) (sreg ctx res) (spc ctx s)) →
      TrInstr ctx pc (.Iload chunk addr args res s) c
  | store (ctx pc c chunk addr args src s) :
      c.get (spc ctx pc) =
        some (.Istore chunk (saddr ctx addr) (sregs ctx args) (sreg ctx src) (spc ctx s)) →
      TrInstr ctx pc (.Istore chunk addr args src s) c
  | call (ctx pc c sg ros args res s) :
      res ≤ ctx.mreg →
      c.get (spc ctx pc) =
        some (.Icall sg (sros ctx ros) (sregs ctx args) (sreg ctx res) (spc ctx s)) →
      TrInstr ctx pc (.Icall sg ros args res s) c
  | call_inlined (ctx pc sg id args res s c f pc1 ctx') :
      res ≤ ctx.mreg →
      fenv.get id = some f →
      c.get (spc ctx pc) = some (.Inop pc1) →
      TrMoves c pc1 (sregs ctx args) (sregs ctx' f.fn_params) (spc ctx' f.fn_entrypoint) →
      TrFunbody ctx' f c →
      ctx'.retinfo = some (spc ctx s, sreg ctx res) →
      ContextBelow ctx ctx' →
      ContextStackCall ctx ctx' →
      TrInstr ctx pc (.Icall sg (.inr id) args res s) c
  | tailcall (ctx pc c sg ros args) :
      c.get (spc ctx pc) = some (.Itailcall sg (sros ctx ros) (sregs ctx args)) →
      ctx.retinfo = none →
      TrInstr ctx pc (.Itailcall sg ros args) c
  | tailcall_call (ctx pc c sg ros args res s) :
      c.get (spc ctx pc) = some (.Icall sg (sros ctx ros) (sregs ctx args) res s) →
      ctx.retinfo = some (s, res) →
      TrInstr ctx pc (.Itailcall sg ros args) c
  | tailcall_inlined (ctx pc sg id args c f pc1 ctx') :
      fenv.get id = some f →
      c.get (spc ctx pc) = some (.Inop pc1) →
      TrMoves c pc1 (sregs ctx args) (sregs ctx' f.fn_params) (spc ctx' f.fn_entrypoint) →
      TrFunbody ctx' f c →
      ctx'.retinfo = ctx.retinfo →
      ContextBelow ctx ctx' →
      ContextStackTailcall ctx f ctx' →
      TrInstr ctx pc (.Itailcall sg (.inr id) args) c
  | builtin (ctx pc c ef args res s) :
      (match res with | .BR r => r ≤ ctx.mreg | _ => True) →
      c.get (spc ctx pc) =
        some (.Ibuiltin ef (args.map (sbuiltinarg ctx)) (sbuiltinres ctx res) (spc ctx s)) →
      TrInstr ctx pc (.Ibuiltin ef args res s) c
  | cond (ctx pc cond args s1 s2 c) :
      c.get (spc ctx pc) = some (.Icond cond (sregs ctx args) (spc ctx s1) (spc ctx s2)) →
      TrInstr ctx pc (.Icond cond args s1 s2) c
  | jumptable (ctx pc r tbl c) :
      c.get (spc ctx pc) = some (.Ijumptable (sreg ctx r) (tbl.map (spc ctx))) →
      TrInstr ctx pc (.Ijumptable r tbl) c
  | ret (ctx pc or c) :
      c.get (spc ctx pc) = some (.Ireturn (or.map (sreg ctx))) →
      ctx.retinfo = none →
      TrInstr ctx pc (.Ireturn or) c
  | return_inlined (ctx pc or c rinfo) :
      c.get (spc ctx pc) = some (inlineReturn ctx or rinfo) →
      ctx.retinfo = some rinfo →
      TrInstr ctx pc (.Ireturn or) c

/-- `Inliningspec.tr_funbody` -/
inductive TrFunbody : Context → RTL.Function → Code → Prop where
  | intro (ctx f c) :
      (∀ r, r ∈ f.fn_params → r ≤ ctx.mreg) →
      (∀ pc i, f.fn_code.get pc = some i → TrInstr ctx pc i c) →
      ctx.mstk = Max.max f.fn_stacksize 0 →
      minSafeAlignment f.fn_stacksize ∣ ctx.dstk →
      ctx.dstk ≥ 0 →
      ctx.dstk + ctx.mstk ≤ stacksize →
      TrFunbody ctx f c
end

/-- `Inliningspec.fenv_agree` -/
def FenvAgree (fe : Funenv) : Prop := ∀ id f, fe.get id = some f → fenv.get id = some f

end INLINING_SPEC

/-! ## Expansion leaves older code unchanged -/

/-- The final state of a list traversal by `ptree_mfold` (Rocq's `mlist_iter2`). -/
def iterState {A : Type} (f : Positive → A → Mon Unit) (l : List (Positive × A)) (s : State) :
    State :=
  l.foldl (fun s1 p => (f p.1 p.2 s1).2) s

theorem iterState_cons {A : Type} (f : Positive → A → Mon Unit) (p : Positive × A)
    (l : List (Positive × A)) (s : State) :
    iterState f (p :: l) s = iterState f l (f p.1 p.2 s).2 := rfl

/-- `Inliningspec.ptree_mfold_spec` -/
theorem ptreeMfold_spec {A : Type} (f : Positive → A → Mon Unit) (t : PTree A) (s : State) :
    (ptreeMfold f t s).2 = iterState f (PTree.elements t) s := rfl

theorem iterState_incr {A : Type} {f : Positive → A → Mon Unit} (hf : ∀ k v, IncrM (f k v)) :
    ∀ (l : List (Positive × A)) (s : State), Sincr s (iterState f l s)
  | [], s => Sincr.refl s
  | p :: l, s => (hf p.1 p.2 s).trans (iterState_incr hf l _)

/-- Properties of a recursor `r` used for nested inlining. -/
structure RecIncr (r : Funenv → Context → RTL.Function → Mon Unit) : Prop where
  incr : ∀ fe ctx f, IncrM (r fe ctx f)
  unchanged : ∀ fe ctx f s pc, ctx.dpc ≤ s.st_nextnode → pc < ctx.dpc →
    (r fe ctx f s).2.st_code.get pc = s.st_code.get pc

theorem canInline_some {fe : Funenv} {rec : Recursor} {ros : Sum Reg Ident} {id : Ident}
    {f : RTL.Function} {r : Funenv → Context → RTL.Function → Mon Unit}
    (h : canInline fe rec ros = some (id, f, r)) :
    ros = .inr id ∧ rec = some r ∧ fe.get id = some f := by
  unfold canInline at h
  split at h
  · next id' r' =>
    cases hg : fe.get id' with
    | none => rw [hg] at h; cases h
    | some f' => rw [hg] at h; cases h; exact ⟨rfl, rfl, hg⟩
  · cases h

section EXPAND_INSTR
variable (fe : Funenv) (rec : Recursor) (hrec : ∀ r, rec = some r → RecIncr r)
include hrec

omit hrec in
theorem inlineFunction_incr (r : Funenv → Context → RTL.Function → Mon Unit) (hr : RecIncr r)
    (ctx : Context) (id : Ident) (f : RTL.Function) (args : List Reg) (retpc : Node)
    (retreg : Reg) : IncrM (inlineFunction fe r ctx id f args retpc retreg) :=
  incrM_bind (reserveNodes_incr _) fun _ => incrM_bind (reserveRegs_incr _) fun _ =>
    incrM_bind (hr.incr _ _ _) fun _ => addMoves_incr _ _ _

omit hrec in
theorem inlineTailFunction_incr (r : Funenv → Context → RTL.Function → Mon Unit) (hr : RecIncr r)
    (ctx : Context) (id : Ident) (f : RTL.Function) (args : List Reg) :
    IncrM (inlineTailFunction fe r ctx id f args) :=
  incrM_bind (reserveNodes_incr _) fun _ => incrM_bind (reserveRegs_incr _) fun _ =>
    incrM_bind (hr.incr _ _ _) fun _ => addMoves_incr _ _ _

theorem expandInstr_incr (ctx : Context) (pc : Node) (i : Instruction) :
    IncrM (expandInstr fe rec ctx pc i) := by
  cases i with
  | Icall sg ros args res s =>
    simp only [expandInstr]
    split
    · exact setInstr_incr _ _
    · next id f r hci =>
      obtain ⟨_, hr, _⟩ := canInline_some hci
      exact incrM_bind (inlineFunction_incr fe r (hrec r hr) _ _ _ _ _ _)
        fun _ => setInstr_incr _ _
  | Itailcall sg ros args =>
    simp only [expandInstr]
    split
    · split <;> exact setInstr_incr _ _
    · next id f r hci =>
      obtain ⟨_, hr, _⟩ := canInline_some hci
      exact incrM_bind (inlineTailFunction_incr fe r (hrec r hr) _ _ _ _)
        fun _ => setInstr_incr _ _
  | Ireturn or =>
    simp only [expandInstr]
    split <;> exact setInstr_incr _ _
  | _ => exact setInstr_incr _ _

theorem expandCfgRec_incr (ctx : Context) (f : RTL.Function) :
    IncrM (expandCfgRec fe rec ctx f) :=
  incrM_bind (requestStack_incr _) fun _ =>
    ptreeMfold_incr (fun k v => expandInstr_incr fe rec hrec ctx k v) _

end EXPAND_INSTR

theorem setInstr_get (p : Node) (i : Instruction) (s : State) {pc' : Node} (h : pc' ≠ p) :
    (setInstr p i s).2.st_code.get pc' = s.st_code.get pc' :=
  PTree.gso _ _ _ _ (Ne.symm h)

theorem setInstr_get_same (p : Node) (i : Instruction) (s : State) :
    (setInstr p i s).2.st_code.get p = some i := by
  show (s.st_code.set p i).get p = some i
  simp

/-- The state after the two reservations of `inline_function`. -/
def reserved (s : State) (f : RTL.Function) : State :=
  { { s with st_nextnode := s.st_nextnode.add (maxPcFunction f) } with
    st_nextreg := s.st_nextreg.add (maxRegFunction f) }

/-- The context of a function inlined at a call. -/
def ictx (ctx : Context) (s : State) (f : RTL.Function) (retpc : Node) (retreg : Reg) : Context :=
  callcontext ctx s.st_nextnode s.st_nextreg (maxRegFunction f) f.fn_stacksize retpc retreg

/-- The context of a function inlined at a tail call. -/
def tctx (ctx : Context) (s : State) (f : RTL.Function) : Context :=
  tailcontext ctx s.st_nextnode s.st_nextreg (maxRegFunction f) f.fn_stacksize

theorem inlineFunction_eq (r : Funenv → Context → RTL.Function → Mon Unit) (ctx : Context)
    (id : Ident) (f : RTL.Function) (args : List Reg) (retpc : Node) (retreg : Reg) (s : State) :
    inlineFunction fe r ctx id f args retpc retreg s =
      addMoves (sregs ctx args) (sregs (ictx ctx s f retpc retreg) f.fn_params)
        (spc (ictx ctx s f retpc retreg) f.fn_entrypoint)
        (r (fe.remove id) (ictx ctx s f retpc retreg) f (reserved s f)).2 := rfl

theorem inlineTailFunction_eq (r : Funenv → Context → RTL.Function → Mon Unit) (ctx : Context)
    (id : Ident) (f : RTL.Function) (args : List Reg) (s : State) :
    inlineTailFunction fe r ctx id f args s =
      addMoves (sregs ctx args) (sregs (tctx ctx s f) f.fn_params) (spc (tctx ctx s f) f.fn_entrypoint)
        (r (fe.remove id) (tctx ctx s f) f (reserved s f)).2 := rfl

theorem reserved_incr (s : State) (f : RTL.Function) : Sincr s (reserved s f) :=
  (reserveNodes_incr _ s).trans (reserveRegs_incr _ _)

theorem inline_unchanged_aux (r : Funenv → Context → RTL.Function → Mon Unit) (hr : RecIncr r)
    (ctx' : Context) (f : RTL.Function) (srcs dsts : List Reg) (e : Node) (s : State)
    (hdpc : ctx'.dpc = s.st_nextnode) {pc' : Node} (hp : pc' < s.st_nextnode) :
    (addMoves srcs dsts e (r fe ctx' f (reserved s f)).2).2.st_code.get pc' = s.st_code.get pc' := by
  have I1 := (reserved_incr s f).nextnode
  have I2 := (hr.incr fe ctx' f (reserved s f)).nextnode
  rw [add_moves_unchanged srcs dsts e (rfl : _ = ((addMoves srcs dsts e _).1, _))
    (.inl (by pos_omega))]
  rw [hr.unchanged _ _ _ _ _ (by rw [hdpc]; exact I1) (by rw [hdpc]; exact hp)]
  rfl


section EXPAND_EQ
variable {fe : Funenv} {rec : Recursor} {ctx : Context} {pc : Node}

theorem expandInstr_call_none {sg : Signature} {ros : Sum Reg Ident} {args : List Reg} {res : Reg}
    {s : Node} (h : canInline fe rec ros = none) :
    expandInstr fe rec ctx pc (.Icall sg ros args res s) =
      setInstr (spc ctx pc) (.Icall sg (sros ctx ros) (sregs ctx args) (sreg ctx res) (spc ctx s)) := by
  simp only [expandInstr, h]

theorem expandInstr_call_some {sg : Signature} {ros : Sum Reg Ident} {args : List Reg} {res : Reg}
    {s : Node} {id : Ident} {f : RTL.Function} {r : Funenv → Context → RTL.Function → Mon Unit}
    (h : canInline fe rec ros = some (id, f, r)) :
    expandInstr fe rec ctx pc (.Icall sg ros args res s) =
      (inlineFunction fe r ctx id f args s res >>= fun n => setInstr (spc ctx pc) (.Inop n)) := by
  simp only [expandInstr, h]

theorem expandInstr_tailcall_none_none {sg : Signature} {ros : Sum Reg Ident} {args : List Reg}
    (h : canInline fe rec ros = none) (h2 : ctx.retinfo = none) :
    expandInstr fe rec ctx pc (.Itailcall sg ros args) =
      setInstr (spc ctx pc) (.Itailcall sg (sros ctx ros) (sregs ctx args)) := by
  simp only [expandInstr, h, h2]

theorem expandInstr_tailcall_none_some {sg : Signature} {ros : Sum Reg Ident} {args : List Reg}
    {rpc : Node} {rreg : Reg} (h : canInline fe rec ros = none) (h2 : ctx.retinfo = some (rpc, rreg)) :
    expandInstr fe rec ctx pc (.Itailcall sg ros args) =
      setInstr (spc ctx pc) (.Icall sg (sros ctx ros) (sregs ctx args) rreg rpc) := by
  simp only [expandInstr, h, h2]

theorem expandInstr_tailcall_some {sg : Signature} {ros : Sum Reg Ident} {args : List Reg}
    {id : Ident} {f : RTL.Function} {r : Funenv → Context → RTL.Function → Mon Unit}
    (h : canInline fe rec ros = some (id, f, r)) :
    expandInstr fe rec ctx pc (.Itailcall sg ros args) =
      (inlineTailFunction fe r ctx id f args >>= fun n => setInstr (spc ctx pc) (.Inop n)) := by
  simp only [expandInstr, h]

theorem expandInstr_return_none {or : Option Reg} (h2 : ctx.retinfo = none) :
    expandInstr fe rec ctx pc (.Ireturn or) = setInstr (spc ctx pc) (.Ireturn (or.map (sreg ctx))) := by
  simp only [expandInstr, h2]

theorem expandInstr_return_some {or : Option Reg} {rinfo : Node × Reg} (h2 : ctx.retinfo = some rinfo) :
    expandInstr fe rec ctx pc (.Ireturn or) = setInstr (spc ctx pc) (inlineReturn ctx or rinfo) := by
  simp only [expandInstr, h2]

end EXPAND_EQ

section EXPAND_INSTR2
variable (fe : Funenv) (rec : Recursor) (hrec : ∀ r, rec = some r → RecIncr r)
include hrec

/-- `Inliningspec.expand_instr_unchanged` -/
theorem expand_instr_unchanged (ctx : Context) (pc : Node) (i : Instruction) (s : State)
    {pc' : Node} (hp : pc' < s.st_nextnode) (hne : pc' ≠ spc ctx pc) :
    (expandInstr fe rec ctx pc i s).2.st_code.get pc' = s.st_code.get pc' := by
  cases i with
  | Icall sg ros args res s0 =>
    rcases hci : canInline fe rec ros with _ | ⟨id, f, r⟩
    · rw [expandInstr_call_none hci]; exact setInstr_get _ _ _ hne
    · obtain ⟨_, hr, _⟩ := canInline_some hci
      rw [expandInstr_call_some hci]
      show (setInstr _ _ (inlineFunction fe r ctx id f args s0 res s).2).2.st_code.get pc' = _
      rw [setInstr_get _ _ _ hne, inlineFunction_eq]
      exact inline_unchanged_aux r (hrec r hr) _ f _ _ _ s rfl hp
  | Itailcall sg ros args =>
    rcases hci : canInline fe rec ros with _ | ⟨id, f, r⟩
    · rcases hri : ctx.retinfo with _ | ⟨rpc, rreg⟩
      · rw [expandInstr_tailcall_none_none hci hri]; exact setInstr_get _ _ _ hne
      · rw [expandInstr_tailcall_none_some hci hri]; exact setInstr_get _ _ _ hne
    · obtain ⟨_, hr, _⟩ := canInline_some hci
      rw [expandInstr_tailcall_some hci]
      show (setInstr _ _ (inlineTailFunction fe r ctx id f args s).2).2.st_code.get pc' = _
      rw [setInstr_get _ _ _ hne, inlineTailFunction_eq]
      exact inline_unchanged_aux r (hrec r hr) _ f _ _ _ s rfl hp
  | Ireturn or =>
    rcases hri : ctx.retinfo with _ | rinfo
    · rw [expandInstr_return_none hri]; exact setInstr_get _ _ _ hne
    · rw [expandInstr_return_some hri]; exact setInstr_get _ _ _ hne
  | _ => exact setInstr_get _ _ _ hne

/-- `Inliningspec.iter_expand_instr_unchanged` -/
theorem iter_expand_instr_unchanged (ctx : Context) {pc : Node} :
    ∀ (l : List (Positive × Instruction)) (s : State), pc < s.st_nextnode →
    pc ∉ (l.map Prod.fst).map (spc ctx) →
    (iterState (expandInstr fe rec ctx) l s).st_code.get pc = s.st_code.get pc
  | [], _, _, _ => rfl
  | (pc1, i1) :: l, s, hp, hn => by
    rw [iterState_cons]
    have I := (expandInstr_incr fe rec hrec ctx pc1 i1 s).nextnode
    rw [iter_expand_instr_unchanged ctx l _ (by pos_omega)
      (fun h => hn (List.mem_cons_of_mem _ h))]
    exact expand_instr_unchanged fe rec hrec ctx pc1 i1 s hp
      (fun h => hn (by rw [h]; exact List.mem_cons_self))

/-- `Inliningspec.expand_cfg_rec_unchanged` -/
theorem expand_cfg_rec_unchanged (ctx : Context) (f : RTL.Function) (s : State) {pc : Node}
    (hd : ctx.dpc ≤ s.st_nextnode) (hp : pc < ctx.dpc) :
    (expandCfgRec fe rec ctx f s).2.st_code.get pc = s.st_code.get pc := by
  show (iterState (expandInstr fe rec ctx) (PTree.elements f.fn_code)
    (requestStack (ctx.dstk + ctx.mstk) s).2).st_code.get pc = _
  rw [iter_expand_instr_unchanged fe rec hrec ctx _ _ (by
    show pc.toNat < s.st_nextnode.toNat
    have : pc.toNat < ctx.dpc.toNat := hp
    have : ctx.dpc.toNat ≤ s.st_nextnode.toNat := hd
    omega)]
  · rfl
  · intro h
    rw [List.map_map] at h
    obtain ⟨⟨pc1, i1⟩, _, he⟩ := List.mem_map.mp h
    exact shiftpos_not_below pc1 ctx.dpc (by rw [← he] at hp; exact hp)

end EXPAND_INSTR2

/-- `expand_cfg_rec` satisfies the hypotheses on the recursor. -/
theorem expandCfgFuel_recIncr : ∀ n, RecIncr (expandCfgFuel n)
  | 0 => ⟨fun fe ctx f => expandCfgRec_incr fe none (fun _ h => by cases h) ctx f,
      fun fe ctx f s pc hd hp => expand_cfg_rec_unchanged fe none (fun _ h => by cases h) ctx f s hd hp⟩
  | n + 1 =>
    have hrec : ∀ r, some (expandCfgFuel n) = some r → RecIncr r :=
      fun r h => by cases h; exact expandCfgFuel_recIncr n
    ⟨fun fe ctx f => expandCfgRec_incr fe _ hrec ctx f,
      fun fe ctx f s pc hd hp => expand_cfg_rec_unchanged fe _ hrec ctx f s hd hp⟩

/-- `Inliningspec.expand_cfg_unchanged` -/
theorem expand_cfg_unchanged (fe : Funenv) (ctx : Context) (f : RTL.Function) (s : State)
    {pc : Node} (hd : ctx.dpc ≤ s.st_nextnode) (hp : pc < ctx.dpc) :
    (expandCfg fe ctx f s).2.st_code.get pc = s.st_code.get pc :=
  (expandCfgFuel_recIncr _).unchanged fe ctx f s pc hd hp

end Inlining
end RiscV
end CC
