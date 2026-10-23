/-
  [x86-64 instance of `CCLib/backend/UnusedglobproofGlobals.lean`: the same development, in
  namespace `CC.X86`, over the x86-64 operators, registers and conventions.]

  Elimination of unreferenced static definitions: semantic preservation —
  port of `backend/Unusedglobproof.v`, part 2 (lines 446–756): kept
  identifiers, `transform_find_symbol_1/2`, `meminj_preserves_globals`,
  `init_meminj` and its properties, `globals_symbols_inject`,
  `symbol_address_inject`, `regset_inject` and its lemmas, `match_stacks`
  and its lemmas.
-/
import CCLib.x86.UnusedglobproofSpec
import CCLib.x86.OpInject
import CCLib.common.EventsInject
import CCLib.common.EventsMem
import CCLib.common.GlobalenvsTransf
import CCLib.common.GlobalenvsInitMem
import CCLib.common.Simulation

namespace CC
namespace X86
namespace Unusedglob

open Op RTL Smallstep
open Integers (Ptrofs)

section SOUNDNESS
variable {p tp : RTL.Program} {used : IS}

/-- `Unusedglobproof.transform_find_symbol_1` -/
theorem transform_find_symbol_1 (TRANSF : MatchProg1 used p tp) {id : Ident} {b : Block}
    (hs : Genv.findSymbol p.globalenv id = some b) (hk : id ∈ used) :
    ∃ b', Genv.findSymbol tp.globalenv id = some b' := by
  obtain ⟨g, P⟩ := ASTProgram.defmap_dom (Genv.findSymbol_inversion hs)
  have Q := TRANSF.defs id
  rw [if_pos (IS.mem_iff.2 hk), P] at Q
  exact Genv.findSymbol_exists (ASTProgram.in_defmap Q)

/-- `Unusedglobproof.transform_find_symbol_2` -/
theorem transform_find_symbol_2 (TRANSF : MatchProg1 used p tp) {id : Ident} {b : Block}
    (hs : Genv.findSymbol tp.globalenv id = some b) :
    id ∈ used ∧ ∃ b', Genv.findSymbol p.globalenv id = some b' := by
  obtain ⟨g, P⟩ := ASTProgram.defmap_dom (Genv.findSymbol_inversion hs)
  rw [TRANSF.defs id] at P
  split at P
  · next hm => exact ⟨IS.mem_iff.1 hm, Genv.findSymbol_exists (ASTProgram.in_defmap P)⟩
  · cases P

variable (p tp used) in
/-- `Unusedglobproof.meminj_preserves_globals` -/
structure MeminjPreservesGlobals (f : Val.Meminj) : Prop where
  symbols_inject_1 : ∀ id b b' delta, f b = some (b', delta) →
    Genv.findSymbol p.globalenv id = some b → delta = 0 ∧ Genv.findSymbol tp.globalenv id = some b'
  symbols_inject_2 : ∀ id b, id ∈ used → Genv.findSymbol p.globalenv id = some b →
    ∃ b', Genv.findSymbol tp.globalenv id = some b' ∧ f b = some (b', 0)
  symbols_inject_3 : ∀ id b', Genv.findSymbol tp.globalenv id = some b' →
    ∃ b, Genv.findSymbol p.globalenv id = some b ∧ f b = some (b', 0)
  defs_inject : ∀ b b' delta gd, f b = some (b', delta) → Genv.findDef p.globalenv b = some gd →
    Genv.findDef tp.globalenv b' = some gd ∧ delta = 0 ∧ ∀ id, RefDef gd id → id ∈ used
  defs_rev_inject : ∀ b b' delta gd, f b = some (b', delta) →
    Genv.findDef tp.globalenv b' = some gd → Genv.findDef p.globalenv b = some gd ∧ delta = 0

variable (p tp) in
/-- `Unusedglobproof.init_meminj` -/
def initMeminj : Val.Meminj := fun b =>
  match Genv.invertSymbol p.globalenv b with
  | some id =>
    match Genv.findSymbol tp.globalenv id with
    | some b' => some (b', 0)
    | none => none
  | none => none

theorem symbInjective_prog (q : RTL.Program) : Genv.SymbInjective q.globalenv :=
  Genv.symbInjective_globalenv q.prog_public q.prog_defs

/-- `Unusedglobproof.init_meminj_eq` -/
theorem init_meminj_eq {id : Ident} {b b' : Block} (h1 : Genv.findSymbol p.globalenv id = some b)
    (h2 : Genv.findSymbol tp.globalenv id = some b') : initMeminj p tp b = some (b', 0) := by
  unfold initMeminj
  rw [Genv.find_invertSymbol (symbInjective_prog p) h1]
  simp only [h2]

/-- `Unusedglobproof.init_meminj_invert` -/
theorem init_meminj_invert {b b' : Block} {delta : Z} (h : initMeminj p tp b = some (b', delta)) :
    delta = 0 ∧ ∃ id, Genv.findSymbol p.globalenv id = some b ∧
      Genv.findSymbol tp.globalenv id = some b' := by
  unfold initMeminj at h
  split at h
  · next id hid =>
    split at h
    · next b'' hb =>
      cases h
      exact ⟨rfl, id, Genv.invert_findSymbol hid, hb⟩
    · cases h
  · cases h

/-- `Unusedglobproof.init_meminj_preserves_globals` -/
theorem init_meminj_preserves_globals (TRANSF : MatchProg1 used p tp)
    (USED : ValidUsedSet p used) : MeminjPreservesGlobals p tp used (initMeminj p tp) where
  symbols_inject_1 id b b' delta hf hs := by
    obtain ⟨A, id1, B, C⟩ := init_meminj_invert hf
    have := symbInjective_prog p _ _ _ B hs
    subst this
    exact ⟨A, C⟩
  symbols_inject_2 id b hk hs := by
    obtain ⟨b', F⟩ := transform_find_symbol_1 TRANSF hs hk
    exact ⟨b', F, init_meminj_eq hs F⟩
  symbols_inject_3 id b' hs := by
    obtain ⟨_, b, F⟩ := transform_find_symbol_2 TRANSF hs
    exact ⟨b, F, init_meminj_eq F hs⟩
  defs_inject b b' delta gd hf hd := by
    obtain ⟨A, id, B, C⟩ := init_meminj_invert hf
    have K := (transform_find_symbol_2 TRANSF C).1
    have P1 : p.defmap.get id = some gd := by
      rw [ASTProgram.defmap_eq, Genv.find_def_symbol]; exact ⟨b, B, hd⟩
    have P2 : tp.defmap.get id = some gd := by
      rw [TRANSF.defs id, if_pos (IS.mem_iff.2 K)]; exact P1
    rw [ASTProgram.defmap_eq, Genv.find_def_symbol] at P2
    obtain ⟨b1, P, Q⟩ := P2
    have : b1 = b' := by
      have := P.symm.trans C
      cases this; rfl
    subst this
    exact ⟨Q, A, fun i hr => USED.closed id gd i K P1 hr⟩
  defs_rev_inject b b' delta gd hf hd := by
    obtain ⟨A, id, B, C⟩ := init_meminj_invert hf
    have P2 : tp.defmap.get id = some gd := by
      rw [ASTProgram.defmap_eq, Genv.find_def_symbol]; exact ⟨b', C, hd⟩
    rw [TRANSF.defs id] at P2
    split at P2
    · rw [ASTProgram.defmap_eq, Genv.find_def_symbol] at P2
      obtain ⟨b1, P, Q⟩ := P2
      have : b1 = b := by
        have := P.symm.trans B
        cases this; rfl
      subst this
      exact ⟨Q, A⟩
    · cases P2

theorem publicSymbol_eq_contains {q : RTL.Program} {id : Ident} {b : Block}
    (hs : Genv.findSymbol q.globalenv id = some b) :
    Genv.publicSymbol q.globalenv id = q.prog_public.contains id := by
  unfold Genv.publicSymbol
  rw [hs]
  show (Genv.globalenv q.prog_public q.prog_defs).genv_public.contains id = _
  rw [Genv.globalenv_public]

theorem publicSymbol_none {q : RTL.Program} {id : Ident}
    (hs : Genv.findSymbol q.globalenv id = none) : Genv.publicSymbol q.globalenv id = false := by
  unfold Genv.publicSymbol; rw [hs]

/-- `Unusedglobproof.globals_symbols_inject` -/
theorem globals_symbols_inject (TRANSF : MatchProg1 used p tp) (USED : ValidUsedSet p used)
    {j : Val.Meminj} (h : MeminjPreservesGlobals p tp used j) :
    SymbolsInject j (Genv.toSenv p.globalenv) (Genv.toSenv tp.globalenv) where
  public_eq id := by
    show Genv.publicSymbol tp.globalenv id = Genv.publicSymbol p.globalenv id
    cases ht : Genv.findSymbol tp.globalenv id with
    | some b' =>
      obtain ⟨b, FS, _⟩ := h.symbols_inject_3 id b' ht
      rw [publicSymbol_eq_contains ht, publicSymbol_eq_contains FS, TRANSF.public_eq]
    | none =>
      rw [publicSymbol_none ht]
      cases hs : Genv.findSymbol p.globalenv id with
      | none => rw [publicSymbol_none hs]
      | some b =>
        rw [publicSymbol_eq_contains hs]
        cases hc : p.prog_public.contains id with
        | false => rfl
        | true =>
          have hk := USED.publics id (by simpa using hc)
          obtain ⟨b', A, _⟩ := h.symbols_inject_2 id b hk hs
          rw [ht] at A; cases A
  find_mapped id b1 b2 delta hf hs := h.symbols_inject_1 id b1 b2 delta hf hs
  find_public id b1 hp hs := by
    have hp' : Genv.publicSymbol p.globalenv id = true := hp
    rw [publicSymbol_eq_contains hs] at hp'
    have hk := USED.publics id (by simpa using hp')
    obtain ⟨b', A, B⟩ := h.symbols_inject_2 id b1 hk hs
    exact ⟨b', B, A⟩
  volatile_eq b1 b2 delta hf := by
    show Genv.blockIsVolatile tp.globalenv b2 = Genv.blockIsVolatile p.globalenv b1
    unfold Genv.blockIsVolatile Genv.findVarInfo
    cases h1 : Genv.findDef p.globalenv b1 with
    | some gd => rw [(h.defs_inject b1 b2 delta gd hf h1).1]
    | none =>
      cases h2 : Genv.findDef tp.globalenv b2 with
      | none => rfl
      | some gd => rw [(h.defs_rev_inject b1 b2 delta gd hf h2).1] at h1; cases h1

/-- `Unusedglobproof.symbol_address_inject` -/
theorem symbol_address_inject {j : Val.Meminj} (h : MeminjPreservesGlobals p tp used j)
    {id : Ident} (hk : id ∈ used) (ofs : Ptrofs) :
    Val.Inject j (Genv.symbolAddress p.globalenv id ofs) (Genv.symbolAddress tp.globalenv id ofs) := by
  unfold Genv.symbolAddress
  cases hs : Genv.findSymbol p.globalenv id with
  | none => exact .undef _
  | some b =>
    obtain ⟨b', A, B⟩ := h.symbols_inject_2 id b hk hs
    rw [A]
    exact .ptr _ B (by rw [Ptrofs.repr_zero, Ptrofs.add_zero])

/-! ## Register sets -/

/-- `Unusedglobproof.regset_inject` -/
def RegsetInject (f : Val.Meminj) (rs rs' : RTL.Regset) : Prop :=
  ∀ r, Val.Inject f (rs.get r) (rs'.get r)

/-- `Unusedglobproof.regs_inject` -/
theorem regs_inject {f : Val.Meminj} {rs rs' : RTL.Regset} (h : RegsetInject f rs rs') :
    ∀ l : List Reg, Val.InjectList f (rs.getList l) (rs'.getList l)
  | [] => .nil
  | r :: l => .cons (h r) (regs_inject h l)

/-- `Unusedglobproof.set_reg_inject` -/
theorem set_reg_inject {f : Val.Meminj} {rs rs' : RTL.Regset} {r : Reg} {v v' : Val}
    (h : RegsetInject f rs rs') (hv : Val.Inject f v v') :
    RegsetInject f (rs.set r v) (rs'.set r v') := by
  intro r0
  rw [PMap.gsspec, PMap.gsspec]
  split
  · exact hv
  · exact h r0

/-- `Unusedglobproof.set_res_inject` -/
theorem set_res_inject {f : Val.Meminj} {rs rs' : RTL.Regset} (res : BuiltinRes Reg) {v v' : Val}
    (h : RegsetInject f rs rs') (hv : Val.Inject f v v') :
    RegsetInject f (regmapSetres res v rs) (regmapSetres res v' rs') := by
  cases res with
  | BR r => exact set_reg_inject h hv
  | _ => exact h

/-- `Unusedglobproof.regset_inject_incr` -/
theorem regset_inject_incr {f f' : Val.Meminj} {rs rs' : RTL.Regset} (h : RegsetInject f rs rs')
    (hi : Val.inject_incr f f') : RegsetInject f' rs rs' :=
  fun r => Val.inject_incr_inject hi (h r)

/-- `Unusedglobproof.regset_undef_inject` -/
theorem regset_undef_inject (f : Val.Meminj) :
    RegsetInject f (PMap.init .Vundef) (PMap.init .Vundef) := by
  intro r; rw [PMap.gi]; exact .undef _

/-- `Unusedglobproof.init_regs_inject` -/
theorem init_regs_inject {f : Val.Meminj} :
    ∀ {args args' : List Val}, Val.InjectList f args args' → ∀ params : List Reg,
      RegsetInject f (initRegs args params) (initRegs args' params)
  | [], [], .nil, params => by
    cases params <;> exact regset_undef_inject f
  | _ :: _, _ :: _, .cons hv hl, [] => regset_undef_inject f
  | _ :: _, _ :: _, .cons hv hl, r :: params => set_reg_inject (init_regs_inject hl params) hv

/-! ## Relating call stacks -/

variable (p tp used) in
/-- `Unusedglobproof.match_stacks` -/
inductive MatchStacks (j : Val.Meminj) :
    List RTL.Stackframe → List RTL.Stackframe → Block → Block → Prop where
  | nil (bound tbound : Block) :
      MeminjPreservesGlobals p tp used j →
      p.globalenv.genv_next ≤ bound → tp.globalenv.genv_next ≤ tbound →
      MatchStacks j [] [] bound tbound
  | cons (res : Reg) (f : RTL.Function) (sp : Block) (pc : Node) (rs : RTL.Regset)
      (s : List RTL.Stackframe) (tsp : Block) (trs : RTL.Regset) (ts : List RTL.Stackframe)
      (bound tbound : Block) :
      MatchStacks j s ts sp tsp →
      (∀ id, RefFunction f id → id ∈ used) →
      j sp = some (tsp, 0) →
      RegsetInject j rs trs →
      sp < bound → tsp < tbound →
      MatchStacks j (.Stackframe res f (.Vptr sp Ptrofs.zero) pc rs :: s)
        (.Stackframe res f (.Vptr tsp Ptrofs.zero) pc trs :: ts) bound tbound

/-- `Unusedglobproof.match_stacks_preserves_globals` -/
theorem match_stacks_preserves_globals {j : Val.Meminj} {s ts : List RTL.Stackframe}
    {bound tbound : Block} (h : MatchStacks p tp used j s ts bound tbound) :
    MeminjPreservesGlobals p tp used j := by
  induction h with
  | nil _ _ hg _ _ => exact hg
  | cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih

theorem symb_range {q : RTL.Program} {id : Ident} {b : Block}
    (h : Genv.findSymbol q.globalenv id = some b) : b < q.globalenv.genv_next :=
  Genv.symbBelow_globalenv q.prog_public q.prog_defs id b h

theorem defs_range {q : RTL.Program} {b : Block} {gd : GlobDef RTL.Fundef Unit}
    (h : Genv.findDef q.globalenv b = some gd) : b < q.globalenv.genv_next :=
  Genv.defsBelow_globalenv q.prog_public q.prog_defs b gd h

/-- `Unusedglobproof.match_stacks_incr` -/
theorem match_stacks_incr {j j' : Val.Meminj} (INCR : Val.inject_incr j j')
    {s ts : List RTL.Stackframe} {bound tbound : Block}
    (h : MatchStacks p tp used j s ts bound tbound)
    (hnew : ∀ b1 b2 delta, j b1 = none → j' b1 = some (b2, delta) → bound ≤ b1 ∧ tbound ≤ b2) :
    MatchStacks p tp used j' s ts bound tbound := by
  induction h with
  | nil bound tbound hg hb htb =>
    have SAME : ∀ b b' delta, b < p.globalenv.genv_next → j' b = some (b', delta) →
        j b = some (b', delta) := by
      intro b b' delta hlt hj
      cases hjb : j b with
      | some q =>
        obtain ⟨b1, d1⟩ := q
        have := (INCR _ _ _ hjb).symm.trans hj
        rw [this]
      | none =>
        have := (hnew _ _ _ hjb hj).1
        exact absurd (Nat.lt_of_lt_of_le hlt hb) (Nat.not_lt.2 this)
    have SAME' : ∀ b b' delta, b' < tp.globalenv.genv_next → j' b = some (b', delta) →
        j b = some (b', delta) := by
      intro b b' delta hlt hj
      cases hjb : j b with
      | some q =>
        obtain ⟨b1, d1⟩ := q
        have := (INCR _ _ _ hjb).symm.trans hj
        rw [this]
      | none =>
        have := (hnew _ _ _ hjb hj).2
        exact absurd (Nat.lt_of_lt_of_le hlt htb) (Nat.not_lt.2 this)
    refine .nil _ _ ⟨?_, ?_, ?_, ?_, ?_⟩ hb htb
    · intro id b b' delta hf hs
      exact hg.symbols_inject_1 id b b' delta (SAME _ _ _ (symb_range hs) hf) hs
    · intro id b hk hs
      obtain ⟨b', A, B⟩ := hg.symbols_inject_2 id b hk hs
      exact ⟨b', A, INCR _ _ _ B⟩
    · intro id b' hs
      obtain ⟨b, A, B⟩ := hg.symbols_inject_3 id b' hs
      exact ⟨b, A, INCR _ _ _ B⟩
    · intro b b' delta gd hf hd
      exact hg.defs_inject b b' delta gd (SAME _ _ _ (defs_range hd) hf) hd
    · intro b b' delta gd hf hd
      exact hg.defs_rev_inject b b' delta gd (SAME' _ _ _ (defs_range hd) hf) hd
  | cons res f sp pc rs s tsp trs ts bound tbound hms hk hsp hrs hb htb ih =>
    refine .cons _ _ _ _ _ _ _ _ _ _ _ (ih ?_) hk (INCR _ _ _ hsp) (regset_inject_incr hrs INCR) hb htb
    intro b1 b2 delta h1 h2
    obtain ⟨A, B⟩ := hnew b1 b2 delta h1 h2
    exact ⟨Nat.le_trans (Nat.le_of_lt hb) A, Nat.le_trans (Nat.le_of_lt htb) B⟩

/-- `Unusedglobproof.match_stacks_bound` -/
theorem match_stacks_bound {j : Val.Meminj} {s ts : List RTL.Stackframe}
    {bound tbound bound' tbound' : Block} (h : MatchStacks p tp used j s ts bound tbound)
    (h1 : bound ≤ bound') (h2 : tbound ≤ tbound') : MatchStacks p tp used j s ts bound' tbound' := by
  cases h with
  | nil _ _ hg hb htb => exact .nil _ _ hg (Nat.le_trans hb h1) (Nat.le_trans htb h2)
  | cons res f sp pc rs s tsp trs ts _ _ hms hk hsp hrs hb htb =>
    exact .cons _ _ _ _ _ _ _ _ _ _ _ hms hk hsp hrs (Nat.lt_of_lt_of_le hb h1)
      (Nat.lt_of_lt_of_le htb h2)

end SOUNDNESS

end Unusedglob
end X86
end CC
