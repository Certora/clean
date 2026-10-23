/-
  [RISC-V instance of `CCLib/backend/InliningproofMatch.lean`: the same development, in
  namespace `CC.RiscV`, over the RISC-V operators, registers and conventions.]

  RTL function inlining: semantic preservation — port of
  `backend/Inliningproof.v`, part 3: the relation between call stacks
  (`match_stacks`, `match_stacks_inside`) and its preservation lemmas.
-/
import CCLib.riscV.InliningproofStacks

namespace CC
namespace RiscV
namespace Inlining

open Op RTL Smallstep
open Integers (Ptrofs)

/-! ## Relating stacks -/

mutual
/-- `Inliningproof.match_stacks` -/
inductive MatchStacks (prog : RTL.Program) (F : Val.Meminj) (m m' : Mem) :
    List RTL.Stackframe → List RTL.Stackframe → Block → Prop where
  | nil (bound1 bound : Block) :
      MatchGlobalenvs prog.globalenv F bound1 → bound1 ≤ bound →
      MatchStacks prog F m m' [] [] bound
  | cons (res : Reg) (f : RTL.Function) (sp : Block) (pc : Node) (rs : RTL.Regset)
      (stk : List RTL.Stackframe) (f' : RTL.Function) (sp' : Block) (rs' : RTL.Regset)
      (stk' : List RTL.Stackframe) (bound : Block) (fenv : Funenv) (ctx : Context) :
      MatchStacksInside prog F m m' stk stk' f' ctx sp' rs' →
      FenvCompat prog fenv →
      TrFunbody fenv f'.fn_stacksize ctx f f'.fn_code →
      AgreeRegs F ctx rs rs' →
      F sp = some (sp', ctx.dstk) →
      RangePrivate F m m' sp' (ctx.dstk + ctx.mstk) f'.fn_stacksize →
      0 ≤ f'.fn_stacksize → f'.fn_stacksize < Ptrofs.max_unsigned →
      (∀ ofs, Mem.perm m' sp' ofs .Max .Nonempty = true → 0 ≤ ofs ∧ ofs ≤ f'.fn_stacksize) →
      res ≤ ctx.mreg →
      sp' < bound →
      MatchStacks prog F m m' (.Stackframe res f (.Vptr sp Ptrofs.zero) pc rs :: stk)
        (.Stackframe (sreg ctx res) f' (.Vptr sp' Ptrofs.zero) (spc ctx pc) rs' :: stk') bound
  | untailcall (stk : List RTL.Stackframe) (res : Reg) (f' : RTL.Function) (sp' : Block)
      (rpc : Node) (rs' : RTL.Regset) (stk' : List RTL.Stackframe) (bound : Block)
      (ctx : Context) :
      MatchStacksInside prog F m m' stk stk' f' ctx sp' rs' →
      RangePrivate F m m' sp' ctx.dstk f'.fn_stacksize →
      0 ≤ f'.fn_stacksize → f'.fn_stacksize < Ptrofs.max_unsigned →
      (∀ ofs, Mem.perm m' sp' ofs .Max .Nonempty = true → 0 ≤ ofs ∧ ofs ≤ f'.fn_stacksize) →
      ctx.retinfo = some (rpc, res) →
      sp' < bound →
      MatchStacks prog F m m' stk (.Stackframe res f' (.Vptr sp' Ptrofs.zero) rpc rs' :: stk')
        bound

/-- `Inliningproof.match_stacks_inside` -/
inductive MatchStacksInside (prog : RTL.Program) (F : Val.Meminj) (m m' : Mem) :
    List RTL.Stackframe → List RTL.Stackframe → RTL.Function → Context → Block → RTL.Regset →
      Prop where
  | base (stk stk' : List RTL.Stackframe) (f' : RTL.Function) (ctx : Context) (sp' : Block)
      (rs' : RTL.Regset) :
      MatchStacks prog F m m' stk stk' sp' → ctx.retinfo = none → ctx.dstk = 0 →
      MatchStacksInside prog F m m' stk stk' f' ctx sp' rs'
  | inlined (res : Reg) (f : RTL.Function) (sp : Block) (pc : Node) (rs : RTL.Regset)
      (stk stk' : List RTL.Stackframe) (f' : RTL.Function) (fenv : Funenv) (ctx : Context)
      (sp' : Block) (rs' : RTL.Regset) (ctx' : Context) :
      MatchStacksInside prog F m m' stk stk' f' ctx' sp' rs' →
      FenvCompat prog fenv →
      TrFunbody fenv f'.fn_stacksize ctx' f f'.fn_code →
      AgreeRegs F ctx' rs rs' →
      F sp = some (sp', ctx'.dstk) →
      RangePrivate F m m' sp' (ctx'.dstk + ctx'.mstk) ctx.dstk →
      res ≤ ctx'.mreg →
      ctx.retinfo = some (spc ctx' pc, sreg ctx' res) →
      ContextBelow ctx' ctx →
      ContextStackCall ctx' ctx →
      MatchStacksInside prog F m m' (.Stackframe res f (.Vptr sp Ptrofs.zero) pc rs :: stk)
        stk' f' ctx sp' rs'
end

section MATCH_STACKS
variable {prog : RTL.Program}

theorem pos_lt_of_lt_of_le {a b c : Positive} (h1 : a < b) (h2 : b ≤ c) : a < c :=
  Nat.lt_of_lt_of_le h1 h2

theorem pos_le_of_lt {a b : Positive} (h : a < b) : a ≤ b := Nat.le_of_lt h

mutual
/-- `Inliningproof.match_stacks_globalenvs` -/
theorem match_stacks_globalenvs {F : Val.Meminj} {m m' : Mem} :
    ∀ {stk stk' bound}, MatchStacks prog F m m' stk stk' bound →
      ∃ b, MatchGlobalenvs prog.globalenv F b
  | _, _, _, .nil b1 _ hmg _ => ⟨b1, hmg⟩
  | _, _, _, .cons _ _ _ _ _ _ _ _ _ _ _ _ _ hms _ _ _ _ _ _ _ _ _ _ =>
      match_stacks_inside_globalenvs hms
  | _, _, _, .untailcall _ _ _ _ _ _ _ _ _ hms _ _ _ _ _ _ => match_stacks_inside_globalenvs hms

/-- `Inliningproof.match_stacks_inside_globalenvs` -/
theorem match_stacks_inside_globalenvs {F : Val.Meminj} {m m' : Mem} :
    ∀ {stk stk' f ctx sp rs'}, MatchStacksInside prog F m m' stk stk' f ctx sp rs' →
      ∃ b, MatchGlobalenvs prog.globalenv F b
  | _, _, _, _, _, _, .base _ _ _ _ _ _ hms _ _ => match_stacks_globalenvs hms
  | _, _, _, _, _, _, .inlined _ _ _ _ _ _ _ _ _ _ _ _ _ hms _ _ _ _ _ _ _ _ _ =>
      match_stacks_inside_globalenvs hms
end

/-- `Inliningproof.match_stacks_bound` -/
theorem match_stacks_bound {F : Val.Meminj} {m m' : Mem} {stk stk' : List RTL.Stackframe}
    {bound bound1 : Block} (h : MatchStacks prog F m m' stk stk' bound) (hle : bound ≤ bound1) :
    MatchStacks prog F m m' stk stk' bound1 := by
  cases h with
  | nil b1 _ hmg hb => exact .nil b1 _ hmg (Nat.le_trans hb hle)
  | cons res f sp pc rs stk f' sp' rs' stk' _ fenv ctx a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 =>
    exact .cons res f sp pc rs stk f' sp' rs' stk' _ fenv ctx a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
      (pos_lt_of_lt_of_le a11 hle)
  | untailcall stk res f' sp' rpc rs' stk' _ ctx a1 a2 a3 a4 a5 a6 a7 =>
    exact .untailcall stk res f' sp' rpc rs' stk' _ ctx a1 a2 a3 a4 a5 a6
      (pos_lt_of_lt_of_le a7 hle)

section INVARIANT
variable {F F1 : Val.Meminj} {m m' m1 m1' : Mem} (INCR : Val.inject_incr F F1)
include INCR

mutual
/-- `Inliningproof.match_stacks_invariant` -/
theorem match_stacks_invariant :
    ∀ {stk stk' bound}, MatchStacks prog F m m' stk stk' bound →
    (∀ b1 b2 delta, F1 b1 = some (b2, delta) → b2 < bound → F b1 = some (b2, delta)) →
    (∀ b1 b2 delta ofs, F1 b1 = some (b2, delta) → b2 < bound →
      Mem.perm m1 b1 ofs .Max .Nonempty = true → Mem.perm m b1 ofs .Max .Nonempty = true) →
    (∀ b ofs, b < bound → Mem.perm m' b ofs .Cur .Freeable = true →
      Mem.perm m1' b ofs .Cur .Freeable = true) →
    (∀ b ofs k p, b < bound → Mem.perm m1' b ofs k p = true → Mem.perm m' b ofs k p = true) →
    MatchStacks prog F1 m1 m1' stk stk' bound
  | _, _, _, .nil b1 _ hmg hb, INJ, _, _, _ =>
      .nil b1 _
        { domain := fun b h => INCR _ _ _ (hmg.domain b h)
          image := fun b1' b2 delta hf h =>
            hmg.image b1' b2 delta (INJ _ _ _ hf (pos_lt_of_lt_of_le h hb)) h
          symbols := hmg.symbols
          functions := hmg.functions
          varinfos := hmg.varinfos } hb
  | _, _, _, .cons res f sp pc rs stk f' sp' rs' stk' _ fenv ctx hms hc hfb hag hsp hpriv hs1 hs2
      hssz hres hb, INJ, PERM1, PERM2, PERM3 =>
      .cons res f sp pc rs stk f' sp' rs' stk' _ fenv ctx
        (match_stacks_inside_invariant hms rs' (fun _ _ => rfl)
          (fun b1 b2 d hf h => INJ b1 b2 d hf (Nat.lt_of_le_of_lt h hb))
          (fun b1 b2 d o hf h => PERM1 b1 b2 d o hf (Nat.lt_of_le_of_lt h hb))
          (fun b o h => PERM2 b o (Nat.lt_of_le_of_lt h hb))
          (fun b o k p h => PERM3 b o k p (Nat.lt_of_le_of_lt h hb)))
        hc hfb (agree_regs_incr hag INCR) (INCR _ _ _ hsp)
        (range_private_invariant hpriv
          (fun b d o hf hp _ _ => ⟨INJ b sp' d hf hb, PERM1 b sp' d o hf hb hp⟩)
          (fun o h => PERM2 sp' o hb h))
        hs1 hs2 (fun o h => hssz o (PERM3 sp' o _ _ hb h)) hres hb
  | _, _, _, .untailcall stk res f' sp' rpc rs' stk' _ ctx hms hpriv hs1 hs2 hssz hret hb,
      INJ, PERM1, PERM2, PERM3 =>
      .untailcall stk res f' sp' rpc rs' stk' _ ctx
        (match_stacks_inside_invariant hms rs' (fun _ _ => rfl)
          (fun b1 b2 d hf h => INJ b1 b2 d hf (Nat.lt_of_le_of_lt h hb))
          (fun b1 b2 d o hf h => PERM1 b1 b2 d o hf (Nat.lt_of_le_of_lt h hb))
          (fun b o h => PERM2 b o (Nat.lt_of_le_of_lt h hb))
          (fun b o k p h => PERM3 b o k p (Nat.lt_of_le_of_lt h hb)))
        (range_private_invariant hpriv
          (fun b d o hf hp _ _ => ⟨INJ b sp' d hf hb, PERM1 b sp' d o hf hb hp⟩)
          (fun o h => PERM2 sp' o hb h))
        hs1 hs2 (fun o h => hssz o (PERM3 sp' o _ _ hb h)) hret hb

/-- `Inliningproof.match_stacks_inside_invariant` -/
theorem match_stacks_inside_invariant :
    ∀ {stk stk' f' ctx sp' rs1}, MatchStacksInside prog F m m' stk stk' f' ctx sp' rs1 →
    ∀ (rs2 : RTL.Regset), (∀ r, r < ctx.dreg → rs2.get r = rs1.get r) →
    (∀ b1 b2 delta, F1 b1 = some (b2, delta) → b2 ≤ sp' → F b1 = some (b2, delta)) →
    (∀ b1 b2 delta ofs, F1 b1 = some (b2, delta) → b2 ≤ sp' →
      Mem.perm m1 b1 ofs .Max .Nonempty = true → Mem.perm m b1 ofs .Max .Nonempty = true) →
    (∀ b ofs, b ≤ sp' → Mem.perm m' b ofs .Cur .Freeable = true →
      Mem.perm m1' b ofs .Cur .Freeable = true) →
    (∀ b ofs k p, b ≤ sp' → Mem.perm m1' b ofs k p = true → Mem.perm m' b ofs k p = true) →
    MatchStacksInside prog F1 m1 m1' stk stk' f' ctx sp' rs2
  | _, _, _, _, _, _, .base stk stk' f' ctx sp' _ hms hret hdstk, rs2, _, INJ, PERM1, PERM2,
      PERM3 =>
      .base stk stk' f' ctx sp' rs2
        (match_stacks_invariant hms
          (fun b1 b2 d hf h => INJ b1 b2 d hf (pos_le_of_lt h))
          (fun b1 b2 d o hf h => PERM1 b1 b2 d o hf (pos_le_of_lt h))
          (fun b o h => PERM2 b o (pos_le_of_lt h))
          (fun b o k p h => PERM3 b o k p (pos_le_of_lt h)))
        hret hdstk
  | _, _, _, _, _, _, .inlined res f sp pc rs stk stk' f' fenv ctx sp' rs' ctx' hms hc hfb hag
      hsp hpad hres hret hbelow hsbelow, rs2, RS, INJ, PERM1, PERM2, PERM3 => by
      have hlt : ∀ r, r < ctx'.dreg → r < ctx.dreg := by
        intro r h; unfold ContextBelow at hbelow; pos_omega
      refine .inlined res f sp pc rs stk stk' f' fenv ctx sp' rs2 ctx'
        (match_stacks_inside_invariant hms rs2 (fun r h => RS r (hlt r h)) INJ PERM1 PERM2 PERM3)
        hc hfb ?_ (INCR _ _ _ hsp) ?_ hres hret hbelow hsbelow
      · refine agree_regs_incr (agree_regs_invariant hag (fun r h1 h2 => RS r ?_)) INCR
        unfold ContextBelow at hbelow; pos_omega
      · exact range_private_invariant hpad
          (fun b d o hf hp _ _ => ⟨INJ b sp' d hf (Nat.le_refl _),
            PERM1 b sp' d o hf (Nat.le_refl _) hp⟩)
          (fun o h => PERM2 sp' o (Nat.le_refl _) h)
end

end INVARIANT

mutual
/-- `Inliningproof.match_stacks_empty` -/
theorem match_stacks_empty {F : Val.Meminj} {m m' : Mem} :
    ∀ {stk stk' bound}, MatchStacks prog F m m' stk stk' bound → stk = [] → stk' = []
  | _, _, _, .nil _ _ _ _, _ => rfl
  | _, _, _, .cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, h => by cases h
  | _, _, _, .untailcall _ _ _ _ _ _ _ _ _ hms _ _ _ _ hret _, h => by
      have := (match_stacks_inside_empty hms h).2
      rw [hret] at this; cases this

/-- `Inliningproof.match_stacks_inside_empty` -/
theorem match_stacks_inside_empty {F : Val.Meminj} {m m' : Mem} :
    ∀ {stk stk' f ctx sp rs}, MatchStacksInside prog F m m' stk stk' f ctx sp rs → stk = [] →
      stk' = [] ∧ ctx.retinfo = none
  | _, _, _, _, _, _, .base _ _ _ _ _ _ hms hret _, h => ⟨match_stacks_empty hms h, hret⟩
  | _, _, _, _, _, _, .inlined _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, h => by cases h
end

end MATCH_STACKS

/-! ## Preservation of `match_stacks` -/

theorem validBlock_of_lt {m : Mem} {b : Block} (h : b < m.nextblock) : Mem.validBlock m b = true := by
  simp [Mem.validBlock, h]

theorem lt_of_validBlock {m : Mem} {b : Block} (h : Mem.validBlock m b = true) : b < m.nextblock := by
  simpa [Mem.validBlock] using h

theorem perm_storev {chunk : Chunk} {m : Mem} {a v : Val} {m' : Mem}
    (h : Mem.storev chunk m a v = some m') (b : Block) (ofs : Z) (k : PermKind) (p : Permission) :
    Mem.perm m' b ofs k p = Mem.perm m b ofs k p := by
  unfold Mem.storev at h
  split at h
  · split at h
    · exact Mem.perm_store_eq h _ _ _ _
    · cases h
  · cases h

theorem alloc_eq_nextblock {m : Mem} {lo hi : Z} {m1 : Mem} {b : Block}
    (h : Mem.alloc m lo hi = (m1, b)) : b = m.nextblock ∧ m1 = (Mem.alloc m lo hi).1 := by
  refine ⟨?_, by rw [h]⟩
  have := congrArg Prod.snd h; simp at this; exact this.symm

section PRESERVE
variable {prog : RTL.Program}

/-- `Inliningproof.match_stacks_inside_set_reg` -/
theorem match_stacks_inside_set_reg {F : Val.Meminj} {m m' : Mem} {stk stk' : List RTL.Stackframe}
    {f' : RTL.Function} {ctx : Context} {sp' : Block} {rs' : RTL.Regset} (r : Reg) (v : Val)
    (h : MatchStacksInside prog F m m' stk stk' f' ctx sp' rs') :
    MatchStacksInside prog F m m' stk stk' f' ctx sp' (rs'.set (sreg ctx r) v) :=
  match_stacks_inside_invariant (Val.inject_incr_refl F) h _
    (fun _ h0 => pgso (Ne.symm (sreg_below_diff h0)))
    (fun _ _ _ hf _ => hf) (fun _ _ _ _ _ _ hp => hp) (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)

/-- `Inliningproof.match_stacks_inside_set_res` -/
theorem match_stacks_inside_set_res {F : Val.Meminj} {m m' : Mem} {stk stk' : List RTL.Stackframe}
    {f' : RTL.Function} {ctx : Context} {sp' : Block} {rs' : RTL.Regset} (res : BuiltinRes Reg)
    (v : Val) (h : MatchStacksInside prog F m m' stk stk' f' ctx sp' rs') :
    MatchStacksInside prog F m m' stk stk' f' ctx sp' (regmapSetres (sbuiltinres ctx res) v rs') := by
  cases res with
  | BR x => exact match_stacks_inside_set_reg x v h
  | _ => exact h

/-- `Inliningproof.match_stacks_inside_store` -/
theorem match_stacks_inside_store {F : Val.Meminj} {m m' m1 m1' : Mem}
    {stk stk' : List RTL.Stackframe} {f' : RTL.Function} {ctx : Context} {sp' : Block}
    {rs' : RTL.Regset} {chunk chunk' : Chunk} {addr addr' v v' : Val}
    (h : MatchStacksInside prog F m m' stk stk' f' ctx sp' rs')
    (hs : Mem.storev chunk m addr v = some m1) (hs' : Mem.storev chunk' m' addr' v' = some m1') :
    MatchStacksInside prog F m1 m1' stk stk' f' ctx sp' rs' :=
  match_stacks_inside_invariant (Val.inject_incr_refl F) h _ (fun _ _ => rfl)
    (fun _ _ _ hf _ => hf)
    (fun _ _ _ _ _ _ hp => by rwa [perm_storev hs] at hp)
    (fun _ _ _ hp => by rwa [perm_storev hs'])
    (fun _ _ _ _ _ hp => by rwa [perm_storev hs'] at hp)

/-- `Inliningproof.match_stacks_inside_alloc_left` -/
theorem match_stacks_inside_alloc_left {F F1 : Val.Meminj} {m m' m1 : Mem} {sz : Z} {b : Block}
    {delta : Z} (ha : Mem.alloc m 0 sz = (m1, b)) (INCR : Val.inject_incr F F1)
    (hother : ∀ b1, b1 ≠ b → F1 b1 = F b1) :
    ∀ {stk stk' f' ctx sp' rs'}, MatchStacksInside prog F m m' stk stk' f' ctx sp' rs' →
    F1 b = some (sp', delta) → delta ≥ ctx.dstk →
    MatchStacksInside prog F1 m1 m' stk stk' f' ctx sp' rs'
  | _, _, _, _, _, _, .base stk stk' f' ctx sp' rs' hms hret hdstk, hb, _ => by
      obtain ⟨hbn, hm1⟩ := alloc_eq_nextblock ha
      refine .base stk stk' f' ctx sp' rs' (match_stacks_invariant INCR hms ?_ ?_
        (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)) hret hdstk
      · intro b1 b2 d hf hlt
        by_cases e : b1 = b
        · subst e; rw [hb] at hf; cases hf; exact absurd hlt (Nat.lt_irrefl _)
        · rw [← hother b1 e]; exact hf
      · intro b1 b2 d o hf hlt hp
        rw [hm1] at hp
        have hi := Mem.perm_alloc_inv hp
        by_cases e : b1 = b
        · subst e; rw [hb] at hf; cases hf; exact absurd hlt (Nat.lt_irrefl _)
        · rwa [if_neg (fun e' => e (e'.trans hbn.symm))] at hi
  | _, _, _, _, _, _, .inlined res f sp pc rs stk stk' f' fenv ctx sp' rs' ctx' hms hc hfb hag hsp
      hpad hres hret hbelow hsbelow, hb, hdelta => by
      obtain ⟨hbn, hm1⟩ := alloc_eq_nextblock ha
      have hsb := hsbelow
      unfold ContextStackCall at hsb
      refine .inlined res f sp pc rs stk stk' f' fenv ctx sp' rs' ctx'
        (match_stacks_inside_alloc_left ha INCR hother hms hb (by zomega))
        hc hfb (agree_regs_incr hag INCR) (INCR _ _ _ hsp) ?_ hres hret hbelow hsbelow
      refine range_private_invariant hpad ?_ (fun _ h => h)
      intro b0 d0 o hf hp h1 h2
      rw [hm1] at hp
      have hi := Mem.perm_alloc_inv hp
      by_cases e : b0 = b
      · subst e
        rw [hb] at hf; cases hf
        rw [if_pos hbn] at hi
        exfalso; zomega
      · rw [if_neg (fun e' => e (e'.trans hbn.symm))] at hi
        exact ⟨(hother b0 e) ▸ hf, hi⟩

/-- `Inliningproof.match_stacks_free_left` -/
theorem match_stacks_free_left {F : Val.Meminj} {m m' m1 : Mem} {stk stk' : List RTL.Stackframe}
    {sp b : Block} {lo hi : Z} (h : MatchStacks prog F m m' stk stk' sp)
    (hfr : Mem.free m b lo hi = some m1) : MatchStacks prog F m1 m' stk stk' sp :=
  match_stacks_invariant (Val.inject_incr_refl F) h (fun _ _ _ hf _ => hf)
    (fun _ _ _ _ _ _ hp => by rw [Mem.free_result hfr] at hp; exact Mem.perm_free_3 hp)
    (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)

/-- `Inliningproof.match_stacks_free_right` -/
theorem match_stacks_free_right {F : Val.Meminj} {m m' m1' : Mem} {stk stk' : List RTL.Stackframe}
    {sp : Block} {lo hi : Z} (h : MatchStacks prog F m m' stk stk' sp)
    (hfr : Mem.free m' sp lo hi = some m1') : MatchStacks prog F m m1' stk stk' sp :=
  match_stacks_invariant (Val.inject_incr_refl F) h (fun _ _ _ hf _ => hf)
    (fun _ _ _ _ _ _ hp => hp)
    (fun b _ hlt hp => by
      rw [Mem.free_result hfr]
      exact Mem.perm_free_1 (.inl (fun e => by subst e; exact Nat.lt_irrefl _ hlt)) hp)
    (fun _ _ _ _ _ hp => by rw [Mem.free_result hfr] at hp; exact Mem.perm_free_3 hp)

section EXTCALL
variable {F1 F2 : Val.Meminj} {m1 m2 m1' m2' : Mem}
  (MAXPERM : ∀ b ofs p, Mem.validBlock m1 b = true → Mem.perm m2 b ofs .Max p = true →
    Mem.perm m1 b ofs .Max p = true)
  (MAXPERM' : ∀ b ofs p, Mem.validBlock m1' b = true → Mem.perm m2' b ofs .Max p = true →
    Mem.perm m1' b ofs .Max p = true)
  (UNCHANGED : Mem.UnchangedOn (locOutOfReach F1 m1) m1' m2')
  (INJ : Mem.Inject F1 m1 m1')
  (INCR : Val.inject_incr F1 F2)
  (SEP : InjectSeparated F1 F2 m1 m1')
include MAXPERM MAXPERM' UNCHANGED INJ INCR SEP

mutual
/-- `Inliningproof.match_stacks_extcall` -/
theorem match_stacks_extcall :
    ∀ {stk stk' bound}, MatchStacks prog F1 m1 m1' stk stk' bound → bound ≤ m1'.nextblock →
      MatchStacks prog F2 m2 m2' stk stk' bound
  | _, _, _, .nil b1 _ hmg hb, hle =>
      .nil b1 _
        { domain := fun b h => INCR _ _ _ (hmg.domain b h)
          image := fun b1' b2 delta hf h => by
            cases e : F1 b1' with
            | some p =>
              obtain ⟨b', d'⟩ := p
              have h2 := (INCR _ _ _ e).symm.trans hf
              simp only [Option.some.injEq, Prod.mk.injEq] at h2
              obtain ⟨rfl, rfl⟩ := h2
              exact hmg.image b1' b' d' e h
            | none =>
              have := (SEP b1' b2 delta e hf).2
              rw [validBlock_of_lt (pos_lt_of_lt_of_le h (Nat.le_trans hb hle))] at this
              cases this
          symbols := hmg.symbols
          functions := hmg.functions
          varinfos := hmg.varinfos } hb
  | _, _, _, .cons res f sp pc rs stk f' sp' rs' stk' _ fenv ctx hms hc hfb hag hsp hpriv hs1 hs2
      hssz hres hb, hle =>
      have hv : Mem.validBlock m1' sp' = true := validBlock_of_lt (pos_lt_of_lt_of_le hb hle)
      .cons res f sp pc rs stk f' sp' rs' stk' _ fenv ctx
        (match_stacks_inside_extcall hms (pos_lt_of_lt_of_le hb hle))
        hc hfb (agree_regs_incr hag INCR) (INCR _ _ _ hsp)
        (range_private_extcall hpriv MAXPERM UNCHANGED INJ INCR SEP hv)
        hs1 hs2 (fun o h => hssz o (MAXPERM' sp' o _ hv h)) hres hb
  | _, _, _, .untailcall stk res f' sp' rpc rs' stk' _ ctx hms hpriv hs1 hs2 hssz hret hb, hle =>
      have hv : Mem.validBlock m1' sp' = true := validBlock_of_lt (pos_lt_of_lt_of_le hb hle)
      .untailcall stk res f' sp' rpc rs' stk' _ ctx
        (match_stacks_inside_extcall hms (pos_lt_of_lt_of_le hb hle))
        (range_private_extcall hpriv MAXPERM UNCHANGED INJ INCR SEP hv)
        hs1 hs2 (fun o h => hssz o (MAXPERM' sp' o _ hv h)) hret hb

/-- `Inliningproof.match_stacks_inside_extcall` -/
theorem match_stacks_inside_extcall :
    ∀ {stk stk' f' ctx sp' rs'}, MatchStacksInside prog F1 m1 m1' stk stk' f' ctx sp' rs' →
      sp' < m1'.nextblock → MatchStacksInside prog F2 m2 m2' stk stk' f' ctx sp' rs'
  | _, _, _, _, _, _, .base stk stk' f' ctx sp' rs' hms hret hdstk, hlt =>
      .base stk stk' f' ctx sp' rs' (match_stacks_extcall hms (pos_le_of_lt hlt)) hret hdstk
  | _, _, _, _, _, _, .inlined res f sp pc rs stk stk' f' fenv ctx sp' rs' ctx' hms hc hfb hag hsp
      hpad hres hret hbelow hsbelow, hlt =>
      .inlined res f sp pc rs stk stk' f' fenv ctx sp' rs' ctx'
        (match_stacks_inside_extcall hms hlt) hc hfb (agree_regs_incr hag INCR) (INCR _ _ _ hsp)
        (range_private_extcall hpad MAXPERM UNCHANGED INJ INCR SEP (validBlock_of_lt hlt))
        hres hret hbelow hsbelow
end

end EXTCALL

/-- `Inliningproof.align_unchanged` -/
theorem align_unchanged {n amount : Z} (hpos : 0 < amount) (hd : amount ∣ n) :
    align n amount = n := by
  obtain ⟨p, rfl⟩ := hd
  unfold align
  rw [zdiv_eq _ _ hpos]
  have e1 : amount * p + amount - 1 = (amount - 1) + amount * p := by zomega
  have e2 : (amount * p + amount - 1) / amount = p := by
    rw [e1, Int.add_mul_ediv_left _ _ (Int.ne_of_gt hpos),
      Int.ediv_eq_zero_of_lt (by zomega) (by zomega), Int.zero_add]
  rw [e2, Int.mul_comm]

/-- `Inliningproof.match_stacks_inside_inlined_tailcall` -/
theorem match_stacks_inside_inlined_tailcall {fenv : Funenv} {F : Val.Meminj} {m m' : Mem}
    {stk stk' : List RTL.Stackframe} {f' : RTL.Function} {ctx : Context} {sp' : Block}
    {rs' : RTL.Regset} {ctx' : Context} {f : RTL.Function}
    (h : MatchStacksInside prog F m m' stk stk' f' ctx sp' rs')
    (hb : ContextBelow ctx ctx') (hst : ContextStackTailcall ctx f ctx')
    (hret : ctx'.retinfo = ctx.retinfo)
    (hpriv : RangePrivate F m m' sp' ctx.dstk f'.fn_stacksize)
    (hfb : TrFunbody fenv f'.fn_stacksize ctx' f f'.fn_code) :
    MatchStacksInside prog F m m' stk stk' f' ctx' sp' rs' := by
  unfold ContextStackTailcall at hst
  cases h with
  | base stk stk' f' ctx sp' rs' hms hret0 hdstk =>
    refine .base _ _ _ _ _ _ hms (hret.trans hret0) ?_
    rw [hst, hdstk]
    exact align_unchanged (minSafeAlignment_pos _) (Int.dvd_zero _)
  | inlined res f0 sp pc rs stk stk' f' fenv0 ctx sp' rs' ctx'' hms hc hfb' hag hsp hpad hres hret0
      hbelow hsbelow =>
    have hle : ctx.dstk ≤ ctx'.dstk := by rw [hst]; exact align_le _ _ (minSafeAlignment_pos _)
    have hsz : ctx'.dstk ≤ f'.fn_stacksize := by
      cases hfb with
      | intro _ _ _ _ _ hmstk _ _ hle2 =>
        have : (0 : Z) ≤ Max.max f.fn_stacksize 0 := Int.le_max_right _ _
        zomega
    have hsb := hsbelow
    unfold ContextStackCall at hsb
    refine .inlined res f0 sp pc rs stk stk' f' fenv0 ctx' sp' rs' ctx'' hms hc hfb' hag hsp ?_
      hres (hret.trans hret0) ?_ (by unfold ContextStackCall; exact ⟨hsb.1, by zomega⟩)
    · intro ofs h1 h2
      by_cases hz : ofs < ctx.dstk
      · exact hpad ofs h1 hz
      · exact hpriv ofs (by zomega) (by zomega)
    · unfold ContextBelow at hbelow hb ⊢; pos_omega

end PRESERVE

end Inlining
end RiscV
end CC
