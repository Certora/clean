/-
  [x86-64 instance of `CCLib/backend/InliningproofBasic.lean`: the same development, in
  namespace `CC.X86`, over the x86-64 operators, registers and conventions.]

  RTL function inlining: semantic preservation — port of
  `backend/Inliningproof.v`, part 1: properties of contexts, agreement
  between register sets (`agree_regs`), execution of the moves of an inlined
  call (`tr_moves_init_regs`) and private stack locations (`loc_private`,
  `range_private`).
-/
import CCLib.x86.Inliningspec
import CCLib.x86.OpInject
import CCLib.common.EventsInject
import CCLib.common.EventsMem

namespace CC
namespace X86
namespace Inlining

open Op RTL Smallstep

/-! ## Properties of contexts and relocations -/

/-- `Inliningproof.sreg_below_diff` -/
theorem sreg_below_diff {ctx : Context} {r r' : Reg} (h : r' < ctx.dreg) : sreg ctx r ≠ r' := by
  intro e
  rw [← e] at h
  exact shiftpos_not_below r ctx.dreg h

/-- `Inliningproof.context_below_diff` -/
theorem context_below_diff {ctx1 ctx2 : Context} {r1 r2 : Reg} (hb : ContextBelow ctx1 ctx2)
    (hr : r1 ≤ ctx1.mreg) : sreg ctx1 r1 ≠ sreg ctx2 r2 := by
  intro e
  have e' := congrArg Positive.toNat e
  have := Positive.toNat_pos r2
  have := Positive.toNat_pos ctx1.dreg
  unfold ContextBelow at hb
  unfold sreg at e'
  pos_omega

/-- `Inliningproof.context_below_lt` -/
theorem context_below_lt {ctx1 ctx2 : Context} {r : Reg} (hb : ContextBelow ctx1 ctx2)
    (hr : r ≤ ctx1.mreg) : sreg ctx1 r < ctx2.dreg := by
  have := Positive.toNat_pos ctx1.dreg
  unfold ContextBelow at hb
  unfold sreg
  pos_omega

/-! ## Agreement between register sets before and after inlining -/

/-- `Inliningproof.agree_regs` -/
def AgreeRegs (F : Val.Meminj) (ctx : Context) (rs rs' : Regset) : Prop :=
  (∀ r, r ≤ ctx.mreg → Val.Inject F (rs.get r) (rs'.get (sreg ctx r))) ∧
  (∀ r, ctx.mreg < r → rs.get r = .Vundef)

/-- `Inliningproof.val_reg_charact` -/
def ValRegCharact (F : Val.Meminj) (ctx : Context) (rs' : Regset) (v : Val) (r : Reg) : Prop :=
  (ctx.mreg < r ∧ v = .Vundef) ∨ (r ≤ ctx.mreg ∧ Val.Inject F v (rs'.get (sreg ctx r)))

/-- `sreg` is injective. -/
theorem sreg_ne {ctx : Context} {r0 r : Reg} (h : r0 ≠ r) : sreg ctx r0 ≠ sreg ctx r :=
  shiftpos_diff _ h

theorem pgso {A : Type} {i j : Positive} {v : A} {m : PMap A} (h : j ≠ i) :
    (m.set i v).get j = m.get j :=
  PMap.gso i j v m (Ne.symm h)

theorem pos_lt_or_le (p q : Positive) : p < q ∨ q ≤ p := by
  show p.toNat < q.toNat ∨ q.toNat ≤ p.toNat
  omega

/-- `Inliningproof.agree_val_reg_gen` -/
theorem agree_val_reg_gen {F : Val.Meminj} {ctx : Context} {rs rs' : Regset} (r : Reg)
    (h : AgreeRegs F ctx rs rs') : ValRegCharact F ctx rs' (rs.get r) r := by
  rcases pos_lt_or_le ctx.mreg r with hl | hl
  · exact .inl ⟨hl, h.2 r hl⟩
  · exact .inr ⟨hl, h.1 r hl⟩

/-- `Inliningproof.agree_val_regs_gen` -/
theorem agree_val_regs_gen {F : Val.Meminj} {ctx : Context} {rs rs' : Regset}
    (h : AgreeRegs F ctx rs rs') :
    ∀ rl : List Reg, ListForall2 (ValRegCharact F ctx rs') (rs.getList rl) rl
  | [] => .nil
  | r :: rl => .cons (agree_val_reg_gen r h) (agree_val_regs_gen h rl)

/-- `Inliningproof.agree_val_reg` -/
theorem agree_val_reg {F : Val.Meminj} {ctx : Context} {rs rs' : Regset} (r : Reg)
    (h : AgreeRegs F ctx rs rs') : Val.Inject F (rs.get r) (rs'.get (sreg ctx r)) := by
  rcases agree_val_reg_gen r h with ⟨_, e⟩ | ⟨_, hi⟩
  · rw [e]; exact .undef _
  · exact hi

/-- `Inliningproof.agree_val_regs` -/
theorem agree_val_regs {F : Val.Meminj} {ctx : Context} {rs rs' : Regset}
    (h : AgreeRegs F ctx rs rs') :
    ∀ rl : List Reg, Val.InjectList F (rs.getList rl) (rs'.getList (sregs ctx rl))
  | [] => .nil
  | r :: rl => .cons (agree_val_reg r h) (agree_val_regs h rl)

/-- `Inliningproof.agree_set_reg` -/
theorem agree_set_reg {F : Val.Meminj} {ctx : Context} {rs rs' : Regset} {r : Reg} {v v' : Val}
    (h : AgreeRegs F ctx rs rs') (hv : Val.Inject F v v') (hr : r ≤ ctx.mreg) :
    AgreeRegs F ctx (rs.set r v) (rs'.set (sreg ctx r) v') := by
  refine ⟨fun r0 h0 => ?_, fun r0 h0 => ?_⟩
  · by_cases e : r0 = r
    · subst e; rw [PMap.gss, PMap.gss]; exact hv
    · rw [pgso e, pgso (sreg_ne e)]; exact h.1 r0 h0
  · rw [pgso (by intro e; subst e; pos_omega)]; exact h.2 r0 h0

/-- `Inliningproof.agree_set_reg_undef` -/
theorem agree_set_reg_undef {F : Val.Meminj} {ctx : Context} {rs rs' : Regset} {r : Reg}
    (v' : Val) (h : AgreeRegs F ctx rs rs') :
    AgreeRegs F ctx (rs.set r .Vundef) (rs'.set (sreg ctx r) v') := by
  refine ⟨fun r0 h0 => ?_, fun r0 h0 => ?_⟩
  · by_cases e : r0 = r
    · subst e; rw [PMap.gss]; exact .undef _
    · rw [pgso e, pgso (sreg_ne e)]; exact h.1 r0 h0
  · by_cases e : r0 = r
    · subst e; rw [PMap.gss]
    · rw [pgso e]; exact h.2 r0 h0

/-- `Inliningproof.agree_set_reg_undef'` -/
theorem agree_set_reg_undef' {F : Val.Meminj} {ctx : Context} {rs rs' : Regset} {r : Reg}
    (h : AgreeRegs F ctx rs rs') : AgreeRegs F ctx (rs.set r .Vundef) rs' := by
  refine ⟨fun r0 h0 => ?_, fun r0 h0 => ?_⟩
  · by_cases e : r0 = r
    · subst e; rw [PMap.gss]; exact .undef _
    · rw [pgso e]; exact h.1 r0 h0
  · by_cases e : r0 = r
    · subst e; rw [PMap.gss]
    · rw [pgso e]; exact h.2 r0 h0

/-- `Inliningproof.agree_regs_invariant` -/
theorem agree_regs_invariant {F : Val.Meminj} {ctx : Context} {rs rs1 rs2 : Regset}
    (h : AgreeRegs F ctx rs rs1)
    (hinv : ∀ r, ctx.dreg ≤ r → r < Positive.add ctx.dreg ctx.mreg → rs2.get r = rs1.get r) :
    AgreeRegs F ctx rs rs2 := by
  refine ⟨fun r hr => ?_, h.2⟩
  have e : rs2.get (sreg ctx r) = rs1.get (sreg ctx r) :=
    hinv _ (shiftpos_above _ _) (by unfold sreg; have := Positive.toNat_pos ctx.dreg; pos_omega)
  rw [e]
  exact h.1 r hr

/-- `Inliningproof.agree_regs_incr` -/
theorem agree_regs_incr {F F' : Val.Meminj} {ctx : Context} {rs1 rs2 : Regset}
    (h : AgreeRegs F ctx rs1 rs2) (hi : Val.inject_incr F F') : AgreeRegs F' ctx rs1 rs2 :=
  ⟨fun r hr => Val.inject_incr_inject hi (h.1 r hr), h.2⟩

/-- `Inliningproof.agree_regs_init` -/
theorem agree_regs_init (F : Val.Meminj) (ctx : Context) (rs : Regset) :
    AgreeRegs F ctx (PMap.init .Vundef) rs :=
  ⟨fun r _ => by rw [PMap.gi]; exact .undef _, fun r _ => by rw [PMap.gi]⟩

theorem initRegs_nil_right (vl : List Val) : initRegs vl [] = PMap.init .Vundef := by
  cases vl <;> rfl

/-- `Inliningproof.agree_regs_init_regs` -/
theorem agree_regs_init_regs {F : Val.Meminj} {ctx : Context} :
    ∀ (rl : List Reg) (vl vl' : List Val), Val.InjectList F vl vl' →
      (∀ r, r ∈ rl → r ≤ ctx.mreg) →
      AgreeRegs F ctx (initRegs vl rl) (initRegs vl' (sregs ctx rl))
  | [], vl, vl', _, _ => by rw [initRegs_nil_right]; exact agree_regs_init _ _ _
  | r :: rl, _, _, .nil, _ => agree_regs_init _ _ _
  | r :: rl, _ :: _, _ :: _, .cons hv hl, hr =>
      agree_set_reg (agree_regs_init_regs rl _ _ hl (fun r' h => hr r' (List.mem_cons_of_mem _ h)))
        hv (hr r List.mem_cons_self)

/-! ## Executing sequences of moves -/

/-- `Inliningproof.tr_moves_init_regs` -/
theorem tr_moves_init_regs (tge : RTL.CGenv) {F : Val.Meminj} {stk : List RTL.Stackframe}
    {f : RTL.Function} {sp : Val} {m : Mem} {ctx1 ctx2 : Context} (hb : ContextBelow ctx1 ctx2) :
    ∀ (rdsts rsrcs : List Reg) (vl : List Val) (pc1 pc2 : Node) (rs1 : Regset),
    TrMoves f.fn_code pc1 (sregs ctx1 rsrcs) (sregs ctx2 rdsts) pc2 →
    (∀ r, r ∈ rdsts → r ≤ ctx2.mreg) →
    ListForall2 (ValRegCharact F ctx1 rs1) vl rsrcs →
    ∃ rs2 : RTL.Regset, Smallstep.Star (RTL.Step tge) (RTL.State.State stk f sp pc1 rs1 m) E0
        (RTL.State.State stk f sp pc2 rs2 m) ∧
      AgreeRegs F ctx2 (initRegs vl rdsts) rs2 ∧ ∀ r, r < ctx2.dreg → rs2.get r = rs1.get r
  | [], rsrcs, vl, pc1, pc2, rs1, htr, _, _ => by
      generalize sregs ctx1 rsrcs = S at htr
      cases htr with
      | nil =>
        refine ⟨rs1, .refl _, ?_, fun _ _ => rfl⟩
        rw [initRegs_nil_right]; exact agree_regs_init _ _ _
  | a :: rdsts, _, _, pc1, pc2, rs1, htr, hd, .nil => by
      cases htr with
      | nil => exact ⟨rs1, .refl _, agree_regs_init _ _ _, fun _ _ => rfl⟩
  | a :: rdsts, b1 :: rsrcs, a1 :: vl, pc1, pc2, rs1, htr, hd, .cons hc hl => by
      have e1 : sregs ctx1 (b1 :: rsrcs) = sreg ctx1 b1 :: sregs ctx1 rsrcs := rfl
      have e2 : sregs ctx2 (a :: rdsts) = sreg ctx2 a :: sregs ctx2 rdsts := rfl
      rw [e1, e2] at htr
      generalize hS1 : sregs ctx1 rsrcs = S1 at htr
      generalize hS2 : sregs ctx2 rdsts = S2 at htr
      cases htr with
      | nil _ _ _ h => rcases h with h | h <;> cases h
      | cons _ _ _ _ _ pc2' _ htr' hcode =>
        obtain ⟨rs2, A, B, C⟩ := tr_moves_init_regs tge hb rdsts rsrcs vl pc1 pc2' rs1 (hS1 ▸ hS2 ▸ htr')
          (fun r h => hd r (List.mem_cons_of_mem _ h)) hl
        refine ⟨rs2.set (sreg ctx2 a) (rs2.get (sreg ctx1 b1)), star_right A
          (RTL.Step.Iop _ _ _ _ _ _ _ _ _ _ _ hcode rfl) rfl, ?_, ?_⟩
        · show AgreeRegs F ctx2 ((initRegs vl rdsts).set a a1) _
          rcases hc with ⟨_, e⟩ | ⟨hle, hi⟩
          · rw [e]; exact agree_set_reg_undef _ B
          · refine agree_set_reg B ?_ (hd a List.mem_cons_self)
            rw [C _ (context_below_lt hb hle)]; exact hi
        · intro r hr
          rw [pgso (Ne.symm (sreg_below_diff hr))]
          exact C r hr

/-! ## Memory invariants -/

/-- `Inliningproof.loc_private`: a stack location is private if it is not
    the image of a valid location and we have full rights on it. -/
def LocPrivate (F : Val.Meminj) (m m' : Mem) (sp : Block) (ofs : Z) : Prop :=
  Mem.perm m' sp ofs .Cur .Freeable = true ∧
  ∀ b delta, F b = some (sp, delta) → ¬ Mem.perm m b (ofs - delta) .Max .Nonempty = true

/-- `Inliningproof.range_private` -/
def RangePrivate (F : Val.Meminj) (m m' : Mem) (sp : Block) (lo hi : Z) : Prop :=
  ∀ ofs, lo ≤ ofs → ofs < hi → LocPrivate F m m' sp ofs

/-- `Inliningproof.range_private_invariant` -/
theorem range_private_invariant {F F1 : Val.Meminj} {m m' m1 m1' : Mem} {sp : Block} {lo hi : Z}
    (h : RangePrivate F m m' sp lo hi)
    (hinj : ∀ b delta ofs, F1 b = some (sp, delta) → Mem.perm m1 b ofs .Max .Nonempty = true →
      lo ≤ ofs + delta → ofs + delta < hi →
      F b = some (sp, delta) ∧ Mem.perm m b ofs .Max .Nonempty = true)
    (hperm : ∀ ofs, Mem.perm m' sp ofs .Cur .Freeable = true →
      Mem.perm m1' sp ofs .Cur .Freeable = true) :
    RangePrivate F1 m1 m1' sp lo hi := by
  intro ofs h1 h2
  obtain ⟨A, B⟩ := h ofs h1 h2
  refine ⟨hperm _ A, fun b delta hf hp => ?_⟩
  obtain ⟨P, Q⟩ := hinj b delta (ofs - delta) hf hp (by zomega) (by zomega)
  exact B b delta P Q

/-- `Inliningproof.range_private_perms` -/
theorem range_private_perms {F : Val.Meminj} {m m' : Mem} {sp : Block} {lo hi : Z}
    (h : RangePrivate F m m' sp lo hi) :
    ∀ ofs, lo ≤ ofs → ofs < hi → Mem.perm m' sp ofs .Cur .Freeable = true :=
  fun ofs h1 h2 => (h ofs h1 h2).1

/-- `Inliningproof.range_private_alloc_left` -/
theorem range_private_alloc_left {F F1 : Val.Meminj} {m m' m1 : Mem} {sp' sp : Block}
    {base hi sz : Z} (h : RangePrivate F m m' sp' base hi)
    (ha : Mem.alloc m 0 sz = (m1, sp)) (hf : F1 sp = some (sp', base))
    (hother : ∀ b, b ≠ sp → F1 b = F b) :
    RangePrivate F1 m1 m' sp' (base + Max.max sz 0) hi := by
  intro ofs h1 h2
  have hmax : 0 ≤ Max.max sz 0 := Int.le_max_right _ _
  obtain ⟨A, B⟩ := h ofs (by zomega) h2
  refine ⟨A, fun b delta hfb hp => ?_⟩
  have hsp : sp = m.nextblock := by
    have := congrArg Prod.snd ha; simp at this; exact this.symm
  have hm1 : m1 = (Mem.alloc m 0 sz).1 := by rw [ha]
  rw [hm1] at hp
  have hi := Mem.perm_alloc_inv hp
  by_cases e : b = sp
  · subst e
    rw [if_pos hsp] at hi
    rw [hf] at hfb; cases hfb
    have : sz ≤ Max.max sz 0 := Int.le_max_left _ _
    zomega
  · rw [if_neg (fun e' => e (e'.trans hsp.symm))] at hi
    rw [hother b e] at hfb
    exact B b delta hfb hi

/-- `Inliningproof.range_private_free_left` -/
theorem range_private_free_left {F : Val.Meminj} {m m' m1 : Mem} {sp b : Block} {base sz hi : Z}
    (h : RangePrivate F m m' sp (base + Max.max sz 0) hi)
    (hfr : Mem.free m b 0 sz = some m1) (hf : F b = some (sp, base)) (hm : Mem.Inject F m m') :
    RangePrivate F m1 m' sp base hi := by
  intro ofs h1 h2
  have hmax : 0 ≤ Max.max sz 0 := Int.le_max_right _ _
  have hrp := Mem.free_range_perm hfr
  have hm1 := Mem.free_result hfr
  by_cases hz : ofs < base + Max.max sz 0
  · have hsz : ofs - base < sz := by
      have : Max.max sz 0 = sz ∨ Max.max sz 0 = 0 := by
        rcases Int.le_total sz 0 with hh | hh
        · exact .inr (Int.max_eq_right hh)
        · exact .inl (Int.max_eq_left hh)
      rcases this with e | e <;> zomega
    have hsz0 : 0 < sz := by
      rcases Int.le_total sz 0 with hh | hh
      · rw [Int.max_eq_right hh] at hz; zomega
      · zomega
    refine ⟨?_, fun b0 delta hf0 hp => ?_⟩
    · have := Mem.perm_inject hf hm
        (Mem.rangePerm_perm _ _ _ _ _ _ hrp (ofs - base) (by zomega) hsz)
      rwa [show ofs - base + base = ofs by zomega] at this
    · rw [hm1] at hp
      by_cases e : b0 = b
      · subst e
        rw [hf] at hf0; cases hf0
        rw [Mem.perm_free_inside _ _ _ _ _ _ _ (by zomega) hsz] at hp; cases hp
      · have hp' := Mem.perm_free_3 hp
        have hb := Mem.perm_cur_max (Mem.perm_implies
          (Mem.rangePerm_perm _ _ _ _ _ _ hrp (ofs - base) (by zomega) hsz) (q := .Nonempty) (by decide))
        rcases hm.no_overlap b0 sp delta b sp base (ofs - delta) (ofs - base) e hf0 hf hp' hb
          with h' | h'
        · exact h' rfl
        · zomega
  · obtain ⟨A, B⟩ := h ofs (by zomega) h2
    refine ⟨A, fun b0 delta hf0 hp => B b0 delta hf0 ?_⟩
    rw [hm1] at hp
    exact Mem.perm_free_3 hp

/-- `Inliningproof.range_private_extcall` -/
theorem range_private_extcall {F F' : Val.Meminj} {m1 m2 m1' m2' : Mem} {sp : Block} {base hi : Z}
    (h : RangePrivate F m1 m1' sp base hi)
    (hperm : ∀ b ofs p, Mem.validBlock m1 b = true → Mem.perm m2 b ofs .Max p = true →
      Mem.perm m1 b ofs .Max p = true)
    (hunch : Mem.UnchangedOn (locOutOfReach F m1) m1' m2')
    (hm : Mem.Inject F m1 m1') (hincr : Val.inject_incr F F')
    (hsep : InjectSeparated F F' m1 m1') (hvb : Mem.validBlock m1' sp = true) :
    RangePrivate F' m2 m2' sp base hi := by
  intro ofs h1 h2
  obtain ⟨A, B⟩ := h ofs h1 h2
  refine ⟨hunch.perm_1 (fun b0 delta hf0 hp => B b0 delta hf0 hp) A, fun b delta hf hp => ?_⟩
  cases e : F b with
  | some p =>
    obtain ⟨sp1, delta1⟩ := p
    have := hincr _ _ _ e
    rw [hf] at this; cases this
    refine B b delta e (hperm _ _ _ ?_ hp)
    cases hv : Mem.validBlock m1 b
    · rw [hm.freeblocks b hv] at e; cases e
    · rfl
  | none =>
    have := (hsep b sp delta e hf).2
    rw [hvb] at this; cases this

end Inlining
end X86
end CC
