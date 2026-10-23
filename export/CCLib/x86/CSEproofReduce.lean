/-
  [x86-64 instance of `CCLib/backend/CSEproofReduce.lean`: the same development, in
  namespace `CC.X86`, over the x86-64 operators, registers and conventions.]

  Port of the `REDUCE` / `REDUCELD` sections and of `analysis_correct_1`,
  `analysis_correct_entry` from CompCert `backend/CSEproof.v`.

  The order `Numbering.ge` of `CSEdomain.v` (stated with `numbering_holds`) is
  defined here as `CSEproof.NumberingGe`.
-/
import CCLib.x86.CSEproof

namespace CC
namespace X86
namespace CSEproof

open ValueDomain ValueAnalysis RTL CSEdomain CSE Op

/-! ## Soundness of `reduce` -/

section REDUCE
variable {A : Type} {f : (Valnum → Option Rhs) → A → List Valnum → Option (A × List Valnum)}
  {V : Type} {ge : RTL.CGenv} {sp : Val} {rs : RTL.Regset} {m : Mem}
  {sem : A → List Val → Option V}
  (f_sound : ∀ (eqs : Valnum → Option Rhs) (valu : Valuation) op args op' args',
    (∀ v rhs, eqs v = some rhs → RhsEvalTo valu ge sp m rhs (valu v)) →
    f eqs op args = some (op', args') →
    sem op' (args'.map valu) = sem op (args.map valu))
  {n : Numbering} {valu : Valuation} (n_holds : NumberingHolds valu ge sp rs m n)
include f_sound n_holds

/-- `CSEproof.reduce_rec_sound` -/
theorem reduce_rec_sound : ∀ (niter : Nat) (op : A) (args : List Valnum) (op' : A)
    (rl' : List Reg) (res : V),
    reduceRec f n niter op args = some (op', rl') →
    sem op (args.map valu) = some res →
    sem op' (rs.getList rl') = some res
  | 0, _, _, _, _, _, h, _ => by cases h
  | niter + 1, op, args, op', rl', res, h, hs => by
    simp only [reduceRec] at h
    cases e : f (fun v => findValnumNum v n.num_eqs) op args with
    | none => rw [e] at h; cases h
    | some p =>
      obtain ⟨op1, args1⟩ := p
      rw [e] at h
      dsimp only at h
      have S1 : sem op1 (args1.map valu) = some res := by
        rw [← hs]
        refine f_sound _ valu _ _ _ _ (fun v rhs hv => ?_) e
        have EH := n_holds.num_holds_eq _ (find_valnum_num_charact v rhs _ hv)
        cases EH with
        | eq_holds_strict _ _ h1 _ => exact h1
      cases e2 : reduceRec f n niter op1 args1 with
      | some q =>
        rw [e2] at h; cases h
        exact reduce_rec_sound niter op1 args1 op' rl' res e2 S1
      | none =>
        rw [e2] at h
        dsimp only at h
        cases e3 : regsValnums n args1 with
        | none => rw [e3] at h; cases h
        | some rl =>
          rw [e3] at h; cases h
          rw [regs_valnums_sound n_holds e3]; exact S1

/-- `CSEproof.reduce_sound` -/
theorem reduce_sound {op : A} {rl : List Reg} {vl : List Valnum} {op' : A} {rl' : List Reg}
    {res : V} (h : reduce f n op rl vl = (op', rl'))
    (hv : vl.map valu = rs.getList rl) (hs : sem op (rs.getList rl) = some res) :
    sem op' (rs.getList rl') = some res := by
  unfold reduce at h
  cases e : reduceRec f n 4 op vl with
  | none => rw [e] at h; cases h; exact hs
  | some p =>
    rw [e] at h; cases h
    exact reduce_rec_sound f_sound n_holds 4 op vl op' rl' res e (by rw [hv]; exact hs)

end REDUCE

section REDUCELD
variable {A : Type} {f : (Valnum → Option Rhs) → A → List Valnum → Option (A × List Valnum)}
  {ge : RTL.CGenv} {sp : Val} {rs : RTL.Regset} {m : Mem}
  {sem : A → List Val → Option Val}
  (f_sound : ∀ (eqs : Valnum → Option Rhs) (valu : Valuation) op args op' args' r,
    (∀ v rhs, eqs v = some rhs → RhsEvalTo valu ge sp m rhs (valu v)) →
    f eqs op args = some (op', args') →
    sem op (args.map valu) = some r →
    ∃ r', sem op' (args'.map valu) = some r' ∧ Val.Lessdef r r')
  {n : Numbering} {valu : Valuation} (n_holds : NumberingHolds valu ge sp rs m n)
include f_sound n_holds

/-- `CSEproof.reduce_rec_lessdef_sound` -/
theorem reduce_rec_lessdef_sound : ∀ (niter : Nat) (op : A) (args : List Valnum) (op' : A)
    (rl' : List Reg) (r : Val),
    reduceRec f n niter op args = some (op', rl') →
    sem op (args.map valu) = some r →
    ∃ r', sem op' (rs.getList rl') = some r' ∧ Val.Lessdef r r'
  | 0, _, _, _, _, _, h, _ => by cases h
  | niter + 1, op, args, op', rl', r, h, hs => by
    simp only [reduceRec] at h
    cases e : f (fun v => findValnumNum v n.num_eqs) op args with
    | none => rw [e] at h; cases h
    | some p =>
      obtain ⟨op1, args1⟩ := p
      rw [e] at h
      dsimp only at h
      obtain ⟨r1, S1, L1⟩ : ∃ r1, sem op1 (args1.map valu) = some r1 ∧ Val.Lessdef r r1 := by
        refine f_sound _ valu _ _ _ _ _ (fun v rhs hv => ?_) e hs
        have EH := n_holds.num_holds_eq _ (find_valnum_num_charact v rhs _ hv)
        cases EH with
        | eq_holds_strict _ _ h1 _ => exact h1
      cases e2 : reduceRec f n niter op1 args1 with
      | some q =>
        rw [e2] at h; cases h
        obtain ⟨r2, S2, L2⟩ := reduce_rec_lessdef_sound niter op1 args1 op' rl' r1 e2 S1
        exact ⟨r2, S2, Val.lessdef_trans L1 L2⟩
      | none =>
        rw [e2] at h
        dsimp only at h
        cases e3 : regsValnums n args1 with
        | none => rw [e3] at h; cases h
        | some rl =>
          rw [e3] at h; cases h
          rw [regs_valnums_sound n_holds e3]; exact ⟨r1, S1, L1⟩

/-- `CSEproof.reduce_lessdef_sound` -/
theorem reduce_lessdef_sound {op : A} {rl : List Reg} {vl : List Valnum} {op' : A}
    {rl' : List Reg} {r : Val} (h : reduce f n op rl vl = (op', rl'))
    (hv : vl.map valu = rs.getList rl) (hs : sem op (rs.getList rl) = some r) :
    ∃ r', sem op' (rs.getList rl') = some r' ∧ Val.Lessdef r r' := by
  unfold reduce at h
  cases e : reduceRec f n 4 op vl with
  | none => rw [e] at h; cases h; exact ⟨r, hs, Val.lessdef_refl r⟩
  | some p =>
    rw [e] at h; cases h
    exact reduce_rec_lessdef_sound f_sound n_holds 4 op vl op' rl' r e (by rw [hv]; exact hs)

end REDUCELD

/-! ## Correctness of the static analysis -/

/-- `CSEdomain.Numbering.ge`: `n1` is less informative than `n2`. -/
def NumberingGe (n1 n2 : Numbering) : Prop :=
  ∀ valu ge sp rs m, NumberingHolds valu ge sp rs m n2 → NumberingHolds valu ge sp rs m n1

theorem numberingGe_top (n : Numbering) : NumberingGe numberingTop n :=
  fun valu ge sp rs m _ => empty_numbering_holds valu ge sp rs m

theorem numberingGe_refl (n : Numbering) : NumberingGe n n := fun _ _ _ _ _ h => h

/-- `CSEproof.analysis_correct_1` -/
theorem analysis_correct_1 (o : ValueAOp.Options) {ge : RTL.CGenv} {sp : Val} {rs : RTL.Regset}
    {m : Mem} {f : RTL.Function} {dm : Defmap} {vapprox : PMap VAState}
    {approx : PMap Numbering} {pc pc' : Node} {i : Instruction}
    (h : CSE.analyze o f dm vapprox = some approx) (hc : f.fn_code.get pc = some i)
    (hs : pc' ∈ successorsInstr i)
    (hn : ∃ valu, NumberingHolds valu ge sp rs m (CSE.transfer o f dm vapprox pc (approx.get pc))) :
    ∃ valu, NumberingHolds valu ge sp rs m (approx.get pc') := by
  have GE := Kildall.BBlock.fixpoint_solution numberingTop f.fn_code successorsInstr
    (CSE.transfer o f dm vapprox) f.fn_entrypoint NumberingGe numberingGe_top numberingGe_refl
    h hc hs
  obtain ⟨valu, NH⟩ := hn
  exact ⟨valu, GE _ _ _ _ _ NH⟩

/-- `CSEproof.analysis_correct_entry` -/
theorem analysis_correct_entry (o : ValueAOp.Options) {ge : RTL.CGenv} {sp : Val}
    {rs : RTL.Regset} {m : Mem} {f : RTL.Function} {dm : Defmap} {vapprox : PMap VAState}
    {approx : PMap Numbering} (h : CSE.analyze o f dm vapprox = some approx) :
    ∃ valu, NumberingHolds valu ge sp rs m (approx.get f.fn_entrypoint) := by
  rw [Kildall.BBlock.fixpoint_entry numberingTop f.fn_code successorsInstr
    (CSE.transfer o f dm vapprox) f.fn_entrypoint NumberingGe numberingGe_top numberingGe_refl h]
  exact ⟨fun _ => .Vundef, empty_numbering_holds _ _ _ _ _⟩

end CSEproof
end X86
end CC
