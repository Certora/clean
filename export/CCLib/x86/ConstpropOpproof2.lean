/-
  Correctness of strength reduction for the x86 back end — port of
  `x86/ConstpropOpproof.v`, part 2: `addr_strength_reduction_32_generic_correct`,
  `addr_strength_reduction_32_correct`, `addr_strength_reduction_64_generic_correct`,
  `addr_strength_reduction_64_correct`, `addr_strength_reduction_correct` and
  `op_strength_reduction_correct`.

  `Archi.ptr64` is `true` in this port, so `addr_strength_reduction_32` is
  its generic part (the 32-bit pointer cases are dead code, as in Rocq on a
  64-bit target).
-/
import CCLib.x86.ConstpropOpproof
import CCLib.aarch64.ConstpropOpproof2

namespace CC
namespace X86
namespace ConstpropOpproof

open ValueDomain Op ConstpropOp
open CC.ConstpropOp (Options)
open CC.ConstpropOpproof (get_I get_L get_F get_FS vmatch_of_eq
  addl_symbol_lessdef addl_stk_lessdef_l addl_stk_lessdef_r)
open Integers (Ptrofs)

/-! ### Integer identities used by the generic reductions -/

private theorem int_signed_add (x : Integers.Int) (y : Z) :
    Integers.Int.repr (Integers.Int.signed x + y) = Integers.Int.add x (Integers.Int.repr y) := by
  rw [Integers.Int.repr_add, Integers.Int.repr_signed]

private theorem int_signed_mul_add (x : Integers.Int) (y z : Z) :
    Integers.Int.repr (Integers.Int.signed x * y + z) =
      Integers.Int.add (Integers.Int.mul x (Integers.Int.repr y)) (Integers.Int.repr z) := by
  rw [Integers.Int.repr_add, Integers.Int.repr_mul, Integers.Int.repr_signed]

private theorem int64_signed_add (x : Integers.Int64) (y : Z) :
    Integers.Int64.repr (Integers.Int64.signed x + y) =
      Integers.Int64.add x (Integers.Int64.repr y) := by
  rw [Integers.Int64.repr_add, Integers.Int64.repr_signed]

private theorem int64_signed_mul_add (x : Integers.Int64) (y z : Z) :
    Integers.Int64.repr (Integers.Int64.signed x * y + z) =
      Integers.Int64.add (Integers.Int64.mul x (Integers.Int64.repr y)) (Integers.Int64.repr z) := by
  rw [Integers.Int64.repr_add, Integers.Int64.repr_mul, Integers.Int64.repr_signed]

private theorem ptrofs_repr_of_int64 (n : Z) :
    Ptrofs.repr n = Ptrofs.of_int64 (Integers.Int64.repr n) :=
  (Integers.MI.repr_unsigned (w := 64) _).symm

section STRENGTH_REDUCTION
variable {F V : Type} {ge : Genv F V} {bc : BlockClassification} {sp : Block} {ae : Aenv}
  {e : RTL.Regset} {m : Mem}

set_option hygiene false in
/-- Decompose the argument equation `hvl` and read the integer constants. -/
local macro "prep" MATCH:term "," hvl:ident "," hev:ident : tactic => `(tactic| (
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at $hvl:ident
  simp only [Regmap.getList, List.map_cons, List.map_nil] at $hev:ident ⊢
  first | obtain ⟨h1, h2⟩ := $hvl:ident | have h1 := $hvl:ident
  try (rw [get_I $MATCH h1.symm] at $hev:ident)
  try (rw [get_I $MATCH h2.symm] at $hev:ident)
  try (rw [get_L $MATCH h1.symm] at $hev:ident)
  try (rw [get_L $MATCH h2.symm] at $hev:ident)))

/-- `ConstpropOpproof.addr_strength_reduction_32_generic_correct` -/
theorem addr_strength_reduction_32_generic_correct (MATCH : Ematch bc e ae)
    (addr : Addressing) (args : List Reg) (vl : List Aval) (res : Val)
    (hvl : vl = args.map (fun r => AE.get r ae))
    (hev : evalAddressing32 ge (.Vptr sp Ptrofs.zero) addr (e.getList args) = some res) :
    ∃ res', evalAddressing32 ge (.Vptr sp Ptrofs.zero) (addrStrengthReduction32Generic addr args vl).1
        (e.getList (addrStrengthReduction32Generic addr args vl).2) = some res' ∧
      Val.Lessdef res res' := by
  unfold addrStrengthReduction32Generic
  split
  case h_5 => exact ⟨res, hev, .refl _⟩
  all_goals prep MATCH, hvl, hev
  all_goals simp only [evalAddressing32, Option.some.injEq] at hev
  all_goals subst hev
  all_goals refine ⟨_, rfl, ?_⟩
  · rw [int_signed_add, Val.add_assoc, Val.add_permut]; exact .refl _
  · rw [int_signed_add, Val.add_assoc]; exact .refl _
  · rw [int_signed_mul_add]; exact .refl _
  · rw [int_signed_add, Val.add_permut]; exact .refl _

/-- `ConstpropOpproof.addr_strength_reduction_32_correct` -/
theorem addr_strength_reduction_32_correct (MATCH : Ematch bc e ae)
    (addr : Addressing) (args : List Reg) (vl : List Aval) (res : Val)
    (hvl : vl = args.map (fun r => AE.get r ae))
    (hev : evalAddressing32 ge (.Vptr sp Ptrofs.zero) addr (e.getList args) = some res) :
    ∃ res', evalAddressing32 ge (.Vptr sp Ptrofs.zero) (addrStrengthReduction32 addr args vl).1
        (e.getList (addrStrengthReduction32 addr args vl).2) = some res' ∧
      Val.Lessdef res res' := by
  simp only [addrStrengthReduction32, Archi.ptr64, if_true]
  exact addr_strength_reduction_32_generic_correct MATCH addr args vl res hvl hev

/-- `ConstpropOpproof.addr_strength_reduction_64_generic_correct` -/
theorem addr_strength_reduction_64_generic_correct (MATCH : Ematch bc e ae)
    (addr : Addressing) (args : List Reg) (vl : List Aval) (res : Val)
    (hvl : vl = args.map (fun r => AE.get r ae))
    (hev : evalAddressing64 ge (.Vptr sp Ptrofs.zero) addr (e.getList args) = some res) :
    ∃ res', evalAddressing64 ge (.Vptr sp Ptrofs.zero) (addrStrengthReduction64Generic addr args vl).1
        (e.getList (addrStrengthReduction64Generic addr args vl).2) = some res' ∧
      Val.Lessdef res res' := by
  unfold addrStrengthReduction64Generic
  split
  case h_5 => exact ⟨res, hev, .refl _⟩
  all_goals prep MATCH, hvl, hev
  all_goals simp only [evalAddressing64, Option.some.injEq] at hev
  all_goals subst hev
  all_goals refine ⟨_, rfl, ?_⟩
  · rw [int64_signed_add, Val.addl_assoc, Val.addl_permut]; exact .refl _
  · rw [int64_signed_add, Val.addl_assoc]; exact .refl _
  · rw [int64_signed_mul_add]; exact .refl _
  · rw [int64_signed_add, Val.addl_permut]; exact .refl _

/-- `ConstpropOpproof.addr_strength_reduction_64_correct` -/
theorem addr_strength_reduction_64_correct (GENV : GenvMatch bc ge) (STACK : bc sp = .BCstack)
    (MATCH : Ematch bc e ae)
    (addr : Addressing) (args : List Reg) (vl : List Aval) (res : Val)
    (hvl : vl = args.map (fun r => AE.get r ae))
    (hev : evalAddressing64 ge (.Vptr sp Ptrofs.zero) addr (e.getList args) = some res) :
    ∃ res', evalAddressing64 ge (.Vptr sp Ptrofs.zero) (addrStrengthReduction64 addr args vl).1
        (e.getList (addrStrengthReduction64 addr args vl).2) = some res' ∧
      Val.Lessdef res res' := by
  simp only [addrStrengthReduction64, Archi.ptr64, Bool.not_true, Bool.false_eq_true, if_false]
  split
  case h_8 => exact addr_strength_reduction_64_generic_correct MATCH addr args vl res hvl hev
  all_goals prep MATCH, hvl, hev
  all_goals simp only [evalAddressing64, Option.some.injEq] at hev
  all_goals subst hev
  all_goals simp only [evalAddressing64, Archi.ptr64, if_true, Val.offsetPtr,
    Ptrofs.add_zero_l, ptrofs_repr_of_int64]
  all_goals refine ⟨_, rfl, ?_⟩
  · exact addl_symbol_lessdef (vmatch_ptr_gl GENV (vmatch_of_eq MATCH h1))
  · exact addl_stk_lessdef_l (vmatch_ptr_stk (vmatch_of_eq MATCH h1) STACK)
  · exact addl_symbol_lessdef (addl_symbol_lessdef (vmatch_ptr_gl GENV (vmatch_of_eq MATCH h1)))
  · rw [Val.addl_commut (.Vlong _)]
    exact addl_symbol_lessdef (addl_symbol_lessdef (vmatch_ptr_gl GENV (vmatch_of_eq MATCH h2)))
  · exact addl_stk_lessdef_l (addl_stk_lessdef_l (vmatch_ptr_stk (vmatch_of_eq MATCH h1) STACK))
  · exact addl_stk_lessdef_l (addl_stk_lessdef_r (vmatch_ptr_stk (vmatch_of_eq MATCH h2) STACK))
  · show Val.Lessdef (Val.addl _ (Val.addl (.Vlong _) _)) _
    rw [← Val.addl_assoc]
    exact addl_symbol_lessdef (addl_symbol_lessdef (vmatch_ptr_gl GENV (vmatch_of_eq MATCH h1)))

/-- `ConstpropOpproof.addr_strength_reduction_correct` -/
theorem addr_strength_reduction_correct (GENV : GenvMatch bc ge) (STACK : bc sp = .BCstack)
    (MATCH : Ematch bc e ae)
    (addr : Addressing) (args : List Reg) (vl : List Aval) (res : Val)
    (hvl : vl = args.map (fun r => AE.get r ae))
    (hev : evalAddressing ge (.Vptr sp Ptrofs.zero) addr (e.getList args) = some res) :
    ∃ res', evalAddressing ge (.Vptr sp Ptrofs.zero) (addrStrengthReduction addr args vl).1
        (e.getList (addrStrengthReduction addr args vl).2) = some res' ∧
      Val.Lessdef res res' := by
  simp only [addrStrengthReduction, Archi.ptr64, if_true]
  split
  · simp only [evalAddressing, Archi.ptr64, if_true] at hev ⊢
    exact addr_strength_reduction_64_correct GENV STACK MATCH addr args vl res hvl hev
  · exact ⟨res, hev, .refl _⟩

/-- `ConstpropOpproof.op_strength_reduction_correct` -/
theorem op_strength_reduction_correct (o : Options)
    (GENV : GenvMatch bc ge) (STACK : bc sp = .BCstack)
    (MATCH : Ematch bc e ae) (op : Operation) (args : List Reg) (vl : List Aval) (v : Val)
    (hvl : vl = args.map (fun r => AE.get r ae))
    (hev : evalOperation ge (.Vptr sp Ptrofs.zero) op (e.getList args) m = some v) :
    OpSim ge sp e m (opStrengthReduction o op args vl) v := by
  unfold opStrengthReduction
  cases op
  all_goals dsimp only
  all_goals first
    | exact ⟨v, hev, .refl _⟩
    | skip
  case Ocmp c =>
    have E : evalOperation ge (.Vptr sp Ptrofs.zero) (.Ocmp c) (e.getList args) m =
        some (Val.ofOptbool (evalCondition c (e.getList args) m)) := by
      generalize e.getList args = l
      rcases l with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
    rw [E, Option.some.injEq] at hev; subst hev
    exact make_cmp_correct MATCH c args vl hvl
  case Osel c ty =>
    split
    · rename_i r1 r2 args' _ _ vl'
      simp only [List.map_cons, List.cons.injEq] at hvl
      simp only [Regmap.getList, List.map_cons] at hev
      unfold evalOperation at hev
      dsimp only at hev
      simp only [Option.some.injEq] at hev; subst hev
      exact make_select_correct o MATCH c ty r1 r2 args' vl' hvl.2.2
    · exact ⟨v, hev, .refl _⟩
  case Olea addr =>
    have E : ∀ a l, evalOperation ge (.Vptr sp Ptrofs.zero) (.Olea a) l m =
        evalAddressing32 ge (.Vptr sp Ptrofs.zero) a l := by
      intro a l; rcases l with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
    rw [E] at hev
    obtain ⟨res', h1, h2⟩ := addr_strength_reduction_32_correct MATCH addr args vl v hvl hev
    generalize addrStrengthReduction32 addr args vl = p at h1 h2 ⊢
    obtain ⟨a', args'⟩ := p
    exact ⟨res', (E _ _).trans h1, h2⟩
  case Oleal addr =>
    have E : ∀ a l, evalOperation ge (.Vptr sp Ptrofs.zero) (.Oleal a) l m =
        evalAddressing64 ge (.Vptr sp Ptrofs.zero) a l := by
      intro a l; rcases l with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
    rw [E] at hev
    obtain ⟨res', h1, h2⟩ := addr_strength_reduction_64_correct GENV STACK MATCH addr args vl v hvl hev
    generalize addrStrengthReduction64 addr args vl = p at h1 h2 ⊢
    obtain ⟨a', args'⟩ := p
    exact ⟨res', (E _ _).trans h1, h2⟩
  all_goals split
  all_goals first
    | exact ⟨v, hev, .refl _⟩
    | skip
  all_goals
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hvl
    simp only [Regmap.getList, List.map_cons, List.map_nil] at hev
    unfold evalOperation at hev
    dsimp only at hev
  all_goals
    first | obtain ⟨h1, h2⟩ := hvl | have h1 := hvl
    try (have H1 := get_I MATCH h1.symm)
    try (have H1 := get_L MATCH h1.symm)
    try (have HF1 := get_F MATCH h1.symm)
    try (have HF1 := get_FS MATCH h1.symm)
    try (have H2 := get_I MATCH h2.symm)
    try (have H2 := get_L MATCH h2.symm)
    try (have HF2 := get_F MATCH h2.symm)
    try (have HF2 := get_FS MATCH h2.symm)
    try (simp only [Option.some.injEq] at hev; subst hev)
    try subst h1
    try subst h2
    try (rw [H1])
    try (rw [H2])
    try simp only [Val.sub_add_opp, Val.subl_addl_opp]
  all_goals have MATCH' : ∀ r, Vmatch bc (e.get r) (AE.get r ae) := MATCH
  all_goals with_reducible first
    | exact make_cast8signed_correct _ (MATCH' _)
    | exact make_cast8unsigned_correct _ (MATCH' _)
    | exact make_cast16signed_correct _ (MATCH' _)
    | exact make_cast16unsigned_correct _ (MATCH' _)
    | exact make_addimm_correct _ _
    | exact make_mulimm_correct _ _
    | (rw [Val.mul_commut]; exact make_mulimm_correct _ _)
    | exact make_divimm_correct _ _ _ hev H2
    | exact make_divuimm_correct _ _ _ hev H2
    | exact make_moduimm_correct _ _ _ hev H2
    | exact make_andimm_correct _ _ (MATCH' _)
    | (rw [Val.and_commut]; exact make_andimm_correct _ _ (MATCH' _))
    | exact make_orimm_correct _ _
    | (rw [Val.or_commut]; exact make_orimm_correct _ _)
    | exact make_xorimm_correct _ _
    | (rw [Val.xor_commut]; exact make_xorimm_correct _ _)
    | exact make_shlimm_correct _ _ _ H2
    | exact make_shrimm_correct _ _ _ H2
    | exact make_shruimm_correct _ _ _ H2
    | exact make_addlimm_correct _ _
    | exact make_mullimm_correct _ _
    | (rw [Val.mull_commut]; exact make_mullimm_correct _ _)
    | exact make_divlimm_correct _ _ _ hev H2
    | exact make_divluimm_correct _ _ _ hev H2
    | exact make_modluimm_correct _ _ _ hev H2
    | exact make_andlimm_correct _ _ _
    | (rw [Val.andl_commut]; exact make_andlimm_correct _ _ _)
    | exact make_orlimm_correct _ _
    | (rw [Val.orl_commut]; exact make_orlimm_correct _ _)
    | exact make_xorlimm_correct _ _
    | (rw [Val.xorl_commut]; exact make_xorlimm_correct _ _)
    | exact make_shllimm_correct _ _ _ H2
    | exact make_shrlimm_correct _ _ _ H2
    | exact make_shrluimm_correct _ _ _ H2
    | exact make_mulfimm_correct _ _ _ HF2
    | exact make_mulfimm_correct_2 _ _ _ HF1
    | exact make_mulfsimm_correct _ _ _ HF2
    | exact make_mulfsimm_correct_2 _ _ _ HF1

end STRENGTH_REDUCTION

end ConstpropOpproof
end X86
end CC
