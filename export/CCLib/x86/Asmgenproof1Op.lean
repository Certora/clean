/-
  Correctness proof for x86-64 generation: auxiliary results, part 3 —
  port of the end of `x86/Asmgenproof1.v`: `transl_addressing_mode_32_correct`,
  `transl_op_correct`, `transl_load_correct`, `transl_store_correct`.

  Differences from Rocq: the `ArgsInv` / `TranslOp` tactics become the
  inversion lemmas `iop1_inv`, `iop2_inv`, … and the generic lemmas
  `op_single`, `op_single_nf`, `op_multi`.
-/
import CCLib.x86.Asmgenproof1Cond

namespace CC
namespace X86
namespace Asmgenproof1

open Asm Asmgen Asmgenproof0 Smallstep Conventions1 Op

/-! ### Inversion of the argument-shape helpers of `transl_op` -/

theorem assert_OK {A : Type} {b : Bool} {k : Res A} {c : A} (h : Asmgen.assert b k = .OK c) :
    b = true ∧ k = .OK c := by
  unfold Asmgen.assert at h
  split at h
  · exact ⟨by assumption, h⟩
  · cases h

theorem iop1_inv {a1 res : Mreg} {mk : Ireg → Instruction} {k c : Code}
    (h : iop1 a1 res mk k = .OK c) : a1 = res ∧ ∃ r, pregOf res = .IR r ∧ c = mk r :: k := by
  obtain ⟨h1, h⟩ := assert_OK h
  simp only [res_bind_OK, res_pure_OK] at h
  obtain ⟨r, hr, rfl⟩ := h
  exact ⟨of_decide_eq_true h1, r, ireg_of_eq hr, rfl⟩

theorem iop2_inv {a1 a2 res : Mreg} {mk : Ireg → Ireg → Instruction} {k c : Code}
    (h : iop2 a1 a2 res mk k = .OK c) :
    a1 = res ∧ ∃ r r2, pregOf res = .IR r ∧ pregOf a2 = .IR r2 ∧ c = mk r r2 :: k := by
  obtain ⟨h1, h⟩ := assert_OK h
  simp only [res_bind_OK, res_pure_OK] at h
  obtain ⟨r, hr, r2, hr2, rfl⟩ := h
  exact ⟨of_decide_eq_true h1, r, r2, ireg_of_eq hr, ireg_of_eq hr2, rfl⟩

theorem ishift_inv {a1 a2 res : Mreg} {mk : Ireg → Instruction} {k c : Code}
    (h : ishift a1 a2 res mk k = .OK c) :
    a1 = res ∧ a2 = .CX ∧ ∃ r, pregOf res = .IR r ∧ c = mk r :: k := by
  obtain ⟨h1, h⟩ := assert_OK h
  obtain ⟨h2, h⟩ := assert_OK h
  simp only [res_bind_OK, res_pure_OK] at h
  obtain ⟨r, hr, rfl⟩ := h
  exact ⟨of_decide_eq_true h1, of_decide_eq_true h2, r, ireg_of_eq hr, rfl⟩

theorem fop1_inv {a1 res : Mreg} {mk : Freg → Instruction} {k c : Code}
    (h : fop1 a1 res mk k = .OK c) : a1 = res ∧ ∃ r, pregOf res = .FR r ∧ c = mk r :: k := by
  obtain ⟨h1, h⟩ := assert_OK h
  simp only [res_bind_OK, res_pure_OK] at h
  obtain ⟨r, hr, rfl⟩ := h
  exact ⟨of_decide_eq_true h1, r, freg_of_eq hr, rfl⟩

theorem fop2_inv {a1 a2 res : Mreg} {mk : Freg → Freg → Instruction} {k c : Code}
    (h : fop2 a1 a2 res mk k = .OK c) :
    a1 = res ∧ ∃ r r2, pregOf res = .FR r ∧ pregOf a2 = .FR r2 ∧ c = mk r r2 :: k := by
  obtain ⟨h1, h⟩ := assert_OK h
  simp only [res_bind_OK, res_pure_OK] at h
  obtain ⟨r, hr, r2, hr2, rfl⟩ := h
  exact ⟨of_decide_eq_true h1, r, r2, freg_of_eq hr, freg_of_eq hr2, rfl⟩

theorem mulh_inv {a1 a2 res : Mreg} {mk : Ireg → Instruction} {k c : Code}
    (h : mulh a1 a2 res mk k = .OK c) :
    a1 = .AX ∧ res = .DX ∧ ∃ r2, pregOf a2 = .IR r2 ∧ c = mk r2 :: k := by
  obtain ⟨h1, h⟩ := assert_OK h
  obtain ⟨h2, h⟩ := assert_OK h
  simp only [res_bind_OK, res_pure_OK] at h
  obtain ⟨r, hr, rfl⟩ := h
  exact ⟨of_decide_eq_true h1, of_decide_eq_true h2, r, ireg_of_eq hr, rfl⟩

theorem divop_inv {a1 a2 res dst : Mreg} {c c' : Code} (h : divop a1 a2 res dst c = .OK c') :
    a1 = .AX ∧ a2 = .CX ∧ res = dst ∧ c' = c := by
  obtain ⟨h1, h⟩ := assert_OK h
  obtain ⟨h2, h⟩ := assert_OK h
  obtain ⟨h3, h⟩ := assert_OK h
  cases h
  exact ⟨of_decide_eq_true h1, of_decide_eq_true h2, of_decide_eq_true h3, rfl⟩

section CONSTRUCTORS
variable {ge : Asm.CGenv} {fn : Asm.Function}

/-! ### Generic shapes of the generated code -/

/-- A single instruction that writes one data register and advances `PC`
(without touching the flags). -/
theorem op_single {i : Instruction} {k : Code} {rs : Regset} {m : Mem} {rd : Preg} {v v' : Val}
    {P : Preg → Prop}
    (hi : execInstr ge fn i rs m = .Next (nextinstr (rs.set rd v')) m) (hrd : dataPreg rd = true)
    (hv : Val.Lessdef v v') :
    ∃ rs', ExecStraight ge fn (i :: k) rs m k rs' m ∧ Val.Lessdef v (rs' rd) ∧
      ∀ r, dataPreg r = true → r ≠ rd → P r → rs' r = rs r :=
  ⟨_, .one _ _ _ _ _ _ hi (nextinstr_set_pc _ _ (data_diff hrd rfl)),
    by rwa [nextinstr_set_same _ _ hrd], fun _ h1 h2 _ => nextinstr_set_other _ _ h1 h2⟩

/-- A single instruction that writes one data register, undefines the flags
and advances `PC`. -/
theorem op_single_nf {i : Instruction} {k : Code} {rs : Regset} {m : Mem} {rd : Preg}
    {v v' : Val} {P : Preg → Prop}
    (hi : execInstr ge fn i rs m = .Next (nextinstrNf (rs.set rd v')) m)
    (hrd : dataPreg rd = true) (hv : Val.Lessdef v v') :
    ∃ rs', ExecStraight ge fn (i :: k) rs m k rs' m ∧ Val.Lessdef v (rs' rd) ∧
      ∀ r, dataPreg r = true → r ≠ rd → P r → rs' r = rs r :=
  ⟨_, .one _ _ _ _ _ _ hi (nextinstrNf_set_pc _ _ (data_diff hrd rfl)),
    by rwa [nextinstrNf_set_same _ _ hrd], fun _ h1 h2 _ => nextinstrNf_set_other _ _ h1 h2⟩

/-- A sequence of instructions computing `w` into `rd`. -/
theorem op_multi {c k : Code} {rs : Regset} {m : Mem} {rd : Preg} {v w : Val}
    {P : Preg → Prop}
    (hex : ∃ rs', ExecStraight ge fn c rs m k rs' m ∧ rs' rd = w ∧
      ∀ r, dataPreg r = true → r ≠ rd → P r → rs' r = rs r)
    (hv : Val.Lessdef v w) :
    ∃ rs', ExecStraight ge fn c rs m k rs' m ∧ Val.Lessdef v (rs' rd) ∧
      ∀ r, dataPreg r = true → r ≠ rd → P r → rs' r = rs r :=
  let ⟨rs', A, B, C⟩ := hex
  ⟨rs', A, B ▸ hv, C⟩

theorem maketotal_lessdef {o : Option Val} {v : Val} (h : o = some v) :
    Val.Lessdef v (Val.maketotal o) := by
  subst h; exact .refl _

/-! ### 32-bit addressing modes (`lea`) -/

theorem mul_lessdef_scale (v : Val) (i : Z) :
    Val.Lessdef (Val.mul v (.Vint (Integers.Int.repr i)))
      (if i = 1 then v else Val.mul v (.Vint (Integers.Int.repr i))) := by
  by_cases h : i = 1
  · subst h; rw [if_pos rfl]
    cases v <;> simp only [Val.mul] <;> try exact .undef _
    rw [show Integers.Int.repr 1 = Integers.Int.one from rfl, Integers.Int.mul_one]
    exact .refl _
  · rw [if_neg h]; exact .refl _

theorem add_zero_l_int (n : Integers.Int) :
    Val.add (.Vint Integers.Int.zero) (.Vint n) = .Vint n := by
  simp [Val.add, Integers.Int.add_zero_l]

/-- `Asmgenproof1.transl_addressing_mode_32_correct` -/
theorem transl_addressing_mode_32_correct {addr : Addressing} {args : List Mreg} {am : Addrmode}
    (rs : Regset) {v : Val} (h : translAddressing addr args = .OK am)
    (hv : Op.evalAddressing32 ge (rs (.IR .RSP)) addr ((args.map pregOf).map rs) = some v) :
    Val.Lessdef v (evalAddrmode32 ge am rs) := by
  cases addr <;> rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, args⟩⟩⟩ <;>
    simp only [translAddressing, res_bind_OK, res_pure_OK] at h <;>
    simp only [Op.evalAddressing32, List.map, Archi.ptr64, if_true, reduceCtorEq,
      Option.some.injEq] at hv <;>
    (try cases h) <;> subst hv
  case Aindexed.cons.nil.intro r h =>
    obtain ⟨hr, rfl⟩ := h
    simp only [evalAddrmode32, ireg_of_eq hr, add_zero_l_int]
    exact .refl _
  case Aindexed2.cons.cons.nil.intro r h =>
    obtain ⟨hr1, r2, hr2, rfl⟩ := h
    simp only [evalAddrmode32, ireg_of_eq hr1, ireg_of_eq hr2, if_pos, Val.add_assoc]
    exact .refl _
  case Ascaled.cons.nil.intro r h =>
    obtain ⟨hr, rfl⟩ := h
    simp only [evalAddrmode32, ireg_of_eq hr]
    rw [Val.add_permut, add_zero_l_int]
    exact Val.add_lessdef (mul_lessdef_scale _ _) (.refl _)
  case Aindexed2scaled.cons.cons.nil.intro r h =>
    obtain ⟨hr1, r2, hr2, rfl⟩ := h
    simp only [evalAddrmode32, ireg_of_eq hr1, ireg_of_eq hr2]
    exact Val.add_lessdef (.refl _) (Val.add_lessdef (mul_lessdef_scale _ _) (.refl _))


/-! ### Multiply-high and division shapes -/

/-- `mulhs`/`mulhu`: one instruction writing `RAX` and `RDX`. -/
theorem op_mulh {i : Instruction} {k : Code} {rs : Regset} {m : Mem} {a b : Val}
    {P : Preg → Prop}
    (hi : execInstr ge fn i rs m = .Next (nextinstrNf ((rs.set (.IR .RAX) a).set (.IR .RDX) b)) m)
    (hP : ∀ r, P r → r ≠ .IR .RAX) :
    ∃ rs', ExecStraight ge fn (i :: k) rs m k rs' m ∧ Val.Lessdef b (rs' (.IR .RDX)) ∧
      ∀ r, dataPreg r = true → r ≠ .IR .RDX → P r → rs' r = rs r := by
  refine ⟨_, .one _ _ _ _ _ _ hi (by rfl), ?_, ?_⟩
  · simp [nextinstrNf, nextinstr, undefRegs, flagRegs, Regset.set]; exact .refl _
  · intro r hr h1 h2
    have h3 := hP r h2
    cases r <;> simp_all [dataPreg, nextinstrNf, nextinstr, undefRegs, flagRegs, Regset.set]

/-- Division: sign/zero-extend into `RDX`, then `div`/`idiv` by `RCX`. -/
theorem op_div {T : Type} {proj : Val → Option T} {inj : T → Val}
    {divmod : T → T → T → Option (T × T)} {i1 i2 : Instruction} {k : Code} {rs : Regset}
    {m : Mem} {x : Val} {nh nl d q r : T}
    (h1 : execInstr ge fn i1 rs m = .Next (nextinstrNf (rs.set (.IR .RDX) x)) m)
    (h2 : ∀ rs', execInstr ge fn i2 rs' m = execDiv proj inj divmod .RCX rs' m)
    (hx : proj x = some nh) (hl : proj (rs (.IR .RAX)) = some nl)
    (hd : proj (rs (.IR .RCX)) = some d) (hdm : divmod nh nl d = some (q, r)) :
    ∃ rs', ExecStraight ge fn (i1 :: i2 :: k) rs m k rs' m ∧ rs' (.IR .RAX) = inj q ∧
      rs' (.IR .RDX) = inj r ∧
      ∀ r, dataPreg r = true → r ≠ .IR .RAX → r ≠ .IR .RDX → rs' r = rs r := by
  refine ⟨_, exec_straight_two (rs3 := nextinstrNf (((nextinstrNf (rs.set (.IR .RDX) x)).set
    (.IR .RAX) (inj q)).set (.IR .RDX) (inj r))) h1 ?_ (by rfl) (by rfl), ?_, ?_, ?_⟩
  · rw [h2]; unfold execDiv
    have e1 : nextinstrNf (rs.set (.IR .RDX) x) (.IR .RDX) = x := rfl
    have e2 : nextinstrNf (rs.set (.IR .RDX) x) (.IR .RAX) = rs (.IR .RAX) := rfl
    have e3 : nextinstrNf (rs.set (.IR .RDX) x) (.IR .RCX) = rs (.IR .RCX) := rfl
    rw [e1, e2, e3, hx, hl, hd]; dsimp only; rw [hdm]
  · rfl
  · rfl
  · intro r hr h1 h2
    cases r <;> simp_all [dataPreg, nextinstrNf, nextinstr, undefRegs, flagRegs, Regset.set]

/-! ### Operations, loads and stores -/

set_option maxHeartbeats 2000000 in
/-- `Asmgenproof1.transl_op_correct` -/
theorem transl_op_correct {op : Operation} {args : List Mreg} {res : Mreg} {k c : Code}
    (rs : Regset) (m : Mem) {v : Val} (h : translOp op args res k = .OK c)
    (hev : evalOperation ge (rs (.IR .RSP)) op ((args.map pregOf).map rs) m = some v) :
    ∃ rs', ExecStraight ge fn c rs m k rs' m ∧ Val.Lessdef v (rs' (pregOf res)) ∧
      ∀ r, dataPreg r = true → r ≠ pregOf res → PregNotin r (destroyedByOp op) →
        rs' r = rs r := by
  cases op
  case Ocmp cond =>
    unfold translOp at h
    simp only [res_bind_OK] at h; obtain ⟨r, h0, h⟩ := h
    rw [ireg_of_eq h0]
    obtain ⟨rs1, A, B, C⟩ := transl_cond_correct (ge := ge) (fn := fn) rs m h
    obtain ⟨rs2, A2, B2, C2⟩ := mk_setcc_correct (ge := ge) (fn := fn)
      (testcondForCondition cond) r k rs1 m
    unfold Op.evalOperation at hev; cases hev
    refine ⟨rs2, exec_straight_trans A A2, ?_, fun r' h1 h2 h3 => ?_⟩
    · rw [B2]
      revert B
      cases evalCondition cond ((args.map pregOf).map rs) m with
      | none => intro _; exact .undef _
      | some b => intro B; rw [B.1]; exact .refl _
    · rw [C2 r' h1 ⟨h3 .AX (.head _), h3 .CX (.tail _ (.head _))⟩ h2, C r' h1]
  case Osel cond ty =>
    rcases args with _ | ⟨a1, _ | ⟨a2, args⟩⟩ <;> unfold translOp at h <;> try cases h
    obtain ⟨hd, hb⟩ := assert_OK h
    clear h
    cases of_decide_eq_true hd
    simp only [res_bind_OK] at hb; obtain ⟨r, h0, r2, h2, h⟩ := hb
    unfold Op.evalOperation at hev
    simp only [List.map, ireg_of_eq h0, ireg_of_eq h2] at hev ⊢
    cases hev
    obtain ⟨rs1, A, B, C⟩ := transl_sel_correct (ge := ge) (fn := fn) ty rs m h
    exact ⟨rs1, A, B, fun r' h1 h2 _ => C r' h1 h2⟩
  case Olea addr =>
    unfold translOp at h
    simp only [res_bind_OK, res_pure_OK] at h; obtain ⟨am, ha, r, h0, rfl⟩ := h
    rw [ireg_of_eq h0]
    unfold Op.evalOperation at hev
    have E := transl_addressing_mode_32_correct (ge := ge) rs ha hev
    refine op_single rfl rfl ?_
    rw [normalize_addrmode_32_correct]; exact E
  case Oleal addr =>
    unfold translOp at h
    simp only [res_bind_OK, res_pure_OK] at h; obtain ⟨am, ha, r, h0, rfl⟩ := h
    rw [ireg_of_eq h0]
    unfold Op.evalOperation at hev
    have E := transl_addressing_mode_64_correct (ge := ge) rs ha hev
    have EV := normalize_addrmode_64_correct (ge := ge) am rs
    revert EV
    cases normalizeAddrmode64 am with
    | mk am' od =>
      cases od with
      | none =>
        intro EV; dsimp only at EV ⊢
        exact op_single rfl rfl (EV ▸ E)
      | some delta =>
        intro EV; dsimp only at EV ⊢
        refine ⟨_, exec_straight_two rfl rfl (nextinstr_pc _) (by rfl), ?_, ?_⟩
        · simp only [nextinstrNf, nextinstr, undefRegs, flagRegs, Regset.set]
          simpa [EV] using E
        · intro r' h1 h2 _
          cases r' <;> simp_all [dataPreg, nextinstrNf, nextinstr, undefRegs, flagRegs, Regset.set]
  all_goals (rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, args⟩⟩⟩ <;>
              unfold translOp at h <;> dsimp only at h <;> (try cases h))
  all_goals first
    | (guard_hyp h : iop1 _ _ _ _ = _
       obtain ⟨rfl, r, e0, rfl⟩ := iop1_inv h
       simp only [List.map, e0] at hev ⊢)
    | (guard_hyp h : iop2 _ _ _ _ _ = _
       obtain ⟨rfl, r, r2, e0, e2, rfl⟩ := iop2_inv h
       simp only [List.map, e0, e2] at hev ⊢)
    | (guard_hyp h : ishift _ _ _ _ _ = _
       obtain ⟨rfl, rfl, r, e0, rfl⟩ := ishift_inv h
       simp only [List.map, e0] at hev ⊢)
    | (guard_hyp h : fop1 _ _ _ _ = _
       obtain ⟨rfl, r, e0, rfl⟩ := fop1_inv h
       simp only [List.map, e0] at hev ⊢)
    | (guard_hyp h : fop2 _ _ _ _ _ = _
       obtain ⟨rfl, r, r2, e0, e2, rfl⟩ := fop2_inv h
       simp only [List.map, e0, e2] at hev ⊢)
    | skip
  all_goals (try simp only [List.map] at hev)
  all_goals (unfold Op.evalOperation at hev; (try dsimp only at hev))
  all_goals (try (cases hev; first
    | exact op_single rfl rfl (.refl _)
    | exact op_single_nf rfl rfl (.refl _)))
  all_goals (try (
    simp only [res_bind_OK, res_pure_OK] at h
    first
      | (obtain ⟨r, h0, r1, h1, rfl⟩ := h
         (try rw [ireg_of_eq h0] at hev); (try rw [freg_of_eq h0] at hev)
         (try rw [ireg_of_eq h1] at hev); (try rw [freg_of_eq h1] at hev)
         (try rw [ireg_of_eq h0]); (try rw [freg_of_eq h0])
         (try rw [ireg_of_eq h1]); (try rw [freg_of_eq h1]))
      | (obtain ⟨r, h0, rfl⟩ := h
         first | rw [ireg_of_eq h0] | rw [freg_of_eq h0])
    first
      | (cases hev; exact op_single rfl rfl (.refl _))
      | (cases hev; exact op_single_nf rfl rfl (.refl _))
      | exact op_single rfl rfl (maketotal_lessdef hev)
      | (cases hev; split
         · exact op_single_nf rfl rfl (by subst_vars; exact .refl _)
         · first | exact op_single_nf rfl rfl (.refl _) | exact op_single rfl rfl (.refl _))))
  case Omove.cons.nil =>
    obtain ⟨rs2, A, B, C⟩ := mk_mov_correct (ge := ge) (fn := fn) rs m h
    cases hev
    exact ⟨rs2, A, B ▸ .refl _, fun r h1 h2 _ => C r h1 h2⟩
  case Ocast8signed.cons.nil =>
    simp only [res_bind_OK] at h; obtain ⟨r1, h1, r, h0, h⟩ := h
    rw [ireg_of_eq h1] at hev; rw [ireg_of_eq h0]; cases hev
    obtain ⟨rs2, A, B, C⟩ := mk_intconv_correct (ge := ge) (fn := fn) (sem := Val.signExt 8) rs m h
      (fun _ _ _ _ _ => rfl)
    exact ⟨rs2, A, by rw [B]; exact .refl _,
      fun r hr h1 h2 => C r hr h1 (h2 .AX (.head _))⟩
  case Ocast8unsigned.cons.nil =>
    simp only [res_bind_OK] at h; obtain ⟨r1, h1, r, h0, h⟩ := h
    rw [ireg_of_eq h1] at hev; rw [ireg_of_eq h0]; cases hev
    obtain ⟨rs2, A, B, C⟩ := mk_intconv_correct (ge := ge) (fn := fn) (sem := Val.zeroExt 8) rs m h
      (fun _ _ _ _ _ => rfl)
    exact ⟨rs2, A, by rw [B]; exact .refl _,
      fun r hr h1 h2 => C r hr h1 (h2 .AX (.head _))⟩
  case Omulhs.cons.cons.nil =>
    obtain ⟨rfl, rfl, r2, e2, rfl⟩ := mulh_inv h
    simp only [e2] at hev; cases hev
    exact op_mulh rfl (fun r h => h .AX (.head _))
  case Omulhu.cons.cons.nil =>
    obtain ⟨rfl, rfl, r2, e2, rfl⟩ := mulh_inv h
    simp only [e2] at hev; cases hev
    exact op_mulh rfl (fun r h => h .AX (.head _))
  case Omullhs.cons.cons.nil =>
    obtain ⟨rfl, rfl, r2, e2, rfl⟩ := mulh_inv h
    simp only [e2] at hev; cases hev
    exact op_mulh rfl (fun r h => h .AX (.head _))
  case Omullhu.cons.cons.nil =>
    obtain ⟨rfl, rfl, r2, e2, rfl⟩ := mulh_inv h
    simp only [e2] at hev; cases hev
    exact op_mulh rfl (fun r h => h .AX (.head _))
  case Odiv.cons.cons.nil =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := divop_inv h
    try simp only [List.map] at hev
    obtain ⟨nh, nl, d, q, r, A, B, C, D, E, F⟩ := divs_mods_exists (v1 := rs (.IR .RAX)) (v2 := rs (.IR .RCX))
      (Or.inl (by intro e; exact absurd (e.symm.trans hev) (by simp)))
    obtain ⟨rs', X, Y, Z, W⟩ := op_div (ge := ge) (fn := fn) (k := k) (rs := rs) (m := m) (i1 := .Pcltd)
      (i2 := .Pidivl .RCX) (proj := projInt) (inj := .Vint) rfl (fun _ => rfl) (by rw [A]; rfl) (by rw [B]; rfl)
      (by rw [C]; rfl) D
    have hev' := hev
    change _ = some v at hev'
    rw [show rs (pregOf .AX) = rs (.IR .RAX) from rfl, show rs (pregOf .CX) = rs (.IR .RCX) from rfl,
      E] at hev'
    cases hev'
    exact ⟨rs', X, by show Val.Lessdef _ (rs' (.IR .RAX)); rw [Y]; exact .refl _,
      fun r h1 h2 h3 => W r h1 (h3 .AX (.head _)) (h3 .DX (.tail _ (.head _)))⟩
  case Omod.cons.cons.nil =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := divop_inv h
    try simp only [List.map] at hev
    obtain ⟨nh, nl, d, q, r, A, B, C, D, E, F⟩ := divs_mods_exists (v1 := rs (.IR .RAX)) (v2 := rs (.IR .RCX))
      (Or.inr (by intro e; exact absurd (e.symm.trans hev) (by simp)))
    obtain ⟨rs', X, Y, Z, W⟩ := op_div (ge := ge) (fn := fn) (k := k) (rs := rs) (m := m) (i1 := .Pcltd)
      (i2 := .Pidivl .RCX) (proj := projInt) (inj := .Vint) rfl (fun _ => rfl) (by rw [A]; rfl) (by rw [B]; rfl)
      (by rw [C]; rfl) D
    have hev' := hev
    change _ = some v at hev'
    rw [show rs (pregOf .AX) = rs (.IR .RAX) from rfl, show rs (pregOf .CX) = rs (.IR .RCX) from rfl,
      F] at hev'
    cases hev'
    exact ⟨rs', X, by show Val.Lessdef _ (rs' (.IR .RDX)); rw [Z]; exact .refl _,
      fun r h1 h2 h3 => W r h1 (h3 .AX (.head _)) (h3 .DX (.tail _ (.head _)))⟩
  case Odivu.cons.cons.nil =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := divop_inv h
    try simp only [List.map] at hev
    obtain ⟨n, d, q, r, B, C, D, E, F⟩ := divu_modu_exists (v1 := rs (.IR .RAX)) (v2 := rs (.IR .RCX))
      (Or.inl (by intro e; exact absurd (e.symm.trans hev) (by simp)))
    obtain ⟨rs', X, Y, Z, W⟩ := op_div (ge := ge) (fn := fn) (k := k) (rs := rs) (m := m) (i1 := .Pxorl_r .RDX)
      (i2 := .Pdivl .RCX) (proj := projInt) (inj := .Vint) rfl (fun _ => rfl) (rfl) (by rw [B]; rfl)
      (by rw [C]; rfl) D
    have hev' := hev
    change _ = some v at hev'
    rw [show rs (pregOf .AX) = rs (.IR .RAX) from rfl, show rs (pregOf .CX) = rs (.IR .RCX) from rfl,
      E] at hev'
    cases hev'
    exact ⟨rs', X, by show Val.Lessdef _ (rs' (.IR .RAX)); rw [Y]; exact .refl _,
      fun r h1 h2 h3 => W r h1 (h3 .AX (.head _)) (h3 .DX (.tail _ (.head _)))⟩
  case Omodu.cons.cons.nil =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := divop_inv h
    try simp only [List.map] at hev
    obtain ⟨n, d, q, r, B, C, D, E, F⟩ := divu_modu_exists (v1 := rs (.IR .RAX)) (v2 := rs (.IR .RCX))
      (Or.inr (by intro e; exact absurd (e.symm.trans hev) (by simp)))
    obtain ⟨rs', X, Y, Z, W⟩ := op_div (ge := ge) (fn := fn) (k := k) (rs := rs) (m := m) (i1 := .Pxorl_r .RDX)
      (i2 := .Pdivl .RCX) (proj := projInt) (inj := .Vint) rfl (fun _ => rfl) (rfl) (by rw [B]; rfl)
      (by rw [C]; rfl) D
    have hev' := hev
    change _ = some v at hev'
    rw [show rs (pregOf .AX) = rs (.IR .RAX) from rfl, show rs (pregOf .CX) = rs (.IR .RCX) from rfl,
      F] at hev'
    cases hev'
    exact ⟨rs', X, by show Val.Lessdef _ (rs' (.IR .RDX)); rw [Z]; exact .refl _,
      fun r h1 h2 h3 => W r h1 (h3 .AX (.head _)) (h3 .DX (.tail _ (.head _)))⟩
  case Odivl.cons.cons.nil =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := divop_inv h
    try simp only [List.map] at hev
    obtain ⟨nh, nl, d, q, r, A, B, C, D, E, F⟩ := divls_modls_exists (v1 := rs (.IR .RAX)) (v2 := rs (.IR .RCX))
      (Or.inl (by intro e; exact absurd (e.symm.trans hev) (by simp)))
    obtain ⟨rs', X, Y, Z, W⟩ := op_div (ge := ge) (fn := fn) (k := k) (rs := rs) (m := m) (i1 := .Pcqto)
      (i2 := .Pidivq .RCX) (proj := projLong) (inj := .Vlong) rfl (fun _ => rfl) (by rw [A]; rfl) (by rw [B]; rfl)
      (by rw [C]; rfl) D
    have hev' := hev
    change _ = some v at hev'
    rw [show rs (pregOf .AX) = rs (.IR .RAX) from rfl, show rs (pregOf .CX) = rs (.IR .RCX) from rfl,
      E] at hev'
    cases hev'
    exact ⟨rs', X, by show Val.Lessdef _ (rs' (.IR .RAX)); rw [Y]; exact .refl _,
      fun r h1 h2 h3 => W r h1 (h3 .AX (.head _)) (h3 .DX (.tail _ (.head _)))⟩
  case Omodl.cons.cons.nil =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := divop_inv h
    try simp only [List.map] at hev
    obtain ⟨nh, nl, d, q, r, A, B, C, D, E, F⟩ := divls_modls_exists (v1 := rs (.IR .RAX)) (v2 := rs (.IR .RCX))
      (Or.inr (by intro e; exact absurd (e.symm.trans hev) (by simp)))
    obtain ⟨rs', X, Y, Z, W⟩ := op_div (ge := ge) (fn := fn) (k := k) (rs := rs) (m := m) (i1 := .Pcqto)
      (i2 := .Pidivq .RCX) (proj := projLong) (inj := .Vlong) rfl (fun _ => rfl) (by rw [A]; rfl) (by rw [B]; rfl)
      (by rw [C]; rfl) D
    have hev' := hev
    change _ = some v at hev'
    rw [show rs (pregOf .AX) = rs (.IR .RAX) from rfl, show rs (pregOf .CX) = rs (.IR .RCX) from rfl,
      F] at hev'
    cases hev'
    exact ⟨rs', X, by show Val.Lessdef _ (rs' (.IR .RDX)); rw [Z]; exact .refl _,
      fun r h1 h2 h3 => W r h1 (h3 .AX (.head _)) (h3 .DX (.tail _ (.head _)))⟩
  case Odivlu.cons.cons.nil =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := divop_inv h
    try simp only [List.map] at hev
    obtain ⟨n, d, q, r, B, C, D, E, F⟩ := divlu_modlu_exists (v1 := rs (.IR .RAX)) (v2 := rs (.IR .RCX))
      (Or.inl (by intro e; exact absurd (e.symm.trans hev) (by simp)))
    obtain ⟨rs', X, Y, Z, W⟩ := op_div (ge := ge) (fn := fn) (k := k) (rs := rs) (m := m) (i1 := .Pxorq_r .RDX)
      (i2 := .Pdivq .RCX) (proj := projLong) (inj := .Vlong) rfl (fun _ => rfl) (rfl) (by rw [B]; rfl)
      (by rw [C]; rfl) D
    have hev' := hev
    change _ = some v at hev'
    rw [show rs (pregOf .AX) = rs (.IR .RAX) from rfl, show rs (pregOf .CX) = rs (.IR .RCX) from rfl,
      E] at hev'
    cases hev'
    exact ⟨rs', X, by show Val.Lessdef _ (rs' (.IR .RAX)); rw [Y]; exact .refl _,
      fun r h1 h2 h3 => W r h1 (h3 .AX (.head _)) (h3 .DX (.tail _ (.head _)))⟩
  case Omodlu.cons.cons.nil =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := divop_inv h
    try simp only [List.map] at hev
    obtain ⟨n, d, q, r, B, C, D, E, F⟩ := divlu_modlu_exists (v1 := rs (.IR .RAX)) (v2 := rs (.IR .RCX))
      (Or.inr (by intro e; exact absurd (e.symm.trans hev) (by simp)))
    obtain ⟨rs', X, Y, Z, W⟩ := op_div (ge := ge) (fn := fn) (k := k) (rs := rs) (m := m) (i1 := .Pxorq_r .RDX)
      (i2 := .Pdivq .RCX) (proj := projLong) (inj := .Vlong) rfl (fun _ => rfl) (rfl) (by rw [B]; rfl)
      (by rw [C]; rfl) D
    have hev' := hev
    change _ = some v at hev'
    rw [show rs (pregOf .AX) = rs (.IR .RAX) from rfl, show rs (pregOf .CX) = rs (.IR .RCX) from rfl,
      F] at hev'
    cases hev'
    exact ⟨rs', X, by show Val.Lessdef _ (rs' (.IR .RDX)); rw [Z]; exact .refl _,
      fun r h1 h2 h3 => W r h1 (h3 .AX (.head _)) (h3 .DX (.tail _ (.head _)))⟩
  case Oshrximm.cons.nil =>
    obtain ⟨h1, h⟩ := assert_OK h; obtain ⟨h2, h⟩ := assert_OK h
    cases of_decide_eq_true h1; cases of_decide_eq_true h2
    try simp only [List.map] at hev
    obtain ⟨rs2, A, B, C⟩ := mk_shrximm_correct (ge := ge) (fn := fn) rs m h hev
    exact ⟨rs2, A, by show Val.Lessdef _ (rs2 (.IR .RAX)); rw [B]; exact .refl _,
      fun r h1 h2 h3 => C r h1 h2 (h3 .CX (.head _))⟩
  case Oshrxlimm.cons.nil =>
    obtain ⟨h1, h⟩ := assert_OK h; obtain ⟨h2, h⟩ := assert_OK h
    cases of_decide_eq_true h1; cases of_decide_eq_true h2
    try simp only [List.map] at hev
    obtain ⟨rs2, A, B, C⟩ := mk_shrxlimm_correct (ge := ge) (fn := fn) rs m h hev
    exact ⟨rs2, A, by show Val.Lessdef _ (rs2 (.IR .RAX)); rw [B]; exact .refl _,
      fun r h1 h2 h3 => C r h1 h2 (h3 .DX (.head _))⟩

/-- `Asmgenproof1.transl_load_correct` -/
theorem transl_load_correct {chunk : Chunk} {addr : Addressing} {args : List Mreg} {dest : Mreg}
    {k c : Code} (rs : Regset) (m : Mem) {a v : Val}
    (h : translLoad chunk addr args dest k = .OK c)
    (hev : Op.evalAddressing ge (rs (.IR .RSP)) addr ((args.map pregOf).map rs) = some a)
    (hld : Mem.loadv chunk m a = some v) :
    ∃ rs', ExecStraight ge fn c rs m k rs' m ∧ rs' (pregOf dest) = v ∧
      ∀ r, dataPreg r = true → r ≠ pregOf dest → rs' r = rs r := by
  unfold translLoad at h
  simp only [res_bind_OK] at h; obtain ⟨am, ha, h⟩ := h
  have EA := transl_addressing_mode_correct (ge := ge) rs ha hev
  have EA' : evalAddrmode ge am rs = a := by
    cases EA with
    | refl => rfl
    | undef => simp [Mem.loadv] at hld
  rw [← EA'] at hld
  refine ⟨nextinstrNf (rs.set (pregOf dest) v), ?_, nextinstrNf_set_same _ _ (preg_of_data dest),
    fun r hr hne => nextinstrNf_set_other _ _ hr hne⟩
  have hpc := nextinstrNf_set_pc rs v (preg_of_not_PC dest)
  cases chunk <;> (try cases h) <;>
    (simp only [res_bind_OK, res_pure_OK] at h; obtain ⟨r, hr, rfl⟩ := h
     first | rw [ireg_of_eq hr] at hpc ⊢ | rw [freg_of_eq hr] at hpc ⊢
     exact .one _ _ _ _ _ _ (exec_load_eq hld) hpc)

/-- `Asmgenproof1.transl_store_correct` -/
theorem transl_store_correct {chunk : Chunk} {addr : Addressing} {args : List Mreg} {src : Mreg}
    {k c : Code} (rs : Regset) (m : Mem) {a : Val} {m' : Mem}
    (h : translStore chunk addr args src k = .OK c)
    (hev : Op.evalAddressing ge (rs (.IR .RSP)) addr ((args.map pregOf).map rs) = some a)
    (hst : Mem.storev chunk m a (rs (pregOf src)) = some m') :
    ∃ rs', ExecStraight ge fn c rs m k rs' m' ∧
      ∀ r, dataPreg r = true → PregNotin r (destroyedByStore chunk addr) → rs' r = rs r := by
  unfold translStore at h
  simp only [res_bind_OK] at h; obtain ⟨am, ha, h⟩ := h
  have EA := transl_addressing_mode_correct (ge := ge) rs ha hev
  have EA' : evalAddrmode ge am rs = a := by
    cases EA with
    | refl => rfl
    | undef => simp [Mem.storev] at hst
  rw [← EA'] at hst
  cases chunk <;> (try cases h) <;>
    (simp only [res_bind_OK, res_pure_OK] at h; obtain ⟨r, hr, h⟩ := h
     first | rw [ireg_of_eq hr] at hst | rw [freg_of_eq hr] at hst
     first
     | (guard_hyp h : mkStorebyte _ _ _ = _
        obtain ⟨rs2, A, B⟩ := mk_storebyte_correct (fn := fn) rs h hst
        exact ⟨rs2, A, fun r hr _ => B r hr⟩)
     | (subst h
        exact ⟨_, .one _ _ _ _ _ _ (exec_store_eq (l := []) hst) (nextinstrNf_pc _),
          fun r hr _ => nextinstr_nf_inv1 _ hr⟩))

end CONSTRUCTORS

end Asmgenproof1
end X86
end CC
