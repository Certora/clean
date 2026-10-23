/-
  Correctness proof for RISC-V code generation: auxiliary results, part 1 —
  port of the beginning of `riscV/Asmgenproof1.v`: the decomposition of
  integer constants (`make_immed32_sound`, `make_immed64_sound`), properties
  of registers (`ireg_of_not_X31`), and the correctness of the constructor
  functions for constants and arithmetic with an immediate
  (`load_hilo32_correct`, `loadimm32_correct`, `opimm32_correct`,
  `load_hilo64_correct`, `loadimm64_correct`, `opimm64_correct`,
  `addptrofs_correct`, `addptrofs_correct_2`).

  Differences from Rocq:
  * The `Simpl` tactic becomes rewriting with the register-update lemmas
    `nextinstr_set_*` below.
  * The decomposition lemmas are proved by bit-blasting (`bv_decide`) rather
    than by `eqmod` reasoning.
  * The linker parameters `low_half`/`high_half` (`Asm.HalfSplit`) are an
    explicit argument `sym` of `exec_straight`.
-/
import CCLib.riscV.Asmgenproof0

namespace CC
namespace RiscV
namespace Asmgenproof1

open Asm Asmgen Asmgenproof0 Smallstep Conventions1

/-! ## Decomposition of integer constants -/

/-- `Asmgenproof1.make_immed32_sound` -/
theorem make_immed32_sound (n : Integers.Int) :
    match makeImmed32 n with
    | .Imm32_single imm => n = imm
    | .Imm32_pair hi lo => n = Integers.Int.add (Integers.Int.shl hi (Integers.Int.repr 12)) lo := by
  unfold makeImmed32
  by_cases h : Integers.Int.eq n (Integers.Int.sign_ext 12 n) = true
  · simp only [h, if_true]
  · simp only [h]
    simp only [Integers.Int.add, Integers.Int.shl, Integers.Int.shru, Integers.Int.sub,
      Integers.Int.sign_ext, Integers.Int.repr, Integers.MI.add, Integers.MI.shl,
      Integers.MI.shru, Integers.MI.sub, Integers.MI.sign_ext, Integers.MI.repr]
    simp
    bv_decide

/-- `Asmgenproof1.make_immed64_sound` -/
theorem make_immed64_sound (n : Integers.Int64) :
    match makeImmed64 n with
    | .Imm64_single imm => n = imm
    | .Imm64_pair hi lo =>
        n = Integers.Int64.add (Integers.Int64.sign_ext 32
          (Integers.Int64.shl hi (Integers.Int64.repr 12))) lo
    | .Imm64_large imm => n = imm := by
  unfold makeImmed64
  by_cases h : Integers.Int64.eq n (Integers.Int64.sign_ext 12 n) = true
  · simp only [h, if_true]; simpa [Integers.Int64.eq, Integers.MI.eq] using h
  · simp only [h]
    by_cases h2 : Integers.Int64.eq n (Integers.Int64.add (Integers.Int64.sign_ext 32
        (Integers.Int64.shl (Integers.Int64.zero_ext 20 (Integers.Int64.shru
          (Integers.Int64.sub n (Integers.Int64.sign_ext 12 n)) (Integers.Int64.repr 12)))
          (Integers.Int64.repr 12))) (Integers.Int64.sign_ext 12 n)) = true
    · simp only [h2, if_true]; simpa [Integers.Int64.eq, Integers.MI.eq] using h2
    · simp only [h2, Bool.false_eq_true, if_false]

/-! ## Properties of registers -/

/-- No machine register is mapped to `X31`. -/
theorem preg_of_not_X31 (r : Mreg) : pregOf r ≠ .IR .X31 := by
  cases r <;> simp [pregOf]

/-- `Asmgenproof1.ireg_of_not_X31` -/
theorem ireg_of_not_X31 {m : Mreg} {r : Ireg} (h : iregOf m = .OK r) : Preg.IR r ≠ .IR .X31 := by
  rw [← ireg_of_eq h]; exact preg_of_not_X31 m

/-- `Asmgenproof1.ireg_of_not_X31'` -/
theorem ireg_of_not_X31' {m : Mreg} {r : Ireg} (h : iregOf m = .OK r) : r ≠ .X31 :=
  fun e => ireg_of_not_X31 h (congrArg Preg.IR e)

/-! ## Register-update lemmas (the `Simpl` tactic of Rocq) -/

/-- Reading a register of `rs.set r v`. -/
theorem Regset.get_set (rs : Regset) (r r' : Preg) (v : Val) :
    rs.set r v r' = if r' = r then v else rs r' := rfl

/-- `PC` after `nextinstr (rs # r <- v)` with `r ≠ PC`. -/
theorem nextinstr_set_pc (rs : Regset) {r : Preg} (v : Val) (h : r ≠ .PC) :
    nextinstr (rs.set r v) .PC = Val.offsetPtr (rs .PC) Integers.Ptrofs.one := by
  rw [nextinstr_pc, Regset.gso _ _ (Ne.symm h)]

/-- The register written by `nextinstr (rs # rd <- v)`. -/
theorem nextinstr_set_same (rs : Regset) {rd : Preg} (v : Val) (h : rd ≠ .PC) :
    nextinstr (rs.set rd v) rd = v := by
  rw [nextinstr_inv _ h, Regset.gss]

/-- The registers left unchanged by `nextinstr (rs # rd <- v)`. -/
theorem nextinstr_set_other (rs : Regset) {r rd : Preg} (v : Val) (h : r ≠ .PC)
    (hne : r ≠ rd) : nextinstr (rs.set rd v) r = rs r := by
  rw [nextinstr_inv _ h, Regset.gso _ _ hne]

theorem ir_ne_pc (r : Ireg) : Preg.IR r ≠ .PC := by simp
theorem fr_ne_pc (r : Freg) : Preg.FR r ≠ .PC := by simp

/-! ## Correctness of RISC-V constructor functions -/

section CONSTRUCTORS
variable {sym : HalfSplit} {ge : Asm.CGenv} {fn : Asm.Function}

/-- One instruction of the form `rd := v` followed by `nextinstr`. -/
theorem exec_straight_set {i : Instruction} {k : Code} {rs : Regset} {m : Mem} {rd : Preg}
    {v : Val} (hrd : rd ≠ .PC)
    (h : execInstr sym ge fn i rs m = .Next (nextinstr (rs.set rd v)) m) :
    ExecStraight sym ge fn (i :: k) rs m k (nextinstr (rs.set rd v)) m :=
  .one _ _ _ _ _ _ h (nextinstr_set_pc _ _ hrd)

/-- `Asmgenproof1.load_hilo32_correct` -/
theorem load_hilo32_correct (rd : Ireg) (hi lo : Integers.Int) (k : Code) (rs : Regset)
    (m : Mem) :
    ∃ rs', ExecStraight sym ge fn (loadHilo32 rd hi lo k) rs m k rs' m ∧
      rs' (.IR rd) = .Vint (Integers.Int.add (Integers.Int.shl hi (Integers.Int.repr 12)) lo) ∧
      ∀ r, r ≠ .PC → r ≠ .IR rd → rs' r = rs r := by
  unfold loadHilo32
  by_cases h : Integers.Int.eq lo Integers.Int.zero = true
  · have hlo : lo = Integers.Int.zero := by simpa [Integers.Int.eq, Integers.MI.eq] using h
    subst hlo
    simp only [h, if_true]
    refine ⟨_, exec_straight_set (ir_ne_pc rd) rfl, ?_, fun r h1 h2 => nextinstr_set_other _ _ h1 h2⟩
    rw [nextinstr_set_same _ _ (ir_ne_pc rd), Integers.Int.add_zero]
  · simp only [h, Bool.false_eq_true, if_false]
    refine ⟨_, .step _ _ _ _ _ _ _ _ _ rfl (nextinstr_set_pc _ _ (ir_ne_pc rd))
      (exec_straight_set (ir_ne_pc rd) rfl), ?_, fun r h1 h2 => ?_⟩
    · rw [nextinstr_set_same _ _ (ir_ne_pc rd)]
      simp only [get0w, nextinstr_set_same _ _ (ir_ne_pc rd), Val.add]
    · rw [nextinstr_set_other _ _ h1 h2, nextinstr_set_other _ _ h1 h2]

/-- `Asmgenproof1.loadimm32_correct` -/
theorem loadimm32_correct (rd : Ireg) (n : Integers.Int) (k : Code) (rs : Regset) (m : Mem) :
    ∃ rs', ExecStraight sym ge fn (loadimm32 rd n k) rs m k rs' m ∧
      rs' (.IR rd) = .Vint n ∧ ∀ r, r ≠ .PC → r ≠ .IR rd → rs' r = rs r := by
  unfold loadimm32
  have E := make_immed32_sound n
  split
  · rename_i imm heq
    rw [heq] at E; subst E
    refine ⟨_, exec_straight_set (ir_ne_pc rd) rfl, ?_, fun r h1 h2 => nextinstr_set_other _ _ h1 h2⟩
    rw [nextinstr_set_same _ _ (ir_ne_pc rd)]
    simp only [get0w, Val.add, Integers.Int.add_zero_l]
  · rename_i hi lo heq
    rw [heq] at E
    rw [E]
    exact load_hilo32_correct rd hi lo k rs m

/-- `Asmgenproof1.opimm32_correct` -/
theorem opimm32_correct (op : Ireg → Ireg0 → Ireg0 → Instruction)
    (opi : Ireg → Ireg0 → Integers.Int → Instruction) (sem : Val → Val → Val) (m : Mem)
    (hop : ∀ d s1 s2 rs, execInstr sym ge fn (op d s1 s2) rs m =
      .Next (nextinstr (rs.set (.IR d) (sem (get0w rs s1) (get0w rs s2)))) m)
    (hopi : ∀ d s n rs, execInstr sym ge fn (opi d s n) rs m =
      .Next (nextinstr (rs.set (.IR d) (sem (get0w rs s) (.Vint n)))) m)
    (rd r1 : Ireg) (n : Integers.Int) (k : Code) (rs : Regset) (h1 : r1 ≠ .X31) :
    ∃ rs', ExecStraight sym ge fn (opimm32 op opi rd r1 n k) rs m k rs' m ∧
      rs' (.IR rd) = sem (rs (.IR r1)) (.Vint n) ∧
      ∀ r, r ≠ .PC → r ≠ .IR rd → r ≠ .IR .X31 → rs' r = rs r := by
  unfold opimm32
  have E := make_immed32_sound n
  split
  · rename_i imm heq
    rw [heq] at E; subst E
    refine ⟨_, exec_straight_set (ir_ne_pc rd) (hopi _ _ _ _), ?_,
      fun r h1 h2 _ => nextinstr_set_other _ _ h1 h2⟩
    rw [nextinstr_set_same _ _ (ir_ne_pc rd)]; rfl
  · rename_i hi lo heq
    rw [heq] at E
    obtain ⟨rs', A, B, C⟩ := load_hilo32_correct (sym := sym) (ge := ge) (fn := fn) .X31 hi lo
      (op rd r1 Ireg.X31 :: k) rs m
    refine ⟨_, exec_straight_trans A (exec_straight_set (ir_ne_pc rd) (hop _ _ _ _)), ?_,
      fun r h1 h2 h3 => ?_⟩
    · rw [nextinstr_set_same _ _ (ir_ne_pc rd)]
      simp only [get0w]
      rw [B, C _ (ir_ne_pc r1) (fun e => h1 (Preg.IR.inj e)), ← E]
    · rw [nextinstr_set_other _ _ h1 h2, C _ h1 h3]

/-- `Asmgenproof1.load_hilo64_correct` -/
theorem load_hilo64_correct (rd : Ireg) (hi lo : Integers.Int64) (k : Code) (rs : Regset)
    (m : Mem) :
    ∃ rs', ExecStraight sym ge fn (loadHilo64 rd hi lo k) rs m k rs' m ∧
      rs' (.IR rd) = .Vlong (Integers.Int64.add (Integers.Int64.sign_ext 32
        (Integers.Int64.shl hi (Integers.Int64.repr 12))) lo) ∧
      ∀ r, r ≠ .PC → r ≠ .IR rd → rs' r = rs r := by
  unfold loadHilo64
  by_cases h : Integers.Int64.eq lo Integers.Int64.zero = true
  · have hlo : lo = Integers.Int64.zero := by simpa [Integers.Int64.eq, Integers.MI.eq] using h
    subst hlo
    simp only [h, if_true]
    refine ⟨_, exec_straight_set (ir_ne_pc rd) rfl, ?_, fun r h1 h2 => nextinstr_set_other _ _ h1 h2⟩
    rw [nextinstr_set_same _ _ (ir_ne_pc rd), Integers.Int64.add_zero]
  · simp only [h, Bool.false_eq_true, if_false]
    refine ⟨_, .step _ _ _ _ _ _ _ _ _ rfl (nextinstr_set_pc _ _ (ir_ne_pc rd))
      (exec_straight_set (ir_ne_pc rd) rfl), ?_, fun r h1 h2 => ?_⟩
    · rw [nextinstr_set_same _ _ (ir_ne_pc rd)]
      simp only [get0l, nextinstr_set_same _ _ (ir_ne_pc rd), Val.addl]
    · rw [nextinstr_set_other _ _ h1 h2, nextinstr_set_other _ _ h1 h2]

/-- `Asmgenproof1.loadimm64_correct` -/
theorem loadimm64_correct (rd : Ireg) (n : Integers.Int64) (k : Code) (rs : Regset) (m : Mem) :
    ∃ rs', ExecStraight sym ge fn (loadimm64 rd n k) rs m k rs' m ∧
      rs' (.IR rd) = .Vlong n ∧
      ∀ r, r ≠ .PC → r ≠ .IR rd → r ≠ .IR .X31 → rs' r = rs r := by
  unfold loadimm64
  have E := make_immed64_sound n
  split
  · rename_i imm heq
    rw [heq] at E; subst E
    refine ⟨_, exec_straight_set (ir_ne_pc rd) rfl, ?_,
      fun r h1 h2 _ => nextinstr_set_other _ _ h1 h2⟩
    rw [nextinstr_set_same _ _ (ir_ne_pc rd)]
    simp only [get0l, Val.addl, Integers.Int64.add_zero_l]
  · rename_i hi lo heq
    rw [heq] at E
    obtain ⟨rs', A, B, C⟩ := load_hilo64_correct (sym := sym) (ge := ge) (fn := fn) rd hi lo k rs m
    exact ⟨rs', A, by rw [B, ← E], fun r h1 h2 _ => C r h1 h2⟩
  · rename_i imm heq
    rw [heq] at E; subst E
    refine ⟨_, .one _ _ _ _ _ _ rfl (nextinstr_set_pc _ _ (ir_ne_pc rd)), ?_,
      fun r h1 h2 h3 => ?_⟩
    · rw [nextinstr_set_same _ _ (ir_ne_pc rd)]
    · rw [nextinstr_set_other _ _ h1 h2, Regset.gso _ _ h3]

/-- `Asmgenproof1.opimm64_correct` -/
theorem opimm64_correct (op : Ireg → Ireg0 → Ireg0 → Instruction)
    (opi : Ireg → Ireg0 → Integers.Int64 → Instruction) (sem : Val → Val → Val) (m : Mem)
    (hop : ∀ d s1 s2 rs, execInstr sym ge fn (op d s1 s2) rs m =
      .Next (nextinstr (rs.set (.IR d) (sem (get0l rs s1) (get0l rs s2)))) m)
    (hopi : ∀ d s n rs, execInstr sym ge fn (opi d s n) rs m =
      .Next (nextinstr (rs.set (.IR d) (sem (get0l rs s) (.Vlong n)))) m)
    (rd r1 : Ireg) (n : Integers.Int64) (k : Code) (rs : Regset) (h1 : r1 ≠ .X31) :
    ∃ rs', ExecStraight sym ge fn (opimm64 op opi rd r1 n k) rs m k rs' m ∧
      rs' (.IR rd) = sem (rs (.IR r1)) (.Vlong n) ∧
      ∀ r, r ≠ .PC → r ≠ .IR rd → r ≠ .IR .X31 → rs' r = rs r := by
  unfold opimm64
  have E := make_immed64_sound n
  have h1' : Preg.IR r1 ≠ .IR .X31 := fun e => h1 (Preg.IR.inj e)
  split
  · rename_i imm heq
    rw [heq] at E; subst E
    refine ⟨_, exec_straight_set (ir_ne_pc rd) (hopi _ _ _ _), ?_,
      fun r h1 h2 _ => nextinstr_set_other _ _ h1 h2⟩
    rw [nextinstr_set_same _ _ (ir_ne_pc rd)]; rfl
  · rename_i hi lo heq
    rw [heq] at E
    obtain ⟨rs', A, B, C⟩ := load_hilo64_correct (sym := sym) (ge := ge) (fn := fn) .X31 hi lo
      (op rd r1 Ireg.X31 :: k) rs m
    refine ⟨_, exec_straight_trans A (exec_straight_set (ir_ne_pc rd) (hop _ _ _ _)), ?_,
      fun r h1 h2 h3 => ?_⟩
    · rw [nextinstr_set_same _ _ (ir_ne_pc rd)]
      simp only [get0l]
      rw [B, C _ (ir_ne_pc r1) h1', ← E]
    · rw [nextinstr_set_other _ _ h1 h2, C _ h1 h3]
  · rename_i imm heq
    rw [heq] at E; subst E
    refine ⟨_, .step _ _ _ _ _ _ _ _ _ rfl (nextinstr_set_pc _ _ (ir_ne_pc .X31))
      (exec_straight_set (ir_ne_pc rd) (hop _ _ _ _)), ?_, fun r h1 h2 h3 => ?_⟩
    · rw [nextinstr_set_same _ _ (ir_ne_pc rd)]
      simp only [get0l]
      rw [nextinstr_set_same _ _ (ir_ne_pc .X31), nextinstr_set_other _ _ (ir_ne_pc r1) h1',
        Regset.gso _ _ h1']
    · rw [nextinstr_set_other _ _ h1 h2, nextinstr_set_other _ _ h1 h3, Regset.gso _ _ h3]

theorem ptrofs_of_int64_to_int64 (n : Integers.Ptrofs) :
    Integers.Ptrofs.of_int64 (Integers.Ptrofs.to_int64 n) = n := by
  simp only [Integers.Ptrofs.of_int64, Integers.Ptrofs.to_int64, Integers.MI.repr,
    Integers.MI.unsigned]
  apply BitVec.eq_of_toNat_eq
  simp

/-- `Asmgenproof1.addptrofs_correct` -/
theorem addptrofs_correct (rd r1 : Ireg) (n : Integers.Ptrofs) (k : Code) (rs : Regset) (m : Mem)
    (h1 : r1 ≠ .X31) :
    ∃ rs', ExecStraight sym ge fn (addptrofs rd r1 n k) rs m k rs' m ∧
      Val.Lessdef (Val.offsetPtr (rs (.IR r1)) n) (rs' (.IR rd)) ∧
      ∀ r, r ≠ .PC → r ≠ .IR rd → r ≠ .IR .X31 → rs' r = rs r := by
  unfold addptrofs
  by_cases hn : n = Integers.Ptrofs.zero
  · subst hn
    simp only [if_true]
    refine ⟨_, exec_straight_set (ir_ne_pc rd) rfl, ?_, fun r h1 h2 _ => nextinstr_set_other _ _ h1 h2⟩
    rw [nextinstr_set_same _ _ (ir_ne_pc rd)]
    cases hv : rs (.IR r1) <;> simp only [Val.offsetPtr] <;> try exact .undef _
    all_goals first | exact .refl _ | (rw [Integers.Ptrofs.add_zero]; exact .refl _)
  · simp only [hn, if_false, show Archi.ptr64 = true from rfl, if_true]
    obtain ⟨rs', A, B, C⟩ := opimm64_correct (sym := sym) (ge := ge) (fn := fn) .Paddl .Paddil
      Val.addl m (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) rd r1 (Integers.Ptrofs.to_int64 n) k rs h1
    refine ⟨rs', A, ?_, C⟩
    rw [B]
    cases rs (.IR r1) <;> simp only [Val.offsetPtr, Val.addl] <;> try exact .undef _
    simp only [show Archi.ptr64 = true from rfl, if_true, ptrofs_of_int64_to_int64]
    exact .refl _

/-- `Asmgenproof1.addptrofs_correct_2` -/
theorem addptrofs_correct_2 (rd r1 : Ireg) (n : Integers.Ptrofs) (k : Code) (rs : Regset)
    (m : Mem) (b : Block) (ofs : Integers.Ptrofs) (h1 : r1 ≠ .X31)
    (h2 : rs (.IR r1) = .Vptr b ofs) :
    ∃ rs', ExecStraight sym ge fn (addptrofs rd r1 n k) rs m k rs' m ∧
      rs' (.IR rd) = .Vptr b (Integers.Ptrofs.add ofs n) ∧
      ∀ r, r ≠ .PC → r ≠ .IR rd → r ≠ .IR .X31 → rs' r = rs r := by
  obtain ⟨rs', A, B, C⟩ := addptrofs_correct (sym := sym) (ge := ge) (fn := fn) rd r1 n k rs m h1
  rw [h2] at B
  refine ⟨rs', A, ?_, C⟩
  generalize rs' (.IR rd) = v at B
  cases B; rfl

/-! ### Translation of conditional branches -/

theorem cmpu_bool_of_cmp_bool {vp : Block → Z → Bool} {c : Comparison}
    (hc : c = .Ceq ∨ c = .Cne) {v1 v2 : Val} {b : Bool} (h : Val.cmp_bool c v1 v2 = some b) :
    Val.cmpu_bool vp c v1 v2 = some b := by
  cases v1 <;> cases v2 <;> simp [Val.cmp_bool] at h
  rcases hc with rfl | rfl <;>
    simp [Val.cmpu_bool, ← h, Integers.Int.cmp, Integers.Int.cmpu, Integers.MI.cmp,
      Integers.MI.cmpu]

theorem cmplu_bool_of_cmpl_bool {vp : Block → Z → Bool} {c : Comparison}
    (hc : c = .Ceq ∨ c = .Cne) {v1 v2 : Val} {b : Bool} (h : Val.cmpl_bool c v1 v2 = some b) :
    Val.cmplu_bool vp c v1 v2 = some b := by
  cases v1 <;> cases v2 <;> simp [Val.cmpl_bool] at h
  rcases hc with rfl | rfl <;>
    simp [Val.cmplu_bool, ← h, Integers.Int64.cmp, Integers.Int64.cmpu, Integers.MI.cmp,
      Integers.MI.cmpu]

/-- `Asmgenproof1.transl_cbranch_int32s_correct` -/
theorem transl_cbranch_int32s_correct (cmp : Comparison) (r1 r2 : Ireg0) (lbl : Label)
    (rs : Regset) (m : Mem) (b : Bool) (h : Val.cmp_bool cmp (get0w rs r1) (get0w rs r2) = some b) :
    execInstr sym ge fn (translCbranchInt32s cmp r1 r2 lbl) rs m =
      evalBranch fn lbl rs m (some b) := by
  cases cmp
  · show evalBranch fn lbl rs m (Val.cmpu_bool _ .Ceq _ _) = _
    rw [cmpu_bool_of_cmp_bool (.inl rfl) h]
  · show evalBranch fn lbl rs m (Val.cmpu_bool _ .Cne _ _) = _
    rw [cmpu_bool_of_cmp_bool (.inr rfl) h]
  · show evalBranch fn lbl rs m (Val.cmp_bool .Clt _ _) = _
    rw [h]
  · show evalBranch fn lbl rs m (Val.cmp_bool .Cge _ _) = _
    rw [show Comparison.Cge = Comparison.Cle.swap from rfl, Val.swap_cmp_bool, h]
  · show evalBranch fn lbl rs m (Val.cmp_bool .Clt _ _) = _
    rw [show Comparison.Clt = Comparison.Cgt.swap from rfl, Val.swap_cmp_bool, h]
  · show evalBranch fn lbl rs m (Val.cmp_bool .Cge _ _) = _
    rw [h]

/-- `Asmgenproof1.transl_cbranch_int32u_correct` -/
theorem transl_cbranch_int32u_correct (cmp : Comparison) (r1 r2 : Ireg0) (lbl : Label)
    (rs : Regset) (m : Mem) (b : Bool)
    (h : Val.cmpu_bool (Mem.validPointer m) cmp (get0w rs r1) (get0w rs r2) = some b) :
    execInstr sym ge fn (translCbranchInt32u cmp r1 r2 lbl) rs m =
      evalBranch fn lbl rs m (some b) := by
  cases cmp
  · show evalBranch fn lbl rs m (Val.cmpu_bool _ .Ceq _ _) = _
    rw [h]
  · show evalBranch fn lbl rs m (Val.cmpu_bool _ .Cne _ _) = _
    rw [h]
  · show evalBranch fn lbl rs m (Val.cmpu_bool _ .Clt _ _) = _
    rw [h]
  · show evalBranch fn lbl rs m (Val.cmpu_bool _ .Cge _ _) = _
    rw [show Comparison.Cge = Comparison.Cle.swap from rfl, Val.swap_cmpu_bool, h]
  · show evalBranch fn lbl rs m (Val.cmpu_bool _ .Clt _ _) = _
    rw [show Comparison.Clt = Comparison.Cgt.swap from rfl, Val.swap_cmpu_bool, h]
  · show evalBranch fn lbl rs m (Val.cmpu_bool _ .Cge _ _) = _
    rw [h]

/-- `Asmgenproof1.transl_cbranch_int64s_correct` -/
theorem transl_cbranch_int64s_correct (cmp : Comparison) (r1 r2 : Ireg0) (lbl : Label)
    (rs : Regset) (m : Mem) (b : Bool) (h : Val.cmpl_bool cmp (get0l rs r1) (get0l rs r2) = some b) :
    execInstr sym ge fn (translCbranchInt64s cmp r1 r2 lbl) rs m =
      evalBranch fn lbl rs m (some b) := by
  cases cmp
  · show evalBranch fn lbl rs m (Val.cmplu_bool _ .Ceq _ _) = _
    rw [cmplu_bool_of_cmpl_bool (.inl rfl) h]
  · show evalBranch fn lbl rs m (Val.cmplu_bool _ .Cne _ _) = _
    rw [cmplu_bool_of_cmpl_bool (.inr rfl) h]
  · show evalBranch fn lbl rs m (Val.cmpl_bool .Clt _ _) = _
    rw [h]
  · show evalBranch fn lbl rs m (Val.cmpl_bool .Cge _ _) = _
    rw [show Comparison.Cge = Comparison.Cle.swap from rfl, Val.swap_cmpl_bool, h]
  · show evalBranch fn lbl rs m (Val.cmpl_bool .Clt _ _) = _
    rw [show Comparison.Clt = Comparison.Cgt.swap from rfl, Val.swap_cmpl_bool, h]
  · show evalBranch fn lbl rs m (Val.cmpl_bool .Cge _ _) = _
    rw [h]

/-- `Asmgenproof1.transl_cbranch_int64u_correct` -/
theorem transl_cbranch_int64u_correct (cmp : Comparison) (r1 r2 : Ireg0) (lbl : Label)
    (rs : Regset) (m : Mem) (b : Bool)
    (h : Val.cmplu_bool (Mem.validPointer m) cmp (get0l rs r1) (get0l rs r2) = some b) :
    execInstr sym ge fn (translCbranchInt64u cmp r1 r2 lbl) rs m =
      evalBranch fn lbl rs m (some b) := by
  cases cmp
  · show evalBranch fn lbl rs m (Val.cmplu_bool _ .Ceq _ _) = _
    rw [h]
  · show evalBranch fn lbl rs m (Val.cmplu_bool _ .Cne _ _) = _
    rw [h]
  · show evalBranch fn lbl rs m (Val.cmplu_bool _ .Clt _ _) = _
    rw [h]
  · show evalBranch fn lbl rs m (Val.cmplu_bool _ .Cge _ _) = _
    rw [show Comparison.Cge = Comparison.Cle.swap from rfl, Val.swap_cmplu_bool, h]
  · show evalBranch fn lbl rs m (Val.cmplu_bool _ .Clt _ _) = _
    rw [show Comparison.Clt = Comparison.Cgt.swap from rfl, Val.swap_cmplu_bool, h]
  · show evalBranch fn lbl rs m (Val.cmplu_bool _ .Cge _ _) = _
    rw [h]

theorem swap_cmpf (c : Comparison) (v1 v2 : Val) : Val.cmpf c.swap v1 v2 = Val.cmpf c v2 v1 := by
  cases v1 <;> cases v2 <;> simp [Val.cmpf, Val.cmpf_bool, Floats.Float.cmp_swap]

theorem swap_cmpfs (c : Comparison) (v1 v2 : Val) :
    Val.cmpfs c.swap v1 v2 = Val.cmpfs c v2 v1 := by
  cases v1 <;> cases v2 <;> simp [Val.cmpfs, Val.cmpfs_bool, Floats.Float32.cmp_swap]

theorem negate_cmpfs_eq (v1 v2 : Val) : Val.notbool (Val.cmpfs .Cne v1 v2) = Val.cmpfs .Ceq v1 v2 := by
  cases v1 <;> cases v2 <;> simp only [Val.cmpfs, Val.cmpfs_bool, Val.ofOptbool] <;> try rfl
  rw [Floats.Float32.cmp_ne_eq]
  cases Floats.Float32.cmp .Ceq _ _ <;> rfl

/-- `Asmgenproof1.transl_cond_float_correct` -/
theorem transl_cond_float_correct (rs : Regset) (m : Mem) (cmp : Comparison) (rd : Ireg)
    (r1 r2 : Freg) (insn : Instruction) (normal : Bool) (v : Val)
    (h : translCondFloat cmp rd r1 r2 = (insn, normal))
    (hv : v = (if normal then Val.cmpf cmp (rs (.FR r1)) (rs (.FR r2))
      else Val.notbool (Val.cmpf cmp (rs (.FR r1)) (rs (.FR r2))))) :
    execInstr sym ge fn insn rs m = .Next (nextinstr (rs.set (.IR rd) v)) m := by
  subst hv
  cases cmp <;> simp only [translCondFloat, Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
  · rfl
  · show Outcome.Next _ _ = _
    simp only [Bool.false_eq_true, if_false, Val.negate_cmpf_eq]
  · rfl
  · rfl
  · show Outcome.Next (nextinstr (rs.set (.IR rd) (Val.cmpf .Clt _ _))) m = _
    rw [show Comparison.Clt = Comparison.Cgt.swap from rfl, swap_cmpf]; rfl
  · show Outcome.Next (nextinstr (rs.set (.IR rd) (Val.cmpf .Cle _ _))) m = _
    rw [show Comparison.Cle = Comparison.Cge.swap from rfl, swap_cmpf]; rfl

/-- `Asmgenproof1.transl_cond_single_correct` -/
theorem transl_cond_single_correct (rs : Regset) (m : Mem) (cmp : Comparison) (rd : Ireg)
    (r1 r2 : Freg) (insn : Instruction) (normal : Bool) (v : Val)
    (h : translCondSingle cmp rd r1 r2 = (insn, normal))
    (hv : v = (if normal then Val.cmpfs cmp (rs (.FR r1)) (rs (.FR r2))
      else Val.notbool (Val.cmpfs cmp (rs (.FR r1)) (rs (.FR r2))))) :
    execInstr sym ge fn insn rs m = .Next (nextinstr (rs.set (.IR rd) v)) m := by
  subst hv
  cases cmp <;> simp only [translCondSingle, Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
  · rfl
  · show Outcome.Next _ _ = _
    simp only [Bool.false_eq_true, if_false, negate_cmpfs_eq]
  · rfl
  · rfl
  · show Outcome.Next (nextinstr (rs.set (.IR rd) (Val.cmpfs .Clt _ _))) m = _
    rw [show Comparison.Clt = Comparison.Cgt.swap from rfl, swap_cmpfs]; rfl
  · show Outcome.Next (nextinstr (rs.set (.IR rd) (Val.cmpfs .Cle _ _))) m = _
    rw [show Comparison.Cle = Comparison.Cge.swap from rfl, swap_cmpfs]; rfl

/-- `Asmgenproof1.branch_on_X31` -/
theorem branch_on_X31 (normal : Bool) (lbl : Label) (rs : Regset) (m : Mem) (b : Bool)
    (h : rs (.IR .X31) = Val.ofBool (normal == b)) :
    execInstr sym ge fn (if normal then .Pbnew Ireg.X31 .X0 lbl else .Pbeqw Ireg.X31 .X0 lbl) rs m =
      evalBranch fn lbl rs m (some b) := by
  cases normal <;> cases b <;> simp only [if_true, Bool.false_eq_true, if_false] <;>
    (show evalBranch fn lbl rs m (Val.cmpu_bool _ _ (rs (.IR .X31)) _) = _) <;>
    rw [h] <;> rfl

end CONSTRUCTORS

end Asmgenproof1
end RiscV
end CC
