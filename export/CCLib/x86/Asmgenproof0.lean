/-
  Correctness proof for Asm generation: machine-independent framework —
  port of `backend/Asmgenproof0.v` (whole file), x86-64 instance.  This file
  follows `CCLib/backend/Asmgenproof0.lean` (the aarch64 instance); in Rocq
  the file is shared, but it is stated over the target's `Asm`, `Asmgen` and
  `Mach`, which the port instantiates per target.

  Ported: the properties of `preg_of`, `ireg_of`, `freg_of`, `nextinstr`
  and `undef_regs`; `preg_notin`; the agreement relation `agree` between
  Mach and Asm register states and its preservation lemmas; the
  correspondence of Mach and Asm calling conventions for external calls
  and builtins (`extcall_arguments_match`, `builtin_args_match`,
  `agree_set_res`); `code_tail` and `transl_code_at_pc`;
  `return_address_offset` and its existence (`return_address_exists`) and
  uniqueness (`return_address_offset_correct`); `find_label`,
  `label_pos_code_tail`, `tail_nolabel`; straight-line execution
  (`exec_straight`, `exec_straight_opt` and their lemmas,
  `exec_straight_steps_1/2`); `match_stack`, `parent_sp_def`,
  `parent_ra_def`, `lessdef_parent_sp`, `lessdef_parent_ra`.

  Differences from Rocq:
  * Rocq's `is_tail c1 c2` is Lean's suffix relation `c1 <:+ c2`, and
    `list_length_z` is the length cast to `Z`.
  * `Archi.win64` is an explicit argument `win64` (it determines the
    callee-save registers and the location of stack arguments).
  * The x86 stack pointer `SP` is the integer register `RSP`, so Rocq's
    `SP` (a `preg`) is written `.IR SP`; the return address `RA` is a
    pseudo-register of its own.
  * The section hypotheses of `RETADDR_EXISTS` (`transl_instr_tail`,
    `transf_function_inv`, `transf_function_len`) are discharged by the
    target-specific `Asmgenproof`; here they are explicit arguments.
  * The hint databases and the `TailNoLabel` tactic are not ported.
-/
import CCLib.x86.Asmgen
import CCLib.x86.OpTheory

namespace CC
namespace X86
namespace Asmgenproof0

open Asm Asmgen Smallstep Conventions1

/-- `omega` after unfolding the `Z` abbreviation. -/
local macro "zomega" : tactic => `(tactic| ((try simp only [Z] at *) <;> omega))

/-! ## Processor registers and register states -/

/-- `Asmgenproof0.ireg_of_eq` -/
theorem ireg_of_eq {r : Mreg} {r' : Ireg} (h : iregOf r = .OK r') : pregOf r = .IR r' := by
  unfold iregOf at h
  split at h
  · rename_i h1; cases h; exact h1
  · cases h

/-- `Asmgenproof0.freg_of_eq` -/
theorem freg_of_eq {r : Mreg} {r' : Freg} (h : fregOf r = .OK r') : pregOf r = .FR r' := by
  unfold fregOf at h
  split at h
  · rename_i h1; cases h; exact h1
  · cases h

/-- `Asmgenproof0.preg_of_injective` -/
theorem preg_of_injective {r1 r2 : Mreg} (h : pregOf r1 = pregOf r2) : r1 = r2 := by
  cases r1 <;> cases r2 <;> first | rfl | (simp [pregOf] at h)

/-- `Asmgenproof0.preg_of_data` -/
theorem preg_of_data (r : Mreg) : dataPreg (pregOf r) = true := by
  cases r <;> rfl

/-- `Asmgenproof0.data_diff` -/
theorem data_diff {r r' : Preg} (h1 : dataPreg r = true) (h2 : dataPreg r' = false) : r ≠ r' := by
  rintro rfl; rw [h1] at h2; cases h2

/-- `Asmgenproof0.preg_of_not_SP` -/
theorem preg_of_not_SP (r : Mreg) : pregOf r ≠ (.IR SP) := by
  cases r <;> simp [pregOf]

/-- `Asmgenproof0.preg_of_not_PC` -/
theorem preg_of_not_PC (r : Mreg) : pregOf r ≠ .PC :=
  data_diff (preg_of_data r) rfl

/-- `Asmgenproof0.preg_of_not_RA` -/
theorem preg_of_not_RA (r : Mreg) : pregOf r ≠ .RA := by
  cases r <;> simp [pregOf]

theorem Regset.gss (rs : Regset) (r : Preg) (v : Val) : rs.set r v r = v := by
  simp [Regset.set]

theorem Regset.gso (rs : Regset) {r r' : Preg} (v : Val) (h : r' ≠ r) : rs.set r v r' = rs r' := by
  simp [Regset.set, h]

/-- `Asmgenproof0.nextinstr_pc` -/
theorem nextinstr_pc (rs : Regset) :
    nextinstr rs .PC = Val.offsetPtr (rs .PC) Integers.Ptrofs.one :=
  Regset.gss _ _ _

/-- `Asmgenproof0.nextinstr_inv` -/
theorem nextinstr_inv {r : Preg} (rs : Regset) (h : r ≠ .PC) : nextinstr rs r = rs r :=
  Regset.gso _ _ h

/-- `Asmgenproof0.nextinstr_inv1` -/
theorem nextinstr_inv1 {r : Preg} (rs : Regset) (h : dataPreg r = true) : nextinstr rs r = rs r :=
  nextinstr_inv rs (data_diff h rfl)

/-- `Asmgenproof0.nextinstr_set_preg` -/
theorem nextinstr_set_preg (rs : Regset) (m : Mreg) (v : Val) :
    nextinstr (rs.set (pregOf m) v) .PC = Val.offsetPtr (rs .PC) Integers.Ptrofs.one := by
  rw [nextinstr_pc, Regset.gso _ _ (preg_of_not_PC m).symm]

/-- `Asmgenproof0.undef_regs_other` -/
theorem undef_regs_other {r : Preg} :
    ∀ (rl : List Preg) (rs : Regset), (∀ r', r' ∈ rl → r ≠ r') → undefRegs rl rs r = rs r
  | [], _, _ => rfl
  | a :: rl, rs, h => by
    simp only [undefRegs]
    rw [undef_regs_other rl _ (fun r' hr => h r' (List.mem_cons_of_mem _ hr)),
      Regset.gso _ _ (h a List.mem_cons_self)]

/-- `Asmgenproof0.preg_notin` -/
def PregNotin (r : Preg) (rl : List Mreg) : Prop := ∀ mr, mr ∈ rl → r ≠ pregOf mr

/-- `Asmgenproof0.preg_of_notin` -/
theorem preg_of_notin {r : Preg} (rl : List Mreg) (h : ∀ mr, r ≠ pregOf mr) : PregNotin r rl :=
  fun mr _ => h mr

/-- `Asmgenproof0.undef_regs_other_2` -/
theorem undef_regs_other_2 {r : Preg} {rl : List Mreg} (rs : Regset) (h : PregNotin r rl) :
    undefRegs (rl.map pregOf) rs r = rs r := by
  apply undef_regs_other
  intro r' hr
  obtain ⟨mr, hm, rfl⟩ := List.mem_map.mp hr
  exact h mr hm

/-! ## Agreement between Mach registers and processor registers -/

/-- `Asmgenproof0.agree` -/
structure Agree (ms : Mach.Regset) (sp : Val) (rs : Regset) : Prop where
  agree_sp : rs (.IR SP) = sp
  agree_sp_def : sp ≠ .Vundef
  agree_mregs : ∀ r : Mreg, Val.Lessdef (ms r) (rs (pregOf r))

variable {ms : Mach.Regset} {sp : Val} {rs : Regset}

/-- `Asmgenproof0.preg_val` -/
theorem preg_val (h : Agree ms sp rs) (r : Mreg) : Val.Lessdef (ms r) (rs (pregOf r)) :=
  h.agree_mregs r

/-- `Asmgenproof0.preg_vals` -/
theorem preg_vals (h : Agree ms sp rs) :
    ∀ l : List Mreg, Val.LessdefList (l.map ms) ((l.map pregOf).map rs)
  | [] => .nil
  | a :: l => .cons (preg_val h a) (preg_vals h l)

/-- `Asmgenproof0.sp_val` -/
theorem sp_val (h : Agree ms sp rs) : sp = rs (.IR SP) := h.agree_sp.symm

/-- `Asmgenproof0.ireg_val` -/
theorem ireg_val (h : Agree ms sp rs) {r : Mreg} {r' : Ireg} (hr : iregOf r = .OK r') :
    Val.Lessdef (ms r) (rs (.IR r')) := by
  rw [← ireg_of_eq hr]; exact preg_val h r

/-- `Asmgenproof0.freg_val` -/
theorem freg_val (h : Agree ms sp rs) {r : Mreg} {r' : Freg} (hr : fregOf r = .OK r') :
    Val.Lessdef (ms r) (rs (.FR r')) := by
  rw [← freg_of_eq hr]; exact preg_val h r

/-- `Asmgenproof0.agree_exten_1` -/
theorem agree_exten_1 {rs' : Regset} (h : Agree ms sp rs)
    (h1 : ∀ mr, rs' (pregOf mr) = rs (pregOf mr)) (h2 : rs' (.IR SP) = rs (.IR SP)) : Agree ms sp rs' :=
  ⟨h2.trans h.agree_sp, h.agree_sp_def, fun r => by rw [h1]; exact h.agree_mregs r⟩

/-- `Asmgenproof0.agree_exten` -/
theorem agree_exten {rs' : Regset} (h : Agree ms sp rs)
    (h1 : ∀ r, dataPreg r = true → rs' r = rs r) : Agree ms sp rs' :=
  agree_exten_1 h (fun mr => h1 _ (preg_of_data mr)) (h1 _ rfl)

/-- `Asmgenproof0.agree_set_mreg` -/
theorem agree_set_mreg {r : Mreg} {v : Val} {rs' : Regset} (h : Agree ms sp rs)
    (hv : Val.Lessdef v (rs' (pregOf r)))
    (ho : ∀ r', dataPreg r' = true → r' ≠ pregOf r → rs' r' = rs r') :
    Agree (Mach.Regset.set r v ms) sp rs' := by
  refine ⟨?_, h.agree_sp_def, ?_⟩
  · rw [ho _ rfl (preg_of_not_SP r).symm]; exact h.agree_sp
  · intro r0
    by_cases e : r0 = r
    · subst e; rw [Mach.Regset.gss]; exact hv
    · rw [Mach.Regset.gso _ _ e, ho _ (preg_of_data r0) (fun h' => e (preg_of_injective h'))]
      exact h.agree_mregs r0

/-- `Asmgenproof0.agree_set_mreg_parallel` -/
theorem agree_set_mreg_parallel {r : Mreg} {v v' : Val} (h : Agree ms sp rs)
    (hv : Val.Lessdef v v') : Agree (Mach.Regset.set r v ms) sp (rs.set (pregOf r) v') :=
  agree_set_mreg h (by rw [Regset.gss]; exact hv) (fun _ _ hne => Regset.gso _ _ hne)

/-- `Asmgenproof0.agree_set_other` -/
theorem agree_set_other {r : Preg} (v : Val) (h : Agree ms sp rs) (hr : dataPreg r = false) :
    Agree ms sp (rs.set r v) :=
  agree_exten h (fun _ hd => Regset.gso _ _ (data_diff hd hr))

/-- `Asmgenproof0.agree_set_other_1` -/
theorem agree_set_other_1 {r : Preg} (v : Val) (h : Agree ms sp rs) (h1 : r ≠ (.IR SP))
    (h2 : ∀ mr, r ≠ pregOf mr) : Agree ms sp (rs.set r v) :=
  agree_exten_1 h (fun mr => Regset.gso _ _ (h2 mr).symm) (Regset.gso _ _ h1.symm)

/-- `Asmgenproof0.agree_nextinstr` -/
theorem agree_nextinstr (h : Agree ms sp rs) : Agree ms sp (nextinstr rs) :=
  agree_set_other _ h rfl

/-- `Asmgenproof0.agree_set_pair` -/
theorem agree_set_pair (p : RPair Mreg) {v v' : Val} (h : Agree ms sp rs) (hv : Val.Lessdef v v') :
    Agree (Mach.setPair p v ms) sp (setPair (p.map pregOf) v' rs) := by
  cases p with
  | One r => exact agree_set_mreg_parallel h hv
  | Twolong rhi rlo =>
    exact agree_set_mreg_parallel (agree_set_mreg_parallel h (Val.hiword_lessdef hv))
      (Val.loword_lessdef hv)

/-- `Asmgenproof0.agree_undef_nondata_regs` -/
theorem agree_undef_nondata_regs :
    ∀ (rl : List Preg) {rs : Regset}, Agree ms sp rs → (∀ r, r ∈ rl → dataPreg r = false) →
      Agree ms sp (undefRegs rl rs)
  | [], _, h, _ => h
  | a :: rl, _, h, hd => by
    simp only [undefRegs]
    exact agree_undef_nondata_regs rl (agree_set_other _ h (hd a List.mem_cons_self))
      (fun r hr => hd r (List.mem_cons_of_mem _ hr))

/-- `Asmgenproof0.agree_undef_regs` -/
theorem agree_undef_regs {rl : List Mreg} {rs' : Regset} (h : Agree ms sp rs)
    (ho : ∀ r', dataPreg r' = true → PregNotin r' rl → rs' r' = rs r') :
    Agree (Mach.undefRegs rl ms) sp rs' := by
  refine ⟨?_, h.agree_sp_def, ?_⟩
  · rw [ho _ rfl (fun mr _ => (preg_of_not_SP mr).symm)]; exact h.agree_sp
  · intro r
    by_cases hr : r ∈ rl
    · rw [Mach.undefRegs_same _ _ _ hr]; exact .undef _
    · rw [Mach.undefRegs_other _ _ _ hr, ho _ (preg_of_data r)]
      · exact h.agree_mregs r
      · intro mr hm he
        exact hr (preg_of_injective he ▸ hm)

/-- `Asmgenproof0.agree_undef_regs2` -/
theorem agree_undef_regs2 {rl : List Mreg} {rs' : Regset} (h : Agree (Mach.undefRegs rl ms) sp rs)
    (ho : ∀ r', dataPreg r' = true → PregNotin r' rl → rs' r' = rs r') :
    Agree (Mach.undefRegs rl ms) sp rs' := by
  refine ⟨?_, h.agree_sp_def, ?_⟩
  · rw [ho _ rfl (fun mr _ => (preg_of_not_SP mr).symm)]; exact h.agree_sp
  · intro r
    by_cases hr : r ∈ rl
    · rw [Mach.undefRegs_same _ _ _ hr]; exact .undef _
    · rw [ho _ (preg_of_data r)]
      · exact h.agree_mregs r
      · intro mr hm he
        exact hr (preg_of_injective he ▸ hm)

/-- `Asmgenproof0.agree_set_undef_mreg` -/
theorem agree_set_undef_mreg {r : Mreg} {v : Val} {rl : List Mreg} {rs' : Regset}
    (h : Agree ms sp rs) (hv : Val.Lessdef v (rs' (pregOf r)))
    (ho : ∀ r', dataPreg r' = true → r' ≠ pregOf r → PregNotin r' rl → rs' r' = rs r') :
    Agree (Mach.Regset.set r v (Mach.undefRegs rl ms)) sp rs' := by
  apply agree_set_mreg (rs := rs'.set (pregOf r) (rs (pregOf r))) _ hv
  · intro r' _ hne; exact (Regset.gso _ _ hne).symm
  · apply agree_undef_regs h
    intro r' hd hn
    by_cases e : r' = pregOf r
    · subst e; exact Regset.gss _ _ _
    · rw [Regset.gso _ _ e]; exact ho r' hd e hn

/-- `Asmgenproof0.agree_undef_caller_save_regs` -/
theorem agree_undef_caller_save_regs (win64 : Bool) (h : Agree ms sp rs) :
    Agree (Mach.undefCallerSaveRegs win64 ms) sp (Asm.undefCallerSaveRegs win64 rs) := by
  refine ⟨?_, h.agree_sp_def, ?_⟩
  · simp only [Asm.undefCallerSaveRegs, decide_true, Bool.true_or, if_true]; exact h.agree_sp
  · intro r
    simp only [Mach.undefCallerSaveRegs, Asm.undefCallerSaveRegs]
    have hsp : decide (pregOf r = (.IR SP)) = false := decide_eq_false (preg_of_not_SP r)
    rw [hsp, Bool.false_or]
    cases hc : isCalleeSave win64 r
    · exact .undef _
    · have : pregOf r ∈ (Mreg.allMregs.filter (isCalleeSave win64)).map pregOf :=
        List.mem_map.mpr ⟨r, List.mem_filter.mpr ⟨Mreg.allMregs_complete r, hc⟩, rfl⟩
      simp only [this, decide_true, if_true]
      exact h.agree_mregs r

/-- `Asmgenproof0.agree_change_sp` -/
theorem agree_change_sp {sp' : Val} (h : Agree ms sp rs) (hsp : sp' ≠ .Vundef) :
    Agree ms sp' (rs.set (.IR SP) sp') :=
  ⟨Regset.gss _ _ _, hsp, fun r => by rw [Regset.gso _ _ (preg_of_not_SP r)]; exact h.agree_mregs r⟩

/-! ## Mach and Asm calling conventions for external functions -/

/-- `Asmgenproof0.extcall_arg_match` -/
theorem extcall_arg_match {win64 : Bool} {m m' : Mem} {l : Loc} {v : Val} (h : Agree ms sp rs)
    (hm : Mem.Extends m m') (ha : Mach.ExtcallArg win64 ms m sp l v) :
    ∃ v', Asm.ExtcallArg win64 rs m' l v' ∧ Val.Lessdef v v' := by
  cases ha with
  | reg r => exact ⟨_, .reg r, preg_val h r⟩
  | stack ofs ty v hl =>
    obtain ⟨v', A, B⟩ := Mem.loadv_extends hm hl (.refl _)
    rw [sp_val h] at A
    exact ⟨v', .stack ofs ty _ v' rfl A, B⟩

/-- `Asmgenproof0.extcall_arg_pair_match` -/
theorem extcall_arg_pair_match {win64 : Bool} {m m' : Mem} {p : RPair Loc} {v : Val} (h : Agree ms sp rs)
    (hm : Mem.Extends m m') (ha : Mach.ExtcallArgPair win64 ms m sp p v) :
    ∃ v', Asm.ExtcallArgPair win64 rs m' p v' ∧ Val.Lessdef v v' := by
  cases ha with
  | one l v hl =>
    obtain ⟨v', A, B⟩ := extcall_arg_match h hm hl
    exact ⟨v', .one _ _ A, B⟩
  | twolong hi lo vhi vlo h1 h2 =>
    obtain ⟨v1, A1, B1⟩ := extcall_arg_match h hm h1
    obtain ⟨v2, A2, B2⟩ := extcall_arg_match h hm h2
    exact ⟨_, .twolong _ _ _ _ A1 A2, Val.longofwords_lessdef B1 B2⟩

/-- `Asmgenproof0.extcall_args_match` -/
theorem extcall_args_match {win64 : Bool} {m m' : Mem} (h : Agree ms sp rs) (hm : Mem.Extends m m') :
    ∀ {ll : List (RPair Loc)} {vl : List Val}, ListForall2 (Mach.ExtcallArgPair win64 ms m sp) ll vl →
      ∃ vl', ListForall2 (Asm.ExtcallArgPair win64 rs m') ll vl' ∧ Val.LessdefList vl vl'
  | [], [], .nil => ⟨[], .nil, .nil⟩
  | _ :: _, _ :: _, .cons ha hl => by
    obtain ⟨v1, A, B⟩ := extcall_arg_pair_match h hm ha
    obtain ⟨vl', C, D⟩ := extcall_args_match h hm hl
    exact ⟨v1 :: vl', .cons A C, .cons B D⟩

/-- `Asmgenproof0.extcall_arguments_match` -/
theorem extcall_arguments_match {win64 : Bool} {m m' : Mem} {sg : Signature} {args : List Val}
    (h : Agree ms sp rs) (hm : Mem.Extends m m') (ha : Mach.ExtcallArguments win64 ms m sp sg args) :
    ∃ args', Asm.ExtcallArguments win64 rs m' sg args' ∧ Val.LessdefList args args' :=
  extcall_args_match h hm ha

/-! ## Arguments and results of builtins -/

/-- `Asmgenproof0.builtin_arg_match` -/
theorem builtin_arg_match {ge : Senv} (rs : Regset) (sp : Val) (m : Mem) {a : BuiltinArg Mreg}
    {v : Val} (h : EvalBuiltinArg ge (fun r => rs (pregOf r)) sp m a v) :
    EvalBuiltinArg ge rs sp m (BuiltinArg.map pregOf a) v := by
  induction h with
  | BA x => exact .BA _
  | BA_int n => exact .BA_int n
  | BA_long n => exact .BA_long n
  | BA_float n => exact .BA_float n
  | BA_single n => exact .BA_single n
  | BA_loadstack chunk ofs v hl => exact .BA_loadstack _ _ _ hl
  | BA_addrstack ofs => exact .BA_addrstack ofs
  | BA_loadglobal chunk id ofs v hl => exact .BA_loadglobal _ _ _ _ hl
  | BA_addrglobal id ofs => exact .BA_addrglobal id ofs
  | BA_splitlong hi lo vhi vlo _ _ ih1 ih2 => exact .BA_splitlong _ _ _ _ ih1 ih2
  | BA_addptr a1 a2 v1 v2 _ _ ih1 ih2 => exact .BA_addptr _ _ _ _ ih1 ih2

/-- `Asmgenproof0.builtin_args_match` -/
theorem builtin_args_match {ge : Senv} {m m' : Mem} (h : Agree ms sp rs) (hm : Mem.Extends m m') :
    ∀ {al : List (BuiltinArg Mreg)} {vl : List Val}, EvalBuiltinArgs ge ms sp m al vl →
      ∃ vl', EvalBuiltinArgs ge rs sp m' (al.map (BuiltinArg.map pregOf)) vl' ∧
        Val.LessdefList vl vl'
  | [], [], .nil => ⟨[], .nil, .nil⟩
  | _ :: _, _ :: _, .cons ha hl => by
    obtain ⟨v1, A, B⟩ := evalBuiltinArg_lessdef (e2 := fun r => rs (pregOf r))
      (fun r => preg_val h r) hm ha
    obtain ⟨vl', C, D⟩ := builtin_args_match h hm hl
    exact ⟨v1 :: vl', .cons (builtin_arg_match rs sp m' A) C, .cons B D⟩

/-- `Asmgenproof0.agree_set_res` -/
theorem agree_set_res :
    ∀ (res : BuiltinRes Mreg) {ms : Mach.Regset} {rs : Regset} {v v' : Val},
      Agree ms sp rs → Val.Lessdef v v' →
      Agree (Mach.setRes res v ms) sp (Asm.setRes (BuiltinRes.map pregOf res) v' rs)
  | .BR _, _, _, _, _, h, hv => agree_set_mreg_parallel h hv
  | .BR_none, _, _, _, _, h, _ => h
  | .BR_splitlong hi lo, _, _, _, _, h, hv =>
    agree_set_res lo (agree_set_res hi h (Val.hiword_lessdef hv)) (Val.loword_lessdef hv)

/-- `Asmgenproof0.set_res_other_1` -/
theorem set_res_other_1 {r : Preg} (hr : ∀ mr, r ≠ pregOf mr) :
    ∀ (res : BuiltinRes Mreg) (v : Val) (rs : Regset),
      Asm.setRes (BuiltinRes.map pregOf res) v rs r = rs r
  | .BR x, _, rs => Regset.gso rs _ (hr x)
  | .BR_none, _, _ => rfl
  | .BR_splitlong hi lo, v, rs => by
    show Asm.setRes (BuiltinRes.map pregOf lo) _ (Asm.setRes (BuiltinRes.map pregOf hi) _ rs) r = _
    rw [set_res_other_1 hr lo, set_res_other_1 hr hi]

/-- `Asmgenproof0.set_res_other` -/
theorem set_res_other {r : Preg} (res : BuiltinRes Mreg) (v : Val) (rs : Regset)
    (hr : dataPreg r = false) : Asm.setRes (BuiltinRes.map pregOf res) v rs r = rs r :=
  set_res_other_1 (fun mr => (data_diff (preg_of_data mr) hr).symm) res v rs

/-! ## Correspondence between Mach code and Asm code -/

/-- `Asmgenproof0.find_instr_in` -/
theorem find_instr_in : ∀ {c : Code} {pos : Z} {i : Instruction}, findInstr pos c = some i → i ∈ c
  | [], _, _, h => by simp [findInstr] at h
  | a :: c, pos, i, h => by
    simp only [findInstr] at h
    split at h
    · cases h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (find_instr_in h)

/-- `Asmgenproof0.code_tail`: `c2` is the tail of `c1` starting at position
    `pos`. -/
inductive CodeTail : Z → Code → Code → Prop where
  | zero (c : Code) : CodeTail 0 c c
  | succ (pos : Z) (i : Instruction) (c1 c2 : Code) :
      CodeTail pos c1 c2 → CodeTail (pos + 1) (i :: c1) c2

/-- `Asmgenproof0.code_tail_pos` -/
theorem code_tail_pos {pos : Z} {c1 c2 : Code} (h : CodeTail pos c1 c2) : 0 ≤ pos := by
  induction h with
  | zero => exact Int.le_refl _
  | succ _ _ _ _ _ ih => zomega

/-- `Asmgenproof0.find_instr_tail` -/
theorem find_instr_tail : ∀ {c1 : Code} {i : Instruction} {c2 : Code} {pos : Z},
    CodeTail pos c1 (i :: c2) → findInstr pos c1 = some i
  | [], _, _, _, h => by cases h
  | a :: c1, i, c2, pos, h => by
    simp only [findInstr]
    cases h with
    | zero => simp
    | succ pos' _ _ _ h' =>
      have := code_tail_pos h'
      rw [if_neg (by zomega), show pos' + 1 - 1 = pos' by zomega]
      exact find_instr_tail h'

/-- `Asmgenproof0.code_tail_bounds_1` -/
theorem code_tail_bounds_1 {fn c : Code} {ofs : Z} (h : CodeTail ofs fn c) :
    0 ≤ ofs ∧ ofs ≤ (fn.length : Z) := by
  induction h with
  | zero => zomega
  | succ _ _ _ _ _ ih => simp only [List.length_cons]; zomega

/-- `Asmgenproof0.code_tail_bounds_2` -/
theorem code_tail_bounds_2 {fn : Code} {ofs : Z} {i : Instruction} {c : Code}
    (h : CodeTail ofs fn (i :: c)) : 0 ≤ ofs ∧ ofs < (fn.length : Z) := by
  generalize e : i :: c = c' at h
  induction h with
  | zero => subst e; simp only [List.length_cons]; zomega
  | succ _ _ _ _ _ ih => have := ih e; simp only [List.length_cons]; zomega

/-- `Asmgenproof0.code_tail_next` -/
theorem code_tail_next {fn : Code} {ofs : Z} {i : Instruction} {c : Code}
    (h : CodeTail ofs fn (i :: c)) : CodeTail (ofs + 1) fn c := by
  generalize e : i :: c = c' at h
  induction h with
  | zero => subst e; exact .succ _ _ _ _ (.zero _)
  | succ _ _ _ _ _ ih => exact .succ _ _ _ _ (ih e)

/-- `Asmgenproof0.code_tail_next_int` -/
theorem code_tail_next_int {fn : Code} {ofs : Integers.Ptrofs} {i : Instruction} {c : Code}
    (hlen : (fn.length : Z) ≤ Integers.Ptrofs.max_unsigned)
    (h : CodeTail (Integers.Ptrofs.unsigned ofs) fn (i :: c)) :
    CodeTail (Integers.Ptrofs.unsigned (Integers.Ptrofs.add ofs Integers.Ptrofs.one)) fn c := by
  rw [Integers.Ptrofs.add_unsigned, Integers.Ptrofs.unsigned_one]
  have := code_tail_bounds_2 h
  rw [Integers.Ptrofs.unsigned_repr (by zomega) (by zomega)]
  exact code_tail_next h

/-- `Asmgenproof0.transl_code_at_pc` -/
inductive TranslCodeAtPc (ge : Mach.CGenv) :
    Val → Block → Mach.Function → Mach.Code → Bool → Asm.Function → Asm.Code → Prop where
  | intro (b : Block) (ofs : Integers.Ptrofs) (f : Mach.Function) (c : Mach.Code) (ep : Bool)
      (tf : Asm.Function) (tc : Asm.Code) :
      Genv.findFunctPtr ge b = some (.Internal f) →
      transfFunction f = .OK tf →
      translCode f c ep = .OK tc →
      CodeTail (Integers.Ptrofs.unsigned ofs) tf.fn_code tc →
      TranslCodeAtPc ge (.Vptr b ofs) b f c ep tf tc

/-! ## Return addresses -/

/-- `Asmgenproof0.return_address_offset`: `ofs` is the offset of the Asm
    instruction following the call, in the code generated for `f`. -/
def ReturnAddressOffset (f : Mach.Function) (c : Mach.Code)
    (ofs : Integers.Ptrofs) : Prop :=
  ∀ tf tc, transfFunction f = .OK tf → translCode f c false = .OK tc →
    CodeTail (Integers.Ptrofs.unsigned ofs) tf.fn_code tc

/-- `Asmgenproof0.is_tail_code_tail` -/
theorem is_tail_code_tail {c1 c2 : Code} (h : c1 <:+ c2) : ∃ ofs, CodeTail ofs c2 c1 := by
  obtain ⟨l, rfl⟩ := h
  induction l with
  | nil => exact ⟨0, .zero _⟩
  | cons a l ih =>
    obtain ⟨ofs, h⟩ := ih
    exact ⟨ofs + 1, .succ _ _ _ _ h⟩

section RETADDR_EXISTS
variable
  (transl_instr_tail : ∀ f i ep k c, translInstr f i ep k = .OK c → k <:+ c)
  (transf_function_inv : ∀ f tf, transfFunction f = .OK tf →
    ∃ tc ep, translCode f f.fn_code ep = .OK tc ∧ tc <:+ tf.fn_code)
  (transf_function_len : ∀ f tf, transfFunction f = .OK tf →
    (tf.fn_code.length : Z) ≤ Integers.Ptrofs.max_unsigned)

include transl_instr_tail in
/-- `Asmgenproof0.transl_code_tail` -/
theorem transl_code_tail (f : Mach.Function) {c1 c2 : Mach.Code} (h : c1 <:+ c2) :
    ∀ {tc2 : Code} {ep2 : Bool}, translCode f c2 ep2 = .OK tc2 →
      ∃ tc1 ep1, translCode f c1 ep1 = .OK tc1 ∧ tc1 <:+ tc2 := by
  obtain ⟨l, rfl⟩ := h
  induction l with
  | nil => intro tc2 ep2 h; exact ⟨tc2, ep2, h, List.suffix_refl _⟩
  | cons a l ih =>
    intro tc2 ep2 h
    simp only [List.cons_append, translCode] at h
    cases e : translCode f (l ++ c1) (it1IsParent ep2 a) with
    | Error _ => rw [e] at h; cases h
    | OK x =>
      rw [e] at h
      obtain ⟨tc1, ep1, A, B⟩ := ih e
      exact ⟨tc1, ep1, A, B.trans (transl_instr_tail _ _ _ _ _ h)⟩

include transl_instr_tail transf_function_inv transf_function_len in
/-- `Asmgenproof0.return_address_exists` -/
theorem return_address_exists (f : Mach.Function) (sg : Signature) (ros : Sum Mreg Ident)
    (c : Mach.Code) (h : (Mach.Instruction.Mcall sg ros :: c) <:+ f.fn_code) :
    ∃ ra, ReturnAddressOffset f c ra := by
  cases TF : transfFunction f with
  | Error _ => exact ⟨Integers.Ptrofs.zero, fun tf _ h _ => by rw [TF] at h; cases h⟩
  | OK tf =>
    obtain ⟨tc1, ep1, TR1, TL1⟩ := transf_function_inv _ _ TF
    obtain ⟨tc2, ep2, TR2, TL2⟩ := transl_code_tail transl_instr_tail f h TR1
    simp only [translCode] at TR2
    cases e : translCode f c (it1IsParent ep2 (.Mcall sg ros)) with
    | Error _ => rw [e] at TR2; cases TR2
    | OK x =>
      rw [e] at TR2
      have e' : translCode f c false = .OK x := by
        cases ros <;> exact e
      have TL3 : x <:+ tf.fn_code :=
        ((transl_instr_tail _ _ _ _ _ TR2).trans TL2).trans TL1
      obtain ⟨ofs, CT⟩ := is_tail_code_tail TL3
      refine ⟨Integers.Ptrofs.repr ofs, fun tf' tc' h1 h2 => ?_⟩
      rw [TF] at h1; cases h1
      rw [e'] at h2; cases h2
      have := code_tail_bounds_1 CT
      have := transf_function_len _ _ TF
      rw [Integers.Ptrofs.unsigned_repr (by zomega) (by zomega)]
      exact CT

end RETADDR_EXISTS

/-- `Asmgenproof0.code_tail_no_bigger` -/
theorem code_tail_no_bigger {pos : Z} {c1 c2 : Code} (h : CodeTail pos c1 c2) :
    c2.length ≤ c1.length := by
  induction h with
  | zero => exact Nat.le_refl _
  | succ _ _ _ _ _ ih => simp only [List.length_cons]; zomega

/-- `Asmgenproof0.code_tail_unique` -/
theorem code_tail_unique : ∀ {fn c : Code} {pos pos' : Z},
    CodeTail pos fn c → CodeTail pos' fn c → pos = pos'
  | [], _, _, _, h1, h2 => by cases h1; cases h2; rfl
  | a :: fn, c, pos, pos', h1, h2 => by
    cases h1 with
    | zero =>
      cases h2 with
      | zero => rfl
      | succ _ _ _ _ h => have := code_tail_no_bigger h; simp at this; zomega
    | succ p _ _ _ h1' =>
      cases h2 with
      | zero => have := code_tail_no_bigger h1'; simp at this; zomega
      | succ p' _ _ _ h2' => rw [code_tail_unique h1' h2']

/-- `Asmgenproof0.return_address_offset_correct` -/
theorem return_address_offset_correct {ge : Mach.CGenv} {b : Block}
    {ofs : Integers.Ptrofs} {fb : Block} {f : Mach.Function} {c : Mach.Code} {tf : Asm.Function}
    {tc : Code} {ofs' : Integers.Ptrofs}
    (h : TranslCodeAtPc ge (.Vptr b ofs) fb f c false tf tc)
    (hr : ReturnAddressOffset f c ofs') : ofs' = ofs := by
  cases h with
  | intro _ _ _ _ _ _ _ _ TF TC CT =>
    have := code_tail_unique CT (hr _ _ TF TC)
    rw [← Integers.Ptrofs.repr_unsigned ofs, ← Integers.Ptrofs.repr_unsigned ofs', this]

/-! ## Labels -/

/-- `Asmgenproof0.find_label` -/
def findLabel (lbl : Label) : Code → Option Code
  | [] => none
  | instr :: c' => if isLabel lbl instr then some c' else findLabel lbl c'

/-- `Asmgenproof0.label_pos_code_tail` -/
theorem label_pos_code_tail (lbl : Label) : ∀ (c : Code) (pos : Z) {c' : Code},
    findLabel lbl c = some c' →
    ∃ pos', labelPos lbl pos c = some pos' ∧ CodeTail (pos' - pos) c c' ∧
      pos < pos' ∧ pos' ≤ pos + c.length
  | [], _, _, h => by simp [findLabel] at h
  | a :: c, pos, c', h => by
    simp only [findLabel] at h
    simp only [labelPos]
    split at h
    · rename_i hl
      cases h
      refine ⟨pos + 1, by simp [hl], ?_, by zomega, by simp only [List.length_cons]; zomega⟩
      rw [show pos + 1 - pos = 0 + 1 by zomega]
      exact .succ _ _ _ _ (.zero _)
    · rename_i hl
      obtain ⟨pos', A, B, C⟩ := label_pos_code_tail lbl c (pos + 1) h
      refine ⟨pos', by simp [hl, A], ?_, by zomega, by simp only [List.length_cons]; zomega⟩
      rw [show pos' - pos = (pos' - (pos + 1)) + 1 by zomega]
      exact .succ _ _ _ _ B

/-- `Asmgenproof0.tail_nolabel` -/
def TailNolabel (k c : Code) : Prop :=
  k <:+ c ∧ ∀ lbl, findLabel lbl c = findLabel lbl k

/-- `Asmgenproof0.tail_nolabel_refl` -/
theorem tail_nolabel_refl (c : Code) : TailNolabel c c := ⟨List.suffix_refl _, fun _ => rfl⟩

/-- `Asmgenproof0.tail_nolabel_trans` -/
theorem tail_nolabel_trans {c1 c2 c3 : Code} (h1 : TailNolabel c2 c3) (h2 : TailNolabel c1 c2) :
    TailNolabel c1 c3 :=
  ⟨h2.1.trans h1.1, fun lbl => (h1.2 lbl).trans (h2.2 lbl)⟩

/-- `Asmgenproof0.nolabel` -/
def Nolabel (i : Instruction) : Prop :=
  match i with
  | .Plabel _ => False
  | _ => True

/-- `Asmgenproof0.tail_nolabel_cons` -/
theorem tail_nolabel_cons {i : Instruction} {c k : Code} (hi : Nolabel i) (h : TailNolabel k c) :
    TailNolabel k (i :: c) := by
  refine ⟨h.1.trans (List.suffix_cons _ _), fun lbl => ?_⟩
  rw [← h.2 lbl]
  simp only [findLabel]
  have : isLabel lbl i = false := by
    cases i <;> simp_all [isLabel, Nolabel]
  rw [this]; rfl

/-- `Asmgenproof0.tail_nolabel_find_label` -/
theorem tail_nolabel_find_label (lbl : Label) {k c : Code} (h : TailNolabel k c) :
    findLabel lbl c = findLabel lbl k := h.2 lbl

/-- `Asmgenproof0.tail_nolabel_is_tail` -/
theorem tail_nolabel_is_tail {k c : Code} (h : TailNolabel k c) : k <:+ c := h.1

/-! ## Execution of straight-line code -/

section STRAIGHTLINE
variable (ge : Asm.CGenv) (fn : Asm.Function)

/-- `Asmgenproof0.exec_straight`: straight-line execution of a sequence of
    instructions taken from the first list. -/
inductive ExecStraight : Code → Regset → Mem → Code → Regset → Mem → Prop where
  | one (i1 : Instruction) (c : Code) (rs1 : Regset) (m1 : Mem) (rs2 : Regset) (m2 : Mem) :
      execInstr ge fn i1 rs1 m1 = .Next rs2 m2 →
      rs2 .PC = Val.offsetPtr (rs1 .PC) Integers.Ptrofs.one →
      ExecStraight (i1 :: c) rs1 m1 c rs2 m2
  | step (i : Instruction) (c : Code) (rs1 : Regset) (m1 : Mem) (rs2 : Regset) (m2 : Mem)
      (c' : Code) (rs3 : Regset) (m3 : Mem) :
      execInstr ge fn i rs1 m1 = .Next rs2 m2 →
      rs2 .PC = Val.offsetPtr (rs1 .PC) Integers.Ptrofs.one →
      ExecStraight c rs2 m2 c' rs3 m3 →
      ExecStraight (i :: c) rs1 m1 c' rs3 m3

/-- `Asmgenproof0.exec_straight_opt`: a variant allowing zero steps. -/
inductive ExecStraightOpt : Code → Regset → Mem → Code → Regset → Mem → Prop where
  | refl (c : Code) (rs : Regset) (m : Mem) : ExecStraightOpt c rs m c rs m
  | intro (c1 : Code) (rs1 : Regset) (m1 : Mem) (c2 : Code) (rs2 : Regset) (m2 : Mem) :
      ExecStraight ge fn c1 rs1 m1 c2 rs2 m2 → ExecStraightOpt c1 rs1 m1 c2 rs2 m2

variable {ge fn}

/-- `Asmgenproof0.exec_straight_trans` -/
theorem exec_straight_trans {c1 : Code} {rs1 : Regset} {m1 : Mem} {c2 : Code} {rs2 : Regset}
    {m2 : Mem} {c3 : Code} {rs3 : Regset} {m3 : Mem}
    (h1 : ExecStraight ge fn c1 rs1 m1 c2 rs2 m2)
    (h2 : ExecStraight ge fn c2 rs2 m2 c3 rs3 m3) :
    ExecStraight ge fn c1 rs1 m1 c3 rs3 m3 := by
  induction h1 with
  | one i c rs1 m1 rs2 m2 e p => exact .step _ _ _ _ _ _ _ _ _ e p h2
  | step i c rs1 m1 rs2 m2 c' rs3 m3 e p _ ih => exact .step _ _ _ _ _ _ _ _ _ e p (ih h2)

/-- `Asmgenproof0.exec_straight_two` -/
theorem exec_straight_two {i1 i2 : Instruction} {c : Code} {rs1 : Regset} {m1 : Mem}
    {rs2 : Regset} {m2 : Mem} {rs3 : Regset} {m3 : Mem}
    (e1 : execInstr ge fn i1 rs1 m1 = .Next rs2 m2)
    (e2 : execInstr ge fn i2 rs2 m2 = .Next rs3 m3)
    (p1 : rs2 .PC = Val.offsetPtr (rs1 .PC) Integers.Ptrofs.one)
    (p2 : rs3 .PC = Val.offsetPtr (rs2 .PC) Integers.Ptrofs.one) :
    ExecStraight ge fn (i1 :: i2 :: c) rs1 m1 c rs3 m3 :=
  .step _ _ _ _ _ _ _ _ _ e1 p1 (.one _ _ _ _ _ _ e2 p2)

/-- `Asmgenproof0.exec_straight_three` -/
theorem exec_straight_three {i1 i2 i3 : Instruction} {c : Code} {rs1 : Regset} {m1 : Mem}
    {rs2 : Regset} {m2 : Mem} {rs3 : Regset} {m3 : Mem} {rs4 : Regset} {m4 : Mem}
    (e1 : execInstr ge fn i1 rs1 m1 = .Next rs2 m2)
    (e2 : execInstr ge fn i2 rs2 m2 = .Next rs3 m3)
    (e3 : execInstr ge fn i3 rs3 m3 = .Next rs4 m4)
    (p1 : rs2 .PC = Val.offsetPtr (rs1 .PC) Integers.Ptrofs.one)
    (p2 : rs3 .PC = Val.offsetPtr (rs2 .PC) Integers.Ptrofs.one)
    (p3 : rs4 .PC = Val.offsetPtr (rs3 .PC) Integers.Ptrofs.one) :
    ExecStraight ge fn (i1 :: i2 :: i3 :: c) rs1 m1 c rs4 m4 :=
  .step _ _ _ _ _ _ _ _ _ e1 p1 (exec_straight_two e2 e3 p2 p3)

/-- `Asmgenproof0.exec_straight_steps_1` -/
theorem exec_straight_steps_1 (win64 : Bool) {c : Code} {rs : Regset} {m : Mem} {c' : Code}
    {rs' : Regset} {m' : Mem} (h : ExecStraight ge fn c rs m c' rs' m')
    (hlen : (fn.fn_code.length : Z) ≤ Integers.Ptrofs.max_unsigned) :
    ∀ {b : Block} {ofs : Integers.Ptrofs}, rs .PC = .Vptr b ofs →
      Genv.findFunctPtr ge b = some (.Internal fn) →
      CodeTail (Integers.Ptrofs.unsigned ofs) fn.fn_code c →
      Smallstep.Plus (Asm.Step win64 ge) (Asm.State.State rs m) E0 (Asm.State.State rs' m') := by
  induction h with
  | one i1 c rs1 m1 rs2 m2 e p =>
    intro b ofs hpc hf ct
    exact plus_one (Asm.Step.exec_step_internal _ _ _ _ _ _ _ _ hpc hf (find_instr_tail ct) e)
  | step i c rs1 m1 rs2 m2 c' rs3 m3 e p _ ih =>
    intro b ofs hpc hf ct
    refine plus_left (Asm.Step.exec_step_internal _ _ _ _ _ _ _ _ hpc hf (find_instr_tail ct) e)
      (plus_star (ih (ofs := Integers.Ptrofs.add ofs Integers.Ptrofs.one) ?_ hf
        (code_tail_next_int hlen ct))) (E0_left _).symm
    rw [p, hpc]; rfl

/-- `Asmgenproof0.exec_straight_steps_2` -/
theorem exec_straight_steps_2 {c : Code} {rs : Regset} {m : Mem} {c' : Code}
    {rs' : Regset} {m' : Mem} (h : ExecStraight ge fn c rs m c' rs' m')
    (hlen : (fn.fn_code.length : Z) ≤ Integers.Ptrofs.max_unsigned) :
    ∀ {b : Block} {ofs : Integers.Ptrofs}, rs .PC = .Vptr b ofs →
      Genv.findFunctPtr ge b = some (.Internal fn) →
      CodeTail (Integers.Ptrofs.unsigned ofs) fn.fn_code c →
      ∃ ofs', rs' .PC = .Vptr b ofs' ∧ CodeTail (Integers.Ptrofs.unsigned ofs') fn.fn_code c' := by
  induction h with
  | one i1 c rs1 m1 rs2 m2 e p =>
    intro b ofs hpc hf ct
    exact ⟨Integers.Ptrofs.add ofs Integers.Ptrofs.one, by rw [p, hpc]; rfl,
      code_tail_next_int hlen ct⟩
  | step i c rs1 m1 rs2 m2 c' rs3 m3 e p _ ih =>
    intro b ofs hpc hf ct
    exact ih (by rw [p, hpc]; rfl) hf (code_tail_next_int hlen ct)

/-- `Asmgenproof0.exec_straight_opt_left` -/
theorem exec_straight_opt_left {c3 : Code} {rs3 : Regset} {m3 : Mem} {c1 : Code} {rs1 : Regset}
    {m1 : Mem} {c2 : Code} {rs2 : Regset} {m2 : Mem}
    (h1 : ExecStraight ge fn c1 rs1 m1 c2 rs2 m2)
    (h2 : ExecStraightOpt ge fn c2 rs2 m2 c3 rs3 m3) :
    ExecStraight ge fn c1 rs1 m1 c3 rs3 m3 := by
  cases h2 with
  | refl => exact h1
  | intro => rename_i h; exact exec_straight_trans h1 h

/-- `Asmgenproof0.exec_straight_opt_right` -/
theorem exec_straight_opt_right {c3 : Code} {rs3 : Regset} {m3 : Mem} {c1 : Code} {rs1 : Regset}
    {m1 : Mem} {c2 : Code} {rs2 : Regset} {m2 : Mem}
    (h1 : ExecStraightOpt ge fn c1 rs1 m1 c2 rs2 m2)
    (h2 : ExecStraight ge fn c2 rs2 m2 c3 rs3 m3) :
    ExecStraight ge fn c1 rs1 m1 c3 rs3 m3 := by
  cases h1 with
  | refl => exact h2
  | intro => rename_i h; exact exec_straight_trans h h2

/-- `Asmgenproof0.exec_straight_opt_step` -/
theorem exec_straight_opt_step {i : Instruction} {c : Code} {rs1 : Regset} {m1 : Mem}
    {rs2 : Regset} {m2 : Mem} {c' : Code} {rs3 : Regset} {m3 : Mem}
    (e : execInstr ge fn i rs1 m1 = .Next rs2 m2)
    (p : rs2 .PC = Val.offsetPtr (rs1 .PC) Integers.Ptrofs.one)
    (h : ExecStraightOpt ge fn c rs2 m2 c' rs3 m3) :
    ExecStraight ge fn (i :: c) rs1 m1 c' rs3 m3 := by
  cases h with
  | refl => exact .one _ _ _ _ _ _ e p
  | intro => rename_i h; exact .step _ _ _ _ _ _ _ _ _ e p h

/-- `Asmgenproof0.exec_straight_opt_step_opt` -/
theorem exec_straight_opt_step_opt {i : Instruction} {c : Code} {rs1 : Regset} {m1 : Mem}
    {rs2 : Regset} {m2 : Mem} {c' : Code} {rs3 : Regset} {m3 : Mem}
    (e : execInstr ge fn i rs1 m1 = .Next rs2 m2)
    (p : rs2 .PC = Val.offsetPtr (rs1 .PC) Integers.Ptrofs.one)
    (h : ExecStraightOpt ge fn c rs2 m2 c' rs3 m3) :
    ExecStraightOpt ge fn (i :: c) rs1 m1 c' rs3 m3 :=
  .intro _ _ _ _ _ _ (exec_straight_opt_step e p h)

end STRAIGHTLINE

/-! ## Properties of the Mach call stack -/

section MATCH_STACK
variable (ge : Mach.CGenv)

/-- `Asmgenproof0.match_stack` -/
inductive MatchStack : List Mach.Stackframe → Prop where
  | nil : MatchStack []
  | cons (fb : Block) (sp ra : Val) (c : Mach.Code) (s : List Mach.Stackframe)
      (f : Mach.Function) (tf : Asm.Function) (tc : Code) :
      Genv.findFunctPtr ge fb = some (.Internal f) →
      TranslCodeAtPc ge ra fb f c false tf tc →
      sp ≠ .Vundef →
      MatchStack s →
      MatchStack (.Stackframe fb sp ra c :: s)

variable {ge}

/-- `Asmgenproof0.parent_sp_def` -/
theorem parent_sp_def : ∀ {s : List Mach.Stackframe}, MatchStack ge s →
    Mach.parentSp s ≠ .Vundef
  | [], _ => by simp [Mach.parentSp, Val.Vnullptr]
  | _ :: _, .cons _ _ _ _ _ _ _ _ _ _ hsp _ => hsp

/-- `Asmgenproof0.parent_ra_def` -/
theorem parent_ra_def : ∀ {s : List Mach.Stackframe}, MatchStack ge s →
    Mach.parentRa s ≠ .Vundef
  | [], _ => by simp [Mach.parentRa, Val.Vnullptr]
  | _ :: _, .cons _ _ _ _ _ _ _ _ _ ht _ _ => by cases ht; simp [Mach.parentRa]

/-- `Asmgenproof0.lessdef_parent_sp` -/
theorem lessdef_parent_sp {s : List Mach.Stackframe} {v : Val} (h : MatchStack ge s)
    (hl : Val.Lessdef (Mach.parentSp s) v) : v = Mach.parentSp s := by
  generalize hp : Mach.parentSp s = p at hl ⊢
  cases hl with
  | refl => rfl
  | undef => exact absurd hp (parent_sp_def h)

/-- `Asmgenproof0.lessdef_parent_ra` -/
theorem lessdef_parent_ra {s : List Mach.Stackframe} {v : Val} (h : MatchStack ge s)
    (hl : Val.Lessdef (Mach.parentRa s) v) : v = Mach.parentRa s := by
  generalize hp : Mach.parentRa s = p at hl ⊢
  cases hl with
  | refl => rfl
  | undef => exact absurd hp (parent_ra_def h)

end MATCH_STACK

end Asmgenproof0
end X86
end CC
