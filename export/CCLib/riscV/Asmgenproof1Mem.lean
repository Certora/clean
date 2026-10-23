/-
  Correctness proof for RISC-V code generation: auxiliary results, part 4 —
  memory accesses and function epilogues (port of the end of
  `riscV/Asmgenproof1.v`: `indexed_memory_access_correct` through
  `make_epilogue_correct`).

  Differences from Rocq: the port's target is 64-bit (`Archi.ptr64 = true`),
  so only the 64-bit branch of `indexed_memory_access` is reachable and is
  the one treated here.
-/
import CCLib.riscV.Asmgenproof1Op

namespace CC
namespace RiscV
namespace Asmgenproof1

open Asm Asmgen Asmgenproof0 Smallstep Conventions1 Op

theorem ptrofs_of_int64_add (a b : Integers.Int64) :
    Integers.Ptrofs.of_int64 (Integers.Int64.add a b) =
      Integers.Ptrofs.add (Integers.Ptrofs.of_int64 a) (Integers.Ptrofs.of_int64 b) := by
  simp only [Integers.Ptrofs.of_int64, Integers.Int64.add, Integers.Ptrofs.add, Integers.MI.repr,
    Integers.MI.unsigned, Integers.MI.add]
  apply BitVec.eq_of_toNat_eq
  simp
  show _ = ((a : BitVec 64) + (b : BitVec 64)).toNat
  rw [BitVec.toNat_add]
  omega

/-- `Val.offset_ptr (Val.addl v (Vlong n)) d = Val.offset_ptr v (of_int64 n + d)`
on 64-bit targets. -/
theorem offsetPtr_addl_long (v : Val) (n : Integers.Int64) (d : Integers.Ptrofs) :
    Val.offsetPtr (Val.addl v (.Vlong n)) d =
      Val.offsetPtr v (Integers.Ptrofs.add (Integers.Ptrofs.of_int64 n) d) := by
  cases v <;> simp [Val.addl, Val.offsetPtr, Archi.ptr64, Integers.Ptrofs.add_assoc]

section CONSTRUCTORS
variable {sym : HalfSplit} {ge : Asm.CGenv} {fn : Asm.Function}

/-- `Asmgenproof1.indexed_memory_access_correct` -/
theorem indexed_memory_access_correct (mk : Ireg → Offset → Instruction) (base : Ireg)
    (ofs : Integers.Ptrofs) (k : Code) (rs : Regset) (m : Mem) (hb : base ≠ .X31) :
    ∃ base' ofs' rs', ExecStraightOpt sym ge fn (indexedMemoryAccess mk base ofs k) rs m
        (mk base' ofs' :: k) rs' m ∧
      Val.offsetPtr (rs' (.IR base')) (evalOffset sym ge ofs') =
        Val.offsetPtr (rs (.IR base)) ofs ∧
      ∀ r, r ≠ .PC → r ≠ .IR .X31 → rs' r = rs r := by
  have hb' : Preg.IR base ≠ .IR .X31 := fun e => hb (Preg.IR.inj e)
  unfold indexedMemoryAccess
  rw [if_pos (show Archi.ptr64 = true from rfl)]
  have E := make_immed64_sound (Integers.Ptrofs.to_int64 ofs)
  split
  · rename_i imm heq
    rw [heq] at E
    refine ⟨base, _, rs, .refl _ _ _, ?_, fun _ _ _ => rfl⟩
    show Val.offsetPtr _ (Integers.Ptrofs.of_int64 imm) = _
    rw [← E, ptrofs_of_int64_to_int64]
  · rename_i hi lo heq
    rw [heq] at E
    refine ⟨_, _, _, .intro _ _ _ _ _ _ (.step _ _ _ _ _ _ _ _ _ rfl
      (nextinstr_set_pc _ _ (ir_ne_pc _)) (.one _ _ _ _ _ _ rfl
        (nextinstr_set_pc _ _ (ir_ne_pc _)))), ?_, fun r h1 h2 => ?_⟩
    · show Val.offsetPtr (nextinstr (Regset.set _ (.IR .X31) _) (.IR .X31))
        (Integers.Ptrofs.of_int64 lo) = _
      rw [nextinstr_set_same _ _ (ir_ne_pc _)]
      simp only [get0l]
      rw [nextinstr_set_same _ _ (ir_ne_pc _), nextinstr_set_other _ _ (ir_ne_pc _) hb',
        offsetPtr_addl_long, ← ptrofs_of_int64_add, ← E, ptrofs_of_int64_to_int64]
    · rw [nextinstr_set_other _ _ h1 h2, nextinstr_set_other _ _ h1 h2]
  · rename_i imm heq
    rw [heq] at E
    refine ⟨_, _, _, .intro _ _ _ _ _ _ (.step _ _ _ _ _ _ _ _ _ rfl
      (nextinstr_set_pc _ _ (ir_ne_pc _)) (.one _ _ _ _ _ _ rfl
        (nextinstr_set_pc _ _ (ir_ne_pc _)))), ?_, fun r h1 h2 => ?_⟩
    · show Val.offsetPtr (nextinstr (Regset.set _ (.IR .X31) _) (.IR .X31))
        Integers.Ptrofs.zero = _
      rw [nextinstr_set_same _ _ (ir_ne_pc _)]
      simp only [get0l]
      rw [nextinstr_set_same _ _ (ir_ne_pc _), nextinstr_set_other _ _ (ir_ne_pc _) hb',
        Regset.gso _ _ hb', offsetPtr_addl_long, Integers.Ptrofs.add_zero, ← E,
        ptrofs_of_int64_to_int64]
    · rw [nextinstr_set_other _ _ h1 h2, nextinstr_set_other _ _ h1 h2, Regset.gso _ _ h2]

/-- `Asmgenproof1.indexed_load_access_correct` -/
theorem indexed_load_access_correct (chunk : Chunk) (mk : Ireg → Offset → Instruction)
    (rd : Preg) (m : Mem)
    (EXEC : ∀ base ofs rs, execInstr sym ge fn (mk base ofs) rs m =
      execLoad sym ge chunk rs m rd base ofs)
    (base : Ireg) (ofs : Integers.Ptrofs) (k : Code) (rs : Regset) (v : Val)
    (LOAD : Mem.loadv chunk m (Val.offsetPtr (rs (.IR base)) ofs) = some v)
    (hb : base ≠ .X31) (hrd : rd ≠ .PC) :
    ∃ rs', ExecStraight sym ge fn (indexedMemoryAccess mk base ofs k) rs m k rs' m ∧
      rs' rd = v ∧ ∀ r, r ≠ .PC → r ≠ .IR .X31 → r ≠ rd → rs' r = rs r := by
  obtain ⟨b', o', rs', A, B, C⟩ :=
    indexed_memory_access_correct (sym := sym) (ge := ge) (fn := fn) mk base ofs k rs m hb
  refine ⟨_, exec_straight_opt_right A (.one _ _ _ _ _ _ ?_ (nextinstr_set_pc _ _ hrd)),
    nextinstr_set_same _ _ hrd, fun r h1 h2 h3 => ?_⟩
  · rw [EXEC]; unfold execLoad; rw [B, LOAD]
  · rw [nextinstr_set_other _ _ h1 h3, C r h1 h2]

/-- `Asmgenproof1.indexed_store_access_correct` -/
theorem indexed_store_access_correct (chunk : Chunk) (mk : Ireg → Offset → Instruction)
    (r1 : Preg) (m : Mem)
    (EXEC : ∀ base ofs rs, execInstr sym ge fn (mk base ofs) rs m =
      execStore sym ge chunk rs m r1 base ofs)
    (base : Ireg) (ofs : Integers.Ptrofs) (k : Code) (rs : Regset) (m' : Mem)
    (STORE : Mem.storev chunk m (Val.offsetPtr (rs (.IR base)) ofs) (rs r1) = some m')
    (hb : base ≠ .X31) (h31 : r1 ≠ .IR .X31) (hpc : r1 ≠ .PC) :
    ∃ rs', ExecStraight sym ge fn (indexedMemoryAccess mk base ofs k) rs m k rs' m' ∧
      ∀ r, r ≠ .PC → r ≠ .IR .X31 → rs' r = rs r := by
  obtain ⟨b', o', rs', A, B, C⟩ :=
    indexed_memory_access_correct (sym := sym) (ge := ge) (fn := fn) mk base ofs k rs m hb
  refine ⟨_, exec_straight_opt_right A (.one _ _ _ _ _ _ ?_ (nextinstr_pc _)),
    fun r h1 h2 => ?_⟩
  · rw [EXEC]; unfold execStore; rw [B, C r1 hpc h31, STORE]
  · rw [nextinstr_inv _ h1, C r h1 h2]

/-- `Asmgenproof1.loadind_correct` -/
theorem loadind_correct (base : Ireg) (ofs : Integers.Ptrofs) (ty : ATyp) (dst : Mreg)
    (k c : Code) (rs : Regset) (m : Mem) (v : Val)
    (TR : loadind base ofs ty dst k = .OK c)
    (LOAD : Mem.loadv (Chunk.ofTyp ty) m (Val.offsetPtr (rs (.IR base)) ofs) = some v)
    (hb : base ≠ .X31) :
    ∃ rs', ExecStraight sym ge fn c rs m k rs' m ∧ rs' (pregOf dst) = v ∧
      ∀ r, r ≠ .PC → r ≠ .IR .X31 → r ≠ pregOf dst → rs' r = rs r := by
  have X : ∃ mk, c = indexedMemoryAccess mk base ofs k ∧
      ∀ b o rs', execInstr sym ge fn (mk b o) rs' m =
        execLoad sym ge (Chunk.ofTyp ty) rs' m (pregOf dst) b o := by
    unfold loadind at TR
    split at TR <;> cases TR <;> rename_i e <;> rw [e] <;> exact ⟨_, rfl, fun _ _ _ => rfl⟩
  obtain ⟨mk, rfl, SEM⟩ := X
  exact indexed_load_access_correct _ mk _ m SEM base ofs k rs v LOAD hb (preg_of_not_PC dst)

/-- `Asmgenproof1.storeind_correct` -/
theorem storeind_correct (base : Ireg) (ofs : Integers.Ptrofs) (ty : ATyp) (src : Mreg)
    (k c : Code) (rs : Regset) (m m' : Mem)
    (TR : storeind src base ofs ty k = .OK c)
    (STORE : Mem.storev (Chunk.ofTyp ty) m (Val.offsetPtr (rs (.IR base)) ofs)
      (rs (pregOf src)) = some m')
    (hb : base ≠ .X31) :
    ∃ rs', ExecStraight sym ge fn c rs m k rs' m' ∧
      ∀ r, r ≠ .PC → r ≠ .IR .X31 → rs' r = rs r := by
  have X : ∃ mk, c = indexedMemoryAccess mk base ofs k ∧
      ∀ b o rs', execInstr sym ge fn (mk b o) rs' m =
        execStore sym ge (Chunk.ofTyp ty) rs' m (pregOf src) b o := by
    unfold storeind at TR
    split at TR <;> cases TR <;> rename_i e <;> rw [e] <;> exact ⟨_, rfl, fun _ _ _ => rfl⟩
  obtain ⟨mk, rfl, SEM⟩ := X
  exact indexed_store_access_correct _ mk _ m SEM base ofs k rs m' STORE hb
    (preg_of_not_X31 src) (preg_of_not_PC src)

/-- `Asmgenproof1.loadind_ptr_correct` -/
theorem loadind_ptr_correct (base : Ireg) (ofs : Integers.Ptrofs) (dst : Ireg) (k : Code)
    (rs : Regset) (m : Mem) (v : Val)
    (LOAD : Mem.loadv Mptr m (Val.offsetPtr (rs (.IR base)) ofs) = some v)
    (hb : base ≠ .X31) :
    ∃ rs', ExecStraight sym ge fn (loadindPtr base ofs dst k) rs m k rs' m ∧
      rs' (.IR dst) = v ∧ ∀ r, r ≠ .PC → r ≠ .IR .X31 → r ≠ .IR dst → rs' r = rs r :=
  indexed_load_access_correct _ _ _ m (fun _ _ _ => rfl) base ofs k rs v LOAD hb (ir_ne_pc _)

/-- `Asmgenproof1.storeind_ptr_correct` -/
theorem storeind_ptr_correct (base : Ireg) (ofs : Integers.Ptrofs) (src : Ireg) (k : Code)
    (rs : Regset) (m m' : Mem)
    (STORE : Mem.storev Mptr m (Val.offsetPtr (rs (.IR base)) ofs) (rs (.IR src)) = some m')
    (hb : base ≠ .X31) (hsrc : src ≠ .X31) :
    ∃ rs', ExecStraight sym ge fn (storeindPtr src base ofs k) rs m k rs' m' ∧
      ∀ r, r ≠ .PC → r ≠ .IR .X31 → rs' r = rs r :=
  indexed_store_access_correct _ _ (.IR src) m (fun _ _ _ => rfl) base ofs k rs m' STORE hb
    (fun e => hsrc (Preg.IR.inj e)) (ir_ne_pc _)

/-- `Asmgenproof1.transl_memory_access_correct` -/
theorem transl_memory_access_correct (mk : Ireg → Offset → Instruction) (addr : Addressing)
    (args : List Mreg) (k c : Code) (rs : Regset) (m : Mem) (v : Val)
    (TR : translMemoryAccess mk addr args k = .OK c)
    (EV : evalAddressing ge (rs (.IR SP)) addr ((args.map pregOf).map rs) = some v) :
    ∃ base ofs rs', ExecStraightOpt sym ge fn c rs m (mk base ofs :: k) rs' m ∧
      Val.offsetPtr (rs' (.IR base)) (evalOffset sym ge ofs) = v ∧
      ∀ r, r ≠ .PC → r ≠ .IR .X31 → rs' r = rs r := by
  revert TR EV
  cases addr <;> rcases args with _ | ⟨a1, _ | ⟨a2, args⟩⟩ <;> intro TR EV <;>
    simp only [translMemoryAccess, res_bind_OK, res_pure_OK, reduceCtorEq, Res.OK.injEq] at TR <;>
    simp only [evalAddressing, List.map, Option.some.injEq] at EV
  · obtain ⟨r1, hr1, rfl⟩ := TR
    subst EV
    rw [ireg_of_eq hr1]
    exact indexed_memory_access_correct _ _ _ k rs m (ireg_of_not_X31' hr1)
  · subst TR EV
    refine ⟨_, _, _, .intro _ _ _ _ _ _ (.one _ _ _ _ _ _ rfl
      (nextinstr_set_pc _ _ (ir_ne_pc _))), ?_, fun r h1 h2 => nextinstr_set_other _ _ h1 h2⟩
    rw [nextinstr_set_same _ _ (ir_ne_pc _)]
    exact sym.low_high_half _ _ _
  · subst TR EV
    exact indexed_memory_access_correct _ _ _ k rs m (by decide)

/-- `Asmgenproof1.transl_load_access_correct` -/
theorem transl_load_access_correct (chunk : Chunk) (mk : Ireg → Offset → Instruction)
    (addr : Addressing) (args : List Mreg) (k c : Code) (rd : Preg) (rs : Regset) (m : Mem)
    (v v' : Val)
    (INSTR : ∀ base ofs rs, execInstr sym ge fn (mk base ofs) rs m =
      execLoad sym ge chunk rs m rd base ofs)
    (TR : translMemoryAccess mk addr args k = .OK c)
    (EV : evalAddressing ge (rs (.IR SP)) addr ((args.map pregOf).map rs) = some v)
    (LOAD : Mem.loadv chunk m v = some v') (hrd : rd ≠ .PC) :
    ∃ rs', ExecStraight sym ge fn c rs m k rs' m ∧ rs' rd = v' ∧
      ∀ r, r ≠ .PC → r ≠ .IR .X31 → r ≠ rd → rs' r = rs r := by
  obtain ⟨base, ofs, rs', A, B, C⟩ :=
    transl_memory_access_correct (sym := sym) mk addr args k c rs m v TR EV
  refine ⟨_, exec_straight_opt_right A (.one _ _ _ _ _ _ ?_ (nextinstr_set_pc _ _ hrd)),
    nextinstr_set_same _ _ hrd, fun r h1 h2 h3 => ?_⟩
  · rw [INSTR]; unfold execLoad; rw [B, LOAD]
  · rw [nextinstr_set_other _ _ h1 h3, C r h1 h2]

/-- `Asmgenproof1.transl_store_access_correct` -/
theorem transl_store_access_correct (chunk : Chunk) (mk : Ireg → Offset → Instruction)
    (addr : Addressing) (args : List Mreg) (k c : Code) (r1 : Preg) (rs : Regset) (m : Mem)
    (v : Val) (m' : Mem)
    (INSTR : ∀ base ofs rs, execInstr sym ge fn (mk base ofs) rs m =
      execStore sym ge chunk rs m r1 base ofs)
    (TR : translMemoryAccess mk addr args k = .OK c)
    (EV : evalAddressing ge (rs (.IR SP)) addr ((args.map pregOf).map rs) = some v)
    (STORE : Mem.storev chunk m v (rs r1) = some m') (hpc : r1 ≠ .PC) (h31 : r1 ≠ .IR .X31) :
    ∃ rs', ExecStraight sym ge fn c rs m k rs' m' ∧
      ∀ r, r ≠ .PC → r ≠ .IR .X31 → rs' r = rs r := by
  obtain ⟨base, ofs, rs', A, B, C⟩ :=
    transl_memory_access_correct (sym := sym) mk addr args k c rs m v TR EV
  refine ⟨_, exec_straight_opt_right A (.one _ _ _ _ _ _ ?_ (nextinstr_pc _)),
    fun r h1 h2 => ?_⟩
  · rw [INSTR]; unfold execStore; rw [B, C r1 hpc h31, STORE]
  · rw [nextinstr_inv _ h1, C r h1 h2]

/-- `Asmgenproof1.transl_load_correct` -/
theorem transl_load_correct (chunk : Chunk) (addr : Addressing) (args : List Mreg) (dst : Mreg)
    (k c : Code) (rs : Regset) (m : Mem) (a v : Val)
    (TR : translLoad chunk addr args dst k = .OK c)
    (EV : evalAddressing ge (rs (.IR SP)) addr ((args.map pregOf).map rs) = some a)
    (LOAD : Mem.loadv chunk m a = some v) :
    ∃ rs', ExecStraight sym ge fn c rs m k rs' m ∧ rs' (pregOf dst) = v ∧
      ∀ r, r ≠ .PC → r ≠ .IR .X31 → r ≠ pregOf dst → rs' r = rs r := by
  have X : ∃ mk, translMemoryAccess mk addr args k = .OK c ∧
      ∀ base ofs rs, execInstr sym ge fn (mk base ofs) rs m =
        execLoad sym ge chunk rs m (pregOf dst) base ofs := by
    cases chunk <;> simp only [translLoad, res_bind_OK, reduceCtorEq] at TR <;>
      obtain ⟨r, hr, TR⟩ := TR <;>
      first
        | (rw [ireg_of_eq hr]; exact ⟨_, TR, fun _ _ _ => rfl⟩)
        | (rw [freg_of_eq hr]; exact ⟨_, TR, fun _ _ _ => rfl⟩)
  obtain ⟨mk, B, C⟩ := X
  exact transl_load_access_correct chunk mk addr args k c _ rs m a v C B EV LOAD
    (preg_of_not_PC dst)

/-- `Asmgenproof1.transl_store_correct` -/
theorem transl_store_correct (chunk : Chunk) (addr : Addressing) (args : List Mreg) (src : Mreg)
    (k c : Code) (rs : Regset) (m : Mem) (a : Val) (m' : Mem)
    (TR : translStore chunk addr args src k = .OK c)
    (EV : evalAddressing ge (rs (.IR SP)) addr ((args.map pregOf).map rs) = some a)
    (STORE : Mem.storev chunk m a (rs (pregOf src)) = some m') :
    ∃ rs', ExecStraight sym ge fn c rs m k rs' m' ∧
      ∀ r, r ≠ .PC → r ≠ .IR .X31 → rs' r = rs r := by
  have X : ∃ mk, translMemoryAccess mk addr args k = .OK c ∧
      ∀ base ofs rs, execInstr sym ge fn (mk base ofs) rs m =
        execStore sym ge chunk rs m (pregOf src) base ofs := by
    cases chunk <;> simp only [translStore, res_bind_OK, reduceCtorEq] at TR <;>
      obtain ⟨r, hr, TR⟩ := TR <;>
      first
        | (rw [ireg_of_eq hr]; exact ⟨_, TR, fun _ _ _ => rfl⟩)
        | (rw [freg_of_eq hr]; exact ⟨_, TR, fun _ _ _ => rfl⟩)
  obtain ⟨mk, B, C⟩ := X
  exact transl_store_access_correct chunk mk addr args k c _ rs m a m' C B EV STORE
    (preg_of_not_PC src) (preg_of_not_X31 src)

theorem dataPreg_ne_RA {r : Preg} (h : dataPreg r = true) : r ≠ .IR RA := by
  rintro rfl; cases h

/-- `Asmgenproof1.make_epilogue_correct` -/
theorem make_epilogue_correct (o : Options) (ge0 : Mach.CGenv) (f : Mach.Function) (m : Mem)
    (stk : Block) (soff : Integers.Ptrofs) (cs : List Mach.Stackframe) (m' : Mem)
    (ms : Mach.Regset) (rs : Regset) (k : Code) (tm : Mem)
    (LP : Mach.loadStack m (.Vptr stk soff) Tptr f.fn_link_ofs = some (Mach.parentSp cs))
    (LRA : Mach.loadStack m (.Vptr stk soff) Tptr f.fn_retaddr_ofs = some (Mach.parentRa cs))
    (FREE : Mem.free m stk 0 f.fn_stacksize = some m')
    (AG : Agree ms (.Vptr stk soff) rs) (MEXT : Mem.Extends m tm) (MCS : MatchStack o ge0 cs) :
    ∃ rs' tm', ExecStraight sym ge fn (makeEpilogue f k) rs tm k rs' tm' ∧
      Agree ms (Mach.parentSp cs) rs' ∧ Mem.Extends m' tm' ∧
      rs' (.IR RA) = Mach.parentRa cs ∧ rs' (.IR SP) = Mach.parentSp cs ∧
      ∀ r, r ≠ .PC → r ≠ .IR RA → r ≠ .IR SP → r ≠ .IR .X31 → rs' r = rs r := by
  obtain ⟨parent', LP', LDP'⟩ := Mem.loadv_extends MEXT LP (.refl _)
  obtain ⟨ra', LRA', LDRA'⟩ := Mem.loadv_extends MEXT LRA (.refl _)
  have e1 := lessdef_parent_sp MCS LDP'
  have e2 := lessdef_parent_ra MCS LDRA'
  subst e1 e2
  obtain ⟨tm', FREE', MEXT'⟩ := Mem.free_parallel_extends MEXT FREE
  have hsp : rs (.IR SP) = .Vptr stk soff := AG.agree_sp
  obtain ⟨rs1, A1, B1, C1⟩ := loadind_ptr_correct (sym := sym) (ge := ge) (fn := fn) SP
    f.fn_retaddr_ofs RA (.Pfreeframe f.fn_stacksize f.fn_link_ofs :: k) rs tm _
    (by rw [hsp]; exact LRA') (by decide)
  have hsp1 : rs1 (.IR SP) = .Vptr stk soff := by
    rw [C1 _ (by simp) (by simp) (by simp), hsp]
  refine ⟨nextinstr ((rs1.set (.IR SP) (Mach.parentSp cs)).set (.IR .X31) .Vundef), tm',
    exec_straight_trans A1 (.one _ _ _ _ _ _ ?_ ?_), ?_, MEXT', ?_, ?_, ?_⟩
  · show (match Mem.loadv Mptr tm (Val.offsetPtr (rs1 (.IR SP)) f.fn_link_ofs) with
      | none => Outcome.Stuck
      | some v => match rs1 (.IR SP) with
        | .Vptr stk _ => match Mem.free tm stk 0 f.fn_stacksize with
          | none => .Stuck
          | some m' => .Next (nextinstr ((rs1.set (.IR SP) v).set (.IR .X31) .Vundef)) m'
        | _ => .Stuck) = _
    rw [hsp1]
    have : Mem.loadv Mptr tm (Val.offsetPtr (.Vptr stk soff) f.fn_link_ofs) =
      some (Mach.parentSp cs) := LP'
    rw [this]
    dsimp only
    rw [FREE']
  · exact nextinstr_pc _
  · exact agree_nextinstr (agree_set_other _ (agree_change_sp (agree_exten AG fun r hr =>
      C1 r (data_ne_pc hr) (data_ne_x31 hr) (dataPreg_ne_RA hr)) (parent_sp_def MCS)) rfl)
  · rw [nextinstr_inv _ (by simp), Regset.gso _ _ (by simp), Regset.gso _ _ (by simp), B1]
  · rw [nextinstr_inv _ (by simp), Regset.gso _ _ (by simp), Regset.gss]
  · intro r h1 h2 h3 h4
    rw [nextinstr_inv _ h1, Regset.gso _ _ h4, Regset.gso _ _ h3]
    exact C1 r h1 h4 h2

end CONSTRUCTORS

end Asmgenproof1
end RiscV
end CC
