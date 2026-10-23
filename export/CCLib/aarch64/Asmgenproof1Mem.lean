/-
  Correctness of the AArch64 code generator's constructor functions,
  part 6 — port of the "Translation of addressing modes, loads, stores",
  "Translation of indexed memory accesses" and epilogue sections of
  `aarch64/Asmgenproof1.v`: `transl_addressing_correct`,
  `transl_load_correct`, `transl_store_correct`,
  `indexed_memory_access_correct`, `loadptr_correct`, `storeptr_correct`,
  `loadind_correct`, `storeind_correct`.
-/
import CCLib.aarch64.Asmgenproof1Op

namespace CC
namespace Asmgenproof1

open Asm Asmgen Asmgenproof0 Smallstep Conventions1

theorem addl_zero_of_ptr {v : Val} {b : Block} {o : Integers.Ptrofs} (h : v = .Vptr b o) :
    Val.addl v (.Vlong Integers.Int64.zero) = .Vptr b o := by
  subst h
  show Val.Vptr b (Integers.Ptrofs.add o (Integers.Ptrofs.of_int64 Integers.Int64.zero)) = _
  congr 1
  apply BitVec.eq_of_toNat_eq
  show (BitVec.add o (BitVec.ofInt 64 ((0 : BitVec 64).toNat : _root_.Int))).toNat = o.toNat
  simpa using o.isLt

theorem offsetPtr_addl {v : Val} {ofs : Integers.Ptrofs} {b : Block} {i : Integers.Ptrofs}
    (h : Val.offsetPtr v ofs = .Vptr b i) :
    Val.addl v (.Vlong (Integers.Ptrofs.to_int64 ofs)) = .Vptr b i := by
  cases v <;> simp only [Val.offsetPtr, reduceCtorEq] at h
  simp only [Val.addl, ptrofs_of_int64_to_int64]
  exact h

theorem addl_shll_zero {v1 v2 : Val} {b : Block} {o : Integers.Ptrofs}
    (h : Val.addl v1 (Val.shll v2 (.Vint Integers.Int.zero)) = .Vptr b o) :
    Val.addl v1 v2 = .Vptr b o := by
  cases v2 with
  | Vlong n => rwa [shll_zero] at h
  | _ => cases v1 <;> simp [Val.shll, Val.addl] at h

theorem pregOfIregsp_ne_PC (r : Iregsp) : pregOfIregsp r ≠ .PC := by
  cases r <;> simp [pregOfIregsp]

section CONSTRUCTORS
variable (sym : SymbolSplit) (ge : Asm.CGenv) (fn : Asm.Function)

/-- `Asmgenproof1.transl_addressing_correct` -/
theorem transl_addressing_correct (o : Options) (sz : Z) (addr : Op.Addressing)
    (args : List Mreg) (insn : Asm.Addressing → Instruction) (k : Code) (rs : Regset) (m : Mem)
    (c : Code) (b : Block) (ofs : Integers.Ptrofs)
    (h : translAddressing o sz addr args insn k = .OK c)
    (hev : Op.evalAddressing ge (rs .SP) addr ((args.map pregOf).map rs) = some (.Vptr b ofs)) :
    ∃ ad rs', ExecStraightOpt sym ge fn c rs m (insn ad :: k) rs' m ∧
      evalAddressing sym ge ad rs' = .Vptr b ofs ∧
      ∀ r, dataPreg r = true → rs' r = rs r := by
  cases addr <;> rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, args⟩⟩⟩ <;>
    simp only [translAddressing, reduceCtorEq] at h
  case Aindexed.cons.nil n =>
    simp only [res_bind_OK] at h
    obtain ⟨r1, h1, h⟩ := h
    have e1 := ireg_of_eq h1
    simp only [List.map, e1, Op.evalAddressing, Option.some.injEq] at hev
    split at h <;> simp only [res_pure_OK] at h <;> subst h
    · exact ⟨_, rs, .refl _ _ _, hev, fun _ _ => rfl⟩
    · obtain ⟨rs', A, B, C⟩ := exec_loadimm64 sym ge fn .X16 n
        (insn (.ADreg (.RR1 r1) .X16) :: k) rs m
      refine ⟨_, rs', .intro _ _ _ _ _ _ A, ?_,
        fun r hr => C r (dataPreg_ne_PC hr) (dataPreg_ne_X16 hr)⟩
      show Val.addl (rs' (.IR r1)) (rs' (.IR .X16)) = _
      rw [B, C _ (by simp) (fun e => ne_X16_of e1 (Preg.IR.inj e))]; exact hev
  case Aindexed2.cons.cons.nil =>
    simp only [res_bind_OK, res_pure_OK] at h
    obtain ⟨r1, h1, r2, h2, rfl⟩ := h
    simp only [List.map, ireg_of_eq h1, ireg_of_eq h2, Op.evalAddressing,
      Option.some.injEq] at hev
    exact ⟨_, rs, .refl _ _ _, hev, fun _ _ => rfl⟩
  case Aindexed2shift.cons.cons.nil a =>
    simp only [res_bind_OK] at h
    obtain ⟨r1, h1, r2, h2, h⟩ := h
    simp only [List.map, ireg_of_eq h1, ireg_of_eq h2, Op.evalAddressing,
      Option.some.injEq] at hev
    split at h
    · rename_i ha
      simp only [res_pure_OK] at h; subst h
      rw [Integers.Int.same_if_eq ha] at hev
      exact ⟨_, rs, .refl _ _ _, addl_shll_zero hev, fun _ _ => rfl⟩
    split at h
    · simp only [res_pure_OK] at h; subst h
      exact ⟨_, rs, .refl _ _ _, hev, fun _ _ => rfl⟩
    · simp only [res_pure_OK] at h; subst h
      refine ⟨_, _, .intro _ _ _ _ _ _ (.one _ _ _ _ _ _ rfl (nextinstr_set_PC _ _ (by simp))),
        ?_, fun r hr => ?_⟩
      · show Val.addl (nextinstr (rs.set (.IR .X16) _) (.IR .X16)) (.Vlong Integers.Int64.zero) = _
        rw [nextinstr_set_same _ _ (by simp)]
        exact addl_zero_of_ptr hev
      · rw [nextinstr_set_other _ _ (dataPreg_ne_PC hr) (dataPreg_ne_X16 hr)]
  case Aindexed2ext.cons.cons.nil x a =>
    simp only [res_bind_OK] at h
    obtain ⟨r1, h1, r2, h2, h⟩ := h
    have e1 := ireg_of_eq h1
    simp only [List.map, e1, ireg_of_eq h2, Op.evalAddressing, Option.some.injEq] at hev
    split at h <;> simp only [res_pure_OK] at h <;> subst h
    · refine ⟨_, rs, .refl _ _ _, ?_, fun _ _ => rfl⟩
      cases x <;> exact hev
    · obtain ⟨rs', A, B, C⟩ := exec_arith_extended sym ge fn Val.addl .Paddext (.Padd .X)
        (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl) .X16 r1 r2 x a
        (insn (.ADimm (.RR1 .X16) Integers.Int64.zero) :: k) rs m (ne_X16_of e1)
      refine ⟨_, rs', .intro _ _ _ _ _ _ A, ?_, fun r hr => C r hr (dataPreg_ne_X16 hr)⟩
      show Val.addl (rs' (.IR .X16)) (.Vlong Integers.Int64.zero) = _
      rw [B]; exact addl_zero_of_ptr hev
  case Aglobal.nil id ofs' =>
    simp only [List.map, Op.evalAddressing, Option.some.injEq] at hev
    split at h
    · rename_i hrel
      split at h <;> cases h
      · refine ⟨_, _, .intro _ _ _ _ _ _ (.one _ _ _ _ _ _ rfl (nextinstr_set_PC _ _ (by simp))),
          ?_, fun r hr => ?_⟩
        · show Val.addl (nextinstr (rs.set (.IR .X16) _) (.IR .X16)) _ = _
          rw [nextinstr_set_same _ _ (by simp), sym.symbol_high_low]; exact hev
        · rw [nextinstr_set_other _ _ (dataPreg_ne_PC hr) (dataPreg_ne_X16 hr)]
      · obtain ⟨rs', A, B, C⟩ := exec_loadsymbol sym ge fn o .X16 id ofs'
          (insn (.ADimm (.RR1 .X16) Integers.Int64.zero) :: k) rs m
          (.inr (by simpa using hrel))
        refine ⟨_, rs', .intro _ _ _ _ _ _ A, ?_, fun r hr => C r hr (dataPreg_ne_X16 hr)⟩
        show Val.addl (rs' (.IR .X16)) (.Vlong Integers.Int64.zero) = _
        rw [B]; exact addl_zero_of_ptr hev
    · cases h
  case Ainstack.nil n =>
    simp only [List.map, Op.evalAddressing, Option.some.injEq] at hev
    have E := offsetPtr_addl hev
    split at h <;> cases h
    · exact ⟨_, rs, .refl _ _ _, E, fun _ _ => rfl⟩
    · obtain ⟨rs', A, B, C⟩ := exec_loadimm64 sym ge fn .X16 (Integers.Ptrofs.to_int64 n)
        (insn (.ADreg .XSP .X16) :: k) rs m
      refine ⟨_, rs', .intro _ _ _ _ _ _ A, ?_,
        fun r hr => C r (dataPreg_ne_PC hr) (dataPreg_ne_X16 hr)⟩
      show Val.addl (rs' .SP) (rs' (.IR .X16)) = _
      rw [B, C _ (by simp) (by simp)]; exact E

theorem loadv_ptr {chunk : Chunk} {m : Mem} {a v : Val} (h : Mem.loadv chunk m a = some v) :
    ∃ b o, a = .Vptr b o := by
  cases a <;> simp [Mem.loadv] at h; exact ⟨_, _, rfl⟩

theorem storev_ptr {chunk : Chunk} {m m' : Mem} {a v : Val} (h : Mem.storev chunk m a v = some m') :
    ∃ b o, a = .Vptr b o := by
  cases a <;> simp [Mem.storev] at h; exact ⟨_, _, rfl⟩

/-- Common part of `transl_load_correct`: the addressing sequence followed by
    one load instruction. -/
theorem transl_load_aux (o : Options) (sz : Z) (addr : Op.Addressing) (args : List Mreg)
    (insn : Asm.Addressing → Instruction) (chunk : Chunk) (rd : Preg) (k c : Code) (rs : Regset)
    (m : Mem) (vaddr v : Val)
    (B : translAddressing o sz addr args insn k = .OK c)
    (C : ∀ ad rs', execInstr sym ge fn (insn ad) rs' m = execLoad sym ge chunk id ad rd rs' m)
    (hrd : rd ≠ .PC)
    (hev : Op.evalAddressing ge (rs .SP) addr ((args.map pregOf).map rs) = some vaddr)
    (hld : Mem.loadv chunk m vaddr = some v) :
    ∃ rs', ExecStraight sym ge fn c rs m k rs' m ∧ rs' rd = v ∧
      ∀ r, dataPreg r = true → r ≠ rd → rs' r = rs r := by
  obtain ⟨b, ofs, rfl⟩ := loadv_ptr hld
  obtain ⟨ad, rs', P, Q, R⟩ := transl_addressing_correct sym ge fn o sz addr args insn k rs m c b
    ofs B hev
  refine ⟨_, exec_straight_opt_right P (.one _ _ _ _ _ _ ?_ (nextinstr_set_PC _ _ hrd)),
    nextinstr_set_same _ _ hrd,
    fun r h1 h2 => by rw [nextinstr_set_other _ _ (dataPreg_ne_PC h1) h2]; exact R r h1⟩
  rw [C]; unfold execLoad; rw [Q, hld]; rfl

/-- `Asmgenproof1.transl_load_correct` -/
theorem transl_load_correct (o : Options) (chunk : Chunk) (addr : Op.Addressing)
    (args : List Mreg) (dst : Mreg) (k c : Code) (rs : Regset) (m : Mem) (vaddr v : Val)
    (h : translLoad o chunk addr args dst k = .OK c)
    (hev : Op.evalAddressing ge (rs .SP) addr ((args.map pregOf).map rs) = some vaddr)
    (hld : Mem.loadv chunk m vaddr = some v) :
    ∃ rs', ExecStraight sym ge fn c rs m k rs' m ∧ rs' (pregOf dst) = v ∧
      ∀ r, dataPreg r = true → r ≠ pregOf dst → rs' r = rs r := by
  cases chunk <;> simp only [translLoad, res_bind_OK, reduceCtorEq] at h <;>
    obtain ⟨rd, h0, h⟩ := h <;>
    first
    | (rw [ireg_of_eq h0]
       exact transl_load_aux sym ge fn o _ addr args _ _ _ k c rs m vaddr v h (fun _ _ => rfl)
         (by simp) hev hld)
    | (rw [freg_of_eq h0]
       exact transl_load_aux sym ge fn o _ addr args _ _ _ k c rs m vaddr v h (fun _ _ => rfl)
         (by simp) hev hld)

/-- Common part of `transl_store_correct`. -/
theorem transl_store_aux (o : Options) (sz : Z) (addr : Op.Addressing) (args : List Mreg)
    (insn : Asm.Addressing → Instruction) (chunk : Chunk) (src : Preg) (k c : Code)
    (rs : Regset) (m m' : Mem) (vaddr : Val)
    (B : translAddressing o sz addr args insn k = .OK c)
    (C : ∀ ad rs', execInstr sym ge fn (insn ad) rs' m = execStore sym ge chunk ad (rs' src) rs' m)
    (hsrc : dataPreg src = true)
    (hev : Op.evalAddressing ge (rs .SP) addr ((args.map pregOf).map rs) = some vaddr)
    (hst : Mem.storev chunk m vaddr (rs src) = some m') :
    ∃ rs', ExecStraight sym ge fn c rs m k rs' m' ∧ ∀ r, dataPreg r = true → rs' r = rs r := by
  obtain ⟨b, ofs, rfl⟩ := storev_ptr hst
  obtain ⟨ad, rs', P, Q, R⟩ := transl_addressing_correct sym ge fn o sz addr args insn k rs m c b
    ofs B hev
  refine ⟨_, exec_straight_opt_right P (.one _ _ _ _ _ _ ?_ (nextinstr_pc _)),
    fun r h1 => by rw [nextinstr_inv _ (dataPreg_ne_PC h1)]; exact R r h1⟩
  rw [C]; unfold execStore; rw [Q, R _ hsrc, hst]

/-- `Asmgenproof1.transl_store_correct` -/
theorem transl_store_correct (o : Options) (chunk : Chunk) (addr : Op.Addressing)
    (args : List Mreg) (src : Mreg) (k c : Code) (rs : Regset) (m m' : Mem) (vaddr : Val)
    (h : translStore o chunk addr args src k = .OK c)
    (hev : Op.evalAddressing ge (rs .SP) addr ((args.map pregOf).map rs) = some vaddr)
    (hst : Mem.storev chunk m vaddr (rs (pregOf src)) = some m') :
    ∃ rs', ExecStraight sym ge fn c rs m k rs' m' ∧ ∀ r, dataPreg r = true → rs' r = rs r := by
  have hd := preg_of_data src
  cases chunk <;> simp only [translStore, res_bind_OK, reduceCtorEq] at h <;>
    obtain ⟨r1, h0, h⟩ := h <;>
    first
    | (rw [ireg_of_eq h0] at hst hd
       exact transl_store_aux sym ge fn o _ addr args _ _ _ k c rs m m' vaddr h (fun _ _ => rfl)
         hd hev hst)
    | (rw [freg_of_eq h0] at hst hd
       exact transl_store_aux sym ge fn o _ addr args _ _ _ k c rs m m' vaddr h (fun _ _ => rfl)
         hd hev hst)

/-- `Asmgenproof1.indexed_memory_access_correct` -/
theorem indexed_memory_access_correct (insn : Asm.Addressing → Instruction) (sz : Z)
    (base : Iregsp) (ofs : Integers.Ptrofs) (k : Code) (rs : Regset) (m : Mem) (b : Block)
    (i : Integers.Ptrofs) (hb : pregOfIregsp base ≠ .IR .X16)
    (hv : Val.offsetPtr (rs (pregOfIregsp base)) ofs = .Vptr b i) :
    ∃ ad rs', ExecStraightOpt sym ge fn (indexedMemoryAccess insn sz base ofs k) rs m
        (insn ad :: k) rs' m ∧
      evalAddressing sym ge ad rs' = .Vptr b i ∧
      ∀ r, r ≠ .PC → r ≠ .IR .X16 → rs' r = rs r := by
  have E := offsetPtr_addl hv
  unfold indexedMemoryAccess
  dsimp only
  split
  · exact ⟨_, rs, .refl _ _ _, E, fun _ _ _ => rfl⟩
  · obtain ⟨rs', A, B, C⟩ := exec_loadimm64 sym ge fn .X16 (Integers.Ptrofs.to_int64 ofs)
      (insn (.ADreg base .X16) :: k) rs m
    refine ⟨_, rs', .intro _ _ _ _ _ _ A, ?_, C⟩
    show Val.addl (rs' (pregOfIregsp base)) (rs' (.IR .X16)) = _
    rw [B, C _ (pregOfIregsp_ne_PC _) hb]; exact E

/-- `Asmgenproof1.loadptr_correct` -/
theorem loadptr_correct (base : Iregsp) (ofs : Integers.Ptrofs) (dst : Ireg) (k : Code) (m : Mem)
    (v : Val) (rs : Regset)
    (hld : Mem.loadv .Mint64 m (Val.offsetPtr (rs (pregOfIregsp base)) ofs) = some v)
    (hb : pregOfIregsp base ≠ .IR .X16) :
    ∃ rs', ExecStraight sym ge fn (loadptr base ofs dst k) rs m k rs' m ∧ rs' (.IR dst) = v ∧
      ∀ r, r ≠ .PC → r ≠ .IR .X16 → r ≠ .IR dst → rs' r = rs r := by
  obtain ⟨b, i, hv⟩ := loadv_ptr hld
  obtain ⟨ad, rs', A, B, C⟩ := indexed_memory_access_correct sym ge fn (.Pldrx dst) 8 base ofs k
    rs m b i hb hv
  have hd : Preg.IR dst ≠ .PC := by simp
  refine ⟨_, exec_straight_opt_right A (.one _ _ _ _ _ _ ?_ (nextinstr_set_PC _ _ hd)),
    nextinstr_set_same _ _ hd, fun r h1 h2 h3 => ?_⟩
  · show execLoad sym ge .Mint64 id ad (.IR dst) rs' m = _
    unfold execLoad; rw [B, ← hv, hld]; rfl
  · rw [nextinstr_set_other _ _ h1 h3]; exact C r h1 h2

/-- `Asmgenproof1.storeptr_correct` -/
theorem storeptr_correct (base : Iregsp) (ofs : Integers.Ptrofs) (src : Ireg) (k : Code)
    (m m' : Mem) (rs : Regset)
    (hst : Mem.storev .Mint64 m (Val.offsetPtr (rs (pregOfIregsp base)) ofs) (rs (.IR src)) =
      some m')
    (hb : pregOfIregsp base ≠ .IR .X16) (hsrc : src ≠ .X16) :
    ∃ rs', ExecStraight sym ge fn (storeptr src base ofs k) rs m k rs' m' ∧
      ∀ r, r ≠ .PC → r ≠ .IR .X16 → rs' r = rs r := by
  obtain ⟨b, i, hv⟩ := storev_ptr hst
  obtain ⟨ad, rs', A, B, C⟩ := indexed_memory_access_correct sym ge fn (.Pstrx src) 8 base ofs k
    rs m b i hb hv
  refine ⟨_, exec_straight_opt_right A (.one _ _ _ _ _ _ ?_ (nextinstr_pc _)),
    fun r h1 h2 => by rw [nextinstr_inv _ h1]; exact C r h1 h2⟩
  show execStore sym ge .Mint64 ad (rs' (.IR src)) rs' m = _
  unfold execStore
  rw [B, C _ (by simp) (fun e => hsrc (Preg.IR.inj e)), ← hv, hst]

/-- `Asmgenproof1.loadind_correct` -/
theorem loadind_correct (base : Iregsp) (ofs : Integers.Ptrofs) (ty : ATyp) (dst : Mreg)
    (k c : Code) (rs : Regset) (m : Mem) (v : Val)
    (h : loadind base ofs ty dst k = .OK c)
    (hld : Mem.loadv (Chunk.ofTyp ty) m (Val.offsetPtr (rs (pregOfIregsp base)) ofs) = some v)
    (hb : pregOfIregsp base ≠ .IR .X16) :
    ∃ rs', ExecStraight sym ge fn c rs m k rs' m ∧ rs' (pregOf dst) = v ∧
      ∀ r, dataPreg r = true → r ≠ pregOf dst → rs' r = rs r := by
  obtain ⟨b, i, hv⟩ := loadv_ptr hld
  have X : ∃ sz insn, c = indexedMemoryAccess insn sz base ofs k ∧
      ∀ ad rs', execInstr sym ge fn (insn ad) rs' m =
        execLoad sym ge (Chunk.ofTyp ty) id ad (pregOf dst) rs' m := by
    unfold loadind at h
    split at h <;> cases h <;> rename_i e <;> rw [e] <;> exact ⟨_, _, rfl, fun _ _ => rfl⟩
  obtain ⟨sz, insn, rfl, SEM⟩ := X
  obtain ⟨ad, rs', A, B, C⟩ := indexed_memory_access_correct sym ge fn insn sz base ofs k
    rs m b i hb hv
  have hd : pregOf dst ≠ .PC := preg_of_not_PC dst
  refine ⟨_, exec_straight_opt_right A (.one _ _ _ _ _ _ ?_ (nextinstr_set_PC _ _ hd)),
    nextinstr_set_same _ _ hd, fun r h1 h2 => ?_⟩
  · rw [SEM]; unfold execLoad; rw [B, ← hv, hld]; rfl
  · rw [nextinstr_set_other _ _ (dataPreg_ne_PC h1) h2]
    exact C r (dataPreg_ne_PC h1) (dataPreg_ne_X16 h1)

/-- `Asmgenproof1.storeind_correct` -/
theorem storeind_correct (base : Iregsp) (ofs : Integers.Ptrofs) (ty : ATyp) (src : Mreg)
    (k c : Code) (rs : Regset) (m m' : Mem)
    (h : storeind src base ofs ty k = .OK c)
    (hst : Mem.storev (Chunk.ofTyp ty) m (Val.offsetPtr (rs (pregOfIregsp base)) ofs)
      (rs (pregOf src)) = some m')
    (hb : pregOfIregsp base ≠ .IR .X16) :
    ∃ rs', ExecStraight sym ge fn c rs m k rs' m' ∧ ∀ r, dataPreg r = true → rs' r = rs r := by
  obtain ⟨b, i, hv⟩ := storev_ptr hst
  have X : ∃ sz insn, c = indexedMemoryAccess insn sz base ofs k ∧
      ∀ ad rs', execInstr sym ge fn (insn ad) rs' m =
        execStore sym ge (Chunk.ofTyp ty) ad (rs' (pregOf src)) rs' m := by
    unfold storeind at h
    split at h <;> cases h <;> rename_i e <;> rw [e] <;> exact ⟨_, _, rfl, fun _ _ => rfl⟩
  obtain ⟨sz, insn, rfl, SEM⟩ := X
  obtain ⟨ad, rs', A, B, C⟩ := indexed_memory_access_correct sym ge fn insn sz base ofs k
    rs m b i hb hv
  have hd := preg_of_data src
  refine ⟨_, exec_straight_opt_right A (.one _ _ _ _ _ _ ?_ (nextinstr_pc _)),
    fun r h1 => ?_⟩
  · rw [SEM]; unfold execStore
    rw [B, C _ (dataPreg_ne_PC hd) (dataPreg_ne_X16 hd), ← hv, hst]
  · rw [nextinstr_inv _ (dataPreg_ne_PC h1)]
    exact C r (dataPreg_ne_PC h1) (dataPreg_ne_X16 h1)

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
      rs' (.IR RA) = Mach.parentRa cs ∧ rs' .SP = Mach.parentSp cs ∧
      ∀ r, r ≠ .PC → r ≠ .SP → r ≠ .IR .X30 → r ≠ .IR .X16 → rs' r = rs r := by
  obtain ⟨parent', LP', LDP'⟩ := Mem.loadv_extends MEXT LP (.refl _)
  obtain ⟨ra', LRA', LDRA'⟩ := Mem.loadv_extends MEXT LRA (.refl _)
  have e1 := lessdef_parent_sp MCS LDP'
  have e2 := lessdef_parent_ra MCS LDRA'
  subst e1 e2
  obtain ⟨tm', FREE', MEXT'⟩ := Mem.free_parallel_extends MEXT FREE
  have hsp : rs .SP = .Vptr stk soff := AG.agree_sp
  obtain ⟨rs1, A1, B1, C1⟩ := loadptr_correct sym ge fn .XSP f.fn_retaddr_ofs RA
    (.Pfreeframe f.fn_stacksize f.fn_link_ofs :: k) tm _ rs
    (by show Mem.loadv .Mint64 tm (Val.offsetPtr (rs .SP) _) = _; rw [hsp]; exact LRA')
    (by simp [pregOfIregsp])
  have hsp1 : rs1 .SP = .Vptr stk soff := by rw [C1 _ (by simp) (by simp) (by simp), hsp]
  refine ⟨nextinstr ((rs1.set .SP (Mach.parentSp cs)).set (.IR .X16) .Vundef), tm',
    exec_straight_trans A1 (.one _ _ _ _ _ _ ?_ ?_), ?_, MEXT', ?_, ?_, ?_⟩
  · show (match Mem.loadv .Mint64 tm (Val.offsetPtr (rs1 .SP) f.fn_link_ofs) with
      | none => Outcome.Stuck
      | some v => match rs1 .SP with
        | .Vptr stk _ => match Mem.free tm stk 0 f.fn_stacksize with
          | none => .Stuck
          | some m' => .Next (nextinstr ((rs1.set .SP v).set (.IR .X16) .Vundef)) m'
        | _ => .Stuck) = _
    rw [hsp1]
    have : Mem.loadv .Mint64 tm (Val.offsetPtr (.Vptr stk soff) f.fn_link_ofs) =
      some (Mach.parentSp cs) := LP'
    rw [this]
    dsimp only
    rw [FREE']
  · exact nextinstr_pc _
  · exact agree_nextinstr (agree_set_other _ (agree_change_sp (agree_exten AG fun r hr =>
      C1 r (dataPreg_ne_PC hr) (dataPreg_ne_X16 hr) (dataPreg_ne_RA hr)) (parent_sp_def MCS)) rfl)
  · rw [nextinstr_inv _ (by simp), Regset.gso _ _ (by simp), Regset.gso _ _ (by simp), B1]
  · rw [nextinstr_inv _ (by simp), Regset.gso _ _ (by simp), Regset.gss]
  · intro r h1 h2 h3 h4
    rw [nextinstr_inv _ h1, Regset.gso _ _ h4, Regset.gso _ _ h2]
    exact C1 r h1 h4 h3

end CONSTRUCTORS

end Asmgenproof1
end CC
