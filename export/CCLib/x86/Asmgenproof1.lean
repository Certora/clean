/-
  Correctness proof for x86-64 generation: auxiliary results, part 1 —
  port of the beginning of `x86/Asmgenproof1.v`: properties of
  `nextinstr_nf` (`agree_nextinstr_nf`, `nextinstr_nf_inv`,
  `nextinstr_nf_inv1`, `nextinstr_nf_set_preg`), the smart constructors
  `mk_mov`, `mk_shrximm`, `mk_shrxlimm`, `mk_intconv`, `mk_storebyte`
  (with `addressing_mentions_correct`), the double-width division lemmas
  (`divu_modu_exists`, `divs_mods_exists`, `divlu_modlu_exists`,
  `divls_modls_exists`) and the stack-slot accessors `loadind_correct`,
  `storeind_correct` (with `eval_addrmode_indexed`).

  Differences from Rocq:
  * The port targets x86-64 only (`Archi.ptr64 = true`), so the 32-bit
    branches of `mk_intconv` and `mk_storebyte` are unreachable and their
    correctness lemmas are proved for the 64-bit code.
  * The `Simplif(s)` tactics become `simp` with the register-update lemmas.
-/
import CCLib.x86.Asmgenproof0
import CCLib.lib.IntegersDivmod2
import CCLib.lib.IntegersOverflow

namespace CC
namespace X86
namespace Asmgenproof1

open Asm Asmgen Asmgenproof0 Smallstep Conventions1

/-! ## Correspondence between Mach registers and x86 registers -/

/-- `Asmgenproof1.agree_nextinstr_nf` -/
theorem agree_nextinstr_nf {ms : Mach.Regset} {sp : Val} {rs : Regset} (h : Agree ms sp rs) :
    Agree ms sp (nextinstrNf rs) := by
  unfold nextinstrNf
  apply agree_nextinstr
  apply agree_undef_nondata_regs _ h
  intro r hr
  simp only [flagRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `Asmgenproof1.nextinstr_nf_inv` -/
theorem nextinstr_nf_inv {r : Preg} (rs : Regset) (h1 : r ≠ .PC) (h2 : ∀ c, r ≠ .CR c) :
    nextinstrNf rs r = rs r := by
  unfold nextinstrNf
  rw [nextinstr_inv _ h1]
  apply undef_regs_other
  intro r' hr
  simp only [flagRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact h2 _

/-- `Asmgenproof1.nextinstr_nf_inv1` -/
theorem nextinstr_nf_inv1 {r : Preg} (rs : Regset) (h : dataPreg r = true) :
    nextinstrNf rs r = rs r :=
  nextinstr_nf_inv rs (data_diff h rfl) (fun _ => data_diff h rfl)

/-- `Asmgenproof1.nextinstr_nf_set_preg` -/
theorem nextinstr_nf_set_preg (rs : Regset) (m : Mreg) (v : Val) :
    nextinstrNf (rs.set (pregOf m) v) .PC = Val.offsetPtr (rs .PC) Integers.Ptrofs.one := by
  unfold nextinstrNf
  rw [nextinstr_pc, undef_regs_other _ _ (by simp [flagRegs]),
    Regset.gso _ _ (preg_of_not_PC m).symm]

/-- `nextinstr_nf` sets the `PC` like `nextinstr`. -/
theorem nextinstrNf_pc (rs : Regset) :
    nextinstrNf rs .PC = Val.offsetPtr (rs .PC) Integers.Ptrofs.one := by
  unfold nextinstrNf
  rw [nextinstr_pc, undef_regs_other _ _ (by simp [flagRegs])]

/-- Reading a register of `rs.set r v`. -/
theorem Regset.get_set (rs : Regset) (r r' : Preg) (v : Val) :
    rs.set r v r' = if r' = r then v else rs r' := rfl

/-- `PC` after `nextinstr (rs # r <- v)` with `r ≠ PC`. -/
theorem nextinstr_set_pc (rs : Regset) {r : Preg} (v : Val) (h : r ≠ .PC) :
    nextinstr (rs.set r v) .PC = Val.offsetPtr (rs .PC) Integers.Ptrofs.one := by
  rw [nextinstr_pc, Regset.gso _ _ (Ne.symm h)]

/-- `PC` after `nextinstr_nf (rs # r <- v)` with `r ≠ PC`. -/
theorem nextinstrNf_set_pc (rs : Regset) {r : Preg} (v : Val) (h : r ≠ .PC) :
    nextinstrNf (rs.set r v) .PC = Val.offsetPtr (rs .PC) Integers.Ptrofs.one := by
  rw [nextinstrNf_pc, Regset.gso _ _ (Ne.symm h)]

/-- The registers left unchanged by `nextinstr_nf (rs # rd <- v)`. -/
theorem nextinstrNf_set_other (rs : Regset) {r rd : Preg} (v : Val)
    (h : dataPreg r = true) (hne : r ≠ rd) : nextinstrNf (rs.set rd v) r = rs r := by
  rw [nextinstr_nf_inv1 _ h, Regset.gso _ _ hne]

/-- The registers left unchanged by `nextinstr (rs # rd <- v)`. -/
theorem nextinstr_set_other (rs : Regset) {r rd : Preg} (v : Val)
    (h : dataPreg r = true) (hne : r ≠ rd) : nextinstr (rs.set rd v) r = rs r := by
  rw [nextinstr_inv1 _ h, Regset.gso _ _ hne]

/-- The register written by `nextinstr_nf (rs # rd <- v)`. -/
theorem nextinstrNf_set_same (rs : Regset) {rd : Preg} (v : Val) (h : dataPreg rd = true) :
    nextinstrNf (rs.set rd v) rd = v := by
  rw [nextinstr_nf_inv1 _ h, Regset.gss]

/-- The register written by `nextinstr (rs # rd <- v)`. -/
theorem nextinstr_set_same (rs : Regset) {rd : Preg} (v : Val) (h : dataPreg rd = true) :
    nextinstr (rs.set rd v) rd = v := by
  rw [nextinstr_inv1 _ h, Regset.gss]

/-! ## Correctness of x86-64 constructor functions -/

section CONSTRUCTORS
variable {ge : Asm.CGenv} {fn : Asm.Function}

/-- `Asmgenproof1.mk_mov_correct` -/
theorem mk_mov_correct {rd rs : Preg} {k c : Code} (rs1 : Regset) (m : Mem)
    (h : mkMov rd rs k = .OK c) :
    ∃ rs2, ExecStraight ge fn c rs1 m k rs2 m ∧ rs2 rd = rs1 rs ∧
      ∀ r, dataPreg r = true → r ≠ rd → rs2 r = rs1 r := by
  unfold mkMov at h
  split at h <;> cases h
  · exact ⟨_, .one _ _ _ _ _ _ rfl (nextinstr_set_pc _ _ (by simp)),
      nextinstr_set_same _ _ rfl, fun r hr hne => nextinstr_set_other _ _ hr hne⟩
  · exact ⟨_, .one _ _ _ _ _ _ rfl (nextinstr_set_pc _ _ (by simp)),
      nextinstr_set_same _ _ rfl, fun r hr hne => nextinstr_set_other _ _ hr hne⟩

/-! ### Properties of division -/

/-- `Asmgenproof1.divu_modu_exists` -/
theorem divu_modu_exists {v1 v2 : Val} (h : Val.divu v1 v2 ≠ none ∨ Val.modu v1 v2 ≠ none) :
    ∃ n d q r, v1 = .Vint n ∧ v2 = .Vint d ∧ Integers.Int.divmodu2 Integers.Int.zero n d = some (q, r) ∧
      Val.divu v1 v2 = some (.Vint q) ∧ Val.modu v1 v2 = some (.Vint r) := by
  cases v1 <;> cases v2 <;> simp [Val.divu, Val.modu] at h
  rename_i n d
  have hd : d ≠ Integers.Int.zero := fun e => by subst e; simp [Integers.Int.eq_true] at h
  refine ⟨n, d, Integers.Int.divu n d, Integers.Int.modu n d, rfl, rfl, Integers.Int.divmodu2_divu_modu n d hd, ?_, ?_⟩ <;>
    simp [Val.divu, Val.modu, Integers.Int.eq_false hd]

/-- `Asmgenproof1.divlu_modlu_exists` -/
theorem divlu_modlu_exists {v1 v2 : Val} (h : Val.divlu v1 v2 ≠ none ∨ Val.modlu v1 v2 ≠ none) :
    ∃ n d q r, v1 = .Vlong n ∧ v2 = .Vlong d ∧ Integers.Int64.divmodu2 Integers.Int64.zero n d = some (q, r) ∧
      Val.divlu v1 v2 = some (.Vlong q) ∧ Val.modlu v1 v2 = some (.Vlong r) := by
  cases v1 <;> cases v2 <;> simp [Val.divlu, Val.modlu] at h
  rename_i n d
  have hd : d ≠ Integers.Int64.zero := fun e => by subst e; simp [Integers.Int64.eq_true] at h
  refine ⟨n, d, Integers.Int64.divu n d, Integers.Int64.modu n d, rfl, rfl, Integers.Int64.divmodu2_divu_modu n d hd, ?_, ?_⟩ <;>
    simp [Val.divlu, Val.modlu, Integers.Int64.eq_false hd]

/-- `Asmgenproof1.divs_mods_exists` -/
theorem divs_mods_exists {v1 v2 : Val} (h : Val.divs v1 v2 ≠ none ∨ Val.mods v1 v2 ≠ none) :
    ∃ nh nl d q r, Val.shr v1 (.Vint (Integers.Int.repr 31)) = .Vint nh ∧ v1 = .Vint nl ∧
      v2 = .Vint d ∧ Integers.Int.divmods2 nh nl d = some (q, r) ∧
      Val.divs v1 v2 = some (.Vint q) ∧ Val.mods v1 v2 = some (.Vint r) := by
  cases v1 <;> cases v2 <;> simp only [Val.divs, Val.mods, ne_eq, not_true,
    or_self] at h
  rename_i n d
  have hc : (Integers.Int.eq d Integers.Int.zero || (Integers.Int.eq n (Integers.Int.repr Integers.Int.min_signed) && Integers.Int.eq d Integers.Int.mone))
      = false := by
    cases hb : (Integers.Int.eq d Integers.Int.zero || (Integers.Int.eq n (Integers.Int.repr Integers.Int.min_signed) && Integers.Int.eq d Integers.Int.mone))
    · rfl
    · simp [hb] at h
  have hd : d ≠ Integers.Int.zero := fun e => by subst e; simp [Integers.Int.eq_true] at hc
  have ho : n ≠ Integers.Int.repr Integers.Int.min_signed ∨ d ≠ Integers.Int.mone := by
    by_cases h1 : n = Integers.Int.repr Integers.Int.min_signed
    · right; intro h2; subst h1; subst h2; simp [Integers.Int.eq_true] at hc
    · left; exact h1
  refine ⟨Integers.Int.shr n (Integers.Int.repr 31), n, d, Integers.Int.divs n d, Integers.Int.mods n d, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · simp only [Val.shr, show Integers.Int.ltu (Integers.Int.repr 31) Integers.Int.iwordsize = true by decide, if_true]
  · rw [Integers.Int.shr_lt_zero]; exact Integers.Int.divmods2_divs_mods n d hd ho
  · simp only [Val.divs, hc]; rfl
  · simp only [Val.mods, hc]; rfl

/-- `Asmgenproof1.divls_modls_exists` -/
theorem divls_modls_exists {v1 v2 : Val} (h : Val.divls v1 v2 ≠ none ∨ Val.modls v1 v2 ≠ none) :
    ∃ nh nl d q r, Val.shrl v1 (.Vint (Integers.Int.repr 63)) = .Vlong nh ∧ v1 = .Vlong nl ∧
      v2 = .Vlong d ∧ Integers.Int64.divmods2 nh nl d = some (q, r) ∧
      Val.divls v1 v2 = some (.Vlong q) ∧ Val.modls v1 v2 = some (.Vlong r) := by
  cases v1 <;> cases v2 <;> simp only [Val.divls, Val.modls, ne_eq, not_true,
    or_self] at h
  rename_i n d
  have hc : (Integers.Int64.eq d Integers.Int64.zero ||
      (Integers.Int64.eq n (Integers.Int64.repr Integers.Int64.min_signed) && Integers.Int64.eq d Integers.Int64.mone)) = false := by
    cases hb : (Integers.Int64.eq d Integers.Int64.zero ||
        (Integers.Int64.eq n (Integers.Int64.repr Integers.Int64.min_signed) && Integers.Int64.eq d Integers.Int64.mone))
    · rfl
    · simp [hb] at h
  have hd : d ≠ Integers.Int64.zero := fun e => by subst e; simp [Integers.Int64.eq_true] at hc
  have ho : n ≠ Integers.Int64.repr Integers.Int64.min_signed ∨ d ≠ Integers.Int64.mone := by
    by_cases h1 : n = Integers.Int64.repr Integers.Int64.min_signed
    · right; intro h2; subst h1; subst h2; simp [Integers.Int64.eq_true] at hc
    · left; exact h1
  refine ⟨Integers.Int64.shr n (Integers.Int64.repr 63), n, d, Integers.Int64.divs n d, Integers.Int64.mods n d, ?_, rfl, rfl,
    ?_, ?_, ?_⟩
  · rfl
  · rw [Integers.Int64.shr_lt_zero]; exact Integers.Int64.divmods2_divs_mods n d hd ho
  · simp only [Val.divls, hc]; rfl
  · simp only [Val.modls, hc]; rfl

/-! ### Smart constructors for `shrx`, conversions, small stores -/

/-- `Asmgenproof1.mk_shrximm_correct` -/
theorem mk_shrximm_correct {n : Integers.Int} {k c : Code} (rs1 : Regset) {v : Val} (m : Mem)
    (h : mkShrximm n k = .OK c) (hv : Val.shrx (rs1 (.IR .RAX)) (.Vint n) = some v) :
    ∃ rs2, ExecStraight ge fn c rs1 m k rs2 m ∧ rs2 (.IR .RAX) = v ∧
      ∀ r, dataPreg r = true → r ≠ .IR .RAX → r ≠ .IR .RCX → rs2 r = rs1 r := by
  unfold mkShrximm at h; cases h
  obtain ⟨x, y, hA, hB, hC⟩ := Val.shrx_shr hv
  cases hB; subst hC
  refine ⟨_, .step _ _ _ _ _ _ _ _ _ rfl (nextinstr_pc _)
    (.step _ _ _ _ _ _ _ _ _ rfl (nextinstr_pc _)
    (.step _ _ _ _ _ _ _ _ _ rfl (nextinstr_pc _)
    (.one _ _ _ _ _ _ rfl (nextinstrNf_pc _)))), ?_, ?_⟩
  · simp [nextinstrNf, nextinstr, undefRegs, flagRegs, compareInts, Regset.set, hA, evalTestcond, evalAddrmode32]
    have hz := Integers.Int.lt_sub_overflow x Integers.Int.zero
    simp only [Val.and, Val.sub, Val.sub_overflow, Val.negative, Val.Vzero, Val.add,
      Integers.Int.and_idem, Integers.Int.repr_unsigned, Integers.Int.add_zero_l]
    rw [hz]
    cases x.lt Integers.Int.zero <;> simp [Integers.Int.eq_true, show Integers.Int.eq Integers.Int.zero Integers.Int.one = false from by decide]
  · intro r hr h1 h2
    cases r <;> simp_all [dataPreg, nextinstrNf, nextinstr, undefRegs, flagRegs, compareInts, Regset.set]

/-- `Val.addl v (Val.addl w 0) = Val.addl v w` (used for `leaq`). -/
theorem addl_addl_zero (x y : Val) :
    Val.addl x (Val.addl y (.Vlong (Integers.Int64.repr 0))) = Val.addl x y := by
  have hz : Integers.Int64.repr 0 = Integers.Int64.zero := rfl
  have hp : ∀ o : Integers.Ptrofs,
      Integers.Ptrofs.add o (Integers.Ptrofs.of_int64 Integers.Int64.zero) = o := by
    intro o; apply BitVec.eq_of_toNat_eq
    show (BitVec.add o (BitVec.ofInt 64 ((0 : BitVec 64).toNat : _root_.Int))).toNat = o.toNat
    simpa using o.isLt
  cases x <;> cases y <;> simp [Val.addl, Archi.ptr64, hz, Integers.Int64.add_zero, hp]

theorem ptrofs_of_int64_add_repr_unsigned (ofs : Integers.Ptrofs) :
    Integers.Ptrofs.of_int64 (Integers.Int64.add Integers.Int64.zero
      (Integers.Int64.repr (Integers.Ptrofs.unsigned ofs))) = ofs := by
  rw [Integers.Int64.add_zero_l]
  apply BitVec.eq_of_toNat_eq
  simp [Integers.Ptrofs.of_int64, Integers.MI.repr, Integers.MI.unsigned, Integers.Int64.repr,
    Integers.Ptrofs.unsigned]

/-- `Asmgenproof1.mk_shrxlimm_correct` -/
theorem mk_shrxlimm_correct {n : Integers.Int} {k c : Code} (rs1 : Regset) {v : Val} (m : Mem)
    (h : mkShrxlimm n k = .OK c) (hv : Val.shrxl (rs1 (.IR .RAX)) (.Vint n) = some v) :
    ∃ rs2, ExecStraight ge fn c rs1 m k rs2 m ∧ rs2 (.IR .RAX) = v ∧
      ∀ r, dataPreg r = true → r ≠ .IR .RAX → r ≠ .IR .RDX → rs2 r = rs1 r := by
  have EQ := Val.shrxl_shrl_2 hv
  unfold mkShrxlimm at h; cases h
  by_cases h0 : Integers.Int.eq n Integers.Int.zero = true
  · rw [if_pos h0] at EQ; subst EQ
    simp only [if_pos h0]
    refine ⟨_, .one _ _ _ _ _ _ rfl (nextinstr_pc _), ?_, ?_⟩
    · simp [nextinstr, Regset.set]
    · intro r hr h1 h2
      cases r <;> simp_all [dataPreg, nextinstr, Regset.set]
  · rw [if_neg h0] at EQ; subst EQ
    simp only [if_neg h0]
    refine ⟨_, .step _ _ _ _ _ _ _ _ _ rfl (nextinstrNf_pc _)
      (.step _ _ _ _ _ _ _ _ _ rfl (nextinstrNf_pc _)
      (.step _ _ _ _ _ _ _ _ _ rfl (nextinstr_pc _)
      (.one _ _ _ _ _ _ rfl (nextinstrNf_pc _)))), ?_, ?_⟩
    · simp [nextinstrNf, nextinstr, undefRegs, flagRegs, Regset.set, evalAddrmode64,
        addl_addl_zero]
    · intro r hr h1 h2
      cases r <;> simp_all [dataPreg, nextinstrNf, nextinstr, undefRegs, flagRegs, Regset.set]

/-- `Asmgenproof1.mk_intconv_correct` -/
theorem mk_intconv_correct {mk : Ireg → Ireg → Instruction} {sem : Val → Val} {rd rs : Ireg}
    {k c : Code} (rs1 : Regset) (m : Mem)
    (h : mkIntconv mk rd rs k = .OK c)
    (hsem : ∀ c rd rs r m, execInstr ge c (mk rd rs) r m =
      .Next (nextinstr (r.set (.IR rd) (sem (r (.IR rs))))) m) :
    ∃ rs2, ExecStraight ge fn c rs1 m k rs2 m ∧ rs2 (.IR rd) = sem (rs1 (.IR rs)) ∧
      ∀ r, dataPreg r = true → r ≠ .IR rd → r ≠ .IR .RAX → rs2 r = rs1 r := by
  unfold mkIntconv at h
  simp only [Archi.ptr64, Bool.true_or, if_true] at h; cases h
  refine ⟨_, .one _ _ _ _ _ _ (hsem _ _ _ _ _) (nextinstr_pc _), ?_, ?_⟩
  · simp [nextinstr, Regset.set]
  · intro r hr h1 h2
    cases r <;> simp_all [dataPreg, nextinstr, Regset.set]

/-- `Asmgenproof1.addressing_mentions_correct` -/
theorem addressing_mentions_correct (a : Addrmode) (r : Ireg) (rs1 rs2 : Regset)
    (hag : ∀ r' : Ireg, r' ≠ r → rs1 (.IR r') = rs2 (.IR r'))
    (h : addressingMentions a r = false) :
    evalAddrmode32 ge a rs1 = evalAddrmode32 ge a rs2 := by
  obtain ⟨base, ofs, cst⟩ := a
  simp only [addressingMentions, Bool.or_eq_false_iff] at h
  obtain ⟨h1, h2⟩ := h
  rcases base with _ | b <;> rcases ofs with _ | ⟨r', sc⟩ <;>
    (try simp only [decide_eq_false_iff_not] at h1) <;>
    (try simp only [decide_eq_false_iff_not] at h2) <;>
    first
    | rfl
    | simp only [evalAddrmode32, hag _ (Ne.symm h1), hag _ (Ne.symm h2)]
    | simp only [evalAddrmode32, hag _ (Ne.symm h1)]
    | simp only [evalAddrmode32, hag _ (Ne.symm h2)]

/-- `Asmgenproof1.mk_storebyte_correct` (x86-64: a single `movb`). -/
theorem mk_storebyte_correct {addr : Addrmode} {r : Ireg} {k c : Code} (rs1 : Regset)
    {m1 m2 : Mem} (h : mkStorebyte addr r k = .OK c)
    (hst : Mem.storev .Mint8unsigned m1 (evalAddrmode ge addr rs1) (rs1 (.IR r)) = some m2) :
    ∃ rs2, ExecStraight ge fn c rs1 m1 k rs2 m2 ∧
      ∀ r, dataPreg r = true → rs2 r = rs1 r := by
  unfold mkStorebyte at h
  simp only [Archi.ptr64, Bool.true_or, if_true] at h; cases h
  refine ⟨_, .one _ _ _ _ _ _ ?_ (nextinstrNf_pc _), ?_⟩
  · show execStore ge _ _ _ _ _ _ = _
    unfold execStore; rw [hst]; rfl
  · intro r hr
    exact nextinstr_nf_inv1 _ hr

/-- `Asmgenproof1.eval_addrmode_indexed` -/
theorem eval_addrmode_indexed (base : Ireg) (ofs : Integers.Ptrofs) (rs : Regset)
    (h : match rs (.IR base) with | .Vptr _ _ => True | _ => False) :
    evalAddrmode ge (.Addrmode (some base) none (.inl (Integers.Ptrofs.unsigned ofs))) rs =
      Val.offsetPtr (rs (.IR base)) ofs := by
  revert h
  cases hb : rs (.IR base) <;> intro h <;> simp only at h
  simp [evalAddrmode, evalAddrmode64, Archi.ptr64, hb, Val.addl, Val.offsetPtr,
    ptrofs_of_int64_add_repr_unsigned]

theorem exec_load_eq {chunk : Chunk} {m : Mem} {a : Addrmode} {rs : Regset} {rd : Preg} {v : Val}
    (h : Mem.loadv chunk m (evalAddrmode ge a rs) = some v) :
    execLoad ge chunk m a rs rd = .Next (nextinstrNf (rs.set rd v)) m := by
  unfold execLoad; rw [h]

theorem exec_store_eq {chunk : Chunk} {m m' : Mem} {a : Addrmode} {rs : Regset} {r1 : Preg}
    {l : List Preg} (h : Mem.storev chunk m (evalAddrmode ge a rs) (rs r1) = some m') :
    execStore ge chunk m a rs r1 l = .Next (nextinstrNf (undefRegs l rs)) m' := by
  unfold execStore; rw [h]

/-- `Asmgenproof1.loadind_correct` -/
theorem loadind_correct (base : Ireg) (ofs : Integers.Ptrofs) (ty : ATyp) (dst : Mreg)
    (k : Code) (rs : Regset) (c : Code) (m : Mem) (v : Val)
    (h : loadind base ofs ty dst k = .OK c)
    (hld : Mem.loadv (Chunk.ofTyp ty) m (Val.offsetPtr (rs (.IR base)) ofs) = some v) :
    ∃ rs', ExecStraight ge fn c rs m k rs' m ∧ rs' (pregOf dst) = v ∧
      ∀ r, dataPreg r = true → r ≠ pregOf dst → rs' r = rs r := by
  have hA : evalAddrmode ge (.Addrmode (some base) none (.inl (Integers.Ptrofs.unsigned ofs))) rs =
      Val.offsetPtr (rs (.IR base)) ofs := by
    apply eval_addrmode_indexed
    cases hb : rs (.IR base) <;> simp only [hb, Val.offsetPtr] at hld ⊢ <;> cases hld
  rw [← hA] at hld
  refine ⟨nextinstrNf (rs.set (pregOf dst) v), ?_, ?_, ?_⟩
  · unfold loadind at h
    split at h <;> (try simp only [Archi.ptr64] at h) <;> cases h <;> rename_i heq <;>
      exact .one _ _ _ _ _ _ (by rw [heq]; exact exec_load_eq hld)
        (nextinstrNf_set_pc _ _ (preg_of_not_PC dst))
  · exact nextinstrNf_set_same _ _ (preg_of_data dst)
  · intro r hr hne
    exact nextinstrNf_set_other _ _ hr hne

/-- `Asmgenproof1.storeind_correct` -/
theorem storeind_correct (base : Ireg) (ofs : Integers.Ptrofs) (ty : ATyp) (src : Mreg)
    (k : Code) (rs : Regset) (c : Code) (m m' : Mem)
    (h : storeind src base ofs ty k = .OK c)
    (hst : Mem.storev (Chunk.ofTyp ty) m (Val.offsetPtr (rs (.IR base)) ofs) (rs (pregOf src)) =
      some m') :
    ∃ rs', ExecStraight ge fn c rs m k rs' m' ∧
      ∀ r, dataPreg r = true → PregNotin r (destroyedBySetstack ty) → rs' r = rs r := by
  have hA : evalAddrmode ge (.Addrmode (some base) none (.inl (Integers.Ptrofs.unsigned ofs))) rs =
      Val.offsetPtr (rs (.IR base)) ofs := by
    apply eval_addrmode_indexed
    cases hb : rs (.IR base) <;> simp only [hb, Val.offsetPtr] at hst ⊢ <;> cases hst
  rw [← hA] at hst
  unfold storeind at h
  split at h <;> (try simp only [Archi.ptr64] at h) <;> cases h <;> rename_i heq <;>
    rw [heq] at hst <;>
    refine ⟨_, .one _ _ _ _ _ _ (exec_store_eq hst)
      (by rw [nextinstrNf_pc, undef_regs_other _ _ (by simp)]), ?_⟩ <;>
    intro r hr hn <;> rw [nextinstr_nf_inv1 _ hr] <;>
    first
    | rfl
    | exact undef_regs_other _ _ (by
        intro r' hr'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'; subst hr'
        exact hn .FP0 (by simp [destroyedBySetstack]))

end CONSTRUCTORS

/-! ## Translation of addressing modes -/

section ADDRESSING
open Op

/-- Inversion of a successful `Res` bind (`Errors.bind_inversion`). -/
theorem res_bind_OK {A B : Type} {x : Res A} {f : A → Res B} {b : B} :
    (bind x f = Res.OK b) ↔ ∃ a, x = .OK a ∧ f a = .OK b := by
  cases x <;> simp [bind, Res.bind]

theorem res_pure_OK {A : Type} {a b : A} : (pure a : Res A) = .OK b ↔ a = b := by
  simp [pure]

variable {ge : Asm.CGenv} {fn : Asm.Function}

theorem mull_lessdef_scale (v : Val) (i : Z) :
    Val.Lessdef (Val.mull v (.Vlong (Integers.Int64.repr i)))
      (if i = 1 then v else Val.mull v (.Vlong (Integers.Int64.repr i))) := by
  by_cases h : i = 1
  · subst h; rw [if_pos rfl]
    cases v <;> simp only [Val.mull] <;> try exact .undef _
    rw [show Integers.Int64.repr 1 = Integers.Int64.one from rfl, Integers.Int64.mul_one]
    exact .refl _
  · rw [if_neg h]; exact .refl _

theorem addl_zero_l_long (n : Integers.Int64) :
    Val.addl (.Vlong Integers.Int64.zero) (.Vlong n) = .Vlong n := by
  simp [Val.addl, Integers.Int64.add_zero_l]

theorem ptrofs_add_of_int64_zero (o : Integers.Ptrofs) :
    Integers.Ptrofs.add o (Integers.Ptrofs.of_int64 Integers.Int64.zero) = o := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.add o (BitVec.ofInt 64 ((0 : BitVec 64).toNat : _root_.Int))).toNat = o.toNat
  simpa using o.isLt

theorem addl_zero_symbolAddress (id : Ident) (ofs : Integers.Ptrofs) :
    Val.addl (.Vlong Integers.Int64.zero) (Genv.symbolAddress ge id ofs) =
      Genv.symbolAddress ge id ofs := by
  unfold Genv.symbolAddress
  split
  · simp only [Val.addl, Archi.ptr64, if_true, ptrofs_add_of_int64_zero]
  · rfl

theorem ptrofs_of_int64_repr_signed (ofs : Integers.Ptrofs) :
    Integers.Ptrofs.of_int64 (Integers.Int64.repr (Integers.Ptrofs.signed ofs)) = ofs := by
  apply BitVec.eq_of_toNat_eq
  simp [Integers.Ptrofs.of_int64, Integers.MI.repr, Integers.MI.unsigned, Integers.Int64.repr,
    Integers.Ptrofs.signed, Integers.MI.signed]

/-- `Asmgenproof1.transl_addressing_mode_64_correct` -/
theorem transl_addressing_mode_64_correct {addr : Addressing} {args : List Mreg} {am : Addrmode}
    (rs : Regset) {v : Val} (h : translAddressing addr args = .OK am)
    (hv : Op.evalAddressing64 ge (rs (.IR .RSP)) addr ((args.map pregOf).map rs) = some v) :
    Val.Lessdef v (evalAddrmode64 ge am rs) := by
  cases addr <;> rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, args⟩⟩⟩ <;>
    simp only [translAddressing, res_bind_OK, res_pure_OK] at h <;>
    simp only [Op.evalAddressing64, List.map, Archi.ptr64, if_true, reduceCtorEq,
      Option.some.injEq] at hv <;>
    (try cases h) <;> subst hv
  case Aindexed.cons.nil.intro r h =>
    obtain ⟨hr, rfl⟩ := h
    simp only [evalAddrmode64, ireg_of_eq hr, addl_zero_l_long]
    exact .refl _
  case Aindexed2.cons.cons.nil.intro r h =>
    obtain ⟨hr1, r2, hr2, rfl⟩ := h
    simp only [evalAddrmode64, ireg_of_eq hr1, ireg_of_eq hr2, if_pos, Val.addl_assoc]
    exact .refl _
  case Ascaled.cons.nil.intro r h =>
    obtain ⟨hr, rfl⟩ := h
    simp only [evalAddrmode64, ireg_of_eq hr]
    rw [Val.addl_permut, addl_zero_l_long]
    exact Val.addl_lessdef (mull_lessdef_scale _ _) (.refl _)
  case Aindexed2scaled.cons.cons.nil.intro r h =>
    obtain ⟨hr1, r2, hr2, rfl⟩ := h
    simp only [evalAddrmode64, ireg_of_eq hr1, ireg_of_eq hr2]
    exact Val.addl_lessdef (.refl _) (Val.addl_lessdef (mull_lessdef_scale _ _) (.refl _))
  case Aglobal.nil.refl =>
    simp only [evalAddrmode64, addl_zero_symbolAddress]
    exact .refl _
  case Ainstack.nil.refl =>
    simp only [evalAddrmode64, addl_zero_l_long]
    cases hsp : rs (.IR .RSP) <;> simp only [Val.offsetPtr] <;> try exact .undef _
    simp only [Val.addl, Archi.ptr64, if_true, ptrofs_of_int64_repr_signed]
    exact .refl _

/-- `Asmgenproof1.transl_addressing_mode_correct` -/
theorem transl_addressing_mode_correct {addr : Addressing} {args : List Mreg} {am : Addrmode}
    (rs : Regset) {v : Val} (h : translAddressing addr args = .OK am)
    (hv : Op.evalAddressing ge (rs (.IR .RSP)) addr ((args.map pregOf).map rs) = some v) :
    Val.Lessdef v (evalAddrmode ge am rs) :=
  transl_addressing_mode_64_correct rs h hv

/-- `Asmgenproof1.normalize_addrmode_32_correct` -/
theorem normalize_addrmode_32_correct (am : Addrmode) (rs : Regset) :
    evalAddrmode32 ge (normalizeAddrmode32 am) rs = evalAddrmode32 ge am rs := by
  obtain ⟨base, ofs, n | r⟩ := am
  · simp only [normalizeAddrmode32, evalAddrmode32, Integers.Int.repr_signed]
  · rfl

/-- `Ptrofs.of_int64_to_int64` (64-bit target). -/
theorem ptrofs_of_int64_to_int64 (ofs : Integers.Ptrofs) :
    Integers.Ptrofs.of_int64 (Integers.Ptrofs.to_int64 ofs) = ofs := by
  show BitVec.ofInt 64 ((BitVec.zeroExtend 64 ofs).toNat : _root_.Int) = ofs
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_setWidth]
  have := ofs.isLt
  have h2 : (2 : Nat) ^ Archi.ptrWordsize = 2 ^ 64 := rfl
  have h3 : ofs.toNat < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt h3, Int.emod_eq_of_lt (by omega) (by simp; omega)]
  simp

/-- `Asmgenproof1.normalize_addrmode_64_correct` -/
theorem normalize_addrmode_64_correct (am : Addrmode) (rs : Regset) :
    evalAddrmode64 ge am rs =
      match normalizeAddrmode64 am with
      | (am', none) => evalAddrmode64 ge am' rs
      | (am', some delta) => Val.addl (evalAddrmode64 ge am' rs) (.Vlong delta) := by
  obtain ⟨base, ofs, n | ⟨id, delta⟩⟩ := am
  · by_cases hc : offsetInRange n = true
    · simp only [normalizeAddrmode64, if_pos hc]
    · simp only [normalizeAddrmode64, if_neg hc, evalAddrmode64, Val.addl_assoc]
      congr 2
      simp [Val.addl, show Integers.Int64.repr 0 = Integers.Int64.zero from rfl,
        Integers.Int64.add_zero_l]
  · by_cases hc : ptroffsetInRange delta = true
    · simp only [normalizeAddrmode64, hc, Bool.true_or, if_true]
    · simp only [normalizeAddrmode64, hc, Archi.ptr64, Bool.not_true, Bool.or_false,
        Bool.false_eq_true, if_false, evalAddrmode64, Val.addl_assoc]
      congr 2
      rw [← Genv.shift_symbolAddress_64, ptrofs_of_int64_to_int64, Integers.Ptrofs.add_zero_l]

end ADDRESSING

end Asmgenproof1
end X86
end CC
