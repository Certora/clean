/-
  Correctness proof for common subexpression elimination — port of
  `backend/CSEproof.v`, part 2: equations and memory stores
  (`kill_loads_after_store_holds`, `store_normalized_range_sound`,
  `add_store_result_hold`, `kill_loads_after_storebytes_holds`,
  `load_memcpy`, `shift_memcpy_eq_wf`, `shift_memcpy_eq_holds`,
  `add_memcpy_eqs_charact`, `add_memcpy_holds`, `transfer_builtin_holds`).

  The memory lemma `Mem.storebytes_split` used by Rocq's `load_memcpy` is
  replaced by `Mem.loadbytes_storebytes_inner` (reading back the middle part
  of a stored byte list).
-/
import CCLib.backend.CSEproof
import CCLib.backend.ValueAnalysisSoundInit

namespace CC

namespace Mem

theorem setN_append : ∀ (a b : List MemVal) (p : _root_.Int) (c : ZMap MemVal),
    setN (a ++ b) p c = setN b (p + (a.length : _root_.Int)) (setN a p c)
  | [], b, p, c => by simp [setN]
  | x :: a, b, p, c => by
    show setN (a ++ b) (p + 1) (ZMap.set p x c) = _
    rw [setN_append a b (p + 1) (ZMap.set p x c)]
    simp only [List.length_cons]
    rw [show p + ((a.length + 1 : Nat) : _root_.Int) = p + 1 + (a.length : _root_.Int) by
      push_cast; omega]
    rfl

/-- Reading back the middle part of a written byte list. -/
theorem getN_setN_inner (vl1 vl2 vl3 : List MemVal) (p : _root_.Int) (c : ZMap MemVal) :
    getN vl2.length (p + (vl1.length : _root_.Int)) (setN (vl1 ++ vl2 ++ vl3) p c) = vl2 := by
  rw [setN_append, setN_append, getN_setN_outside vl3 _ _ _ _ (.inl (by simp; omega)),
    getN_setN_same]

/-- `loadbytes` of the middle part of a `storebytes` (replaces Rocq's use of
    `Mem.storebytes_split` in `CSEproof.load_memcpy`). -/
theorem loadbytes_storebytes_inner {m : Mem} {b : Block} {ofs : Z} {bytes1 bytes2 bytes3 : List MemVal}
    {m' : Mem} (h : storebytes m b ofs (bytes1 ++ bytes2 ++ bytes3) = some m') :
    loadbytes m' b (ofs + (bytes1.length : Z)) (bytes2.length : Z) = some bytes2 := by
  have RP := storebytes_range_perm h
  have RP' : rangePerm m' b (ofs + (bytes1.length : Z))
      (ofs + (bytes1.length : Z) + (bytes2.length : Z)) .Cur .Readable = true := by
    have hb1 : (0 : _root_.Int) ≤ (bytes1.length : _root_.Int) := Int.natCast_nonneg _
    have hb3 : (0 : _root_.Int) ≤ (bytes3.length : _root_.Int) := Int.natCast_nonneg _
    refine rangePerm_intro _ _ _ _ _ _ fun o h1 h2 => ?_
    rw [perm_storebytes h]
    refine perm_implies (rangePerm_perm _ _ _ _ _ _ RP o ?_ ?_) (by decide)
    · omega
    · simp only [List.length_append] at *; push_cast; omega
  rw [loadbytes_result RP', storebytes_contents h, PMap.gss,
    show ((bytes2.length : Z)).toNat = bytes2.length from by omega, getN_setN_inner]

end Mem

namespace CSEproof

open ValueDomain ValueAnalysis RTL CSEdomain CSE Op

/-- `CSEproof.load_memcpy` -/
theorem load_memcpy {m : Mem} {b1 : Block} {ofs1 sz : _root_.Int} {bytes : List MemVal}
    {b2 : Block} {ofs2 : _root_.Int} {m' : Mem} {chunk : Chunk} {i : _root_.Int} {v : Val}
    (LB : Mem.loadbytes m b1 ofs1 sz = some bytes) (SB : Mem.storebytes m b2 ofs2 bytes = some m')
    (LD : Mem.load chunk m b1 i = some v) (h1 : ofs1 ≤ i) (h2 : i + sizeChunk chunk ≤ ofs1 + sz)
    (hal : alignChunk chunk ∣ ofs2 - ofs1) :
    Mem.load chunk m' b2 (i + (ofs2 - ofs1)) = some v := by
  have SPOS := sizeChunk_pos chunk
  have LB' : Mem.loadbytes m b1 ofs1 ((i - ofs1) + (sizeChunk chunk + (sz - (i - ofs1) -
      sizeChunk chunk))) = some bytes := by
    rw [show (i - ofs1) + (sizeChunk chunk + (sz - (i - ofs1) - sizeChunk chunk)) = sz by omega]
    exact LB
  obtain ⟨bytes1, bytes23, LB1, LB23, EQ⟩ := Mem.loadbytes_split LB' (by omega) (by omega)
  obtain ⟨bytes2, bytes3, LB2, LB3, EQ'⟩ := Mem.loadbytes_split LB23 (by omega) (by omega)
  subst EQ EQ'
  obtain ⟨bytes2', A, B⟩ := Mem.load_loadbytes LD
  have E : bytes2' = bytes2 := by
    rw [show ofs1 + (i - ofs1) = i by omega] at LB2
    rw [LB2] at A; cases A; rfl
  subst E
  have L1 : (bytes1.length : _root_.Int) = i - ofs1 := by
    have := Mem.loadbytes_length LB1; omega
  have L2 : (bytes2'.length : _root_.Int) = sizeChunk chunk := by
    have := Mem.loadbytes_length A; omega
  rw [← List.append_assoc] at SB
  have LB'' := Mem.loadbytes_storebytes_inner SB
  rw [L1, L2] at LB''
  rw [B, show i + (ofs2 - ofs1) = ofs2 + (i - ofs1) by omega]
  refine Mem.loadbytes_load LB'' ?_
  have VA := Mem.load_valid_access LD
  have hal_i : alignChunk chunk ∣ i := by
    simp only [Mem.validAccess, Bool.and_eq_true] at VA
    exact Int.dvd_of_emod_eq_zero (by simpa using VA.2)
  rw [show ofs2 + (i - ofs1) = i + (ofs2 - ofs1) by omega]
  exact Int.dvd_add hal_i hal

/-- `CSEproof.store_normalized_range_sound` -/
theorem store_normalized_range_sound {bc : BlockClassification} {chunk : Chunk} {v : Val}
    (h : Vmatch bc v (storeNormalizedRange chunk)) : Val.Lessdef (Val.loadResult chunk v) v := by
  cases chunk with
  | Mbool =>
    cases h with
    | Uns _ i _ _ hu => rcases is_uns_1 hu with rfl | rfl <;> exact .refl _
    | Uns_undef => exact .refl _
  | Mint8signed =>
    cases h with
    | Sgn _ i _ _ hs =>
      simp only [Val.loadResult]; rw [(is_sgn_sign_ext (by decide) i).1 hs]; exact .refl _
    | Sgn_undef => exact .refl _
  | Mint8unsigned =>
    cases h with
    | Uns _ i _ _ hu =>
      simp only [Val.loadResult]; rw [(is_uns_zero_ext _ i).1 hu]; exact .refl _
    | Uns_undef => exact .refl _
  | Mint16signed =>
    cases h with
    | Sgn _ i _ _ hs =>
      simp only [Val.loadResult]; rw [(is_sgn_sign_ext (by decide) i).1 hs]; exact .refl _
    | Sgn_undef => exact .refl _
  | Mint16unsigned =>
    cases h with
    | Uns _ i _ _ hu =>
      simp only [Val.loadResult]; rw [(is_uns_zero_ext _ i).1 hu]; exact .refl _
    | Uns_undef => exact .refl _
  | _ => cases v <;> simp [Val.loadResult, Archi.ptr64] <;> constructor

section STORE
variable (o : ValueAOp.Options) {ge : RTL.CGenv} {rs : RTL.Regset}

/-- `CSEproof.kill_loads_after_store_holds` -/
theorem kill_loads_after_store_holds {valu : Valuation} {sp : Block} {m : Mem} {n : Numbering}
    {addr : Addressing} {args : List Reg} {a : Val} {chunk : Chunk} {v : Val} {m' : Mem}
    {bc : BlockClassification} {ae : Aenv} {am : Amem}
    (NH : NumberingHolds valu ge (.Vptr sp Integers.Ptrofs.zero) rs m n)
    (EA : evalAddressing ge (.Vptr sp Integers.Ptrofs.zero) addr (rs.getList args) = some a)
    (ST : Mem.storev chunk m a v = some m') (GM : GenvMatch bc ge) (SP : bc sp = .BCstack)
    (EM : Ematch bc rs ae) :
    NumberingHolds valu ge (.Vptr sp Integers.Ptrofs.zero) rs m'
      (killLoadsAfterStore o (.State ae am) n chunk addr args) := by
  refine kill_equations_hold NH fun r v' hp hv he => ?_
  cases he with
  | op_eval_to op vl v h =>
    exact .op_eval_to _ _ _ (by rw [← opDependsOnMemory_correct ge _ op _ m m' hp]; exact h)
  | load_eval_to chunk' addr' vl a' v' p ha hl =>
    simp only [filterAfterStore, Bool.not_eq_false'] at hp
    cases hv with
    | load_valid _ _ _ _ _ b' ofs' bc' ha2 PM' GM' SP' =>
    rw [ha2] at ha; cases ha
    refine .load_eval_to _ _ _ _ _ _ ha2 ?_
    cases a with
    | Vptr b ofs =>
      simp only [Mem.storev] at ST
      split at ST
      · have PM := match_aptr_of_aval o.strict
          (ValueAOp.eval_static_addressing_sound GM SP addr EA (aregs_sound EM args))
        have D := pdisjoint_sound_strong hp PM' PM GM' SP' GM SP
        simp only [Mem.loadv] at hl ⊢
        split
        · rename_i hc
          rw [if_pos hc] at hl
          rw [Mem.load_store_other ST chunk' b' _ D]; exact hl
        · rename_i hc; rw [if_neg hc] at hl; exact hl
      · cases ST
    | _ => cases ST
  | builtin_eval_to bf args vargs v ha hb =>
    exact .builtin_eval_to _ _ _ _ (builtinArgsDependsOnMemory_correct m' ha hp) hb

/-- `CSEproof.add_store_result_hold` -/
theorem add_store_result_hold {valu1 : Valuation} {sp : Block} {m' : Mem} {n : Numbering}
    {addr : Addressing} {args : List Reg} {a : Val} {chunk : Chunk} {m : Mem} {src : Reg}
    {bc : BlockClassification} {ae : Aenv} {am : Amem}
    (NH : NumberingHolds valu1 ge (.Vptr sp Integers.Ptrofs.zero) rs m' n)
    (EA : evalAddressing ge (.Vptr sp Integers.Ptrofs.zero) addr (rs.getList args) = some a)
    (ST : Mem.storev chunk m a (rs.get src) = some m') (GM : GenvMatch bc ge)
    (SP : bc sp = .BCstack) (EM : Ematch bc rs ae) :
    ∃ valu2, NumberingHolds valu2 ge (.Vptr sp Integers.Ptrofs.zero) rs m'
      (addStoreResult o (.State ae am) n chunk addr args src) := by
  unfold addStoreResult
  simp only [avalue]
  split
  · rename_i INCL
    generalize e1 : valnumReg n src = p1
    obtain ⟨n1, vsrc⟩ := p1
    generalize e2 : valnumRegs n1 args = p2
    obtain ⟨n2, vargs⟩ := p2
    obtain ⟨valu2, A, B, C, D, E⟩ := valnum_reg_holds NH e1
    obtain ⟨valu3, P, Q, R, S, T⟩ := valnum_regs_holds args A e2
    cases a with
    | Vptr b ofs =>
      simp only [Mem.storev] at ST
      split at ST
      · rename_i hc
        refine ⟨valu3, ⟨⟨?_, P.num_holds_wf.wf_num_reg, P.num_holds_wf.wf_num_val⟩, ?_,
          P.num_holds_reg⟩⟩
        · intro e he
          rcases List.mem_cons.mp he with rfl | he
          · exact ⟨pos_lt_of_lt_of_le D T, S⟩
          · exact P.num_holds_wf.wf_num_eqs e he
        · intro eq heq
          rcases List.mem_cons.mp heq with rfl | heq
          · refine .eq_holds_lessdef _ _ (Val.loadResult chunk (rs.get src))
              (.load_eval_to _ _ _ (.Vptr b ofs) _ _ (by rw [← Q]; exact EA) ?_) ?_ ?_
            · simp only [Mem.loadv, if_pos hc]; exact Mem.load_store_same ST
            · rw [R vsrc D, ← B]
              exact store_normalized_range_sound (vmatch_ge (vincl_ge INCL) (EM src))
            · exact .load_valid _ _ _ _ _ b ofs bc (by rw [← Q]; exact EA)
                (match_aptr_of_aval o.strict
                  (ValueAOp.eval_static_addressing_sound GM SP addr EA (aregs_sound EM args)))
                GM SP
          · exact P.num_holds_eq eq heq
      · cases ST
    | _ => cases ST
  · exact ⟨valu1, NH⟩

/-- `CSEproof.kill_loads_after_storebytes_holds` -/
theorem kill_loads_after_storebytes_holds {valu : Valuation} {sp : Block} {m : Mem}
    {n : Numbering} {dst : Aptr} {b : Block} {ofs : Integers.Ptrofs} {bytes : List MemVal}
    {m' : Mem} {bc : BlockClassification} {sz : Z}
    (NH : NumberingHolds valu ge (.Vptr sp Integers.Ptrofs.zero) rs m n)
    (PM : Pmatch bc b ofs dst)
    (SB : Mem.storebytes m b (Integers.Ptrofs.unsigned ofs) bytes = some m')
    (GM : GenvMatch bc ge) (SP : bc sp = .BCstack) (LEN : bytes.length = sz.toNat)
    (SZ : sz ≥ 0) :
    NumberingHolds valu ge (.Vptr sp Integers.Ptrofs.zero) rs m'
      (killLoadsAfterStorebytes n dst sz) := by
  refine kill_equations_hold NH fun r v' hp hv he => ?_
  cases he with
  | op_eval_to op vl v h =>
    exact .op_eval_to _ _ _ (by rw [← opDependsOnMemory_correct ge _ op _ m m' hp]; exact h)
  | load_eval_to chunk' addr' vl a' v' p ha hl =>
    simp only [filterAfterStore, Bool.not_eq_false'] at hp
    cases hv with
    | load_valid _ _ _ _ _ b' ofs' bc' ha2 PM' GM' SP' =>
    rw [ha2] at ha; cases ha
    refine .load_eval_to _ _ _ _ _ _ ha2 ?_
    have D := pdisjoint_sound_strong hp PM' PM GM' SP' GM SP
    have hlen : (bytes.length : _root_.Int) = sz := by rw [LEN]; exact Int.toNat_of_nonneg SZ
    simp only [Mem.loadv] at hl ⊢
    split
    · rename_i hc
      rw [if_pos hc] at hl
      rw [Mem.load_storebytes_other SB chunk' b' _ (by rw [hlen]; exact D)]; exact hl
    · rename_i hc; rw [if_neg hc] at hl; exact hl
  | builtin_eval_to bf args vargs v ha hb =>
    exact .builtin_eval_to _ _ _ _ (builtinArgsDependsOnMemory_correct m' ha hp) hb

end STORE

/-! ### `memcpy` -/

/-- `CSEproof.shift_memcpy_eq_wf` -/
theorem shift_memcpy_eq_wf {src sz delta : Z} {e e' : Equation} {next : Valnum}
    (h : shiftMemcpyEq src sz delta e = some e') (hw : WfEquation next e) : WfEquation next e' := by
  unfold shiftMemcpyEq at h
  split at h
  · dsimp only at h
    split at h
    · cases h; exact ⟨hw.1, fun v hv => by simp [valnumsRhs] at hv⟩
    · cases h
  · cases h

theorem ptrofs_max_unsigned_eq : Integers.Ptrofs.max_unsigned = Integers.Ptrofs.modulus - 1 := rfl

theorem evalAddressing_Ainstack_zero (ge : RTL.CGenv) (sp : Block) (i : Integers.Ptrofs) :
    evalAddressing ge (.Vptr sp Integers.Ptrofs.zero) (.Ainstack i) [] = some (.Vptr sp i) := by
  show some (Val.offsetPtr _ _) = _
  simp only [Val.offsetPtr, Integers.Ptrofs.add_zero_l]

theorem evalAddressing_Ainstack_inv {ge : RTL.CGenv} {sp : Block} {i : Integers.Ptrofs}
    {vl : List Val} {a : Val}
    (h : evalAddressing ge (.Vptr sp Integers.Ptrofs.zero) (.Ainstack i) vl = some a) :
    vl = [] ∧ a = .Vptr sp i := by
  cases vl with
  | nil =>
    rw [evalAddressing_Ainstack_zero] at h; cases h; exact ⟨rfl, rfl⟩
  | cons => cases h

/-- `CSEproof.shift_memcpy_eq_holds` -/
theorem shift_memcpy_eq_holds {src dst sz : Z} {e e' : Equation} {m : Mem} {sp : Block}
    {bytes : List MemVal} {m' : Mem} {valu : Valuation} {ge : RTL.CGenv}
    (h : shiftMemcpyEq src sz (dst - src) e = some e')
    (LB : Mem.loadbytes m sp src sz = some bytes) (SB : Mem.storebytes m sp dst bytes = some m')
    (EH : EquationHolds valu ge (.Vptr sp Integers.Ptrofs.zero) m e) :
    EquationHolds valu ge (.Vptr sp Integers.Ptrofs.zero) m' e' := by
  unfold shiftMemcpyEq at h
  split at h
  · rename_i l strict chunk i vl ap
    dsimp only at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hc
      cases h
      have SPOS := sizeChunk_pos chunk
      have hj : Integers.Ptrofs.unsigned (Integers.Ptrofs.repr (Integers.Ptrofs.unsigned i + (dst - src))) =
          Integers.Ptrofs.unsigned i + (dst - src) :=
        Integers.Ptrofs.unsigned_repr h4 (by
          rw [ptrofs_max_unsigned_eq]
          exact Int.le_sub_one_of_lt (Int.lt_of_lt_of_le (Int.lt_add_of_pos_right _ SPOS) h5))
      have LD : ∀ v, Mem.loadv chunk m (.Vptr sp i) = some v →
          Mem.loadv chunk m' (.Vptr sp (Integers.Ptrofs.repr (Integers.Ptrofs.unsigned i + (dst - src)))) =
            some v := by
        intro v hl
        simp only [Mem.loadv] at hl ⊢
        split at hl
        · rw [hj, if_pos h5]
          exact load_memcpy LB SB hl h1 h2 (Int.dvd_of_emod_eq_zero h3)
        · cases hl
      have EA := evalAddressing_Ainstack_zero ge sp
        (Integers.Ptrofs.repr (Integers.Ptrofs.unsigned i + (dst - src)))
      cases EH with
      | eq_holds_strict _ _ he hv =>
        cases he with
        | load_eval_to _ _ _ a _ _ ha hl =>
        obtain ⟨_, rfl⟩ := evalAddressing_Ainstack_inv ha
        cases hv with
        | load_valid _ _ _ _ _ _ _ bc _ _ GM SP =>
        exact .eq_holds_strict _ _ (.load_eval_to _ _ _ _ _ _ EA (LD _ hl))
          (.load_valid _ _ _ _ _ _ _ bc EA (.stk SP) GM SP)
      | eq_holds_lessdef _ _ v he hld hv =>
        cases he with
        | load_eval_to _ _ _ a _ _ ha hl =>
        obtain ⟨_, rfl⟩ := evalAddressing_Ainstack_inv ha
        cases hv with
        | load_valid _ _ _ _ _ _ _ bc _ _ GM SP =>
        exact .eq_holds_lessdef _ _ v (.load_eval_to _ _ _ _ _ _ EA (LD _ hl)) hld
          (.load_valid _ _ _ _ _ _ _ bc EA (.stk SP) GM SP)
    · cases h
  · cases h

/-- `CSEproof.add_memcpy_eqs_charact` -/
theorem add_memcpy_eqs_charact {e' : Equation} {src sz delta : Z} {eqs2 : List Equation} :
    ∀ {eqs1 : List Equation}, e' ∈ addMemcpyEqs src sz delta eqs1 eqs2 →
    e' ∈ eqs2 ∨ ∃ e, e ∈ eqs1 ∧ shiftMemcpyEq src sz delta e = some e'
  | [], h => .inl h
  | a :: eqs1, h => by
    simp only [addMemcpyEqs] at h
    split at h
    · rcases add_memcpy_eqs_charact h with A | ⟨e, A, B⟩
      · exact .inl A
      · exact .inr ⟨e, List.mem_cons_of_mem _ A, B⟩
    · rename_i e'' SHIFT
      rcases List.mem_cons.mp h with rfl | h
      · exact .inr ⟨a, List.mem_cons_self .., SHIFT⟩
      · rcases add_memcpy_eqs_charact h with A | ⟨e, A, B⟩
        · exact .inl A
        · exact .inr ⟨e, List.mem_cons_of_mem _ A, B⟩

/-- `CSEproof.add_memcpy_holds` -/
theorem add_memcpy_holds {m : Mem} {bsrc : Block} {osrc : Integers.Ptrofs} {sz : Z}
    {bytes : List MemVal} {bdst : Block} {odst : Integers.Ptrofs} {m' : Mem} {valu : Valuation}
    {ge : RTL.CGenv} {sp : Block} {rs : RTL.Regset} {n1 n2 : Numbering}
    {bc : BlockClassification} {asrc adst : Aptr}
    (LB : Mem.loadbytes m bsrc (Integers.Ptrofs.unsigned osrc) sz = some bytes)
    (SB : Mem.storebytes m bdst (Integers.Ptrofs.unsigned odst) bytes = some m')
    (NH1 : NumberingHolds valu ge (.Vptr sp Integers.Ptrofs.zero) rs m n1)
    (NH2 : NumberingHolds valu ge (.Vptr sp Integers.Ptrofs.zero) rs m' n2)
    (PS : Pmatch bc bsrc osrc asrc) (PD : Pmatch bc bdst odst adst) (SP : bc sp = .BCstack)
    (LE : n1.num_next ≤ n2.num_next) :
    NumberingHolds valu ge (.Vptr sp Integers.Ptrofs.zero) rs m' (addMemcpy n1 n2 asrc adst sz) := by
  unfold addMemcpy
  split
  · rename_i src dst
    have A : ∀ {b o i}, Pmatch bc b o (.Stk i) → b = sp ∧ i = o := by
      intro b o i h
      cases h with
      | stk h => exact ⟨bc.bc_stack b sp h SP, rfl⟩
    obtain ⟨rfl, rfl⟩ := A PS
    obtain ⟨rfl, rfl⟩ := A PD
    refine ⟨⟨fun e he => ?_, NH2.num_holds_wf.wf_num_reg, NH2.num_holds_wf.wf_num_val⟩,
      fun eq heq => ?_, NH2.num_holds_reg⟩
    · rcases add_memcpy_eqs_charact he with X | ⟨e0, X, Y⟩
      · exact NH2.num_holds_wf.wf_num_eqs e X
      · exact wf_equation_incr (shift_memcpy_eq_wf Y (NH1.num_holds_wf.wf_num_eqs e0 X)) LE
    · rcases add_memcpy_eqs_charact heq with X | ⟨e0, X, Y⟩
      · exact NH2.num_holds_eq eq X
      · exact shift_memcpy_eq_holds Y LB SB (NH1.num_holds_eq e0 X)
  · exact NH2

/-- `CSEproof.transfer_builtin_holds` -/
theorem transfer_builtin_holds (o : ValueAOp.Options) {ge : RTL.CGenv} {f : RTL.Function}
    {pc : Node} {ef : ExtFun} {args : List (BuiltinArg Reg)} {res : BuiltinRes Reg} {pc' : Node}
    {rs : RTL.Regset} {sp : Block} {m : Mem} {vargs : List Val} {t : Trace} {vres : Val}
    {m' : Mem} {valu : Valuation} {n : Numbering} {dm : Defmap} {vapprox : PMap VAState}
    {ae : Aenv} {am : Amem} {bc : BlockClassification} {rm : Romem}
    (CODEAT : f.fn_code.get pc = some (.Ibuiltin ef args res pc'))
    (BA : EvalBuiltinArgs (Genv.toSenv ge) (fun r => rs.get r) (.Vptr sp Integers.Ptrofs.zero) m
      args vargs)
    (EC : externalCall ef (Genv.toSenv ge) vargs m t vres m')
    (NH : NumberingHolds valu ge (.Vptr sp Integers.Ptrofs.zero) rs m n)
    (APPROX : vapprox.get pc = .State ae am)
    (EM : Ematch bc rs ae) (RM : Romatch bc m rm) (MM : Mmatch bc m am) (GM : GenvMatch bc ge)
    (SM : bc sp = .BCstack) :
    ∃ valu', NumberingHolds valu' ge (.Vptr sp Integers.Ptrofs.zero) (regmapSetres res vres rs) m'
      (CSE.transfer o f dm vapprox pc n) := by
  have CASE1 : ∃ valu', NumberingHolds valu' ge (.Vptr sp Integers.Ptrofs.zero)
      (regmapSetres res vres rs) m' emptyNumbering := ⟨valu, empty_numbering_holds _ _ _ _ _⟩
  have CASE2 : m' = m → ∃ valu', NumberingHolds valu' ge (.Vptr sp Integers.Ptrofs.zero)
      (regmapSetres res vres rs) m' (setResUnknown n res) := fun e => by
    subst e; exact ⟨valu, set_res_unknown_holds NH⟩
  have CASE3 : ∃ valu', NumberingHolds valu' ge (.Vptr sp Integers.Ptrofs.zero)
      (regmapSetres res vres rs) m' (setResUnknown (killAllLoads n) res) :=
    ⟨valu, set_res_unknown_holds (kill_all_loads_hold NH)⟩
  unfold CSE.transfer
  rw [CODEAT]
  dsimp only
  cases ef with
  | EF_external => exact CASE1
  | EF_runtime => exact CASE1
  | EF_malloc => exact CASE1
  | EF_free => exact CASE1
  | EF_inline_asm => exact CASE1
  | EF_vstore => exact CASE3
  | EF_vload => exact CASE2 (by cases EC; rfl)
  | EF_annot => exact CASE2 (by cases EC; rfl)
  | EF_annot_val => exact CASE2 (by cases EC; rfl)
  | EF_debug => exact CASE2 (by cases EC; rfl)
  | EF_builtin name sg =>
    dsimp only
    cases LK : Builtins.lookupBuiltinFunction name sg with
    | some bf =>
      change builtinOrExternalSem name sg _ _ _ _ _ _ at EC
      simp only [builtinOrExternalSem, LK] at EC
      cases EC with
      | intro _ _ _ _ hsem => exact add_builtin_holds NH BA hsem
    | none => exact CASE3
  | EF_memcpy sz al =>
    change ExtcallMemcpySem sz al _ _ _ _ _ _ at EC
    cases EC with
    | intro _ bdst odst bsrc osrc _ bytes _ _ SZ _ _ _ _ LB SB =>
    cases BA with
    | cons h1 BA =>
    cases BA with
    | cons h2 BA =>
    cases BA
    dsimp only
    refine ⟨valu, set_res_unknown_holds ?_⟩
    have PS := aaddr_arg_sound_1 (o := o) EM RM MM GM SM h2
    have PD := aaddr_arg_sound_1 (o := o) EM RM MM GM SM h1
    rw [← APPROX] at PS PD
    exact add_memcpy_holds LB SB NH
      (kill_loads_after_storebytes_holds NH PD SB GM SM (Mem.loadbytes_length LB) SZ) PS PD SM
      (pos_le_refl _)

end CSEproof
end CC
