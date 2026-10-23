/-
  Correctness proof for the layout of activation records, part 4 — port of
  the middle of `backend/Stackingproof.v`: simplification of loads and
  stores, the call-stack invariants (`stack_contents`, `match_stacks`),
  syntactic properties of the translation (labels, code tails),
  preservation of global symbols and functions, and the translation of the
  arguments of external calls and builtins.
-/
import CCLib.backend.StackingproofCallee
import CCLib.common.MemoryBytes

namespace CC
namespace Stackingproof

open Linear Mach Conventions1 Conventions Stacklayout Stacking Bounds Separation
open Lineartyping Smallstep

/-! ## Simplification of loads and stores -/

/-- `Mem.load_bool_int8_unsigned` -/
theorem load_bool_int8_unsigned (m : Mem) (b : Block) (ofs : Z) :
    Mem.load .Mbool m b ofs = (Mem.load .Mint8unsigned m b ofs).map Val.normBool := by
  have hva : Mem.validAccess m .Mbool b ofs .Readable =
      Mem.validAccess m .Mint8unsigned b ofs .Readable := rfl
  unfold Mem.load
  rw [hva]
  split
  · congr 1
    show decodeVal .Mbool (Mem.getN 1 ofs _) = Val.normBool (decodeVal .Mint8unsigned (Mem.getN 1 ofs _))
    unfold decodeVal
    split
    · rfl
    · rfl
  · rfl

/-- `Stackingproof.simplify_load_correct` -/
theorem simplify_load_correct (chunk : Chunk) (m : Mem) (a v : Val)
    (h : Mem.loadv chunk m a = some v) :
    ∃ v', Mem.loadv (simplifyLoad chunk) m a = some v' ∧ Val.Lessdef v v' := by
  cases chunk
  case Mbool =>
    cases a <;> simp only [Mem.loadv, reduceCtorEq] at h
    rename_i b i
    simp only [simplifyLoad, Mem.loadv]
    split at h
    · rename_i hc
      rw [if_pos (by simpa [sizeChunk] using hc)]
      rw [load_bool_int8_unsigned] at h
      cases hl : Mem.load .Mint8unsigned m b (Integers.Ptrofs.unsigned i) with
      | none => rw [hl] at h; cases h
      | some v' =>
        rw [hl] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        exact ⟨v', rfl, Val.norm_bool_is_lessdef v'⟩
    · cases h
  all_goals exact ⟨v, h, .refl _⟩

private theorem storev_congr {c1 c2 : Chunk}
    (hs : ∀ m b ofs v, Mem.store c1 m b ofs v = Mem.store c2 m b ofs v)
    (hsz : sizeChunk c1 = sizeChunk c2) (m : Mem) (a v : Val) :
    Mem.storev c1 m a v = Mem.storev c2 m a v := by
  cases a <;> simp only [Mem.storev, hs, hsz]

/-- `Stackingproof.simplify_store_correct` -/
theorem simplify_store_correct (chunk : Chunk) (m : Mem) (a v : Val) (m' : Mem)
    (h : Mem.storev chunk m a v = some m') : Mem.storev (simplifyStore chunk) m a v = some m' := by
  cases chunk
  case Mbool => rw [storev_congr Mem.store_bool_unsigned_8 rfl] at h; exact h
  case Mint8signed => rw [storev_congr Mem.store_signed_unsigned_8 rfl] at h; exact h
  case Mint16signed => rw [storev_congr Mem.store_signed_unsigned_16 rfl] at h; exact h
  all_goals exact h

/-- `Stackingproof.simplify_load_destroyed` -/
theorem simplify_load_destroyed (chunk : Chunk) (addr : Op.Addressing) :
    destroyedByLoad (simplifyLoad chunk) addr = destroyedByLoad chunk addr := rfl

/-- `Stackingproof.simplify_store_destroyed` -/
theorem simplify_store_destroyed (chunk : Chunk) (addr : Op.Addressing) :
    destroyedByStore (simplifyStore chunk) addr = destroyedByStore chunk addr := rfl

/-! ## Call stack invariants -/

/-- `Stackingproof.stack_contents` -/
def stackContents (abi : AbiKind) (j : Val.Meminj) :
    List Linear.Stackframe → List Mach.Stackframe → MAssert
  | [], [] => pure True
  | .Stackframe f _ ls _ :: cs, .Stackframe _ (.Vptr sp' _) _ _ :: cs' =>
      frameContents abi f j sp' ls (Linear.parentLocset cs) (Mach.parentSp cs')
        (Mach.parentRa cs') ** stackContents abi j cs cs'
  | _, _ => pure False

/-- `Stackingproof.match_stacks` -/
inductive MatchStacks (abi : AbiKind) (tge : Mach.CGenv) (j : Val.Meminj) :
    List Linear.Stackframe → List Mach.Stackframe → Signature → Prop where
  | empty (sg : Signature) : TailcallPossible abi sg → MatchStacks abi tge j [] [] sg
  | cons (f : Linear.Function) (sp : Block) (ls : LTL.Locset) (c : Linear.Code)
      (cs : List Linear.Stackframe) (fb : Block) (sp' : Block) (ra : Val) (c' : Mach.Code)
      (cs' : List Mach.Stackframe) (sg : Signature) (trf : Mach.Function) :
      c <:+ f.fn_code →
      Genv.findFunctPtr tge fb = some (.Internal trf) →
      transfFunction abi f = .OK trf →
      translCode (fenv abi f) c = c' →
      j sp = some (sp', (fenv abi f).fe_stack_data) →
      Val.HasType ra Tptr →
      AgreeLocs abi f ls (Linear.parentLocset cs) →
      (∀ ofs ty, Loc.S .Outgoing ofs ty ∈ RPair.regsList (locArguments abi sg) →
        SlotWithinBounds (bnds abi f) .Outgoing ofs ty) →
      MatchStacks abi tge j cs cs' f.fn_sig →
      MatchStacks abi tge j
        (.Stackframe f (.Vptr sp Integers.Ptrofs.zero) ls c :: cs)
        (.Stackframe fb (.Vptr sp' Integers.Ptrofs.zero) ra c' :: cs') sg

section STACKS
variable {abi : AbiKind} {tge : Mach.CGenv}

/-- `Stackingproof.stack_contents_change_meminj` -/
theorem stack_contents_change_meminj {m : Mem} {j j' : Val.Meminj} (hj : Val.inject_incr j j') :
    ∀ (cs : List Linear.Stackframe) (cs' : List Mach.Stackframe) (P : MAssert),
      m ⊨ stackContents abi j cs cs' ** P → m ⊨ stackContents abi j' cs cs' ** P
  | [], [], _, h => h
  | [], _ :: _, _, h => h
  | _ :: _, [], _, h => h
  | .Stackframe f sp ls c :: cs, .Stackframe fb sp' ra c' :: cs', P, h => by
    cases sp' with
    | Vptr sp' ofs =>
      simp only [stackContents] at h ⊢
      have h1 := (sep_assoc _ _ _).pred.1 h
      have h2 := frame_contents_incr h1 hj
      have h3 := (sep_swap _ _ _).pred.1 h2
      have h4 := stack_contents_change_meminj hj cs cs' _ h3
      exact (sep_assoc _ _ _).pred.2 ((sep_swap _ _ _).pred.1 h4)
    | _ => exact h

/-- `Stackingproof.match_stacks_change_meminj` -/
theorem match_stacks_change_meminj {j j' : Val.Meminj} (hj : Val.inject_incr j j')
    {cs : List Linear.Stackframe} {cs' : List Mach.Stackframe} {sg : Signature}
    (h : MatchStacks abi tge j cs cs' sg) : MatchStacks abi tge j' cs cs' sg := by
  induction h with
  | empty sg h => exact .empty sg h
  | cons f sp ls c cs fb sp' ra c' cs' sg trf h1 h2 h3 h4 h5 h6 h7 h8 _ ih =>
    exact .cons f sp ls c cs fb sp' ra c' cs' sg trf h1 h2 h3 h4 (hj _ _ _ h5) h6 h7 h8 ih

/-- `Stackingproof.match_stacks_change_sig` -/
theorem match_stacks_change_sig {sg1 : Signature} {j : Val.Meminj}
    {cs : List Linear.Stackframe} {cs' : List Mach.Stackframe} {sg : Signature}
    (h : MatchStacks abi tge j cs cs' sg) (htp : TailcallPossible abi sg1) :
    MatchStacks abi tge j cs cs' sg1 := by
  cases h with
  | empty sg _ => exact .empty sg1 htp
  | cons f sp ls c cs fb sp' ra c' cs' sg trf h1 h2 h3 h4 h5 h6 h7 _ h9 =>
    exact .cons f sp ls c cs fb sp' ra c' cs' sg1 trf h1 h2 h3 h4 h5 h6 h7
      (fun ofs ty hin => absurd (htp _ hin) id) h9

/-- `Stackingproof.match_stacks_type_sp` -/
theorem match_stacks_type_sp {j : Val.Meminj} {cs : List Linear.Stackframe}
    {cs' : List Mach.Stackframe} {sg : Signature} (h : MatchStacks abi tge j cs cs' sg) :
    Val.HasType (Mach.parentSp cs') Tptr := by
  cases h with
  | empty => exact Val.Vnullptr_has_type
  | cons => exact Val.Vptr_has_type _ _

/-- `Stackingproof.match_stacks_type_retaddr` -/
theorem match_stacks_type_retaddr {j : Val.Meminj} {cs : List Linear.Stackframe}
    {cs' : List Mach.Stackframe} {sg : Signature} (h : MatchStacks abi tge j cs cs' sg) :
    Val.HasType (Mach.parentRa cs') Tptr := by
  cases h with
  | empty => exact Val.Vnullptr_has_type
  | cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h6 => exact h6

end STACKS

/-! ## Syntactic properties of the translation -/

/-- `Stackingproof.find_label_save_callee_save` -/
theorem find_label_save_callee_save (lbl : Mach.Label) :
    ∀ (l : List Mreg) (ofs : Z) (k : Mach.Code),
      Mach.findLabel lbl (saveCalleeSaveRec l ofs k) = Mach.findLabel lbl k
  | [], _, _ => rfl
  | _ :: l, _, k => by
    simp only [saveCalleeSaveRec, Mach.findLabel, Mach.isLabel, Bool.false_eq_true, if_false]
    exact find_label_save_callee_save lbl l _ k

/-- `Stackingproof.find_label_restore_callee_save` -/
theorem find_label_restore_callee_save (lbl : Mach.Label) :
    ∀ (l : List Mreg) (ofs : Z) (k : Mach.Code),
      Mach.findLabel lbl (restoreCalleeSaveRec l ofs k) = Mach.findLabel lbl k
  | [], _, _ => rfl
  | _ :: l, _, k => by
    simp only [restoreCalleeSaveRec, Mach.findLabel, Mach.isLabel, Bool.false_eq_true, if_false]
    exact find_label_restore_callee_save lbl l _ k

/-- `Stackingproof.transl_code_eq` -/
theorem transl_code_eq (fe : FrameEnv) (i : Linear.Instruction) (c : Linear.Code) :
    translCode fe (i :: c) = translInstr fe i (translCode fe c) := rfl

/-- `Stackingproof.find_label_transl_code` -/
theorem find_label_transl_code (fe : FrameEnv) (lbl : Mach.Label) :
    ∀ (c : Linear.Code),
      Mach.findLabel lbl (translCode fe c) = (Linear.findLabel lbl c).map (translCode fe)
  | [] => rfl
  | i :: c => by
    rw [transl_code_eq]
    have ih := find_label_transl_code fe lbl c
    cases i with
    | Lgetstack sl ofs ty r =>
      cases sl <;> simp only [translInstr, Mach.findLabel, Mach.isLabel, Linear.findLabel,
        Linear.isLabel, Bool.false_eq_true, if_false, ih]
    | Lsetstack r sl ofs ty =>
      cases sl <;> simp only [translInstr, Mach.findLabel, Mach.isLabel, Linear.findLabel,
        Linear.isLabel, Bool.false_eq_true, if_false, ih]
    | Ltailcall sg ros =>
      simp only [translInstr, restoreCalleeSave, find_label_restore_callee_save, Mach.findLabel,
        Mach.isLabel, Linear.findLabel, Linear.isLabel, Bool.false_eq_true, if_false, ih]
    | Lreturn =>
      simp only [translInstr, restoreCalleeSave, find_label_restore_callee_save, Mach.findLabel,
        Mach.isLabel, Linear.findLabel, Linear.isLabel, Bool.false_eq_true, if_false, ih]
    | Llabel l =>
      simp only [translInstr, Mach.findLabel, Mach.isLabel, Linear.findLabel, Linear.isLabel]
      by_cases e : lbl = l
      · simp [e]
      · simp [e, ih]
    | _ =>
      simp only [translInstr, Mach.findLabel, Mach.isLabel, Linear.findLabel, Linear.isLabel,
        Bool.false_eq_true, if_false, ih]

/-- `Stackingproof.transl_find_label` -/
theorem transl_find_label {abi : AbiKind} {f : Linear.Function} {tf : Mach.Function}
    {lbl : Mach.Label} {c : Linear.Code} (h : transfFunction abi f = .OK tf)
    (hf : Linear.findLabel lbl f.fn_code = some c) :
    Mach.findLabel lbl tf.fn_code = some (translCode (fenv abi f) c) := by
  rw [unfold_transf_function h]
  simp only [translBody, saveCalleeSave]
  rw [find_label_save_callee_save, find_label_transl_code, hf]
  rfl

/-- `Stackingproof.find_label_tail` -/
theorem find_label_tail {lbl : Linear.Label} {c c' : Linear.Code}
    (h : Linear.findLabel lbl c = some c') : c' <:+ c := by
  induction c with
  | nil => cases h
  | cons a c ih =>
    simp only [Linear.findLabel] at h
    split at h
    · cases h; exact List.suffix_cons a c'
    · exact (ih h).trans (List.suffix_cons a c)

/-- `Stackingproof.is_tail_save_callee_save` -/
theorem is_tail_save_callee_save :
    ∀ (l : List Mreg) (ofs : Z) (k : Mach.Code), k <:+ saveCalleeSaveRec l ofs k
  | [], _, k => List.suffix_refl k
  | _ :: l, _, k => (is_tail_save_callee_save l _ k).trans (List.suffix_cons _ _)

/-- `Stackingproof.is_tail_restore_callee_save` -/
theorem is_tail_restore_callee_save :
    ∀ (l : List Mreg) (ofs : Z) (k : Mach.Code), k <:+ restoreCalleeSaveRec l ofs k
  | [], _, k => List.suffix_refl k
  | _ :: l, _, k => (is_tail_restore_callee_save l _ k).trans (List.suffix_cons _ _)

/-- `Stackingproof.is_tail_transl_instr` -/
theorem is_tail_transl_instr (fe : FrameEnv) (i : Linear.Instruction) (k : Mach.Code) :
    k <:+ translInstr fe i k := by
  cases i with
  | Lgetstack sl _ _ _ => cases sl <;> exact List.suffix_cons _ _
  | Lsetstack _ sl _ _ =>
    cases sl
    · exact List.suffix_cons _ _
    · exact List.suffix_refl _
    · exact List.suffix_cons _ _
  | Ltailcall _ _ =>
    exact (List.suffix_cons _ _).trans (is_tail_restore_callee_save _ _ _)
  | Lreturn =>
    exact (List.suffix_cons _ _).trans (is_tail_restore_callee_save _ _ _)
  | _ => exact List.suffix_cons _ _

/-- `Stackingproof.is_tail_transl_code` -/
theorem is_tail_transl_code (fe : FrameEnv) {c1 c2 : Linear.Code} (h : c1 <:+ c2) :
    translCode fe c1 <:+ translCode fe c2 := by
  obtain ⟨l, rfl⟩ := h
  induction l with
  | nil => exact List.suffix_refl _
  | cons i l ih =>
    rw [List.cons_append, transl_code_eq]
    exact ih.trans (is_tail_transl_instr fe i _)

/-- `Stackingproof.is_tail_transf_function` -/
theorem is_tail_transf_function {abi : AbiKind} {f : Linear.Function} {tf : Mach.Function}
    {c : Linear.Code} (h : transfFunction abi f = .OK tf) (hc : c <:+ f.fn_code) :
    translCode (fenv abi f) c <:+ tf.fn_code := by
  rw [unfold_transf_function h]
  exact (is_tail_transl_code _ hc).trans (is_tail_save_callee_save _ _ _)

/-! ## Preservation of global symbols and functions -/

section PRESERVATION
variable {abi : AbiKind} {prog : Linear.Program} {tprog : Mach.Program}
  (TRANSF : MatchProg abi prog tprog)
include TRANSF

/-- `Stackingproof.symbols_preserved` -/
theorem symbols_preserved (id : Ident) :
    Genv.findSymbol tprog.globalenv id = Genv.findSymbol prog.globalenv id :=
  find_symbol_transf_partial TRANSF id

/-- `Stackingproof.senv_preserved` -/
theorem senv_preserved : Genv.toSenv tprog.globalenv = Genv.toSenv prog.globalenv :=
  senv_transf_partial TRANSF

/-- `Stackingproof.functions_translated` -/
theorem functions_translated {v : Val} {f : Linear.Fundef}
    (h : Genv.findFunct prog.globalenv v = some f) :
    ∃ tf, Genv.findFunct tprog.globalenv v = some tf ∧ Stacking.transfFundef abi f = .OK tf :=
  find_funct_transf_partial TRANSF h

/-- `Stackingproof.function_ptr_translated` -/
theorem function_ptr_translated {b : Block} {f : Linear.Fundef}
    (h : Genv.findFunctPtr prog.globalenv b = some f) :
    ∃ tf, Genv.findFunctPtr tprog.globalenv b = some tf ∧ Stacking.transfFundef abi f = .OK tf :=
  find_funct_ptr_transf_partial TRANSF h

omit TRANSF in
/-- `Stackingproof.sig_preserved` -/
theorem sig_preserved {f : Linear.Fundef} {tf : Mach.Fundef} (h : Stacking.transfFundef abi f = .OK tf) :
    Mach.funsig tf = Linear.funsig f := by
  cases f with
  | Internal f =>
    simp only [Stacking.transfFundef, ASTFundef.transfPartial] at h
    cases e : transfFunction abi f with
    | Error _ => rw [e] at h; cases h
    | OK tf' =>
      rw [e] at h; cases h
      rw [unfold_transf_function e]; rfl
  | External ef =>
    simp only [Stacking.transfFundef, ASTFundef.transfPartial] at h
    cases h; rfl

/-- `Stackingproof.find_function_translated` -/
theorem find_function_translated {j : Val.Meminj} {ls : LTL.Locset} {rs : Regset} {m : Mem}
    {ros : Sum Mreg Ident} {f : Linear.Fundef} (AG : AgreeRegs j ls rs)
    (hm : m ⊨ globalenvInject prog.globalenv j)
    (FF : Linear.findFunction prog.globalenv ros ls = some f) :
    ∃ bf tf, Mach.findFunctionPtr tprog.globalenv ros rs = some bf ∧
      Genv.findFunctPtr tprog.globalenv bf = some tf ∧ Stacking.transfFundef abi f = .OK tf := by
  obtain ⟨bound, _, E⟩ := hm
  cases ros with
  | inl r =>
    simp only [Linear.findFunction] at FF
    obtain ⟨b, EQ⟩ := Genv.findFunct_inv FF
    rw [EQ, Genv.findFunct_findFunctPtr] at FF
    obtain ⟨tf, A, B⟩ := function_ptr_translated TRANSF FF
    refine ⟨b, tf, ?_, A, B⟩
    have INJ := AG r
    rw [EQ] at INJ
    simp only [Mach.findFunctionPtr]
    generalize rs r = v at INJ ⊢
    cases INJ with
    | ptr delta hb ho =>
      rw [E.domain b (E.functions b f FF)] at hb
      cases hb
      subst ho
      rw [Integers.Ptrofs.repr_zero, Integers.Ptrofs.add_zero]
      simp [Integers.Ptrofs.eq_true]
  | inr id =>
    simp only [Linear.findFunction] at FF
    cases e : Genv.findSymbol prog.globalenv id with
    | none => rw [e] at FF; cases FF
    | some b =>
      rw [e] at FF
      obtain ⟨tf, A, B⟩ := function_ptr_translated TRANSF FF
      exact ⟨b, tf, by simp only [Mach.findFunctionPtr, symbols_preserved TRANSF, e], A, B⟩

end PRESERVATION

/-! ## Preservation of the arguments to an external call -/

section EXTERNAL_ARGUMENTS
variable {abi : AbiKind} {tge : Mach.CGenv} {j : Val.Meminj} {cs : List Linear.Stackframe}
  {cs' : List Mach.Stackframe} {sg : Signature} {ls : LTL.Locset} {rs : Regset} {m' : Mem}
  (MS : MatchStacks abi tge j cs cs' sg) (AGR : AgreeRegs j ls rs)
  (AGARGS : AgreeOutgoingArguments abi sg ls (Linear.parentLocset cs))
  (SEP : m' ⊨ stackContents abi j cs cs')
include MS AGR AGARGS SEP

/-- `Stackingproof.transl_external_argument` -/
theorem transl_external_argument {l : Loc} (hl : l ∈ RPair.regsList (locArguments abi sg)) :
    ∃ v, ExtcallArg rs m' (Mach.parentSp cs') l v ∧ Val.Inject j (ls l) v := by
  have hacc := locArguments_acceptable_2 abi sg l hl
  cases l with
  | R r => exact ⟨rs r, .reg r, AGR r⟩
  | S sl pos ty =>
    cases sl <;> simp only [LocArgumentAcceptable] at hacc
    cases MS with
    | empty _ htp => exact absurd (htp _ hl) id
    | cons f sp ls0 c cs0 fb sp' ra c' cs0' _ trf _ _ _ _ _ _ _ hbnd _ =>
      simp only [stackContents] at SEP
      have hv := slot_outgoing_argument_valid abi f pos ty sg hl
      obtain ⟨v, A, B⟩ := frame_get_outgoing SEP (hbnd _ _ hl) hv
      refine ⟨v, .stack pos ty v A, ?_⟩
      rw [AGARGS ty pos hl]
      exact B

end EXTERNAL_ARGUMENTS

section EXTERNAL_ARGUMENTS2
variable {abi : AbiKind} {tge : Mach.CGenv} {j : Val.Meminj} {cs : List Linear.Stackframe}
  {cs' : List Mach.Stackframe} {sg : Signature} {ls : LTL.Locset} {rs : Regset} {m' : Mem}
  (MS : MatchStacks abi tge j cs cs' sg) (AGR : AgreeRegs j ls rs)
  (AGARGS : AgreeOutgoingArguments abi sg ls (Linear.parentLocset cs))
  (SEP : m' ⊨ stackContents abi j cs cs')
include MS AGR AGARGS SEP

/-- `Stackingproof.transl_external_argument_2` -/
theorem transl_external_argument_2 {p : RPair Loc} (hp : p ∈ locArguments abi sg) :
    ∃ v, ExtcallArgPair rs m' (Mach.parentSp cs') p v ∧ Val.Inject j (Locmap.getpair p ls) v := by
  cases p with
  | One l =>
    obtain ⟨v, A, B⟩ := transl_external_argument MS AGR AGARGS SEP
      (RPair.in_regsList (x := l) (by simp [RPair.regs]) hp)
    exact ⟨v, .one _ _ A, B⟩
  | Twolong l1 l2 =>
    obtain ⟨v1, A1, B1⟩ := transl_external_argument MS AGR AGARGS SEP
      (RPair.in_regsList (x := l1) (by simp [RPair.regs]) hp)
    obtain ⟨v2, A2, B2⟩ := transl_external_argument MS AGR AGARGS SEP
      (RPair.in_regsList (x := l2) (by simp [RPair.regs]) hp)
    exact ⟨_, .twolong _ _ _ _ A1 A2, Val.longofwords_inject B1 B2⟩

/-- `Stackingproof.transl_external_arguments_rec` -/
theorem transl_external_arguments_rec :
    ∀ (locs : List (RPair Loc)), (∀ p ∈ locs, p ∈ locArguments abi sg) →
      ∃ vl, ListForall2 (ExtcallArgPair rs m' (Mach.parentSp cs')) locs vl ∧
        Val.InjectList j (locs.map fun p => Locmap.getpair p ls) vl
  | [], _ => ⟨[], .nil, .nil⟩
  | p :: locs, h => by
    obtain ⟨v, A, B⟩ := transl_external_argument_2 MS AGR AGARGS SEP (h p (by simp))
    obtain ⟨vl, C, D⟩ := transl_external_arguments_rec locs (fun q hq => h q (by simp [hq]))
    exact ⟨v :: vl, .cons A C, .cons B D⟩

/-- `Stackingproof.transl_external_arguments` -/
theorem transl_external_arguments :
    ∃ vl, ExtcallArguments abi rs m' (Mach.parentSp cs') sg vl ∧
      Val.InjectList j ((locArguments abi sg).map fun p => Locmap.getpair p ls) vl :=
  transl_external_arguments_rec MS AGR AGARGS SEP _ (fun _ h => h)

end EXTERNAL_ARGUMENTS2

/-! ## Preservation of the arguments to a builtin -/

/-- Global symbol addresses inject into themselves under `globalenv_inject`. -/
theorem symbolAddress_inject_of_globalenvInject {F V : Type} {ge : Genv F V} {j : Val.Meminj}
    {m : Mem} (h : m ⊨ globalenvInject ge j) (id : Ident) (ofs : Integers.Ptrofs) :
    Val.Inject j ((Genv.toSenv ge).symbolAddress id ofs) ((Genv.toSenv ge).symbolAddress id ofs) := by
  rw [Genv.toSenv_symbolAddress]
  unfold Genv.symbolAddress
  split
  · next b hb =>
    exact .ptr 0 ((globalenvInject_preserves_globals h).1 id b hb)
      (by rw [Integers.Ptrofs.repr_zero, Integers.Ptrofs.add_zero])
  · exact .undef _

section BUILTIN_ARGUMENTS
variable {abi : AbiKind} {f : Linear.Function} {F V : Type} {ge : Genv F V} {j : Val.Meminj}
  {m m' : Mem} {ls ls0 : LTL.Locset} {rs : Regset} {sp sp' : Block} {parent retaddr : Val}
  (INJ : j sp = some (sp', (fenv abi f).fe_stack_data)) (AGR : AgreeRegs j ls rs)
  (SEP : m' ⊨ frameContents abi f j sp' ls ls0 parent retaddr ** minjection j m **
    globalenvInject ge j)
include INJ AGR SEP

omit AGR SEP in
private theorem stack_offset_inject (ofs : Integers.Ptrofs) :
    Val.Inject j (Val.offsetPtr (.Vptr sp Integers.Ptrofs.zero) ofs)
      (Val.offsetPtr (.Vptr sp' Integers.Ptrofs.zero)
        (Integers.Ptrofs.add ofs (Integers.Ptrofs.repr (fenv abi f).fe_stack_data))) := by
  simp only [Val.offsetPtr, Integers.Ptrofs.add_zero_l]
  exact .ptr _ INJ rfl

/-- `Stackingproof.transl_builtin_arg_correct` -/
theorem transl_builtin_arg_correct {a : BuiltinArg Loc} {v : Val}
    (hev : EvalBuiltinArg (Genv.toSenv ge) ls (.Vptr sp Integers.Ptrofs.zero) m a v)
    (VALID : ∀ l ∈ BuiltinArg.params a, locValid abi f l = true)
    (BOUNDS : ∀ sl ofs ty, Loc.S sl ofs ty ∈ BuiltinArg.params a →
      SlotWithinBounds (bnds abi f) sl ofs ty) :
    ∃ v', EvalBuiltinArg (Genv.toSenv ge) rs (.Vptr sp' Integers.Ptrofs.zero) m'
        (translBuiltinArg (fenv abi f) a) v' ∧ Val.Inject j v v' := by
  have SYMB := symbolAddress_inject_of_globalenvInject (sep_proj2 (sep_proj2 SEP))
  have MINJ := sep_proj1 (sep_proj2 SEP)
  induction hev with
  | BA x =>
    have hv := VALID x (by simp [BuiltinArg.params])
    cases x with
    | R r => exact ⟨rs r, .BA r, AGR r⟩
    | S sl ofs ty =>
      cases sl with
      | Local =>
        obtain ⟨v, A, B⟩ := frame_get_local SEP
          (BOUNDS _ _ _ (by simp [BuiltinArg.params])) hv
        exact ⟨v, .BA_loadstack _ _ _ A, B⟩
      | _ => simp [locValid] at hv
  | BA_int n => exact ⟨_, .BA_int n, .int n⟩
  | BA_long n => exact ⟨_, .BA_long n, .long n⟩
  | BA_float n => exact ⟨_, .BA_float n, .float n⟩
  | BA_single n => exact ⟨_, .BA_single n, .single n⟩
  | BA_loadstack chunk ofs v hl =>
    obtain ⟨v', A, B⟩ := loadv_parallel_rule MINJ hl (stack_offset_inject INJ ofs)
    exact ⟨v', .BA_loadstack _ _ _ A, B⟩
  | BA_addrstack ofs => exact ⟨_, .BA_addrstack _, stack_offset_inject INJ ofs⟩
  | BA_loadglobal chunk id ofs v hl =>
    obtain ⟨v', A, B⟩ := loadv_parallel_rule MINJ hl (SYMB id ofs)
    exact ⟨v', .BA_loadglobal _ _ _ _ A, B⟩
  | BA_addrglobal id ofs => exact ⟨_, .BA_addrglobal id ofs, SYMB id ofs⟩
  | BA_splitlong hi lo vhi vlo _ _ ih1 ih2 =>
    obtain ⟨v1, A1, B1⟩ := ih1 (fun l hl => VALID l (by simp [BuiltinArg.params, hl]))
      (fun sl ofs ty hl => BOUNDS sl ofs ty (by simp [BuiltinArg.params, hl]))
    obtain ⟨v2, A2, B2⟩ := ih2 (fun l hl => VALID l (by simp [BuiltinArg.params, hl]))
      (fun sl ofs ty hl => BOUNDS sl ofs ty (by simp [BuiltinArg.params, hl]))
    exact ⟨_, .BA_splitlong _ _ _ _ A1 A2, Val.longofwords_inject B1 B2⟩
  | BA_addptr a1 a2 v1 v2 _ _ ih1 ih2 =>
    obtain ⟨v1', A1, B1⟩ := ih1 (fun l hl => VALID l (by simp [BuiltinArg.params, hl]))
      (fun sl ofs ty hl => BOUNDS sl ofs ty (by simp [BuiltinArg.params, hl]))
    obtain ⟨v2', A2, B2⟩ := ih2 (fun l hl => VALID l (by simp [BuiltinArg.params, hl]))
      (fun sl ofs ty hl => BOUNDS sl ofs ty (by simp [BuiltinArg.params, hl]))
    refine ⟨_, .BA_addptr _ _ _ _ A1 A2, ?_⟩
    simp only [Archi.ptr64, ite_true]
    exact Builtins.addl_inject B1 B2

/-- `Stackingproof.transl_builtin_args_correct` -/
theorem transl_builtin_args_correct :
    ∀ {al : List (BuiltinArg Loc)} {vl : List Val},
    EvalBuiltinArgs (Genv.toSenv ge) ls (.Vptr sp Integers.Ptrofs.zero) m al vl →
    (∀ l ∈ BuiltinArg.paramsList al, locValid abi f l = true) →
    (∀ sl ofs ty, Loc.S sl ofs ty ∈ BuiltinArg.paramsList al →
      SlotWithinBounds (bnds abi f) sl ofs ty) →
    ∃ vl', EvalBuiltinArgs (Genv.toSenv ge) rs (.Vptr sp' Integers.Ptrofs.zero) m'
        (al.map (translBuiltinArg (fenv abi f))) vl' ∧ Val.InjectList j vl vl'
  | [], [], .nil, _, _ => ⟨[], .nil, .nil⟩
  | a :: al, v :: vl, .cons h1 h2, VALID, BOUNDS => by
    obtain ⟨v1', A, B⟩ := transl_builtin_arg_correct INJ AGR SEP h1
      (fun l hl => VALID l (by simp [BuiltinArg.paramsList, hl]))
      (fun sl ofs ty hl => BOUNDS sl ofs ty (by simp [BuiltinArg.paramsList, hl]))
    obtain ⟨vl', C, D⟩ := transl_builtin_args_correct h2
      (fun l hl => VALID l (by simp only [BuiltinArg.paramsList, List.flatMap_cons,
        List.mem_append] at hl ⊢; exact .inr hl))
      (fun sl ofs ty hl => BOUNDS sl ofs ty (by simp only [BuiltinArg.paramsList,
        List.flatMap_cons, List.mem_append] at hl ⊢; exact .inr hl))
    exact ⟨v1' :: vl', .cons A C, .cons B D⟩

end BUILTIN_ARGUMENTS

end Stackingproof
end CC
