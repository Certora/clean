/-
  [RISC-V instance of `CCLib/backend/ValueAnalysisSoundStack.lean`: the same development, in
  namespace `CC.RiscV`, over the RISC-V operators, registers and conventions.]

  Soundness of the value analysis, part 4 — the semantic invariant of
  `backend/ValueAnalysis.v` (section `SOUNDNESS`): `sound_stack`,
  `sound_state_base` and the properties of `sound_stack`.

  Ported: `sound_stack`, `sound_state_base`, `sound_stack_ext`,
  `sound_stack_inv`, `sound_stack_storev`, `sound_stack_storebytes`,
  `sound_stack_free`, `sound_stack_new_bound`, `sound_stack_exten`,
  `sound_succ_state`.

  Differences from Rocq: the section variable `prog` only served to define
  `rm := romem_for prog`; the invariant is stated for an arbitrary
  read-only memory abstraction `rm` (the step is sound for any `rm`, only
  the initial state needs `rm = romem_for prog`).  The analysis options `o`
  and the calling convention `abi` are explicit parameters, as for
  `analyze`.
-/
import CCLib.riscV.ValueAnalysisSoundExtcall

namespace CC
namespace RiscV
namespace ValueAnalysis

open ValueDomain RTL
open Integers (Ptrofs)

section SOUNDNESS
variable (o : ValueAOp.Options) (rm : Romem) (ge : RTL.CGenv)

/-- `ValueAnalysis.sound_stack` -/
inductive SoundStack : BlockClassification → List RTL.Stackframe → Mem → Block → Prop where
  | nil (bc : BlockClassification) (m : Mem) (bound : Block) : SoundStack bc [] m bound
  | public_call {bc : BlockClassification} {res : Reg} {f : RTL.Function} {sp : Block}
      {pc : Node} {e : RTL.Regset} {stk : List RTL.Stackframe} {m : Mem} {bound : Block}
      {bc' : BlockClassification} {bound' : Block} {ae : Aenv}
      (STK : SoundStack bc' stk m sp) (INCR : bound' ≤ bound) (BELOW : bcBelow bc' bound')
      (SP : bc sp = .BCother) (SP' : bc' sp = .BCstack)
      (SAME : ∀ b, b < bound' → b ≠ sp → bc b = bc' b) (GE : GenvMatch bc' ge)
      (AN : VA.Ge ((analyze o  rm f).get pc) (.State (AE.set res Vtop ae) mafterPublicCall))
      (EM : Ematch bc' e ae) :
      SoundStack bc (.Stackframe res f (.Vptr sp Ptrofs.zero) pc e :: stk) m bound
  | private_call {bc : BlockClassification} {res : Reg} {f : RTL.Function} {sp : Block}
      {pc : Node} {e : RTL.Regset} {stk : List RTL.Stackframe} {m : Mem} {bound : Block}
      {bc' : BlockClassification} {bound' : Block} {ae : Aenv} {am : Amem}
      (STK : SoundStack bc' stk m sp) (INCR : bound' ≤ bound) (BELOW : bcBelow bc' bound')
      (SP : bc sp = .BCinvalid) (SP' : bc' sp = .BCstack)
      (SAME : ∀ b, b < bound' → b ≠ sp → bc b = bc' b) (GE : GenvMatch bc' ge)
      (AN : VA.Ge ((analyze o  rm f).get pc)
        (.State (AE.set res (.Ifptr .Nonstack) ae) (mafterPrivateCall am)))
      (EM : Ematch bc' e ae) (CONTENTS : Bmatch bc' m sp am.am_stack) :
      SoundStack bc (.Stackframe res f (.Vptr sp Ptrofs.zero) pc e :: stk) m bound

/-- `ValueAnalysis.sound_state_base` -/
inductive SoundStateBase : RTL.State → Prop where
  | regular {s : List RTL.Stackframe} {f : RTL.Function} {sp : Block} {pc : Node} {e : RTL.Regset}
      {m : Mem} {ae : Aenv} {am : Amem} {bc : BlockClassification}
      (STK : SoundStack o  rm ge bc s m sp)
      (AN : (analyze o  rm f).get pc = .State ae am)
      (EM : Ematch bc e ae) (RO : Romatch bc m rm) (MM : Mmatch bc m am)
      (GE : GenvMatch bc ge) (SP : bc sp = .BCstack) :
      SoundStateBase (.State s f (.Vptr sp Ptrofs.zero) pc e m)
  | call {s : List RTL.Stackframe} {fd : RTL.Fundef} {args : List Val} {m : Mem}
      {bc : BlockClassification}
      (STK : SoundStack o  rm ge bc s m m.nextblock)
      (ARGS : ∀ v, v ∈ args → Vmatch bc v Vtop) (RO : Romatch bc m rm)
      (MM : Mmatch bc m mtop) (GE : GenvMatch bc ge) (NOSTK : BcNostack bc) :
      SoundStateBase (.Callstate s fd args m)
  | ret {s : List RTL.Stackframe} {v : Val} {m : Mem} {bc : BlockClassification}
      (STK : SoundStack o  rm ge bc s m m.nextblock)
      (RES : Vmatch bc v Vtop) (RO : Romatch bc m rm)
      (MM : Mmatch bc m mtop) (GE : GenvMatch bc ge) (NOSTK : BcNostack bc) :
      SoundStateBase (.Returnstate s v m)

/-! ## Properties of the `sound_stack` invariant on call stacks -/

variable {o  rm ge}

/-- `ValueAnalysis.sound_stack_ext` -/
theorem sound_stack_ext {m' : Mem} {bc : BlockClassification} {stk : List RTL.Stackframe} {m : Mem}
    {bound : Block} (h : SoundStack o  rm ge bc stk m bound)
    (INV : ∀ b ofs n bytes, b < bound → bc b = .BCinvalid → n ≥ 0 →
      Mem.loadbytes m' b ofs n = some bytes → Mem.loadbytes m b ofs n = some bytes) :
    SoundStack o  rm ge bc stk m' bound := by
  induction h with
  | nil => exact .nil _ _ _
  | @public_call bc res f sp pc e stk m bound bc' bound' ae STK INCR BELOW SP SP' SAME GE AN EM
      IH =>
    have hsp : sp < bound' := BELOW sp (by rw [SP']; simp)
    refine .public_call (IH fun b ofs n bytes hb hinv hn hl => ?_) INCR BELOW SP SP' SAME GE AN EM
    have hne : b ≠ sp := fun e => by subst e; exact Nat.lt_irrefl _ hb
    have hb' : b < bound' := Nat.lt_trans hb hsp
    exact INV b ofs n bytes (Nat.lt_of_lt_of_le hb' INCR) (by rw [SAME b hb' hne]; exact hinv) hn hl
  | @private_call bc res f sp pc e stk m bound bc' bound' ae am STK INCR BELOW SP SP' SAME GE AN
      EM CONTENTS IH =>
    have hsp : sp < bound' := BELOW sp (by rw [SP']; simp)
    refine .private_call (IH fun b ofs n bytes hb hinv hn hl => ?_) INCR BELOW SP SP' SAME GE AN
      EM (bmatch_ext CONTENTS fun ofs n bytes hl hn => ?_)
    · have hne : b ≠ sp := fun e => by subst e; exact Nat.lt_irrefl _ hb
      have hb' : b < bound' := Nat.lt_trans hb hsp
      exact INV b ofs n bytes (Nat.lt_of_lt_of_le hb' INCR) (by rw [SAME b hb' hne]; exact hinv)
        hn hl
    · exact INV sp ofs n bytes (Nat.lt_of_lt_of_le hsp INCR) SP hn hl

/-- `ValueAnalysis.sound_stack_inv` -/
theorem sound_stack_inv {m' : Mem} {bc : BlockClassification} {stk : List RTL.Stackframe} {m : Mem}
    {bound : Block} (h : SoundStack o  rm ge bc stk m bound)
    (INV : ∀ b ofs n, b < bound → bc b = .BCinvalid → n ≥ 0 →
      Mem.loadbytes m' b ofs n = Mem.loadbytes m b ofs n) :
    SoundStack o  rm ge bc stk m' bound :=
  sound_stack_ext h fun b ofs n bytes hb hi hn hl => by rw [← INV b ofs n hb hi hn]; exact hl

/-- `ValueAnalysis.sound_stack_storev` -/
theorem sound_stack_storev {chunk : Chunk} {m : Mem} {addr v : Val} {m' : Mem}
    {bc : BlockClassification} {aaddr : Aval} {stk : List RTL.Stackframe} {bound : Block}
    (hs : Mem.storev chunk m addr v = some m') (ha : Vmatch bc addr aaddr)
    (h : SoundStack o  rm ge bc stk m bound) : SoundStack o  rm ge bc stk m' bound := by
  cases addr with
  | Vptr b i =>
    simp only [Mem.storev] at hs
    split at hs
    case isFalse => cases hs
    have A : Pmatch bc b i .Ptop := vmatch_ptr_top ha
    cases A with
    | top hb =>
      refine sound_stack_inv h fun b' ofs n _ hi _ => ?_
      exact Mem.loadbytes_store_other hs b' ofs n (.inl fun e => by subst e; exact hb hi)
  | _ => cases hs

/-- `ValueAnalysis.sound_stack_storebytes` -/
theorem sound_stack_storebytes {m : Mem} {b : Block} {ofs : Ptrofs} {bytes : List MemVal}
    {m' : Mem} {bc : BlockClassification} {aaddr : Aval} {stk : List RTL.Stackframe} {bound : Block}
    (hs : Mem.storebytes m b (Ptrofs.unsigned ofs) bytes = some m')
    (ha : Vmatch bc (.Vptr b ofs) aaddr)
    (h : SoundStack o  rm ge bc stk m bound) : SoundStack o  rm ge bc stk m' bound := by
  have A : Pmatch bc b ofs .Ptop := vmatch_ptr_top ha
  cases A with
  | top hb =>
    refine sound_stack_inv h fun b' ofs' n _ hi _ => ?_
    exact Mem.loadbytes_storebytes_other hs b' ofs' n (.inl fun e => by subst e; exact hb hi)

/-- `ValueAnalysis.sound_stack_free` -/
theorem sound_stack_free {m : Mem} {b : Block} {lo hi : Z} {m' : Mem}
    {bc : BlockClassification} {stk : List RTL.Stackframe} {bound : Block}
    (hf : Mem.free m b lo hi = some m')
    (h : SoundStack o  rm ge bc stk m bound) : SoundStack o  rm ge bc stk m' bound :=
  sound_stack_ext h fun _ _ _ _ _ _ _ hl => Mem.loadbytes_free_2 hf hl

/-- `ValueAnalysis.sound_stack_new_bound` -/
theorem sound_stack_new_bound {bc : BlockClassification} {stk : List RTL.Stackframe} {m : Mem}
    {bound bound' : Block} (h : SoundStack o  rm ge bc stk m bound) (hle : bound ≤ bound') :
    SoundStack o  rm ge bc stk m bound' := by
  cases h with
  | nil => exact .nil _ _ _
  | public_call STK INCR BELOW SP SP' SAME GE AN EM =>
    exact .public_call STK (Nat.le_trans INCR hle) BELOW SP SP' SAME GE AN EM
  | private_call STK INCR BELOW SP SP' SAME GE AN EM CONTENTS =>
    exact .private_call STK (Nat.le_trans INCR hle) BELOW SP SP' SAME GE AN EM CONTENTS

/-- `ValueAnalysis.sound_stack_exten` -/
theorem sound_stack_exten {bc : BlockClassification} {stk : List RTL.Stackframe} {m : Mem}
    {bound : Block} {bc1 : BlockClassification} (h : SoundStack o  rm ge bc stk m bound)
    (H : ∀ b, b < bound → bc1 b = bc b) : SoundStack o  rm ge bc1 stk m bound := by
  cases h with
  | nil => exact .nil _ _ _
  | @public_call _ res f sp pc e stk m bound bc' bound' ae STK INCR BELOW SP SP' SAME GE AN EM =>
    have hsp : sp < bound := Nat.lt_of_lt_of_le (BELOW sp (by rw [SP']; simp)) INCR
    refine .public_call STK INCR BELOW (by rw [H sp hsp]; exact SP) SP' (fun b hb hne => ?_) GE AN
      EM
    rw [H b (Nat.lt_of_lt_of_le hb INCR)]; exact SAME b hb hne
  | @private_call _ res f sp pc e stk m bound bc' bound' ae am STK INCR BELOW SP SP' SAME GE AN EM
      CONTENTS =>
    have hsp : sp < bound := Nat.lt_of_lt_of_le (BELOW sp (by rw [SP']; simp)) INCR
    refine .private_call STK INCR BELOW (by rw [H sp hsp]; exact SP) SP' (fun b hb hne => ?_) GE
      AN EM CONTENTS
    rw [H b (Nat.lt_of_lt_of_le hb INCR)]; exact SAME b hb hne

/-! ## Preservation of the semantic invariant by one step of execution -/

/-- `ValueAnalysis.sound_succ_state` -/
theorem sound_succ_state {bc : BlockClassification} {pc : Node} {ae : Aenv} {am : Amem}
    {instr : Instruction} {ae' : Aenv} {am' : Amem} {s : List RTL.Stackframe} {f : RTL.Function}
    {sp : Block} {pc' : Node} {e' : RTL.Regset} {m' : Mem}
    (hn : (analyze o  rm f).get pc = .State ae am) (hcode : f.fn_code.get pc = some instr)
    (hs : pc' ∈ successorsInstr instr) (ht : transfer o f rm pc ae am = .State ae' am')
    (EM : Ematch bc e' ae') (MM : Mmatch bc m' am') (RO : Romatch bc m' rm)
    (GE : GenvMatch bc ge) (SP : bc sp = .BCstack) (STK : SoundStack o  rm ge bc s m' sp) :
    SoundStateBase o  rm ge (.State s f (.Vptr sp Ptrofs.zero) pc' e' m') := by
  obtain ⟨ae'', am'', AN, EM', MM'⟩ := analyze_succ o  hn hcode hs ht EM MM
  exact .regular STK AN EM' RO MM' GE SP

end SOUNDNESS

end ValueAnalysis
end RiscV
end CC
