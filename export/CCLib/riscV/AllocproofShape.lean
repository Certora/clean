/-
  [RISC-V instance of `CCLib/backend/AllocproofShape.lean`: the same development, in
  namespace `CC.RiscV`, over the RISC-V operators, registers and conventions.]

  Correctness of register allocation, part 1 — port of the beginning of
  `backend/Allocproof.v`: `match_prog`, `expand_move(s)`, `wf_move(s)`,
  `expand_block_shape`, and the soundness of the structural checks
  (`extract_moves_sound`, `extract_moves_ext_sound`, `check_succ_sound`,
  `pair_instr_block_sound`, `matching_instr_block`).
-/
import CCLib.riscV.Allocation

namespace CC
namespace RiscV
namespace Allocproof

open Op Allocation LTL

/-- `Allocproof.match_prog` -/
def MatchProg (regalloc : RTL.Function → Res LTL.Function)
    (p : RTL.Program) (tp : LTL.Program) : Prop :=
  transfProgram  regalloc p = .OK tp

/-- `Allocproof.expand_move` -/
def expandMove : Move → LTL.Instruction
  | .MV (.R src) (.R dst) => .Lop .Omove [src] dst
  | .MV (.S sl ofs ty) (.R dst) => .Lgetstack sl ofs ty dst
  | .MV (.R src) (.S sl ofs ty) => .Lsetstack src sl ofs ty
  | .MV (.S _ _ _) (.S _ _ _) => .Lreturn
  | .MVmakelong src1 src2 dst => .Lop .Omakelong [src1, src2] dst
  | .MVlowlong src dst => .Lop .Olowlong [src] dst
  | .MVhighlong src dst => .Lop .Ohighlong [src] dst

/-- `Allocproof.expand_moves` -/
def expandMoves (mv : Moves) (k : Bblock) : Bblock := mv.map expandMove ++ k

/-- `Allocproof.wf_move` -/
def WfMove : Move → Prop
  | .MV (.S _ _ _) (.S _ _ _) => False
  | _ => True

/-- `Allocproof.wf_moves` -/
def WfMoves (mv : Moves) : Prop := ∀ m ∈ mv, WfMove m

/-- `Allocproof.expand_block_shape` -/
inductive ExpandBlockShape : BlockShape → RTL.Instruction → LTL.Bblock → Prop where
  | nop (mv : Moves) (s : RTL.Node) (k : Bblock) :
      WfMoves mv →
      ExpandBlockShape (.BSnop mv s) (.Inop s) (expandMoves mv (.Lbranch s :: k))
  | move (src dst : Reg) (mv : Moves) (s : RTL.Node) (k : Bblock) :
      WfMoves mv →
      ExpandBlockShape (.BSmove src dst mv s) (.Iop .Omove [src] dst s)
        (expandMoves mv (.Lbranch s :: k))
  | makelong (src1 src2 dst : Reg) (mv : Moves) (s : RTL.Node) (k : Bblock) :
      WfMoves mv → Archi.splitlong = true →
      ExpandBlockShape (.BSmakelong src1 src2 dst mv s) (.Iop .Omakelong [src1, src2] dst s)
        (expandMoves mv (.Lbranch s :: k))
  | lowlong (src dst : Reg) (mv : Moves) (s : RTL.Node) (k : Bblock) :
      WfMoves mv → Archi.splitlong = true →
      ExpandBlockShape (.BSlowlong src dst mv s) (.Iop .Olowlong [src] dst s)
        (expandMoves mv (.Lbranch s :: k))
  | highlong (src dst : Reg) (mv : Moves) (s : RTL.Node) (k : Bblock) :
      WfMoves mv → Archi.splitlong = true →
      ExpandBlockShape (.BShighlong src dst mv s) (.Iop .Ohighlong [src] dst s)
        (expandMoves mv (.Lbranch s :: k))
  | op (op : Operation) (args : List Reg) (res : Reg) (mv1 : Moves) (args' : List Mreg)
      (res' : Mreg) (mv2 : Moves) (s : RTL.Node) (k : Bblock) :
      WfMoves mv1 → WfMoves mv2 →
      ExpandBlockShape (.BSop op args res mv1 args' res' mv2 s) (.Iop op args res s)
        (expandMoves mv1 (.Lop op args' res' :: expandMoves mv2 (.Lbranch s :: k)))
  | op_dead (op : Operation) (args : List Reg) (res : Reg) (mv : Moves) (s : RTL.Node)
      (k : Bblock) :
      WfMoves mv →
      ExpandBlockShape (.BSopdead op args res mv s) (.Iop op args res s)
        (expandMoves mv (.Lbranch s :: k))
  | load (chunk : Chunk) (addr : Addressing) (args : List Reg) (dst : Reg) (mv1 : Moves)
      (args' : List Mreg) (dst' : Mreg) (mv2 : Moves) (s : RTL.Node) (k : Bblock) :
      WfMoves mv1 → WfMoves mv2 →
      ExpandBlockShape (.BSload chunk addr args dst mv1 args' dst' mv2 s)
        (.Iload chunk addr args dst s)
        (expandMoves mv1 (.Lload chunk addr args' dst' :: expandMoves mv2 (.Lbranch s :: k)))
  | load2 (addr addr2 : Addressing) (args : List Reg) (dst : Reg) (mv1 : Moves)
      (args1' : List Mreg) (dst1' : Mreg) (mv2 : Moves) (args2' : List Mreg) (dst2' : Mreg)
      (mv3 : Moves) (s : RTL.Node) (k : Bblock) :
      WfMoves mv1 → WfMoves mv2 → WfMoves mv3 → Archi.splitlong = true →
      offsetAddressing addr 4 = some addr2 →
      ExpandBlockShape (.BSload2 addr addr2 args dst mv1 args1' dst1' mv2 args2' dst2' mv3 s)
        (.Iload .Mint64 addr args dst s)
        (expandMoves mv1 (.Lload .Mint32 addr args1' dst1' ::
          expandMoves mv2 (.Lload .Mint32 addr2 args2' dst2' ::
            expandMoves mv3 (.Lbranch s :: k))))
  | load2_1 (addr : Addressing) (args : List Reg) (dst : Reg) (mv1 : Moves)
      (args' : List Mreg) (dst' : Mreg) (mv2 : Moves) (s : RTL.Node) (k : Bblock) :
      WfMoves mv1 → WfMoves mv2 → Archi.splitlong = true →
      ExpandBlockShape (.BSload2_1 addr args dst mv1 args' dst' mv2 s)
        (.Iload .Mint64 addr args dst s)
        (expandMoves mv1 (.Lload .Mint32 addr args' dst' :: expandMoves mv2 (.Lbranch s :: k)))
  | load2_2 (addr addr2 : Addressing) (args : List Reg) (dst : Reg) (mv1 : Moves)
      (args' : List Mreg) (dst' : Mreg) (mv2 : Moves) (s : RTL.Node) (k : Bblock) :
      WfMoves mv1 → WfMoves mv2 → Archi.splitlong = true →
      offsetAddressing addr 4 = some addr2 →
      ExpandBlockShape (.BSload2_2 addr addr2 args dst mv1 args' dst' mv2 s)
        (.Iload .Mint64 addr args dst s)
        (expandMoves mv1 (.Lload .Mint32 addr2 args' dst' :: expandMoves mv2 (.Lbranch s :: k)))
  | load_dead (chunk : Chunk) (addr : Addressing) (args : List Reg) (dst : Reg) (mv : Moves)
      (s : RTL.Node) (k : Bblock) :
      WfMoves mv →
      ExpandBlockShape (.BSloaddead chunk addr args dst mv s) (.Iload chunk addr args dst s)
        (expandMoves mv (.Lbranch s :: k))
  | store (chunk : Chunk) (addr : Addressing) (args : List Reg) (src : Reg) (mv1 : Moves)
      (args' : List Mreg) (src' : Mreg) (s : RTL.Node) (k : Bblock) :
      WfMoves mv1 →
      ExpandBlockShape (.BSstore chunk addr args src mv1 args' src' s)
        (.Istore chunk addr args src s)
        (expandMoves mv1 (.Lstore chunk addr args' src' :: .Lbranch s :: k))
  | store2 (addr addr2 : Addressing) (args : List Reg) (src : Reg) (mv1 : Moves)
      (args1' : List Mreg) (src1' : Mreg) (mv2 : Moves) (args2' : List Mreg) (src2' : Mreg)
      (s : RTL.Node) (k : Bblock) :
      WfMoves mv1 → WfMoves mv2 → Archi.splitlong = true →
      offsetAddressing addr 4 = some addr2 →
      ExpandBlockShape (.BSstore2 addr addr2 args src mv1 args1' src1' mv2 args2' src2' s)
        (.Istore .Mint64 addr args src s)
        (expandMoves mv1 (.Lstore .Mint32 addr args1' src1' ::
          expandMoves mv2 (.Lstore .Mint32 addr2 args2' src2' :: .Lbranch s :: k)))
  | call (sg : Signature) (ros : Sum Reg Ident) (args : List Reg) (res : Reg) (mv1 : Moves)
      (ros' : Sum Mreg Ident) (mv2 : Moves) (s : RTL.Node) (k : Bblock) :
      WfMoves mv1 → WfMoves mv2 →
      ExpandBlockShape (.BScall sg ros args res mv1 ros' mv2 s) (.Icall sg ros args res s)
        (expandMoves mv1 (.Lcall sg ros' :: expandMoves mv2 (.Lbranch s :: k)))
  | tailcall (sg : Signature) (ros : Sum Reg Ident) (args : List Reg) (mv : Moves)
      (ros' : Sum Mreg Ident) (k : Bblock) :
      WfMoves mv →
      ExpandBlockShape (.BStailcall sg ros args mv ros') (.Itailcall sg ros args)
        (expandMoves mv (.Ltailcall sg ros' :: k))
  | builtin (ef : ExtFun) (args : List (BuiltinArg Reg)) (res : BuiltinRes Reg) (mv1 : Moves)
      (args' : List (BuiltinArg Loc)) (res' : BuiltinRes Mreg) (mv2 : Moves) (s : RTL.Node)
      (k : Bblock) :
      WfMoves mv1 → WfMoves mv2 →
      ExpandBlockShape (.BSbuiltin ef args res mv1 args' res' mv2 s) (.Ibuiltin ef args res s)
        (expandMoves mv1 (.Lbuiltin ef args' res' :: expandMoves mv2 (.Lbranch s :: k)))
  | cond (cond : Condition) (args : List Reg) (mv : Moves) (args' : List Mreg)
      (s1 s2 : RTL.Node) (k : Bblock) :
      WfMoves mv →
      ExpandBlockShape (.BScond cond args mv args' s1 s2) (.Icond cond args s1 s2)
        (expandMoves mv (.Lcond cond args' s1 s2 :: k))
  | jumptable (arg : Reg) (mv : Moves) (arg' : Mreg) (tbl : List RTL.Node) (k : Bblock) :
      WfMoves mv →
      ExpandBlockShape (.BSjumptable arg mv arg' tbl) (.Ijumptable arg tbl)
        (expandMoves mv (.Ljumptable arg' tbl :: k))
  | ret (optarg : Option Reg) (mv : Moves) (k : Bblock) :
      WfMoves mv →
      ExpandBlockShape (.BSreturn optarg mv) (.Ireturn optarg) (expandMoves mv (.Lreturn :: k))

/-- `Allocproof.expand_moves_cons` -/
theorem expandMoves_cons (m : Move) (accu : Moves) (b : Bblock) :
    expandMoves (m :: accu).reverse b = expandMoves accu.reverse (expandMove m :: b) := by
  simp [expandMoves]

theorem wfMoves_reverse {accu : Moves} (h : WfMoves accu) : WfMoves accu.reverse :=
  fun m hm => h m (List.mem_reverse.mp hm)

theorem wfMoves_cons {m : Move} {accu : Moves} (hm : WfMove m) (h : WfMoves accu) :
    WfMoves (m :: accu) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hm
  · exact h x hx

theorem isMoveOperation_correct {A : Type} {op : Operation} {args : List A} {a : A}
    (h : isMoveOperation op args = some a) : op = .Omove ∧ args = [a] := by
  unfold isMoveOperation at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · cases h

theorem classifyOperation_move {A : Type} {op : Operation} {args : List A} {a : A}
    (h : classifyOperation op args = .Omove a) : op = .Omove ∧ args = [a] := by
  unfold classifyOperation at h; split at h <;> cases h <;> exact ⟨rfl, rfl⟩

theorem classifyOperation_makelong {A : Type} {op : Operation} {args : List A} {a1 a2 : A}
    (h : classifyOperation op args = .Omakelong a1 a2) : op = .Omakelong ∧ args = [a1, a2] := by
  unfold classifyOperation at h; split at h <;> cases h <;> exact ⟨rfl, rfl⟩

theorem classifyOperation_lowlong {A : Type} {op : Operation} {args : List A} {a : A}
    (h : classifyOperation op args = .Olowlong a) : op = .Olowlong ∧ args = [a] := by
  unfold classifyOperation at h; split at h <;> cases h <;> exact ⟨rfl, rfl⟩

theorem classifyOperation_highlong {A : Type} {op : Operation} {args : List A} {a : A}
    (h : classifyOperation op args = .Ohighlong a) : op = .Ohighlong ∧ args = [a] := by
  unfold classifyOperation at h; split at h <;> cases h <;> exact ⟨rfl, rfl⟩

private theorem extractMoves_ind :
    ∀ (b : Bblock) (accu mv : Moves) (b' : Bblock), extractMoves accu b = (mv, b') →
    WfMoves accu → WfMoves mv ∧ expandMoves accu.reverse b = expandMoves mv b'
  | [], accu, mv, b', h, hw => by
    simp only [extractMoves] at h; cases h; exact ⟨wfMoves_reverse hw, rfl⟩
  | i :: b, accu, mv, b', h, hw => by
    cases i with
    | Lgetstack sl ofs ty dst =>
      simp only [extractMoves] at h
      obtain ⟨A, B⟩ := extractMoves_ind b _ mv b' h (wfMoves_cons trivial hw)
      exact ⟨A, by rw [← B, expandMoves_cons]; rfl⟩
    | Lsetstack src sl ofs ty =>
      simp only [extractMoves] at h
      obtain ⟨A, B⟩ := extractMoves_ind b _ mv b' h (wfMoves_cons trivial hw)
      exact ⟨A, by rw [← B, expandMoves_cons]; rfl⟩
    | Lop op args res =>
      simp only [extractMoves] at h
      split at h
      · next arg harg =>
        obtain ⟨rfl, rfl⟩ := isMoveOperation_correct harg
        obtain ⟨A, B⟩ := extractMoves_ind b _ mv b' h (wfMoves_cons trivial hw)
        exact ⟨A, by rw [← B, expandMoves_cons]; rfl⟩
      · cases h; exact ⟨wfMoves_reverse hw, rfl⟩
    | _ => simp only [extractMoves] at h; cases h; exact ⟨wfMoves_reverse hw, rfl⟩

/-- `Allocproof.extract_moves_sound` -/
theorem extract_moves_sound {b : Bblock} {mv : Moves} {b' : Bblock}
    (h : extractMoves [] b = (mv, b')) : WfMoves mv ∧ b = expandMoves mv b' := by
  have := extractMoves_ind b [] mv b' h (fun _ h => by cases h)
  exact ⟨this.1, this.2⟩

private theorem extractMovesExt_ind :
    ∀ (b : Bblock) (accu mv : Moves) (b' : Bblock), extractMovesExt accu b = (mv, b') →
    WfMoves accu → WfMoves mv ∧ expandMoves accu.reverse b = expandMoves mv b'
  | [], accu, mv, b', h, hw => by
    simp only [extractMovesExt] at h; cases h; exact ⟨wfMoves_reverse hw, rfl⟩
  | i :: b, accu, mv, b', h, hw => by
    cases i with
    | Lgetstack sl ofs ty dst =>
      simp only [extractMovesExt] at h
      obtain ⟨A, B⟩ := extractMovesExt_ind b _ mv b' h (wfMoves_cons trivial hw)
      exact ⟨A, by rw [← B, expandMoves_cons]; rfl⟩
    | Lsetstack src sl ofs ty =>
      simp only [extractMovesExt] at h
      obtain ⟨A, B⟩ := extractMovesExt_ind b _ mv b' h (wfMoves_cons trivial hw)
      exact ⟨A, by rw [← B, expandMoves_cons]; rfl⟩
    | Lop op args res =>
      simp only [extractMovesExt] at h
      split at h
      · next arg harg =>
        obtain ⟨rfl, rfl⟩ := classifyOperation_move harg
        obtain ⟨A, B⟩ := extractMovesExt_ind b _ mv b' h (wfMoves_cons trivial hw)
        exact ⟨A, by rw [← B, expandMoves_cons]; rfl⟩
      · next a1 a2 harg =>
        obtain ⟨rfl, rfl⟩ := classifyOperation_makelong harg
        obtain ⟨A, B⟩ := extractMovesExt_ind b _ mv b' h (wfMoves_cons trivial hw)
        exact ⟨A, by rw [← B, expandMoves_cons]; rfl⟩
      · next arg harg =>
        obtain ⟨rfl, rfl⟩ := classifyOperation_lowlong harg
        obtain ⟨A, B⟩ := extractMovesExt_ind b _ mv b' h (wfMoves_cons trivial hw)
        exact ⟨A, by rw [← B, expandMoves_cons]; rfl⟩
      · next arg harg =>
        obtain ⟨rfl, rfl⟩ := classifyOperation_highlong harg
        obtain ⟨A, B⟩ := extractMovesExt_ind b _ mv b' h (wfMoves_cons trivial hw)
        exact ⟨A, by rw [← B, expandMoves_cons]; rfl⟩
      · cases h; exact ⟨wfMoves_reverse hw, rfl⟩
    | _ => simp only [extractMovesExt] at h; cases h; exact ⟨wfMoves_reverse hw, rfl⟩

/-- `Allocproof.extract_moves_ext_sound` -/
theorem extract_moves_ext_sound {b : Bblock} {mv : Moves} {b' : Bblock}
    (h : extractMovesExt [] b = (mv, b')) : WfMoves mv ∧ b = expandMoves mv b' := by
  have := extractMovesExt_ind b [] mv b' h (fun _ h => by cases h)
  exact ⟨this.1, this.2⟩

/-- `Allocproof.check_succ_sound` -/
theorem check_succ_sound {s : RTL.Node} {b : Bblock} (h : checkSucc s b = true) :
    ∃ k, b = .Lbranch s :: k := by
  unfold checkSucc at h
  split at h
  · next s' k => exact ⟨k, by rw [of_decide_eq_true h]⟩
  · cases h


theorem pairSplit_sound {s : RTL.Node} {b : Bblock} {k : Moves → BlockShape} {bsh : BlockShape}
    (h : pairSplit s b k = some bsh) :
    ∃ mv k', WfMoves mv ∧ b = expandMoves mv (.Lbranch s :: k') ∧ bsh = k mv := by
  unfold pairSplit at h
  split at h
  next mv b1 heq =>
  obtain ⟨W, E⟩ := extract_moves_sound heq
  split at h
  · next hc =>
    obtain ⟨k', rfl⟩ := check_succ_sound hc
    cases h
    exact ⟨mv, k', W, E, rfl⟩
  · cases h

theorem pairIopBlock_sound {op args res s b bsh}
    (h : pairIopBlock op args res s b = some bsh) : ExpandBlockShape bsh (.Iop op args res s) b := by
  unfold pairIopBlock at h
  split at h
  next mv1 b1 heq =>
  obtain ⟨W1, E1⟩ := extract_moves_sound heq
  subst E1
  split at h
  · next op' args' res' b2 =>
    split at h
    next mv2 b3 heq2 =>
    obtain ⟨W2, E2⟩ := extract_moves_sound heq2
    subst E2
    split at h
    · next hc =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨rfl, hc⟩ := hc
      obtain ⟨k, rfl⟩ := check_succ_sound hc
      cases h
      exact .op _ _ _ _ _ _ _ _ _ W1 W2
    · cases h
  · split at h
    · next hc =>
      obtain ⟨k, rfl⟩ := check_succ_sound hc
      cases h
      exact .op_dead _ _ _ _ _ _ W1
    · cases h

theorem pair_instr_block_sound {i : RTL.Instruction} {b : Bblock} {bsh : BlockShape}
    (h : pairInstrBlock i b = some bsh) : ExpandBlockShape bsh i b := by
  cases i with
  | Inop s =>
    rw [pairInstrBlock] at h
    obtain ⟨mv, k, W, rfl, rfl⟩ := pairSplit_sound h
    exact .nop _ _ _ W
  | Iop op args res s =>
    rw [pairInstrBlock] at h
    split at h
    · next arg hc =>
      obtain ⟨rfl, rfl⟩ := classifyOperation_move hc
      obtain ⟨mv, k, W, rfl, rfl⟩ := pairSplit_sound h
      exact .move _ _ _ _ _ W
    · simp only [Archi.splitlong, Bool.false_eq_true, if_false] at h
      exact pairIopBlock_sound h
    · simp only [Archi.splitlong, Bool.false_eq_true, if_false] at h
      exact pairIopBlock_sound h
    · simp only [Archi.splitlong, Bool.false_eq_true, if_false] at h
      exact pairIopBlock_sound h
    · exact pairIopBlock_sound h
  | Iload chunk addr args dst s =>
    rw [pairInstrBlock] at h
    split at h
    next mv1 b1 heq =>
    obtain ⟨W1, E1⟩ := extract_moves_sound heq
    subst E1
    split at h
    · next chunk' addr' args' dst' b2 =>
      rw [if_neg (by simp [Archi.splitlong])] at h
      split at h
      next mv2 b3 heq2 =>
      obtain ⟨W2, E2⟩ := extract_moves_sound heq2
      subst E2
      split at h
      · next hc =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨⟨rfl, rfl⟩, hc⟩ := hc
        obtain ⟨k, rfl⟩ := check_succ_sound hc
        cases h
        exact .load _ _ _ _ _ _ _ _ _ _ W1 W2
      · cases h
    · split at h
      · next hc =>
        obtain ⟨k, rfl⟩ := check_succ_sound hc
        cases h
        exact .load_dead _ _ _ _ _ _ _ W1
      · cases h
  | Istore chunk addr args src s =>
    rw [pairInstrBlock] at h
    split at h
    next mv1 b1 heq =>
    obtain ⟨W1, E1⟩ := extract_moves_sound heq
    subst E1
    split at h
    · next chunk' addr' args' src' b2 =>
      rw [if_neg (by simp [Archi.splitlong])] at h
      split at h
      · next hc =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨⟨rfl, rfl⟩, hc⟩ := hc
        obtain ⟨k, rfl⟩ := check_succ_sound hc
        cases h
        exact .store _ _ _ _ _ _ _ _ _ W1
      · cases h
    · cases h
  | Icall sg ros args res s =>
    rw [pairInstrBlock] at h
    split at h
    next mv1 b1 heq =>
    obtain ⟨W1, E1⟩ := extract_moves_ext_sound heq
    subst E1
    split at h
    · next sg' ros' b2 =>
      split at h
      next mv2 b3 heq2 =>
      obtain ⟨W2, E2⟩ := extract_moves_ext_sound heq2
      subst E2
      split at h
      · next hc =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨rfl, hc⟩ := hc
        obtain ⟨k, rfl⟩ := check_succ_sound hc
        cases h
        exact .call _ _ _ _ _ _ _ _ _ W1 W2
      · cases h
    · cases h
  | Itailcall sg ros args =>
    rw [pairInstrBlock] at h
    split at h
    next mv1 b1 heq =>
    obtain ⟨W1, E1⟩ := extract_moves_ext_sound heq
    subst E1
    split at h
    · next sg' ros' b2 =>
      split at h
      · next hc =>
        cases of_decide_eq_true hc
        cases h
        exact .tailcall _ _ _ _ _ _ W1
      · cases h
    · cases h
  | Ibuiltin ef args res s =>
    rw [pairInstrBlock] at h
    split at h
    next mv1 b1 heq =>
    obtain ⟨W1, E1⟩ := extract_moves_sound heq
    subst E1
    split at h
    · next ef' args' res' b2 =>
      split at h
      next mv2 b3 heq2 =>
      obtain ⟨W2, E2⟩ := extract_moves_sound heq2
      subst E2
      split at h
      · next hc =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨rfl, hc⟩ := hc
        obtain ⟨k, rfl⟩ := check_succ_sound hc
        cases h
        exact .builtin _ _ _ _ _ _ _ _ _ W1 W2
      · cases h
    · cases h
  | Icond cond args s1 s2 =>
    rw [pairInstrBlock] at h
    split at h
    next mv1 b1 heq =>
    obtain ⟨W1, E1⟩ := extract_moves_sound heq
    subst E1
    split at h
    · next cond' args' s1' s2' b2 =>
      split at h
      · next hc =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hc
        cases h
        exact .cond _ _ _ _ _ _ _ W1
      · cases h
    · cases h
  | Ijumptable arg tbl =>
    rw [pairInstrBlock] at h
    split at h
    next mv1 b1 heq =>
    obtain ⟨W1, E1⟩ := extract_moves_sound heq
    subst E1
    split at h
    · next arg' tbl' b2 =>
      split at h
      · next hc =>
        cases of_decide_eq_true hc
        cases h
        exact .jumptable _ _ _ _ _ W1
      · cases h
    · cases h
  | Ireturn optarg =>
    rw [pairInstrBlock] at h
    split at h
    next mv1 b1 heq =>
    obtain ⟨W1, E1⟩ := extract_moves_ext_sound heq
    subst E1
    split at h
    · cases h
      exact .ret _ _ _ W1
    · cases h

/-- `Allocproof.matching_instr_block` -/
theorem matching_instr_block {f1 : RTL.Function} {f2 : LTL.Function} {pc : RTL.Node}
    {bsh : BlockShape} {i : RTL.Instruction} (h : (pairCodes f1 f2).get pc = some bsh)
    (hi : f1.fn_code.get pc = some i) :
    ∃ b, f2.fn_code.get pc = some b ∧ ExpandBlockShape bsh i b := by
  unfold pairCodes at h
  rw [PTree.gcombine _ rfl, hi] at h
  cases hb : f2.fn_code.get pc with
  | none => rw [hb] at h; cases h
  | some b => rw [hb] at h; exact ⟨b, rfl, pair_instr_block_sound h⟩
end Allocproof
end RiscV
end CC
