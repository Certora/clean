/-
  Correctness proof for code linearization — port of
  `backend/Linearizeproof.v`.

  Main result: `Linearizeproof.transf_program_correct`, a forward simulation
  from the LTL semantics of a program to the Linear semantics of its
  linearization `Linearize.transfProgram enumAux prog = .OK tprog`.

  Differences from Rocq: `is_tail` is Lean's list-suffix relation `<:+`;
  `Nodeset.In` is `Linearize.Nodeset.mem`; `Senv.equiv` is the equality of
  symbol environments `senv_transf_partial`.  The (untrusted) enumeration
  heuristic `enumAux` is arbitrary: correctness relies only on the
  validation performed by `Linearize.enumerate`.
-/
import CCLib.backend.Linearize
import CCLib.common.GlobalenvsTransf
import CCLib.backend.CleanupLabelsproof
import CCLib.common.LinkingFundef

namespace CC
namespace Linearizeproof

open Linearize

/-! ### Correctness of the reachability analysis -/

/-- `reachable_entrypoint` -/
theorem reachable_entrypoint (f : LTL.Function) : (reachable f).get f.fn_entrypoint = true := by
  unfold reachable
  cases h : reachableAux f with
  | none => simp
  | some rs =>
      have := Kildall.fixpoint_entry (L := Bool) (NS := NodeSetForward) f.fn_code
        LTL.successorsBlock (fun _ r => r) f.fn_entrypoint true rs h
      rcases this with h1 | h1 <;> exact h1

/-- `reachable_successors` -/
theorem reachable_successors {f : LTL.Function} {pc pc' : LTL.Node} {b : LTL.Bblock}
    (hc : f.fn_code.get pc = some b) (hs : pc' ∈ LTL.successorsBlock b)
    (hr : (reachable f).get pc = true) : (reachable f).get pc' = true := by
  unfold reachable at hr ⊢
  cases h : reachableAux f with
  | none => simp
  | some rs =>
      rw [h] at hr
      have := Kildall.fixpoint_solution (L := Bool) (NS := NodeSetForward) f.fn_code
        LTL.successorsBlock (fun _ r => r) f.fn_entrypoint true rs pc b pc' h hc hs
        (fun _ => rfl)
      simp only at hr ⊢
      rcases this with h1 | h1
      · exact h1.trans hr
      · exact h1

/-! ### Properties of node enumeration -/

theorem mem_set (pc n : Positive) (s : Nodeset) :
    Nodeset.mem pc (s.set n ()) = true ↔ pc = n ∨ Nodeset.mem pc s = true := by
  simp only [Nodeset.mem, PTree.gsspec]
  by_cases h : pc = n
  · simp [h]
  · simp [h]

theorem mem_empty (pc : Positive) : Nodeset.mem pc PTree.empty = false := by
  simp [Nodeset.mem]

/-- `nodeset_of_list_correct` -/
theorem nodesetOfList_correct : ∀ (l : List LTL.Node) (s s' : Nodeset),
    nodesetOfList l s = .OK s' →
    l.Nodup ∧ (∀ pc, Nodeset.mem pc s' = true ↔ Nodeset.mem pc s = true ∨ pc ∈ l) ∧
      (∀ pc, pc ∈ l → Nodeset.mem pc s = false)
  | [], s, s', h => by
      simp only [nodesetOfList] at h
      cases h
      exact ⟨List.nodup_nil, fun pc => by simp, fun pc h => by cases h⟩
  | a :: l, s, s', h => by
      simp only [nodesetOfList] at h
      split at h
      · cases h
      · rename_i hmem
        obtain ⟨A, B, C⟩ := nodesetOfList_correct l _ _ h
        refine ⟨List.nodup_cons.mpr ⟨fun hin => ?_, A⟩, fun pc => ?_, fun pc hin => ?_⟩
        · have := C a hin
          rw [(mem_set a a s).mpr (.inl rfl)] at this
          cases this
        · rw [B, mem_set]
          simp only [List.mem_cons]
          constructor
          · rintro ((h1 | h1) | h1)
            · exact .inr (.inl h1)
            · exact .inl h1
            · exact .inr (.inr h1)
          · rintro (h1 | h1 | h1)
            · exact .inl (.inr h1)
            · exact .inl (.inl h1)
            · exact .inr h1
        · simp only [List.mem_cons] at hin
          rcases hin with rfl | hin
          · simpa using hmem
          · have := C pc hin
            rw [Bool.eq_false_iff] at this ⊢
            intro h'
            exact this ((mem_set pc a s).mpr (.inr h'))

/-- `check_reachable_correct` -/
theorem checkReachable_correct {f : LTL.Function} {reach : PMap Bool} {s : Nodeset}
    {pc : LTL.Node} {i : LTL.Bblock} (hck : checkReachable f reach s = true)
    (hc : f.fn_code.get pc = some i) (hr : reach.get pc = true) : Nodeset.mem pc s = true := by
  have key : ∀ (l : List (Positive × LTL.Bblock)) (ok : Bool),
      l.foldl (fun a p => checkReachableAux reach s a p.1 p.2) ok = true →
      ok = true ∧ ∀ pc i, (pc, i) ∈ l → reach.get pc = true → Nodeset.mem pc s = true := by
    intro l
    induction l with
    | nil => intro ok h; exact ⟨h, fun _ _ h => by cases h⟩
    | cons a l ih =>
        intro ok h
        obtain ⟨A, B⟩ := ih _ h
        obtain ⟨pc1, i1⟩ := a
        simp only [checkReachableAux] at A
        refine ⟨?_, fun pc i hin hr => ?_⟩
        · split at A
          · exact (Bool.and_eq_true _ _ ▸ A).1
          · exact A
        · simp only [List.mem_cons] at hin
          rcases hin with hin | hin
          · cases hin
            rw [if_pos hr] at A
            exact (Bool.and_eq_true _ _ ▸ A).2
          · exact B pc i hin hr
  unfold checkReachable at hck
  rw [PTree.fold_spec] at hck
  exact (key _ _ hck).2 pc i (PTree.elements_correct _ _ _ hc) hr

section ENUM
variable (enumAux : LTL.Function → PMap Bool → List LTL.Node)

/-- `enumerate_complete` -/
theorem enumerate_complete {f : LTL.Function} {enum : List LTL.Node} {pc : LTL.Node}
    {i : LTL.Bblock} (h : enumerate enumAux f = .OK enum) (hc : f.fn_code.get pc = some i)
    (hr : (reachable f).get pc = true) : pc ∈ enum := by
  unfold enumerate at h
  simp only at h
  split at h
  · cases h
  · rename_i s hs
    split at h
    · rename_i hck
      cases h
      have := checkReachable_correct hck hc hr
      obtain ⟨_, B, _⟩ := nodesetOfList_correct _ _ _ hs
      rcases (B pc).mp this with h1 | h1
      · rw [mem_empty] at h1; cases h1
      · exact h1
    · cases h

/-- `enumerate_norepet` -/
theorem enumerate_norepet {f : LTL.Function} {enum : List LTL.Node}
    (h : enumerate enumAux f = .OK enum) : enum.Nodup := by
  unfold enumerate at h
  simp only at h
  split at h
  · cases h
  · rename_i s hs
    split at h
    · cases h
      exact (nodesetOfList_correct _ _ _ hs).1
    · cases h

end ENUM

/-! ### Properties related to labels -/

/-- `unique_labels` -/
def UniqueLabels : Linear.Code → Prop
  | [] => True
  | .Llabel lbl :: c => .Llabel lbl ∉ c ∧ UniqueLabels c
  | _ :: c => UniqueLabels c

theorem uniqueLabels_cons {i : Linear.Instruction} {c : Linear.Code}
    (h : UniqueLabels (i :: c)) : UniqueLabels c := by
  cases i <;> first | exact h.2 | exact h

/-- `find_label_unique` -/
theorem findLabel_unique {lbl : Linear.Label} {c1 : Linear.Code} :
    ∀ {c2 c3 : Linear.Code}, (Linear.Instruction.Llabel lbl :: c1) <:+ c2 → UniqueLabels c2 →
      Linear.findLabel lbl c2 = some c3 → c1 = c3
  | [], _, _, _, h => by simp [Linear.findLabel] at h
  | a :: c2, c3, TAIL, UNIQ, h => by
      simp only [Linear.findLabel] at h
      have hl := Linear.isLabel_correct lbl a
      split at h
      · rename_i hisl
        rw [if_pos hisl] at hl
        subst hl
        cases h
        rcases List.suffix_cons_iff.mp TAIL with h1 | h1
        · cases h1; rfl
        · exact absurd (h1.subset (List.mem_cons_self ..)) UNIQ.1
      · rename_i hisl
        rw [if_neg hisl] at hl
        rcases List.suffix_cons_iff.mp TAIL with h1 | h1
        · cases h1; exact absurd rfl hl
        · exact findLabel_unique h1 (uniqueLabels_cons UNIQ) h

/-- `find_label_add_branch` -/
theorem findLabel_addBranch (lbl : Linear.Label) (k : Linear.Code) (s : Linear.Label) :
    Linear.findLabel lbl (addBranch s k) = Linear.findLabel lbl k := by
  unfold addBranch
  split
  · rfl
  · simp [Linear.findLabel, Linear.isLabel]

/-- `find_label_lin_block` -/
theorem findLabel_linBlock (lbl : Linear.Label) (k : Linear.Code) :
    ∀ b : LTL.Bblock, Linear.findLabel lbl (linearizeBlock b k) = Linear.findLabel lbl k
  | [] => rfl
  | i :: b => by
      cases i <;> simp only [linearizeBlock, Linear.findLabel, Linear.isLabel, Bool.false_eq_true,
        if_false, findLabel_linBlock lbl k b, findLabel_addBranch]
      split <;> simp [Linear.findLabel, Linear.isLabel, findLabel_addBranch]

/-- `linearize_body_cons` -/
theorem linearizeBody_cons (f : LTL.Function) (pc : LTL.Node) (enum : List LTL.Node) :
    linearizeBody f (pc :: enum) =
      match f.fn_code.get pc with
      | none => linearizeBody f enum
      | some b => .Llabel pc :: linearizeBlock b (linearizeBody f enum) := by
  rfl

/-- `find_label_lin_rec` -/
theorem findLabel_linRec (f : LTL.Function) :
    ∀ {enum : List LTL.Node} {pc : LTL.Node} {b : LTL.Bblock}, pc ∈ enum →
      f.fn_code.get pc = some b →
      ∃ k, Linear.findLabel pc (linearizeBody f enum) = some (linearizeBlock b k)
  | [], _, _, h, _ => by cases h
  | a :: enum, pc, b, hin, hc => by
      rw [linearizeBody_cons]
      by_cases hap : a = pc
      · subst hap
        rw [hc]
        exact ⟨linearizeBody f enum, by simp [Linear.findLabel, Linear.isLabel]⟩
      · have hin' : pc ∈ enum := by
          rcases List.mem_cons.mp hin with h | h
          · exact absurd h.symm hap
          · exact h
        obtain ⟨k, hk⟩ := findLabel_linRec f hin' hc
        refine ⟨k, ?_⟩
        split
        · exact hk
        · have : (pc = a) = False := propext ⟨fun h => hap h.symm, False.elim⟩
          simp [Linear.findLabel, Linear.isLabel, this, findLabel_linBlock, hk]

/-- `label_in_add_branch` -/
theorem label_in_addBranch {lbl s : Linear.Label} {k : Linear.Code}
    (h : Linear.Instruction.Llabel lbl ∈ addBranch s k) : Linear.Instruction.Llabel lbl ∈ k := by
  unfold addBranch at h
  split at h
  · exact h
  · simpa using h

/-- `label_in_lin_block` -/
theorem label_in_linBlock {lbl : Linear.Label} {k : Linear.Code} :
    ∀ {b : LTL.Bblock}, Linear.Instruction.Llabel lbl ∈ linearizeBlock b k →
      Linear.Instruction.Llabel lbl ∈ k
  | [], h => h
  | i :: b, h => by
      cases i <;> simp only [linearizeBlock, List.mem_cons, reduceCtorEq, false_or] at h
      all_goals first
        | exact label_in_linBlock h
        | exact h
        | exact label_in_addBranch h
        | skip
      split at h <;> simp only [List.mem_cons, reduceCtorEq, false_or] at h <;>
        exact label_in_addBranch h

/-- `label_in_lin_rec` -/
theorem label_in_linRec (f : LTL.Function) {lbl : Linear.Label} :
    ∀ {enum : List LTL.Node}, Linear.Instruction.Llabel lbl ∈ linearizeBody f enum → lbl ∈ enum
  | [], h => by simp [linearizeBody] at h
  | a :: enum, h => by
      rw [linearizeBody_cons] at h
      split at h
      · exact List.mem_cons_of_mem _ (label_in_linRec f h)
      · rcases List.mem_cons.mp h with h1 | h1
        · cases h1; exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (label_in_linRec f (label_in_linBlock h1))

/-- `unique_labels_add_branch` -/
theorem uniqueLabels_addBranch (lbl : Linear.Label) {k : Linear.Code} (h : UniqueLabels k) :
    UniqueLabels (addBranch lbl k) := by
  unfold addBranch
  split
  · exact h
  · exact h

/-- `unique_labels_lin_block` -/
theorem uniqueLabels_linBlock {k : Linear.Code} (hk : UniqueLabels k) :
    ∀ b : LTL.Bblock, UniqueLabels (linearizeBlock b k)
  | [] => hk
  | i :: b => by
      cases i <;> simp only [linearizeBlock]
      all_goals first
        | exact uniqueLabels_linBlock hk b
        | exact hk
        | exact uniqueLabels_addBranch _ hk
        | skip
      split <;> exact uniqueLabels_addBranch _ hk

/-- `unique_labels_lin_rec` -/
theorem uniqueLabels_linRec (f : LTL.Function) :
    ∀ {enum : List LTL.Node}, enum.Nodup → UniqueLabels (linearizeBody f enum)
  | [], _ => trivial
  | a :: enum, h => by
      rw [linearizeBody_cons]
      have ⟨h1, h2⟩ := List.nodup_cons.mp h
      split
      · exact uniqueLabels_linRec f h2
      · exact ⟨fun hin => h1 (label_in_linRec f (label_in_linBlock hin)),
          uniqueLabels_linBlock (uniqueLabels_linRec f h2) _⟩

/-- `is_tail_find_label` -/
theorem isTail_findLabel {lbl : Linear.Label} {c2 : Linear.Code} :
    ∀ {c1 : Linear.Code}, Linear.findLabel lbl c1 = some c2 → c2 <:+ c1
  | [], h => by simp [Linear.findLabel] at h
  | a :: c1, h => by
      simp only [Linear.findLabel] at h
      split at h
      · cases h; exact List.suffix_cons _ _
      · exact (isTail_findLabel h).trans (List.suffix_cons _ _)

/-- `is_tail_add_branch` -/
theorem isTail_addBranch {lbl : Linear.Label} {c1 c2 : Linear.Code}
    (h : addBranch lbl c1 <:+ c2) : c1 <:+ c2 := by
  unfold addBranch at h
  split at h
  · exact h
  · exact (List.suffix_cons _ _).trans h

/-- `is_tail_lin_block` -/
theorem isTail_linBlock {c1 c2 : Linear.Code} :
    ∀ {b : LTL.Bblock}, linearizeBlock b c1 <:+ c2 → c1 <:+ c2
  | [], h => h
  | i :: b, h => by
      cases i <;> simp only [linearizeBlock] at h
      all_goals first
        | exact isTail_linBlock ((List.suffix_cons _ _).trans h)
        | exact (List.suffix_cons _ _).trans h
        | exact isTail_addBranch h
        | skip
      split at h <;> exact isTail_addBranch ((List.suffix_cons _ _).trans h)

/-- `eval_negate_condition` (now `Op.eval_negateCondition`, as in Rocq's `Op.v`) -/
theorem eval_negateCondition (cond : Op.Condition) (vl : List Val) (m : Mem) :
    Op.evalCondition (Op.negateCondition cond) vl m = (Op.evalCondition cond vl m).map (!·) :=
  Op.eval_negateCondition cond vl m

section TRANSF
variable (enumAux : LTL.Function → PMap Bool → List LTL.Node)

theorem transfFunction_ok {f : LTL.Function} {tf : Linear.Function}
    (h : Linearize.transfFunction enumAux f = .OK tf) :
    ∃ enum, enumerate enumAux f = .OK enum ∧
      tf = { fn_sig := f.fn_sig, fn_stacksize := f.fn_stacksize,
             fn_code := addBranch f.fn_entrypoint (linearizeBody f enum) } := by
  unfold Linearize.transfFunction at h
  split at h
  · cases h
  · rename_i enum he
    cases h
    exact ⟨enum, he, rfl⟩

/-- `stacksize_preserved` -/
theorem stacksize_preserved {f : LTL.Function} {tf : Linear.Function}
    (h : Linearize.transfFunction enumAux f = .OK tf) : tf.fn_stacksize = f.fn_stacksize := by
  obtain ⟨_, _, rfl⟩ := transfFunction_ok enumAux h; rfl

/-- `sig_preserved` -/
theorem sig_preserved {f : LTL.Fundef} {tf : Linear.Fundef}
    (h : Linearize.transfFundef enumAux f = .OK tf) : Linear.funsig tf = LTL.funsig f := by
  cases f with
  | Internal f =>
      simp only [Linearize.transfFundef, ASTFundef.transfPartial] at h
      split at h
      · rename_i tf' htf; cases h
        obtain ⟨_, _, rfl⟩ := transfFunction_ok enumAux htf; rfl
      · cases h
  | External ef => cases h; rfl

/-- `find_label_lin` -/
theorem findLabel_lin {f : LTL.Function} {tf : Linear.Function} {pc : LTL.Node}
    {b : LTL.Bblock} (h : Linearize.transfFunction enumAux f = .OK tf) (hc : f.fn_code.get pc = some b)
    (hr : (reachable f).get pc = true) :
    ∃ k, Linear.findLabel pc tf.fn_code = some (linearizeBlock b k) := by
  obtain ⟨enum, he, rfl⟩ := transfFunction_ok enumAux h
  simp only
  rw [findLabel_addBranch]
  exact findLabel_linRec f (enumerate_complete enumAux he hc hr) hc

/-- `unique_labels_transf_function` -/
theorem uniqueLabels_transfFunction {f : LTL.Function} {tf : Linear.Function}
    (h : Linearize.transfFunction enumAux f = .OK tf) : UniqueLabels tf.fn_code := by
  obtain ⟨enum, he, rfl⟩ := transfFunction_ok enumAux h
  exact uniqueLabels_addBranch _ (uniqueLabels_linRec f (enumerate_norepet enumAux he))

theorem transfFundef_internal {f : LTL.Function} {tf : Linear.Fundef}
    (h : Linearize.transfFundef enumAux (.Internal f) = .OK tf) :
    ∃ tf', tf = .Internal tf' ∧ Linearize.transfFunction enumAux f = .OK tf' := by
  simp only [Linearize.transfFundef, ASTFundef.transfPartial] at h
  split at h
  · rename_i tf' htf; cases h; exact ⟨tf', rfl, htf⟩
  · cases h

theorem transfFundef_external {ef : ExtFun} {tf : Linear.Fundef}
    (h : Linearize.transfFundef enumAux (.External ef) = .OK tf) : tf = .External ef := by
  cases h; rfl

/-! ### The simulation -/

/-- `match_stackframes` -/
inductive MatchStackframes : LTL.Stackframe → Linear.Stackframe → Prop where
  | intro (f sp bb ls tf c) : Linearize.transfFunction enumAux f = .OK tf →
      (∀ pc, pc ∈ LTL.successorsBlock bb → (reachable f).get pc = true) →
      c <:+ tf.fn_code →
      MatchStackframes (.Stackframe f sp ls bb) (.Stackframe tf sp ls (linearizeBlock bb c))

/-- `match_states` -/
inductive MatchStates : LTL.State → Linear.State → Prop where
  | add_branch (s f sp pc ls m tf ts c) : ListForall2 (MatchStackframes enumAux) s ts →
      Linearize.transfFunction enumAux f = .OK tf → (reachable f).get pc = true →
      c <:+ tf.fn_code →
      MatchStates (.State s f sp pc ls m) (.State ts tf sp (addBranch pc c) ls m)
  | cond_taken (s f sp pc ls m tf ts cond args c) : ListForall2 (MatchStackframes enumAux) s ts →
      Linearize.transfFunction enumAux f = .OK tf → (reachable f).get pc = true →
      Op.evalCondition cond (LTL.reglist ls args) m = some true →
      MatchStates (.State s f sp pc (LTL.undefRegs (destroyedByCond cond) ls) m)
        (.State ts tf sp (.Lcond cond args pc :: c) ls m)
  | jumptable (s f sp pc ls m tf ts arg tbl c n) : ListForall2 (MatchStackframes enumAux) s ts →
      Linearize.transfFunction enumAux f = .OK tf → (reachable f).get pc = true →
      ls (.R arg) = .Vint n → CminorSel.listNthZ tbl (Integers.Int.unsigned n) = some pc →
      MatchStates (.State s f sp pc (LTL.undefRegs destroyedByJumptable ls) m)
        (.State ts tf sp (.Ljumptable arg tbl :: c) ls m)
  | block (s f sp bb ls m tf ts c) : ListForall2 (MatchStackframes enumAux) s ts →
      Linearize.transfFunction enumAux f = .OK tf →
      (∀ pc, pc ∈ LTL.successorsBlock bb → (reachable f).get pc = true) →
      c <:+ tf.fn_code →
      MatchStates (.Block s f sp bb ls m) (.State ts tf sp (linearizeBlock bb c) ls m)
  | call (s f ls m tf ts) : ListForall2 (MatchStackframes enumAux) s ts →
      Linearize.transfFundef enumAux f = .OK tf →
      MatchStates (.Callstate s f ls m) (.Callstate ts tf ls m)
  | ret (s ls m ts) : ListForall2 (MatchStackframes enumAux) s ts →
      MatchStates (.Returnstate s ls m) (.Returnstate ts ls m)

/-- `measure` -/
def measure : LTL.State → Nat
  | .Block .. => 1
  | _ => 0

/-- `match_parent_locset` -/
theorem match_parent_locset {s : List LTL.Stackframe} {ts : List Linear.Stackframe}
    (h : ListForall2 (MatchStackframes enumAux) s ts) :
    Linear.parentLocset ts = LTL.parentLocset s := by
  cases h with
  | nil => rfl
  | cons hm _ => cases hm; rfl

section SIM
variable (abi : Conventions1.AbiKind)

/-- `starts_with_correct` -/
theorem startsWith_correct (ge : Linear.CGenv) {lbl : Linear.Label} (s : List Linear.Stackframe)
    (f : Linear.Function) (sp : Val) (ls : LTL.Locset) (m : Mem) :
    ∀ {c1 c3 : Linear.Code}, c1 <:+ f.fn_code → UniqueLabels f.fn_code →
      startsWith lbl c1 = true → Linear.findLabel lbl f.fn_code = some c3 →
      Smallstep.Plus (Linear.Step abi ge) (.State s f sp c1 ls m) E0 (.State s f sp c3 ls m)
  | [], _, _, _, h, _ => by simp [startsWith] at h
  | i :: c1, c3, TAIL, UNIQ, SW, FIND => by
      cases i <;> simp only [startsWith, Bool.false_eq_true] at SW
      rename_i l
      have STEP := Linear.Step.Llabel (abi := abi) (ge := ge) s f sp l c1 ls m
      split at SW
      · rename_i hl
        subst hl
        rw [← findLabel_unique TAIL UNIQ FIND]
        exact Smallstep.plus_one STEP
      · exact Smallstep.plus_left STEP
          (Smallstep.plus_star (startsWith_correct ge s f sp ls m
            ((List.suffix_cons _ _).trans TAIL) UNIQ SW FIND)) rfl

/-- `add_branch_correct` -/
theorem addBranch_correct (ge : Linear.CGenv) {lbl : Linear.Label} {c k : Linear.Code}
    (s : List Linear.Stackframe) {f : LTL.Function} {tf : Linear.Function} (sp : Val)
    (ls : LTL.Locset) (m : Mem)
    (TRF : Linearize.transfFunction enumAux f = .OK tf) (TAIL : k <:+ tf.fn_code)
    (FIND : Linear.findLabel lbl tf.fn_code = some c) :
    Smallstep.Plus (Linear.Step abi ge) (.State s tf sp (addBranch lbl k) ls m) E0
      (.State s tf sp c ls m) := by
  unfold addBranch
  split
  · rename_i SW
    exact startsWith_correct abi ge s tf sp ls m TAIL (uniqueLabels_transfFunction enumAux TRF)
      SW FIND
  · exact Smallstep.plus_one (.Lgoto _ _ _ _ _ _ _ _ FIND)

end SIM

section PRESERVATION
variable (abi : Conventions1.AbiKind) {prog : LTL.Program} {tprog : Linear.Program}
  (TRANSF : Linearize.transfProgram enumAux prog = .OK tprog)
include TRANSF

theorem symbols_preserved (id : Ident) :
    Genv.findSymbol tprog.globalenv id = Genv.findSymbol prog.globalenv id :=
  find_symbol_transf_partial TRANSF id

theorem senv_preserved : Genv.toSenv tprog.globalenv = Genv.toSenv prog.globalenv :=
  senv_transf_partial TRANSF

theorem functions_translated {v : Val} {f : LTL.Fundef}
    (h : Genv.findFunct prog.globalenv v = some f) :
    ∃ tf, Genv.findFunct tprog.globalenv v = some tf ∧ Linearize.transfFundef enumAux f = .OK tf :=
  find_funct_transf_partial TRANSF h

theorem function_ptr_translated {b : Block} {f : LTL.Fundef}
    (h : Genv.findFunctPtr prog.globalenv b = some f) :
    ∃ tf, Genv.findFunctPtr tprog.globalenv b = some tf ∧
      Linearize.transfFundef enumAux f = .OK tf :=
  find_funct_ptr_transf_partial TRANSF h

/-- `find_function_translated` -/
theorem find_function_translated {ros : Sum Mreg Ident} {ls : LTL.Locset} {f : LTL.Fundef}
    (h : LTL.findFunction prog.globalenv ros ls = some f) :
    ∃ tf, Linear.findFunction tprog.globalenv ros ls = some tf ∧
      Linearize.transfFundef enumAux f = .OK tf := by
  cases ros with
  | inl r => exact functions_translated enumAux TRANSF h
  | inr id =>
      simp only [LTL.findFunction, Linear.findFunction, symbols_preserved enumAux TRANSF] at h ⊢
      cases e : Genv.findSymbol prog.globalenv id with
      | none => rw [e] at h; cases h
      | some b => rw [e] at h; exact function_ptr_translated enumAux TRANSF h

set_option maxHeartbeats 1000000 in
/-- `transf_step_correct` -/
theorem transf_step_correct {s1 t s2} (hst : LTL.Step abi prog.globalenv s1 t s2) {s1'}
    (hm : MatchStates enumAux s1 s1') :
    (∃ s2', Smallstep.Plus (Linear.Step abi tprog.globalenv) s1' t s2' ∧
      MatchStates enumAux s2 s2') ∨
    (measure s2 < measure s1 ∧ t = E0 ∧ MatchStates enumAux s2 s1') := by
  have hsym := symbols_preserved enumAux TRANSF
  have hsenv := senv_preserved enumAux TRANSF
  cases hst with
  | start_block s f sp pc rs m bb hc =>
    cases hm with
    | add_branch _ _ _ _ _ _ tf ts c STK TRF REACH TAIL =>
      obtain ⟨k, F⟩ := findLabel_lin enumAux TRF hc REACH
      exact .inl ⟨_, addBranch_correct enumAux abi _ ts sp rs m TRF TAIL F,
        .block _ _ _ _ _ _ _ _ _ STK TRF (fun _ h => reachable_successors hc h REACH)
          (isTail_linBlock (isTail_findLabel F))⟩
    | cond_taken _ _ _ _ ls _ tf ts cond args c STK TRF REACH JUMP =>
      obtain ⟨k, F⟩ := findLabel_lin enumAux TRF hc REACH
      exact .inl ⟨_, Smallstep.plus_one (.Lcond_true _ _ _ _ _ _ _ _ _ _ _ JUMP rfl F),
        .block _ _ _ _ _ _ _ _ _ STK TRF (fun _ h => reachable_successors hc h REACH)
          (isTail_linBlock (isTail_findLabel F))⟩
    | jumptable _ _ _ _ ls _ tf ts arg tbl c n STK TRF REACH ARG JUMP =>
      obtain ⟨k, F⟩ := findLabel_lin enumAux TRF hc REACH
      exact .inl ⟨_, Smallstep.plus_one (.Ljumptable _ _ _ _ _ _ _ _ n _ _ _ ARG JUMP F rfl),
        .block _ _ _ _ _ _ _ _ _ STK TRF (fun _ h => reachable_successors hc h REACH)
          (isTail_linBlock (isTail_findLabel F))⟩
  | Lop s f sp op args res bb rs m v rs' hv hrs =>
    cases hm with
    | block _ _ _ _ _ _ tf ts c STK TRF REACH TAIL =>
      refine .inl ⟨_, Smallstep.plus_one (.Lop _ _ _ _ _ _ _ _ _ v _ ?_ hrs),
        .block _ _ _ _ _ _ _ _ _ STK TRF REACH TAIL⟩
      rw [evalOperation_preserved prog.globalenv tprog.globalenv hsym]; exact hv
  | Lload s f sp chunk addr args dst bb rs m a v rs' ha hv hrs =>
    cases hm with
    | block _ _ _ _ _ _ tf ts c STK TRF REACH TAIL =>
      refine .inl ⟨_, Smallstep.plus_one (.Lload _ _ _ _ _ _ _ _ _ _ a v _ ?_ hv hrs),
        .block _ _ _ _ _ _ _ _ _ STK TRF REACH TAIL⟩
      rw [evalAddressing_preserved prog.globalenv tprog.globalenv hsym]; exact ha
  | Lgetstack s f sp sl ofs ty dst bb rs m rs' hrs =>
    cases hm with
    | block _ _ _ _ _ _ tf ts c STK TRF REACH TAIL =>
      exact .inl ⟨_, Smallstep.plus_one (.Lgetstack _ _ _ _ _ _ _ _ _ _ _ hrs),
        .block _ _ _ _ _ _ _ _ _ STK TRF REACH TAIL⟩
  | Lsetstack s f sp src sl ofs ty bb rs m rs' hrs =>
    cases hm with
    | block _ _ _ _ _ _ tf ts c STK TRF REACH TAIL =>
      exact .inl ⟨_, Smallstep.plus_one (.Lsetstack _ _ _ _ _ _ _ _ _ _ _ hrs),
        .block _ _ _ _ _ _ _ _ _ STK TRF REACH TAIL⟩
  | Lstore s f sp chunk addr args src bb rs m a rs' m' ha hs hrs =>
    cases hm with
    | block _ _ _ _ _ _ tf ts c STK TRF REACH TAIL =>
      refine .inl ⟨_, Smallstep.plus_one (.Lstore _ _ _ _ _ _ _ _ _ _ m' a _ ?_ hs hrs),
        .block _ _ _ _ _ _ _ _ _ STK TRF REACH TAIL⟩
      rw [evalAddressing_preserved prog.globalenv tprog.globalenv hsym]; exact ha
  | Lcall s f sp sig ros bb rs m fd hf hsig =>
    cases hm with
    | block _ _ _ _ _ _ tf ts c STK TRF REACH TAIL =>
      obtain ⟨tfd, A, B⟩ := find_function_translated enumAux TRANSF hf
      exact .inl ⟨_, Smallstep.plus_one (.Lcall _ _ _ _ _ _ _ _ _ A
          (by rw [sig_preserved enumAux B]; exact hsig.symm)),
        .call _ _ _ _ _ _ (.cons (.intro _ _ _ _ _ _ TRF REACH TAIL) STK) B⟩
  | Ltailcall s f sp sig ros bb rs m fd rs' m' hrs hf hsig hfree =>
    cases hm with
    | block _ _ _ _ _ _ tf ts c STK TRF REACH TAIL =>
      subst hrs
      obtain ⟨tfd, A, B⟩ := find_function_translated enumAux TRANSF hf
      have hpl := match_parent_locset enumAux STK
      refine .inl ⟨_, Smallstep.plus_one (.Ltailcall _ _ _ _ _ _ _ _ _ _ _ rfl
          (by rw [hpl]; exact A) (by rw [sig_preserved enumAux B]; exact hsig.symm)
          (by rw [stacksize_preserved enumAux TRF]; exact hfree)), ?_⟩
      rw [hpl]
      exact .call _ _ _ _ _ _ STK B
  | Lbuiltin s f sp ef args res bb rs m vargs t vres rs' m' hargs hcall hrs =>
    cases hm with
    | block _ _ _ _ _ _ tf ts c STK TRF REACH TAIL =>
      refine .inl ⟨_, Smallstep.plus_one (.Lbuiltin _ _ _ _ _ _ _ _ _ vargs t vres _ m' ?_ ?_ hrs),
        .block _ _ _ _ _ _ _ _ _ STK TRF REACH TAIL⟩
      · rw [hsenv]; exact hargs
      · rw [hsenv]; exact hcall
  | Lbranch s f sp pc bb rs m =>
    cases hm with
    | block _ _ _ _ _ _ tf ts c STK TRF REACH TAIL =>
      exact .inr ⟨by simp [measure], rfl,
        .add_branch _ _ _ _ _ _ _ _ _ STK TRF (REACH pc (by simp [LTL.successorsBlock])) TAIL⟩
  | Lcond s f sp cond args pc1 pc2 bb rs b pc rs' m hc hpc hrs =>
    have hneg := eval_negateCondition cond (LTL.reglist rs args) m
    rw [hc] at hneg
    subst pc rs'
    cases hm with
    | block _ _ _ _ _ _ tf ts c STK TRF REACH TAIL =>
      have REACH1 : (reachable f).get pc1 = true := REACH pc1 (by simp [LTL.successorsBlock])
      have REACH2 : (reachable f).get pc2 = true := REACH pc2 (by simp [LTL.successorsBlock])
      simp only [linearizeBlock]
      split
      · cases b
        · exact .inr ⟨by simp [measure], trivial,
            .cond_taken _ _ _ _ _ _ _ _ (Op.negateCondition cond) _ _ STK TRF REACH2 hneg⟩
        · exact .inl ⟨_, Smallstep.plus_one (.Lcond_false _ _ _ _ _ _ _ _ _ _ hneg rfl),
            .add_branch _ _ _ _ _ _ _ _ _ STK TRF REACH1 TAIL⟩
      · cases b
        · exact .inl ⟨_, Smallstep.plus_one (.Lcond_false _ _ _ _ _ _ _ _ _ _ hc rfl),
            .add_branch _ _ _ _ _ _ _ _ _ STK TRF REACH2 TAIL⟩
        · exact .inr ⟨by simp [measure], trivial,
            .cond_taken _ _ _ _ _ _ _ _ cond _ _ STK TRF REACH1 hc⟩
  | Ljumptable s f sp arg tbl bb rs m n pc rs' hn hl hrs =>
    cases hm with
    | block _ _ _ _ _ _ tf ts c STK TRF REACH TAIL =>
      subst hrs
      exact .inr ⟨by simp [measure], rfl,
        .jumptable _ _ _ _ _ _ _ _ _ _ _ _ STK TRF
          (REACH pc (CleanupLabelsproof.listNthZ_mem hl)) hn hl⟩
  | Lreturn s f sp bb rs m m' hfree =>
    cases hm with
    | block _ _ _ _ _ _ tf ts c STK TRF REACH TAIL =>
      refine .inl ⟨_, Smallstep.plus_one (.Lreturn _ _ _ _ _ _ _
          (by rw [stacksize_preserved enumAux TRF]; exact hfree)), ?_⟩
      rw [match_parent_locset enumAux STK]
      exact .ret _ _ _ _ STK
  | function_internal s f rs m m' sp rs' halloc hrs =>
    cases hm with
    | call _ _ _ _ tf ts STK TF =>
      obtain ⟨tf', rfl, TRF⟩ := transfFundef_internal enumAux TF
      have TRF' := TRF
      obtain ⟨enum, _, rfl⟩ := transfFunction_ok enumAux TRF'
      exact .inl ⟨_, Smallstep.plus_one (.function_internal _ _ _ _ _ _ _ halloc hrs),
        .add_branch _ _ _ _ _ _ _ _ _ STK TRF (reachable_entrypoint f)
          (isTail_addBranch (List.suffix_refl _))⟩
  | function_external s ef t args res rs m rs' m' hargs hcall hrs =>
    cases hm with
    | call _ _ _ _ tf ts STK TF =>
      cases transfFundef_external enumAux TF
      refine .inl ⟨_, Smallstep.plus_one (.function_external _ _ _ _ _ _ _ _ _ hargs ?_ hrs),
        .ret _ _ _ _ STK⟩
      rw [hsenv]; exact hcall
  | «return» f sp rs1 bb s rs m =>
    cases hm with
    | ret _ _ _ ts STK =>
      cases STK with
      | cons hf STK =>
        cases hf with
        | intro _ _ _ _ tf c TRF REACH TAIL =>
          exact .inl ⟨_, Smallstep.plus_one (.return _ _ _ _ _ _ _),
            .block _ _ _ _ _ _ _ _ _ STK TRF REACH TAIL⟩

/-- `transf_initial_states` -/
theorem transf_initial_states {st1 : LTL.State} (h : LTL.InitialState prog st1) :
    ∃ st2, Linear.InitialState tprog st2 ∧ MatchStates enumAux st1 st2 := by
  cases h with
  | intro b f m0 hm hs hf hsig =>
      obtain ⟨tf, h1, h2⟩ := function_ptr_translated enumAux TRANSF hf
      refine ⟨_, .intro b tf m0 ?_ ?_ h1 ?_, .call _ _ _ _ _ _ .nil h2⟩
      · exact (init_mem_transf_partial TRANSF).trans hm
      · rw [(match_transform_partial_program TRANSF).main_eq, symbols_preserved enumAux TRANSF]
        exact hs
      · rw [sig_preserved enumAux h2]; exact hsig

omit TRANSF in
/-- `transf_final_states` -/
theorem transf_final_states {st1 : LTL.State} {st2 : Linear.State} {r : Integers.Int}
    (hm : MatchStates enumAux st1 st2) (h : LTL.FinalState st1 r) : Linear.FinalState st2 r := by
  cases h with
  | intro rs m retcode hr =>
      cases hm with
      | ret _ _ _ ts hs =>
          cases hs
          exact .intro _ _ _ hr

/-- `transf_program_correct`: linearization preserves the semantics of
    programs (forward simulation from LTL to Linear), for any enumeration
    heuristic `enumAux`. -/
theorem transf_program_correct :
    Smallstep.ForwardSimulation (LTL.semantics abi prog) (Linear.semantics abi tprog) :=
  Smallstep.forward_simulation_star (L1 := LTL.semantics abi prog)
    (L2 := Linear.semantics abi tprog) (MatchStates enumAux)
    (fun id => by
      show (Genv.toSenv tprog.globalenv).public_symbol id =
        (Genv.toSenv prog.globalenv).public_symbol id
      rw [senv_preserved enumAux TRANSF])
    (fun _ h => transf_initial_states enumAux TRANSF h)
    (fun _ _ _ hm h => transf_final_states enumAux hm h)
    measure
    (fun _ _ _ hst _ hm => transf_step_correct enumAux abi TRANSF hst hm)

end PRESERVATION

end TRANSF

/-! ## Linking (`match_prog`, `transf_program_match`, `TransfLinearizeLink`) -/

/-- `Linearizeproof.match_prog` -/
def MatchProgLink (enumAux : LTL.Function → PMap Bool → List LTL.Node)
    (p : LTL.Program) (tp : Linear.Program) : Prop :=
  Linking.MatchProgramCtx (fun _ f tf => Linearize.transfFundef enumAux f = .OK tf) Eq p tp

/-- `Linearizeproof.transf_program_match` -/
theorem transf_program_match (enumAux : LTL.Function → PMap Bool → List LTL.Node)
    {p : LTL.Program} {tp : Linear.Program}
    (h : Linearize.transfProgram enumAux p = .OK tp) : MatchProgLink enumAux p tp :=
  Linking.match_transform_partial_program h

/-- `Linearizeproof.TransfLinearizeLink` -/
instance transfLinearizeLink (enumAux : LTL.Function → PMap Bool → List LTL.Node) :
    Linking.TransfLink (MatchProgLink enumAux) :=
  Linking.transfPartialLinkAST _

/-- `Linearizeproof.transf_program_correct`, stated for `match_prog`. -/
theorem transf_program_correct_match (enumAux : LTL.Function → PMap Bool → List LTL.Node)
    (abi : Conventions1.AbiKind) {p : LTL.Program} {tp : Linear.Program}
    (h : MatchProgLink enumAux p tp) :
    Smallstep.ForwardSimulation (LTL.semantics abi p) (Linear.semantics abi tp) :=
  transf_program_correct enumAux abi (Linking.transformPartialProgram_of_match h)

end Linearizeproof
end CC
