/-
  Correctness proof for the postorder renumbering of RTL — port of
  `backend/Renumberproof.v`.

  Main result: `Renumberproof.transf_program_correct`, a forward simulation
  from the RTL semantics of a program to the RTL semantics of
  `Renumber.transfProgram` of it.

  Differences from Rocq: `renum_cfg_nodes` is proved directly on the list of
  elements of the code (the port's `PTree.fold` is a fold over
  `PTree.elements`), using `PTree.elements_keys_norepet`; `Senv.equiv` is the
  equality of symbol environments `senv_transf`, so no
  `external_call_symbols_preserved` is needed; `match_program_main` is
  definitional for `transformProgram`.
-/
import CCLib.backend.Renumber
import CCLib.lib.PostorderCorrect
import CCLib.backend.CleanupLabelsproof
import CCLib.common.LinkingFundef

namespace CC
namespace Renumberproof

open RTL Renumber

/-! ### Effect of an injective renaming of nodes on a CFG -/

section RENUMBER
variable (f : PTree Positive)

theorem renumNode_foldl_other (y : Positive) :
    ∀ (l : List (Positive × RTL.Instruction)) (acc : RTL.Code),
      (∀ p ∈ l, f.get p.1 ≠ some y) →
      (l.foldl (fun a p => renumNode f a p.1 p.2) acc).get y = acc.get y
  | [], _, _ => rfl
  | (k, j) :: l, acc, h => by
      simp only [List.foldl_cons]
      rw [renumNode_foldl_other y l _ (fun p hp => h p (List.mem_cons_of_mem _ hp))]
      simp only [renumNode]
      cases e : f.get k with
      | none => rfl
      | some y' =>
          have hne : y' ≠ y := fun heq => h (k, j) (List.mem_cons_self ..) (by rw [e, heq])
          exact PTree.gso _ _ _ _ hne

theorem renumNode_foldl_at
    (finj : ∀ x1 x2 y, f.get x1 = some y → f.get x2 = some y → x1 = x2) :
    ∀ (l : List (Positive × RTL.Instruction)) (acc : RTL.Code) (x y : Positive)
      (i : RTL.Instruction),
      (l.map Prod.fst).Nodup → (x, i) ∈ l → f.get x = some y →
      (l.foldl (fun a p => renumNode f a p.1 p.2) acc).get y = some (renumInstr f i)
  | [], _, _, _, _, _, hm, _ => by simp at hm
  | (k, j) :: l, acc, x, y, i, hnd, hm, hf => by
      simp only [List.map_cons, List.nodup_cons] at hnd
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hm with heq | hm'
      · cases heq
        rw [renumNode_foldl_other f y l _ ?_]
        · simp [renumNode, hf]
        · intro p hp hpy
          have := finj _ _ _ hpy hf
          exact hnd.1 (this ▸ List.mem_map_of_mem hp)
      · exact renumNode_foldl_at finj l _ x y i hnd.2 hm' hf

/-- `renum_cfg_nodes` -/
theorem renum_cfg_nodes
    (finj : ∀ x1 x2 y, f.get x1 = some y → f.get x2 = some y → x1 = x2)
    (c : RTL.Code) (x y : Positive) (i : RTL.Instruction)
    (hc : c.get x = some i) (hf : f.get x = some y) :
    (renumCfg f c).get y = some (renumInstr f i) :=
  renumNode_foldl_at f finj _ _ x y i (PTree.elements_keys_norepet c)
    (PTree.elements_correct c x i hc) hf

end RENUMBER

/-- `pnum` -/
def pnum (f : RTL.Function) : PTree Positive :=
  Postorder.postorder (successorsMap f) f.fn_entrypoint

/-- `reach` -/
def Reach (f : RTL.Function) (pc : RTL.Node) : Prop :=
  Postorder.Reachable (successorsMap f) f.fn_entrypoint pc

/-- `transf_function_at` -/
theorem transf_function_at {f : RTL.Function} {pc : RTL.Node} {i : RTL.Instruction}
    (hc : f.fn_code.get pc = some i) (hr : Reach f pc) :
    (Renumber.transfFunction f).fn_code.get (renumPc (pnum f) pc) = some (renumInstr (pnum f) i) := by
  obtain ⟨hinj, hreach⟩ := Postorder.postorder_correct (successorsMap f) f.fn_entrypoint
  have hne := hreach pc hr (by simp [successorsMap, hc])
  show (renumCfg (pnum f) f.fn_code).get _ = _
  cases e : (pnum f).get pc with
  | none => exact absurd e hne
  | some pc' =>
      simp only [renumPc, e]
      exact renum_cfg_nodes _ hinj _ _ _ _ hc e

/-- `reach_succ` -/
theorem reach_succ {f : RTL.Function} {pc : RTL.Node} {i : RTL.Instruction} {s : RTL.Node}
    (hc : f.fn_code.get pc = some i) (hs : s ∈ successorsInstr i) (hr : Reach f pc) :
    Reach f s :=
  .succ hr (by simp [successorsMap, hc]) hs

/-- `Coqlib.list_nth_z_map` -/
theorem listNthZ_map {A B : Type} (g : A → B) : ∀ {l : List A} {n : Z} {x : A},
    CminorSel.listNthZ l n = some x → CminorSel.listNthZ (l.map g) n = some (g x)
  | [], _, _, h => by simp [CminorSel.listNthZ] at h
  | _ :: _, _, _, h => by
      simp only [CminorSel.listNthZ, List.map_cons] at h ⊢
      split at h
      · cases h; simp [*]
      · rw [if_neg ‹_›]; exact listNthZ_map g h

/-! ### The simulation -/

section PRESERVATION
variable (prog : RTL.Program)

local notation "tprog" => Renumber.transfProgram prog

theorem symbols_preserved (id : Ident) :
    Genv.findSymbol (tprog).globalenv id = Genv.findSymbol prog.globalenv id :=
  find_symbol_transf Renumber.transfFundef prog id

theorem senv_preserved : Genv.toSenv (tprog).globalenv = Genv.toSenv prog.globalenv :=
  senv_transf Renumber.transfFundef prog

theorem functions_translated {v : Val} {f : RTL.Fundef}
    (h : Genv.findFunct prog.globalenv v = some f) :
    Genv.findFunct (tprog).globalenv v = some (Renumber.transfFundef f) :=
  find_funct_transf Renumber.transfFundef h

theorem function_ptr_translated {b : Block} {f : RTL.Fundef}
    (h : Genv.findFunctPtr prog.globalenv b = some f) :
    Genv.findFunctPtr (tprog).globalenv b = some (Renumber.transfFundef f) :=
  find_funct_ptr_transf Renumber.transfFundef h

/-- `sig_preserved` -/
theorem sig_preserved (f : RTL.Fundef) : RTL.funsig (Renumber.transfFundef f) = RTL.funsig f := by
  cases f <;> rfl

/-- `find_function_translated` -/
theorem find_function_translated {ros : Sum Reg Ident} {rs : RTL.Regset} {fd : RTL.Fundef}
    (h : RTL.findFunction prog.globalenv ros rs = some fd) :
    RTL.findFunction (tprog).globalenv ros rs = some (Renumber.transfFundef fd) := by
  cases ros with
  | inl r => exact functions_translated prog h
  | inr id =>
      simp only [RTL.findFunction, symbols_preserved] at h ⊢
      cases e : Genv.findSymbol prog.globalenv id with
      | none => rw [e] at h; cases h
      | some b => rw [e] at h; exact function_ptr_translated prog h

/-- `match_frames` -/
inductive MatchFrames : RTL.Stackframe → RTL.Stackframe → Prop where
  | intro (res f sp pc rs) : Reach f pc →
      MatchFrames (.Stackframe res f sp pc rs)
        (.Stackframe res (Renumber.transfFunction f) sp (renumPc (pnum f) pc) rs)

/-- `match_states` -/
inductive MatchStates : RTL.State → RTL.State → Prop where
  | regular (stk f sp pc rs m stk') : ListForall2 MatchFrames stk stk' → Reach f pc →
      MatchStates (.State stk f sp pc rs m)
        (.State stk' (Renumber.transfFunction f) sp (renumPc (pnum f) pc) rs m)
  | call (stk f args m stk') : ListForall2 MatchFrames stk stk' →
      MatchStates (.Callstate stk f args m) (.Callstate stk' (Renumber.transfFundef f) args m)
  | ret (stk v m stk') : ListForall2 MatchFrames stk stk' →
      MatchStates (.Returnstate stk v m) (.Returnstate stk' v m)

/-- `step_simulation` -/
theorem step_simulation {s1 t s2} (hst : RTL.Step prog.globalenv s1 t s2) {s1'}
    (hm : MatchStates s1 s1') :
    ∃ s2', RTL.Step (tprog).globalenv s1' t s2' ∧ MatchStates s2 s2' := by
  have hsym := symbols_preserved prog
  have hsenv := senv_preserved prog
  cases hst with
  | Inop s f sp pc rs m pc' hc =>
      cases hm with
      | regular _ _ _ _ _ _ stk' hs hr =>
          exact ⟨_, .Inop _ _ _ _ _ _ _ (transf_function_at hc hr),
            .regular _ _ _ _ _ _ _ hs (reach_succ hc (by simp [successorsInstr]) hr)⟩
  | Iop s f sp pc rs m op args res pc' v hc hv =>
      cases hm with
      | regular _ _ _ _ _ _ stk' hs hr =>
          refine ⟨_, .Iop _ _ _ _ _ _ _ _ _ _ v (transf_function_at hc hr) ?_,
            .regular _ _ _ _ _ _ _ hs (reach_succ hc (by simp [successorsInstr]) hr)⟩
          rw [evalOperation_preserved prog.globalenv (tprog).globalenv hsym]; exact hv
  | Iload s f sp pc rs m chunk addr args dst pc' a v hc ha hv =>
      cases hm with
      | regular _ _ _ _ _ _ stk' hs hr =>
          refine ⟨_, .Iload _ _ _ _ _ _ _ _ _ _ _ a v (transf_function_at hc hr) ?_ hv,
            .regular _ _ _ _ _ _ _ hs (reach_succ hc (by simp [successorsInstr]) hr)⟩
          rw [evalAddressing_preserved prog.globalenv (tprog).globalenv hsym]; exact ha
  | Istore s f sp pc rs m chunk addr args src pc' a m' hc ha hv =>
      cases hm with
      | regular _ _ _ _ _ _ stk' hs hr =>
          refine ⟨_, .Istore _ _ _ _ _ _ _ _ _ _ _ a m' (transf_function_at hc hr) ?_ hv,
            .regular _ _ _ _ _ _ _ hs (reach_succ hc (by simp [successorsInstr]) hr)⟩
          rw [evalAddressing_preserved prog.globalenv (tprog).globalenv hsym]; exact ha
  | Icall s f sp pc rs m sig ros args res pc' fd hc hf hsig =>
      cases hm with
      | regular _ _ _ _ _ _ stk' hs hr =>
          exact ⟨_, .Icall _ _ _ _ _ _ _ _ _ _ _ _ (transf_function_at hc hr)
            (find_function_translated prog hf) (by rw [sig_preserved]; exact hsig),
            .call _ _ _ _ _ (.cons (.intro _ _ _ _ _
              (reach_succ hc (by simp [successorsInstr]) hr)) hs)⟩
  | Itailcall s f stk pc rs m sig ros args fd m' hc hf hsig hfree =>
      cases hm with
      | regular _ _ _ _ _ _ stk' hs hr =>
          exact ⟨_, .Itailcall _ _ _ _ _ _ _ _ _ _ _ (transf_function_at hc hr)
            (find_function_translated prog hf) (by rw [sig_preserved]; exact hsig) hfree,
            .call _ _ _ _ _ hs⟩
  | Ibuiltin s f sp pc rs m ef args res pc' vargs t vres m' hc hargs hec =>
      cases hm with
      | regular _ _ _ _ _ _ stk' hs hr =>
          refine ⟨_, .Ibuiltin _ _ _ _ _ _ _ _ _ _ vargs t vres m'
            (transf_function_at hc hr) ?_ ?_,
            .regular _ _ _ _ _ _ _ hs (reach_succ hc (by simp [successorsInstr]) hr)⟩
          · rw [hsenv]; exact hargs
          · rw [hsenv]; exact hec
  | Icond s f sp pc rs m cond args ifso ifnot b pc' hc hcond hpc =>
      cases hm with
      | regular _ _ _ _ _ _ stk' hs hr =>
          subst hpc
          refine ⟨_, .Icond _ _ _ _ _ _ _ _ _ _ b _ (transf_function_at hc hr) hcond rfl, ?_⟩
          have : (if b then renumPc (pnum f) ifso else renumPc (pnum f) ifnot) =
              renumPc (pnum f) (if b then ifso else ifnot) := by cases b <;> rfl
          rw [this]
          exact .regular _ _ _ _ _ _ _ hs
            (reach_succ hc (by cases b <;> simp [successorsInstr]) hr)
  | Ijumptable s f sp pc rs m arg tbl n pc' hc hn hl =>
      cases hm with
      | regular _ _ _ _ _ _ stk' hs hr =>
          refine ⟨_, .Ijumptable _ _ _ _ _ _ _ _ n (renumPc (pnum f) pc')
            (transf_function_at hc hr) hn ?_,
            .regular _ _ _ _ _ _ _ hs (reach_succ hc (CleanupLabelsproof.listNthZ_mem hl) hr)⟩
          exact listNthZ_map _ hl
  | Ireturn s f stk pc rs m or m' hc hfree =>
      cases hm with
      | regular _ _ _ _ _ _ stk' hs hr =>
          exact ⟨_, .Ireturn _ _ _ _ _ _ _ _ (transf_function_at hc hr) hfree, .ret _ _ _ _ hs⟩
  | function_internal s f args m m' stk htyp halloc =>
      cases hm with
      | call _ _ _ _ stk' hs =>
          exact ⟨_, .function_internal _ (Renumber.transfFunction f) _ _ _ _ htyp halloc,
            .regular _ _ _ _ _ _ _ hs .root⟩
  | function_external s ef args res t m m' hec =>
      cases hm with
      | call _ _ _ _ stk' hs =>
          refine ⟨_, .function_external _ _ _ _ _ _ _ ?_, .ret _ _ _ _ hs⟩
          rw [hsenv]; exact hec
  | «return» res f sp pc rs s vres m =>
      cases hm with
      | ret _ _ _ stk' hs =>
          cases hs with
          | cons hf hs =>
              cases hf with
              | intro _ _ _ _ _ hr =>
                  exact ⟨_, .return _ _ _ _ _ _ _ _, .regular _ _ _ _ _ _ _ hs hr⟩

/-- `transf_initial_states` -/
theorem transf_initial_states {st1 : RTL.State} (h : RTL.InitialState prog st1) :
    ∃ st2, RTL.InitialState (tprog) st2 ∧ MatchStates st1 st2 := by
  cases h with
  | intro b f m0 hm hs hf hsig =>
      refine ⟨_, .intro b (Renumber.transfFundef f) m0 ?_ ?_ (function_ptr_translated prog hf) ?_,
        .call _ _ _ _ _ .nil⟩
      · exact (init_mem_transf Renumber.transfFundef prog).trans hm
      · rw [symbols_preserved]; exact hs
      · rw [sig_preserved]; exact hsig

/-- `transf_final_states` -/
theorem transf_final_states {st1 st2 : RTL.State} {r : Integers.Int} (hm : MatchStates st1 st2)
    (h : RTL.FinalState st1 r) : RTL.FinalState st2 r := by
  cases h with
  | intro r m =>
      cases hm with
      | ret _ _ _ ts hs =>
          cases hs
          exact .intro _ _

/-- `transf_program_correct`: renumbering preserves the semantics of RTL
    programs (forward simulation). -/
theorem transf_program_correct :
    Smallstep.ForwardSimulation (RTL.semantics prog) (RTL.semantics (tprog)) :=
  Smallstep.forward_simulation_step (L1 := RTL.semantics prog) (L2 := RTL.semantics (tprog))
    MatchStates
    (fun id => by
      show (Genv.toSenv (tprog).globalenv).public_symbol id =
        (Genv.toSenv prog.globalenv).public_symbol id
      rw [senv_preserved])
    (fun _ h => transf_initial_states prog h)
    (fun _ _ _ hm h => transf_final_states hm h)
    (fun _ _ _ hst _ hm => step_simulation prog hst hm)

end PRESERVATION

/-! ## Linking (`match_prog`, `transf_program_match`, `TransfRenumberLink`)

`MatchProgLink` is Rocq's `match_prog` (the name `MatchProg` is used in some
other proof files for the whole-program equation `transf_program p = OK tp`). -/

/-- `Renumberproof.match_prog` -/
def MatchProgLink (p tp : RTL.Program) : Prop :=
  Linking.MatchProgramCtx (fun _ f tf => tf = Renumber.transfFundef f) Eq p tp

/-- `Renumberproof.transf_program_match` -/
theorem transf_program_match (p : RTL.Program) : MatchProgLink p (Renumber.transfProgram p) :=
  Linking.match_transform_program _ p

/-- `Renumberproof.TransfRenumberLink` -/
instance transfRenumberLink : Linking.TransfLink MatchProgLink :=
  Linking.transfTotalLinkAST _ Renumber.transfFunction ⟨fun _ => rfl, fun _ => rfl⟩

/-- `Renumberproof.transf_program_correct`, stated for `match_prog` as in Rocq. -/
theorem transf_program_correct_match {p tp : RTL.Program} (h : MatchProgLink p tp) :
    Smallstep.ForwardSimulation (RTL.semantics p) (RTL.semantics tp) := by
  rw [Linking.transformProgram_of_match h]
  exact transf_program_correct p

end Renumberproof
end CC
