/-
  [RISC-V instance of `CCLib/backend/CleanupLabelsproof.lean`: the same development, in
  namespace `CC.RiscV`, over the RISC-V operators, registers and conventions.]

  Correctness proof for the clean-up of labels — port of
  `backend/CleanupLabelsproof.v`.

  Main result: `CleanupLabelsproof.transf_program_correct`, a forward
  simulation from the Linear semantics of a program to the Linear semantics
  of `CleanupLabels.transfProgram` of it.

  Also proved here (from `backend/Op.v`): `Op.evalOperation_preserved` and
  `Op.evalAddressing_preserved` (evaluation of operators only depends on the
  symbol table of the global environment).

  Differences from Rocq: `Labelset` is a `PTree Unit`, membership is
  `Labelset.mem`; `incl` is `List.Subset`; `Senv.equiv` is replaced by the
  equality of symbol environments `Genv.senv_transf` (the transformation is
  total and keeps all symbols), so no `external_call_symbols_preserved`
  assumption is needed.
-/
import CCLib.riscV.CleanupLabels
import CCLib.common.GlobalenvsTransf
import CCLib.common.Simulation
import CCLib.common.LinkingTheory
import CCLib.riscV.OpTheory

namespace CC
namespace RiscV

/-! ### Operators only depend on the symbol table (`Op.v`) -/


namespace CleanupLabelsproof

open Linear CleanupLabels

/-! ### Correctness of `labels_branched_to` -/

/-- `instr_branches_to` -/
def instrBranchesTo (i : Linear.Instruction) (lbl : Linear.Label) : Prop :=
  match i with
  | .Lgoto lbl' => lbl = lbl'
  | .Lcond _ _ lbl' => lbl = lbl'
  | .Ljumptable _ tbl => lbl ∈ tbl
  | _ => False

theorem mem_add_self (l : Linear.Label) (s : Labelset) : Labelset.mem l (Labelset.add l s) = true := by
  simp [Labelset.mem, Labelset.add]

theorem mem_add_of_mem {l l' : Linear.Label} {s : Labelset} (h : Labelset.mem l s = true) :
    Labelset.mem l (Labelset.add l' s) = true := by
  by_cases e : l' = l
  · subst e; exact mem_add_self _ _
  · simp only [Labelset.mem, Labelset.add] at *
    rw [PTree.gso _ _ _ _ e]; exact h

theorem mem_foldr_add_of_mem {l : Linear.Label} {s : Labelset} (h : Labelset.mem l s = true) :
    ∀ tbl : List Linear.Label, Labelset.mem l (tbl.foldr Labelset.add s) = true
  | [] => h
  | _ :: tbl => mem_add_of_mem (mem_foldr_add_of_mem h tbl)

theorem mem_foldr_add_of_in {l : Linear.Label} (s : Labelset) :
    ∀ {tbl : List Linear.Label}, l ∈ tbl → Labelset.mem l (tbl.foldr Labelset.add s) = true
  | _ :: tbl, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact mem_add_self _ _
      · exact mem_add_of_mem (mem_foldr_add_of_in s h)

/-- `add_label_branched_to_incr` -/
theorem add_label_branched_to_incr {l : Linear.Label} {ls : Labelset} (i : Linear.Instruction)
    (h : Labelset.mem l ls = true) : Labelset.mem l (CleanupLabels.addLabelBranchedTo ls i) = true := by
  cases i <;> simp only [CleanupLabels.addLabelBranchedTo] <;>
    first | exact h | exact mem_add_of_mem h | exact mem_foldr_add_of_mem h _

/-- `add_label_branched_to_contains` -/
theorem add_label_branched_to_contains (ls : Labelset) {i : Linear.Instruction} {lbl : Linear.Label}
    (h : instrBranchesTo i lbl) : Labelset.mem lbl (CleanupLabels.addLabelBranchedTo ls i) = true := by
  cases i <;> simp only [instrBranchesTo] at h <;> simp only [CleanupLabels.addLabelBranchedTo]
  · subst h; exact mem_add_self _ _
  · subst h; exact mem_add_self _ _
  · exact mem_foldr_add_of_in ls h

theorem foldl_incr {l : Linear.Label} : ∀ (c : Linear.Code) {bto : Labelset}, Labelset.mem l bto = true →
    Labelset.mem l (c.foldl CleanupLabels.addLabelBranchedTo bto) = true
  | [], _, h => h
  | i :: c, _, h => foldl_incr c (add_label_branched_to_incr i h)

theorem foldl_contains {i : Linear.Instruction} {lbl : Linear.Label} (hb : instrBranchesTo i lbl) :
    ∀ (c : Linear.Code) (bto : Labelset), i ∈ c →
      Labelset.mem lbl (c.foldl CleanupLabels.addLabelBranchedTo bto) = true
  | a :: c, bto, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact foldl_incr c (add_label_branched_to_contains bto hb)
      · exact foldl_contains hb c _ h

/-- `labels_branched_to_correct` -/
theorem labels_branched_to_correct {c : Linear.Code} {i : Linear.Instruction} {lbl : Linear.Label}
    (hi : i ∈ c) (hb : instrBranchesTo i lbl) : Labelset.mem lbl (CleanupLabels.labelsBranchedTo c) = true :=
  foldl_contains hb c _ hi

/-! ### Commutation with `find_label` -/

/-- `remove_unused_labels_cons` -/
theorem remove_unused_labels_cons (bto : Labelset) (i : Linear.Instruction) (c : Linear.Code) :
    CleanupLabels.removeUnusedLabels bto (i :: c) = CleanupLabels.removeUnused bto i (CleanupLabels.removeUnusedLabels bto c) := rfl

/-- `find_label_commut` -/
theorem find_label_commut {lbl : Linear.Label} {bto : Labelset} (hin : Labelset.mem lbl bto = true) :
    ∀ {c c' : Linear.Code}, Linear.findLabel lbl c = some c' →
      Linear.findLabel lbl (CleanupLabels.removeUnusedLabels bto c) = some (CleanupLabels.removeUnusedLabels bto c')
  | [], _, h => by simp [Linear.findLabel] at h
  | a :: c, c', h => by
      rw [remove_unused_labels_cons]
      cases a with
      | Llabel l =>
          simp only [Linear.findLabel, Linear.isLabel] at h
          by_cases e : lbl = l
          · subst e
            simp at h; subst h
            simp [CleanupLabels.removeUnused, hin, Linear.findLabel, Linear.isLabel]
          · simp only [e, decide_false] at h
            have ih := find_label_commut hin h
            simp only [CleanupLabels.removeUnused]
            split
            · simp [Linear.findLabel, Linear.isLabel, e, ih]
            · exact ih
      | _ =>
          simp only [Linear.findLabel, Linear.isLabel] at h
          simp only [CleanupLabels.removeUnused, Linear.findLabel, Linear.isLabel]
          exact find_label_commut hin h

/-- `find_label_translated` -/
theorem find_label_translated {f : Linear.Function} {i : Linear.Instruction} {c' c : Linear.Code} {lbl : Linear.Label}
    (hincl : i :: c' ⊆ f.fn_code) (hf : Linear.findLabel lbl f.fn_code = some c)
    (hb : instrBranchesTo i lbl) :
    Linear.findLabel lbl (CleanupLabels.transfFunction f).fn_code =
      some (CleanupLabels.removeUnusedLabels (CleanupLabels.labelsBranchedTo f.fn_code) c) :=
  find_label_commut (labels_branched_to_correct (hincl (List.mem_cons_self ..)) hb) hf

/-- `find_label_incl` -/
theorem find_label_incl {lbl : Linear.Label} : ∀ {c c' : Linear.Code}, Linear.findLabel lbl c = some c' → c' ⊆ c
  | [], _, h => by simp [Linear.findLabel] at h
  | a :: c, c', h => by
      simp only [Linear.findLabel] at h
      split at h
      · cases h; exact List.subset_cons_self _ _
      · exact List.Subset.trans (find_label_incl h) (List.subset_cons_self _ _)

/-- `Coqlib.list_nth_z_in` -/
theorem listNthZ_mem {A : Type} : ∀ {l : List A} {n : Z} {x : A},
    CminorSel.listNthZ l n = some x → x ∈ l
  | [], _, _, h => by simp [CminorSel.listNthZ] at h
  | _ :: _, _, _, h => by
      simp only [CminorSel.listNthZ] at h
      split at h
      · cases h; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (listNthZ_mem h)

/-! ### The simulation -/

section CLEANUP
variable (prog : Linear.Program)


theorem symbols_preserved (id : Ident) : Genv.findSymbol (CleanupLabels.transfProgram prog).globalenv id = Genv.findSymbol prog.globalenv id :=
  find_symbol_transf CleanupLabels.transfFundef prog id

theorem senv_preserved : Genv.toSenv (CleanupLabels.transfProgram prog).globalenv = Genv.toSenv prog.globalenv := senv_transf CleanupLabels.transfFundef prog

theorem functions_translated {v : Val} {f : Linear.Fundef} (h : Genv.findFunct prog.globalenv v = some f) :
    Genv.findFunct (CleanupLabels.transfProgram prog).globalenv v = some (CleanupLabels.transfFundef f) := find_funct_transf CleanupLabels.transfFundef h

theorem function_ptr_translated {b : Block} {f : Linear.Fundef} (h : Genv.findFunctPtr prog.globalenv b = some f) :
    Genv.findFunctPtr (CleanupLabels.transfProgram prog).globalenv b = some (CleanupLabels.transfFundef f) := find_funct_ptr_transf CleanupLabels.transfFundef h

theorem sig_function_translated (f : Linear.Fundef) : Linear.funsig (CleanupLabels.transfFundef f) = Linear.funsig f := by
  cases f <;> rfl

theorem find_function_translated {ros : Sum Mreg Ident} {ls : LTL.Locset} {f : Linear.Fundef}
    (h : Linear.findFunction prog.globalenv ros ls = some f) :
    Linear.findFunction (CleanupLabels.transfProgram prog).globalenv ros ls = some (CleanupLabels.transfFundef f) := by
  cases ros with
  | inl r => exact functions_translated prog h
  | inr id =>
      simp only [Linear.findFunction, symbols_preserved] at h ⊢
      cases e : Genv.findSymbol prog.globalenv id with
      | none => rw [e] at h; cases h
      | some b => rw [e] at h; exact function_ptr_translated prog h

/-- `match_stackframes` -/
inductive MatchStackframes : Linear.Stackframe → Linear.Stackframe → Prop where
  | intro (f sp ls c) : c ⊆ f.fn_code →
      MatchStackframes (.Stackframe f sp ls c)
        (.Stackframe (CleanupLabels.transfFunction f) sp ls (CleanupLabels.removeUnusedLabels (CleanupLabels.labelsBranchedTo f.fn_code) c))

/-- `match_states` -/
inductive MatchStates : Linear.State → Linear.State → Prop where
  | intro (s f sp c ls m ts) : ListForall2 MatchStackframes s ts → c ⊆ f.fn_code →
      MatchStates (.State s f sp c ls m)
        (.State ts (CleanupLabels.transfFunction f) sp (CleanupLabels.removeUnusedLabels (CleanupLabels.labelsBranchedTo f.fn_code) c) ls m)
  | call (s f ls m ts) : ListForall2 MatchStackframes s ts →
      MatchStates (.Callstate s f ls m) (.Callstate ts (CleanupLabels.transfFundef f) ls m)
  | ret (s ls m ts) : ListForall2 MatchStackframes s ts →
      MatchStates (.Returnstate s ls m) (.Returnstate ts ls m)

/-- `measure` -/
def measure : Linear.State → Nat
  | .State _ _ _ c _ _ => c.length
  | _ => 0

/-- `match_parent_locset` -/
theorem match_parent_locset {s ts : List Linear.Stackframe} (h : ListForall2 MatchStackframes s ts) :
    Linear.parentLocset ts = Linear.parentLocset s := by
  cases h with
  | nil => rfl
  | cons hm _ => cases hm; rfl

theorem incl_tail {i : Linear.Instruction} {c c' : Linear.Code} (h : i :: c ⊆ c') : c ⊆ c' :=
  List.Subset.trans (List.subset_cons_self _ _) h

theorem incl_head {i : Linear.Instruction} {c c' : Linear.Code} (h : i :: c ⊆ c') : i :: [] ⊆ c' :=
  fun _ hx => h (by simp at hx; simp [hx])

/-- `transf_step_correct` -/
theorem transf_step_correct {s1 t s2} (hst : Linear.Step  prog.globalenv s1 t s2) {s1'}
    (hm : MatchStates s1 s1') :
    (∃ s2', Linear.Step  (CleanupLabels.transfProgram prog).globalenv s1' t s2' ∧ MatchStates s2 s2') ∨
    (measure s2 < measure s1 ∧ t = E0 ∧ MatchStates s2 s1') := by
  have hsym := symbols_preserved prog
  have hsenv := senv_preserved prog
  cases hst with
  | Lgetstack s f sp sl ofs ty dst b rs m rs' hrs =>
      cases hm with
      | intro _ _ _ _ _ _ ts hs hi =>
          exact .inl ⟨_, .Lgetstack _ _ _ _ _ _ _ _ _ _ _ hrs, .intro _ _ _ _ _ _ _ hs (incl_tail hi)⟩
  | Lsetstack s f sp src sl ofs ty b rs m rs' hrs =>
      cases hm with
      | intro _ _ _ _ _ _ ts hs hi =>
          exact .inl ⟨_, .Lsetstack _ _ _ _ _ _ _ _ _ _ _ hrs, .intro _ _ _ _ _ _ _ hs (incl_tail hi)⟩
  | Lop s f sp op args res b rs m v rs' hv hrs =>
      cases hm with
      | intro _ _ _ _ _ _ ts hs hi =>
          refine .inl ⟨_, .Lop _ _ _ _ _ _ _ _ _ v _ ?_ hrs, .intro _ _ _ _ _ _ _ hs (incl_tail hi)⟩
          rw [Op.evalOperation_preserved prog.globalenv (CleanupLabels.transfProgram prog).globalenv hsym]; exact hv
  | Lload s f sp chunk addr args dst b rs m a v rs' ha hv hrs =>
      cases hm with
      | intro _ _ _ _ _ _ ts hs hi =>
          refine .inl ⟨_, .Lload _ _ _ _ _ _ _ _ _ _ a v _ ?_ hv hrs,
            .intro _ _ _ _ _ _ _ hs (incl_tail hi)⟩
          rw [Op.evalAddressing_preserved prog.globalenv (CleanupLabels.transfProgram prog).globalenv hsym]; exact ha
  | Lstore s f sp chunk addr args src b rs m m' a rs' ha hv hrs =>
      cases hm with
      | intro _ _ _ _ _ _ ts hs hi =>
          refine .inl ⟨_, .Lstore _ _ _ _ _ _ _ _ _ _ m' a _ ?_ hv hrs,
            .intro _ _ _ _ _ _ _ hs (incl_tail hi)⟩
          rw [Op.evalAddressing_preserved prog.globalenv (CleanupLabels.transfProgram prog).globalenv hsym]; exact ha
  | Lcall s f sp sig ros b rs m f' hf hsig =>
      cases hm with
      | intro _ _ _ _ _ _ ts hs hi =>
          refine .inl ⟨_, .Lcall _ _ _ _ _ _ _ _ _ (find_function_translated prog hf)
            (by rw [sig_function_translated]; exact hsig), .call _ _ _ _ _ ?_⟩
          exact .cons (.intro _ _ _ _ (incl_tail hi)) hs
  | Ltailcall s f stk sig ros b rs m rs' f' m' hrs hf hsig hfree =>
      cases hm with
      | intro _ _ _ _ _ _ ts hs hi =>
          refine .inl ⟨_, .Ltailcall _ _ _ _ _ _ _ _ rs' _ m' ?_
            (find_function_translated prog hf)
            (by rw [sig_function_translated]; exact hsig) hfree, .call _ _ _ _ _ hs⟩
          rw [match_parent_locset hs]; exact hrs
  | Lbuiltin s f sp rs m ef args res b vargs t vres rs' m' hargs hec hrs =>
      cases hm with
      | intro _ _ _ _ _ _ ts hs hi =>
          refine .inl ⟨_, .Lbuiltin _ _ _ _ _ _ _ _ _ vargs t vres _ m' ?_ ?_ hrs,
            .intro _ _ _ _ _ _ _ hs (incl_tail hi)⟩
          · rw [hsenv]; exact hargs
          · rw [hsenv]; exact hec
  | Llabel s f sp lbl b rs m =>
      cases hm with
      | intro _ _ _ _ _ _ ts hs hi =>
          cases e : Labelset.mem lbl (CleanupLabels.labelsBranchedTo f.fn_code) with
          | true =>
              refine .inl ⟨_, ?_, .intro _ _ _ _ _ _ _ hs (incl_tail hi)⟩
              rw [remove_unused_labels_cons]
              simp only [CleanupLabels.removeUnused, e, if_true]
              exact .Llabel _ _ _ _ _ _ _
          | false =>
              refine .inr ⟨by simp [measure], rfl, ?_⟩
              rw [remove_unused_labels_cons]
              simp only [CleanupLabels.removeUnused, e]
              exact .intro _ _ _ _ _ _ _ hs (incl_tail hi)
  | Lgoto s f sp lbl b rs m b' hf =>
      cases hm with
      | intro _ _ _ _ _ _ ts hs hi =>
          refine .inl ⟨_, .Lgoto _ _ _ _ _ _ _ _ (find_label_translated hi hf rfl),
            .intro _ _ _ _ _ _ _ hs (List.Subset.trans (find_label_incl hf) (fun _ h => h))⟩
  | Lcond_true s f sp cond args lbl b rs m rs' b' hc hrs hf =>
      cases hm with
      | intro _ _ _ _ _ _ ts hs hi =>
          refine .inl ⟨_, .Lcond_true _ _ _ _ _ _ _ _ _ _ _ hc hrs
            (find_label_translated hi hf rfl),
            .intro _ _ _ _ _ _ _ hs (find_label_incl hf)⟩
  | Lcond_false s f sp cond args lbl b rs m rs' hc hrs =>
      cases hm with
      | intro _ _ _ _ _ _ ts hs hi =>
          exact .inl ⟨_, .Lcond_false _ _ _ _ _ _ _ _ _ _ hc hrs,
            .intro _ _ _ _ _ _ _ hs (incl_tail hi)⟩
  | Ljumptable s f sp arg tbl b rs m n lbl b' rs' hn hl hf hrs =>
      cases hm with
      | intro _ _ _ _ _ _ ts hs hi =>
          have hin : lbl ∈ tbl := listNthZ_mem hl
          exact .inl ⟨_, .Ljumptable _ _ _ _ _ _ _ _ n lbl _ _ hn hl
            (find_label_translated hi hf hin) hrs,
            .intro _ _ _ _ _ _ _ hs (find_label_incl hf)⟩
  | Lreturn s f stk b rs m m' hfree =>
      cases hm with
      | intro _ _ _ _ _ _ ts hs hi =>
          refine .inl ⟨_, ?_, .ret _ _ _ _ hs⟩
          rw [← match_parent_locset hs]
          exact .Lreturn _ _ _ _ _ _ _ hfree
  | function_internal s f rs m rs' m' stk halloc hrs =>
      cases hm with
      | call _ _ _ _ ts hs =>
          exact .inl ⟨_, .function_internal _ _ _ _ _ _ _ halloc hrs,
            .intro _ _ _ _ _ _ _ hs (fun _ h => h)⟩
  | function_external s ef args res rs1 rs2 m t m' hargs hec hrs =>
      cases hm with
      | call _ _ _ _ ts hs =>
          refine .inl ⟨_, .function_external _ _ _ _ _ _ _ _ _ hargs ?_ hrs, .ret _ _ _ _ hs⟩
          rw [hsenv]; exact hec
  | «return» s f sp rs0 c rs m =>
      cases hm with
      | ret _ _ _ ts hs =>
          cases hs with
          | cons hf hs =>
              cases hf with
              | intro _ _ _ _ hi =>
                  exact .inl ⟨_, .return _ _ _ _ _ _ _, .intro _ _ _ _ _ _ _ hs hi⟩

/-- `transf_initial_states` -/
theorem transf_initial_states {st1 : Linear.State} (h : Linear.InitialState prog st1) :
    ∃ st2, Linear.InitialState (CleanupLabels.transfProgram prog) st2 ∧ MatchStates st1 st2 := by
  cases h with
  | intro b f m0 hm hs hf hsig =>
      refine ⟨_, .intro b (CleanupLabels.transfFundef f) m0 ?_ ?_ (function_ptr_translated prog hf) ?_,
        .call _ _ _ _ _ .nil⟩
      · exact (init_mem_transf CleanupLabels.transfFundef prog).trans hm
      · rw [symbols_preserved]; exact hs
      · rw [sig_function_translated]; exact hsig

/-- `transf_final_states` -/
theorem transf_final_states {st1 st2 : Linear.State} {r : Integers.Int} (hm : MatchStates st1 st2)
    (h : Linear.FinalState st1 r) : Linear.FinalState st2 r := by
  cases h with
  | intro rs m retcode hr =>
      cases hm with
      | ret _ _ _ ts hs =>
          cases hs
          exact .intro _ _ _ hr

/-- `transf_program_correct`: label clean-up preserves the semantics of
    Linear programs (forward simulation). -/
theorem transf_program_correct :
    Smallstep.ForwardSimulation (Linear.semantics  prog) (Linear.semantics  (CleanupLabels.transfProgram prog)) :=
  Smallstep.forward_simulation_opt (L1 := Linear.semantics  prog) (L2 := Linear.semantics  (CleanupLabels.transfProgram prog))
    MatchStates
    (fun id => by
      show (Genv.toSenv (CleanupLabels.transfProgram prog).globalenv).public_symbol id = (Genv.toSenv prog.globalenv).public_symbol id
      rw [senv_preserved])
    (fun _ h => transf_initial_states prog h)
    (fun _ _ _ hm h => transf_final_states hm h)
    measure
    (fun _ _ _ hst _ hm => transf_step_correct  prog hst hm)

end CLEANUP

end CleanupLabelsproof
end RiscV
end CC
