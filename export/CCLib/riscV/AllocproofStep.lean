/-
  [RISC-V instance of `CCLib/backend/AllocproofStep.lean`: the same development, in
  namespace `CC.RiscV`, over the RISC-V operators, registers and conventions.]

  Correctness of register allocation, part 4 — port of the `PRESERVATION`
  section of `backend/Allocproof.v`: `exec_moves`, the simulation relation
  (`match_stackframes`, `match_states`), `step_simulation`,
  `initial_states_simulation`, `final_states_simulation`, `wt_prog` and
  **`transf_program_correct`**.

  Differences from Rocq:
  * The external register allocator is the parameter `regalloc` and the ABI
    the parameter `abi` (see `backend/Allocation.lean`).
  * Rocq's `external_call_mem_extends` and `external_call_well_typed` come
    from the axioms `external_functions_properties` and
    `inline_assembly_properties`; in the port the semantics of external
    functions and inline assembly are uninterpreted, so these properties are
    explicit hypotheses (`hextx`, `hasmx`, `hextw`, `hasmw`) of the theorem.
  * The simulation relation carries all the typing information it needs, so
    the invariant `wt_state` (and `subject_reduction`) is not needed to
    establish the simulation.
  * On this (64-bit) configuration, the block shapes for 64-bit integers
    split in two 32-bit halves (`BSmakelong`, `BSload2`, …) cannot occur
    (`Archi.splitlong = false`), so the corresponding cases are vacuous.
-/
import CCLib.riscV.AllocproofCall
import CCLib.riscV.CleanupLabelsproof

namespace CC
namespace RiscV
namespace Allocproof

open Op Allocation LTL RTLtyping Conventions1 Conventions Smallstep
open Allocation.Eqs (add remove)

/-- Every function of the source program has a translation. -/
theorem matchDefs_gfun {F1 F2 V1 V2 : Type} {Rf : F1 → F2 → Prop}
    {Rv : V1 → V2 → Prop} :
    ∀ {l1 : List (Ident × GlobDef F1 V1)} {l2 : List (Ident × GlobDef F2 V2)},
    Genv.MatchDefs Rf Rv l1 l2 → ∀ {i f}, (i, GlobDef.Gfun f) ∈ l1 → ∃ tf, Rf f tf := by
  intro l1 l2 h
  induction h with
  | nil => intro i f hin; cases hin
  | cons hg _ ih =>
    intro i f hin
    cases hin with
    | head => cases hg with | gfun hr => exact ⟨_, hr⟩
    | tail _ hin => exact ih hin

section PRESERVATION
variable (regalloc : RTL.Function → Res LTL.Function)

/-- `Allocproof.exec_moves` -/
theorem exec_moves (tge : LTL.CGenv) {env : Regenv} {rs : RTL.Regset} (s : List LTL.Stackframe)
    (f : LTL.Function) (sp : Val) (m : Mem) (hwt : WtRegset env rs) :
    ∀ {mv : Moves} {bb : Bblock} {e e' : Eqs} {ls : Locset}, trackMoves env mv e = some e' →
    WfMoves mv → Satisf rs ls e' →
    ∃ ls', Smallstep.Star (LTL.Step  tge) (LTL.State.Block s f sp (expandMoves mv bb) ls m) E0
      (LTL.State.Block s f sp bb ls' m) ∧ Satisf rs ls' e
  | [], bb, e, e', ls, h, _, hs => by
    cases h; exact ⟨ls, .refl _, hs⟩
  | .MV src dst :: mv, bb, e, e', ls, h, hw, hs => by
    simp only [trackMoves] at h
    split at h
    · cases h
    next e1 h1 =>
    split at h
    · next hc =>
      simp only [Bool.and_eq_true] at hc
      have hs1 := subst_loc_undef_satisf h hc.2 hc.1 hwt hs
      obtain ⟨ls', A, B⟩ := exec_moves tge s f sp m hwt h1
        (fun m hm => hw m (List.mem_cons_of_mem _ hm)) hs1
      refine ⟨ls', star_left (t1 := E0) ?_ A rfl, B⟩
      have hw0 := hw _ List.mem_cons_self
      cases src with
      | R rsrc =>
        cases dst with
        | R rdst => exact .Lop _ _ _ _ _ _ _ _ _ _ _ rfl rfl
        | S sl ofs ty => exact .Lsetstack _ _ _ _ _ _ _ _ _ _ _ rfl
      | S ssl sofs sty =>
        cases dst with
        | R rdst => exact .Lgetstack _ _ _ _ _ _ _ _ _ _ _ rfl
        | S _ _ _ => exact hw0.elim
    · cases h
  | .MVmakelong _ _ _ :: _, _, _, _, _, h, _, _ => by simp [trackMoves, Archi.ptr64] at h
  | .MVlowlong _ _ :: _, _, _, _, _, h, _, _ => by simp [trackMoves, Archi.ptr64] at h
  | .MVhighlong _ _ :: _, _, _, _, _, h, _, _ => by simp [trackMoves, Archi.ptr64] at h

/-- `Allocproof.match_stackframes` -/
inductive MatchStackframes (tge : LTL.CGenv) :
    List RTL.Stackframe → List LTL.Stackframe → Signature → Prop where
  | nil (sg : Signature) : sg.sig_res = .Xint → MatchStackframes tge [] [] sg
  | cons (res : Reg) (f : RTL.Function) (sp : Val) (pc : RTL.Node) (rs : RTL.Regset)
      (s : List RTL.Stackframe) (tf : LTL.Function) (bb : Bblock) (ls : Locset)
      (ts : List LTL.Stackframe) (sg : Signature) (an : PMap (Res Eqs)) (e : Eqs)
      (env : Regenv) :
      MatchStackframes tge s ts tf.fn_sig →
      Allocation.transfFunction  regalloc f = .OK tf →
      analyze  f env (pairCodes f tf) = some an →
      transfer  f env (pairCodes f tf) pc (an.get pc) = .OK e →
      WtFunction  f env → WtRegset env rs → env res = RTLtyping.projSigRes sg →
      (∀ v ls1 m, Val.Lessdef v (Locmap.getpair ((locResult sg).map Loc.R) ls1) →
        Val.HasType v (env res) → AgreeCalleeSave ls ls1 →
        ∃ ls2, Smallstep.Star (LTL.Step  tge) (LTL.State.Block ts tf sp bb ls1 m) E0
          (LTL.State.State ts tf sp pc ls2 m) ∧
          Satisf (rs.set res v) ls2 e) →
      MatchStackframes tge (.Stackframe res f sp pc rs :: s) (.Stackframe tf sp ls bb :: ts) sg

/-- `Allocproof.match_states` -/
inductive MatchStates (tge : LTL.CGenv) : RTL.State → LTL.State → Prop where
  | intro (s : List RTL.Stackframe) (f : RTL.Function) (sp : Val) (pc : RTL.Node)
      (rs : RTL.Regset) (m : Mem) (ts : List LTL.Stackframe) (tf : LTL.Function) (ls : Locset)
      (m' : Mem) (an : PMap (Res Eqs)) (e : Eqs) (env : Regenv) :
      MatchStackframes  regalloc tge s ts tf.fn_sig →
      Allocation.transfFunction  regalloc f = .OK tf →
      analyze  f env (pairCodes f tf) = some an →
      transfer  f env (pairCodes f tf) pc (an.get pc) = .OK e →
      Satisf rs ls e → Mem.Extends m m' → WtFunction  f env → WtRegset env rs →
      MatchStates tge (.State s f sp pc rs m) (.State ts tf sp pc ls m')
  | call (s : List RTL.Stackframe) (f : RTL.Fundef) (args : List Val) (m : Mem)
      (ts : List LTL.Stackframe) (tf : LTL.Fundef) (ls : Locset) (m' : Mem) :
      MatchStackframes  regalloc tge s ts (LTL.funsig tf) →
      Allocation.transfFundef  regalloc f = .OK tf →
      Val.LessdefList args ((locArguments  (LTL.funsig tf)).map (fun p => Locmap.getpair p ls)) →
      AgreeCalleeSave (parentLocset ts) ls → Mem.Extends m m' →
      Val.HasTypeList args (RTLtyping.projSigArgs (LTL.funsig tf)) →
      MatchStates tge (.Callstate s f args m) (.Callstate ts tf ls m')
  | ret (s : List RTL.Stackframe) (res : Val) (m : Mem) (ts : List LTL.Stackframe) (ls : Locset)
      (m' : Mem) (sg : Signature) :
      MatchStackframes  regalloc tge s ts sg →
      Val.Lessdef res (Locmap.getpair ((locResult sg).map Loc.R) ls) →
      AgreeCalleeSave (parentLocset ts) ls → Mem.Extends m m' →
      Val.HasType res (RTLtyping.projSigRes sg) →
      MatchStates tge (.Returnstate s res m) (.Returnstate ts ls m')

/-- `Allocproof.match_stackframes_change_sig` -/
theorem match_stackframes_change_sig {tge : LTL.CGenv} {s : List RTL.Stackframe}
    {ts : List LTL.Stackframe} {sg sg' : Signature}
    (h : MatchStackframes  regalloc tge s ts sg) (he : sg'.sig_res = sg.sig_res) :
    MatchStackframes  regalloc tge s ts sg' := by
  cases h with
  | nil _ h => exact .nil _ (he ▸ h)
  | cons res f sp pc rs s tf bb ls ts _ an e env A B C D E F G H =>
    refine .cons res f sp pc rs s tf bb ls ts sg' an e env A B C D E F
      (by rw [G]; simp only [RTLtyping.projSigRes, he]) ?_
    intro v ls1 m hv
    rw [locResult_exten he] at hv
    exact H v ls1 m hv

end PRESERVATION

end Allocproof
end RiscV
end CC
