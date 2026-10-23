/-
  Determinacy of the x86-64 assembly semantics — the end of `x86/Asm.v`
  (`semantics_determinate`), split from `Asm.lean` to keep file sizes
  manageable (the x86-64 instance of `CCLib/aarch64/AsmDeterm.lean`).
-/
import CCLib.x86.Asm

namespace CC
namespace X86
namespace Asm

open Op Smallstep

theorem execInstr_builtin (ge : CGenv) (f : Function) (ef : ExtFun)
    (args : List (BuiltinArg Preg)) (res : BuiltinRes Preg) (rs : Regset) (m : Mem) :
    execInstr ge f (.Pbuiltin ef args res) rs m = .Stuck := rfl

theorem singleEvents (win64 : Bool) (p : Program) :
    SingleEvents (semantics win64 p) := by
  intro s t s' h
  have hinj : (Genv.toSenv p.globalenv).SymbolsInjective := Genv.toSenv_symbolsInjective
    (Genv.symbInjective_globalenv p.prog_public p.prog_defs)
  cases h with
  | exec_step_builtin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hec =>
    exact (externalCall_determ _ hinj).traceLength _ _ _ _ _ hec
  | exec_step_external _ _ _ _ _ _ _ _ _ _ _ _ hec =>
    exact (externalCall_determ _ hinj).traceLength _ _ _ _ _ hec
  | _ => simp [E0]

set_option maxHeartbeats 4000000 in
theorem step_determ {win64 : Bool} {ge : CGenv}
    (hinj : (Genv.toSenv ge).SymbolsInjective)
    {s t1 s1 t2 s2} (h1 : Step win64 ge s t1 s1) (h2 : Step win64 ge s t2 s2) :
    MatchTraces (Genv.toSenv ge) t1 t2 ∧ (t1 = t2 → s1 = s2) := by
  cases h1 with
  | exec_step_internal b ofs f i rs m rs' m' hpc hf hi he =>
    cases h2 with
    | exec_step_internal b2 ofs2 f2 i2 _ _ rs2 m2 hpc2 hf2 hi2 he2 =>
      rw [hpc] at hpc2; cases hpc2
      rw [hf] at hf2; cases hf2
      rw [hi] at hi2; cases hi2
      have e := he.symm.trans he2
      injection e with e1 e2
      subst e1 e2
      exact ⟨.nil, fun _ => rfl⟩
    | exec_step_builtin b2 ofs2 f2 _ _ _ _ _ _ _ _ _ _ hpc2 hf2 hi2 =>
      rw [hpc] at hpc2; cases hpc2
      rw [hf] at hf2; cases hf2
      rw [hi] at hi2; cases hi2
      rw [execInstr_builtin] at he; cases he
    | exec_step_external b2 _ _ _ _ _ _ _ _ hpc2 hf2 =>
      rw [hpc] at hpc2; cases hpc2
      rw [hf] at hf2; cases hf2
  | exec_step_builtin b ofs f ef args res rs m vargs t vres rs' m' hpc hf hi hargs hec hrs =>
    cases h2 with
    | exec_step_internal b2 ofs2 f2 i2 _ _ rs2 m2 hpc2 hf2 hi2 he2 =>
      rw [hpc] at hpc2; cases hpc2
      rw [hf] at hf2; cases hf2
      rw [hi] at hi2; cases hi2
      rw [execInstr_builtin] at he2; cases he2
    | exec_step_builtin b2 ofs2 f2 ef2 args2 res2 _ _ vargs2 t2 vres2 rs2 m2 hpc2 hf2 hi2 hargs2
        hec2 hrs2 =>
      rw [hpc] at hpc2; cases hpc2
      rw [hf] at hf2; cases hf2
      rw [hi] at hi2; cases hi2
      have hv := evalBuiltinArgs_determ hargs hargs2
      subst hv
      obtain ⟨hmt, hrest⟩ := (externalCall_determ _ hinj).determ _ _ _ _ _ _ _ _ hec hec2
      refine ⟨hmt, fun ht => ?_⟩
      obtain ⟨hv, hm⟩ := hrest ht
      subst hv hm hrs hrs2
      rfl
    | exec_step_external b2 _ _ _ _ _ _ _ _ hpc2 hf2 =>
      rw [hpc] at hpc2; cases hpc2
      rw [hf] at hf2; cases hf2
  | exec_step_external b ef args res rs m t rs' m' hpc hf hargs hec hrs =>
    cases h2 with
    | exec_step_internal b2 ofs2 f2 i2 _ _ rs2 m2 hpc2 hf2 =>
      rw [hpc] at hpc2; cases hpc2
      rw [hf] at hf2; cases hf2
    | exec_step_builtin b2 ofs2 f2 _ _ _ _ _ _ _ _ _ _ hpc2 hf2 =>
      rw [hpc] at hpc2; cases hpc2
      rw [hf] at hf2; cases hf2
    | exec_step_external b2 ef2 args2 res2 _ _ t2 rs2 m2 hpc2 hf2 hargs2 hec2 hrs2 =>
      rw [hpc] at hpc2; cases hpc2
      rw [hf] at hf2; cases hf2
      have hv := extcallArguments_determ hargs hargs2
      subst hv
      obtain ⟨hmt, hrest⟩ := (externalCall_determ _ hinj).determ _ _ _ _ _ _ _ _ hec hec2
      refine ⟨hmt, fun ht => ?_⟩
      obtain ⟨hv, hm⟩ := hrest ht
      subst hv hm hrs hrs2
      rfl

/-- `Asm.semantics_determinate` -/
theorem semantics_determinate (win64 : Bool) (p : Program) :
    Smallstep.Determinate (semantics win64 p) where
  sd_determ := fun _ _ _ _ _ h1 h2 =>
    step_determ (Genv.toSenv_symbolsInjective
      (Genv.symbInjective_globalenv p.prog_public p.prog_defs)) h1 h2
  sd_traces := singleEvents win64 p
  sd_initial_determ := by
    intro s1 s2 h1 h2
    cases h1 with
    | intro m1 hm1 =>
      cases h2 with
      | intro m2 hm2 =>
        rw [hm1] at hm2; cases hm2; rfl
  sd_final_nostep := by
    intro s r h t s' hs
    cases h with
    | intro rs m r hpc _ =>
      cases hs <;> simp_all [Val.Vnullptr, Archi.ptr64]
  sd_final_determ := by
    intro s r1 r2 h1 h2
    cases h1 with
    | intro rs m _ _ hr1 =>
      cases h2 with
      | intro _ _ _ _ hr2 =>
        rw [hr1] at hr2; cases hr2; rfl

end Asm
end X86
end CC
