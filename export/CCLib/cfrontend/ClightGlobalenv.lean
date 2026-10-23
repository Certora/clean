/-
  The `Globalenvs.v` theorems instantiated for Clight programs: a Clight
  program's global environment and initial memory are the generic
  `Genv.globalenv` / `Genv.initMem` of its public list and definitions, so the
  theorems of `CCLib.common.GlobalenvsTheory` and `CCLib.common.GlobalenvsInitMem` apply to
  `Program.globalenv` and `Program.initMem` directly.
-/
import CCLib.cfrontend.Clight
import CCLib.common.GlobalenvsInitMem
import CCLib.cfrontend.CtypesTheory

namespace CC
namespace Program

theorem globalenv_genv_eq (p : Program) :
    p.globalenv.genv_genv = Genv.globalenv p.prog_public p.prog_defs := rfl

theorem initMem_eq (p : Program) : p.initMem = Genv.initMem p.prog_public p.prog_defs := rfl

/-- `Genv.find_symbol_exists` for a Clight program. -/
theorem findSymbol_exists (p : Program) {id : Ident} {g : GlobDef FunDef Ty}
    (hin : (id, g) ∈ p.prog_defs) : ∃ b, Genv.findSymbol p.globalenv.genv_genv id = some b :=
  Genv.findSymbol_exists hin

/-- `Genv.find_funct_ptr_inversion` for a Clight program. -/
theorem findFunctPtr_inversion (p : Program) {b : Block} {f : FunDef}
    (h : Genv.findFunctPtr p.globalenv.genv_genv b = some f) :
    ∃ id, (id, GlobDef.Gfun f) ∈ p.prog_defs :=
  Genv.findFunctPtr_inversion h

/-- `Genv.find_symbol_not_fresh` for a Clight program. -/
theorem findSymbol_not_fresh (p : Program) {m : Mem} {id : Ident} {b : Block}
    (h : p.initMem = some m) (hs : Genv.findSymbol p.globalenv.genv_genv id = some b) :
    Mem.validBlock m b = true :=
  Genv.findSymbol_not_fresh h hs

/-- `Genv.initmem_inject` for a Clight program. -/
theorem initmem_inject (p : Program) {m : Mem} (h : p.initMem = some m) :
    Mem.Inject (Mem.flatInj m.nextblock) m m :=
  Genv.initmem_inject h

/-- `Genv.init_mem_exists` for a Clight program. -/
theorem initMem_exists (p : Program)
    (h : ∀ id v, (id, GlobDef.Gvar v) ∈ p.prog_defs →
      Genv.initDataListAligned 0 v.gvar_init ∧
      ∀ i o, InitData.Init_addrof i o ∈ v.gvar_init →
        ∃ b, Genv.findSymbol p.globalenv.genv_genv i = some b) :
    ∃ m, p.initMem = some m :=
  Genv.initMem_exists p.prog_public p.prog_defs h

end Program
end CC

namespace CC

/-- The composite environment of every program built by `mkprogram` is well
formed (CompCert gets this from the `prog_comp_env_eq` field of `program` and
`build_composite_env_consistent`). -/
theorem mkprogram_compEnv_wf (types : List CompositeDef) (defs : List (Ident × GlobDef FunDef Ty))
    (pub : List Ident) (main : Ident) : (mkprogram types defs pub main).prog_comp_env.WF := by
  simp only [mkprogram]
  cases h : buildCompositeEnv types with
  | OK env => exact buildCompositeEnv_wf h
  | Error e => exact compositeEnv_wf_empty

end CC
