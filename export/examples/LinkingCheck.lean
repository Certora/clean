/-
  Sanity checks for the generic linking theory (`CCLib/common/LinkingTheory.lean`,
  `CCLib/common/LinkingMatch.lean`): `link` on generic programs computes, resolves an
  `extern` declaration against a definition, and rejects two definitions of
  the same public name or a static name defined in both units.  Also checks
  composite-definition linking and the Clight program linker
  (`CCLib/cfrontend/CtypesLinking.lean`).
-/
import CCLib.cfrontend.CtypesLinking

namespace CC.LinkingCheck

open Linking Linker

/-- The identifiers used below. -/
def idMain : Ident := .xH
def idFoo : Ident := .xO .xH

/-- An `extern` declaration of `foo` (as `EF_external`). -/
def fooDecl : FunDefGen Unit :=
  .External (.EF_external "foo" signature_main) [] .Tvoid cc_default

/-- A definition of `foo`. -/
def fooDef : FunDefGen Unit := .Internal ()

/-- Unit 1 declares `foo` and defines `main`; unit 2 defines `foo`. -/
def unit1 : ASTProgram (FunDefGen Unit) Ty :=
  ⟨[(idFoo, .Gfun fooDecl), (idMain, .Gfun fooDef)], [idFoo, idMain], idMain⟩
def unit2 : ASTProgram (FunDefGen Unit) Ty :=
  ⟨[(idFoo, .Gfun fooDef)], [idFoo], idMain⟩

/-- Linking the two units succeeds. -/
example : (link unit1 unit2).isSome = true := by decide

/-- In the linked program, `foo` is the definition. -/
example (p : ASTProgram (FunDefGen Unit) Ty) (h : link unit1 unit2 = some p) :
    p.defmap.get idFoo = some (.Gfun fooDef) := by
  obtain ⟨_, _, rfl⟩ := link_prog_inv h
  rw [linkProgResult_defmap]
  rfl

/-- Two definitions of `foo` do not link. -/
example : (link unit2 unit2).isSome = false := by decide

/-- A static (non-public) `foo` defined in both units does not link. -/
def unit2Static : ASTProgram (FunDefGen Unit) Ty := ⟨[(idFoo, .Gfun fooDef)], [], idMain⟩
example : (link unit1 unit2Static).isSome = false := by decide

/-- `link_list` over two units, and `link_list_linkorder`: every unit is
    below the result. -/
example : (linkList (.ncons unit1 (.nbase unit2))).isSome = true := by decide

example (p : ASTProgram (FunDefGen Unit) Ty) (h : linkList (.ncons unit1 (.nbase unit2)) = some p) :
    linkorder unit2 p :=
  link_list_linkorder h (.inr rfl)

/-- `extern` and common variable initialisers link with a definitive one. -/
example : linkVarinit [] [.Init_int8 0] = some [.Init_int8 0] := by decide
example : linkVarinit [.Init_space 4] [.Init_int32 7] = some [.Init_int32 7] := by decide
example : linkVarinit [.Init_space 8] [.Init_int32 7] = none := by decide

/-! ### Composite definitions and Clight programs -/

open CtypesLinking

def sA : CompositeDef :=
  .Composite .xH .Struct [.Member_plain (.xO .xH) (.Tint .I32 .Signed noattr)] noattr
def sA' : CompositeDef := .Composite .xH .Struct [] noattr
def sB : CompositeDef := .Composite (.xI .xH) .Union [] noattr

/-- A shared definition is kept once; a new one is appended. -/
example : linkCompositeDefs [sA] [sA, sB] = some [sA, sB] := by decide
/-- Two different definitions of the same struct do not link. -/
example : linkCompositeDefs [sA] [sA'] = none := by decide

/-- A Clight program with no composites, packaged with its
    `prog_comp_env_eq` proof. -/
def emptyProg (defs : List (Ident × GlobDef FunDef Ty)) (pub : List Ident) : WFProgram :=
  ⟨{ prog_defs := defs, prog_public := pub, prog_main := .xH, prog_types := [],
     prog_comp_env := PTree.empty }, rfl⟩

example : (Linker.link (emptyProg [] []) (emptyProg [] [])).isSome = true := by decide

end CC.LinkingCheck
