/-
  Triples for straight-line code over an exactly known local state.

  For functions without addressable locals and without memory footprint, the
  simplest assertion gives the temporary environment exactly: `At L` says that
  the local environment is empty, the temporaries are `L`, and the heap
  fragment is empty.  Each `x = a;` then just pushes a `PTree.set`, and
  evaluating a temporary of a concrete `L` is decided by computation (`rfl`).
  This is the style of the VST tests on scalar code (`verif_dead_if`,
  `verif_logical_compare`, …).
-/
import CCLib.logic.SepHoareCore
import CCLib.logic.FunspecCall

namespace CC
namespace Sep

open HProp

/-- The local state is exactly `L`: no local variables, temporaries `L`, no
    memory. -/
def At (L : TempEnv) : Assn := fun e le hp => e = emptyEnv ∧ le = L ∧ hp = Heap.emp

/-- The local state is exactly known: the local environment is `e0`, the
    temporaries are `L`, and the heap fragment satisfies `H`.  `e0` is
    `emptyEnv` for a function without addressable locals (`AtH`), and binds
    the fresh blocks of the locals otherwise (`CCLib.logic.OneLocal`). -/
def AtE (e0 : Env) (L : TempEnv) (H : HProp) : Assn :=
  fun e le hp => e = e0 ∧ le = L ∧ H hp

/-- The local state is exactly `L` (no local variables, temporaries `L`), and
    the heap fragment satisfies `H`: the form of `At` for functions that own
    memory (globals, or blocks passed by pointer). -/
abbrev AtH (L : TempEnv) (H : HProp) : Assn := AtE emptyEnv L H

section
variable (ge : CGenv) (fe : EntryRel) {func : Function}

/-- `x = a;` where `a` evaluates to `v` in `L`. -/
theorem triple_set_at (L : TempEnv) (id : Ident) (a : Expr) (v : Val)
    (hev : ∀ m, EvalExpr ge emptyEnv L m a v) :
    Triple ge fe func (At L) (.Sset id a) (.only (At (L.set id v))) :=
  triple_set ge fe func _ _ _ _ (fun e le hp m hP _ => by
    obtain ⟨rfl, rfl, hh⟩ := hP
    exact ⟨v, hev m, rfl, rfl, hh⟩)

/-- `if (a) s1 else s2`, where `a` evaluates in `L` to the truth value `bv`. -/
theorem triple_if_at (L : TempEnv) (a : Expr) (s1 s2 : Stmt) (R : ExitConds) (v : Val)
    (bv : Bool) (hev : ∀ m, EvalExpr ge emptyEnv L m a v)
    (hb : ∀ m, Cop.boolVal v (typeof a) m = some bv)
    (h : Triple ge fe func (At L) (if bv then s1 else s2) R) :
    Triple ge fe func (At L) (.Sifthenelse a s1 s2) R := by
  cases bv
  · exact triple_if_false ge fe func _ _ _ _ _ (fun e le hp m hP _ => by
      obtain ⟨rfl, rfl, _⟩ := hP
      exact ⟨v, hev m, hb m⟩) h
  · exact triple_if_true ge fe func _ _ _ _ _ (fun e le hp m hP _ => by
      obtain ⟨rfl, rfl, _⟩ := hP
      exact ⟨v, hev m, hb m⟩) h

/-- `return a;` where `a` evaluates to `v` in `L`, converted to the return
    type as `v'`. -/
theorem triple_return_at (L : TempEnv) (a : Expr) (v v' : Val)
    (hev : ∀ m, EvalExpr ge emptyEnv L m a v)
    (hcast : ∀ m, Cop.semCast v (typeof a) func.fn_return m = some v') :
    Triple ge fe func (At L) (.Sreturn (some a))
      { normal := Assn.no, brk := Assn.no, cont := Assn.no,
        ret := fun r hp => r = v' ∧ hp = Heap.emp } := by
  refine triple_return ge fe func _ _ _ (fun e le hp m h _ => ?_)
  obtain ⟨rfl, rfl, hh⟩ := h
  exact ⟨v, v', m, hp, hev m, hcast m, freeList_emptyEnv _ _, ⟨rfl, hh⟩,
    fun _ hdj hag => ⟨hdj, hag⟩⟩

end

/-- Function entry for a function without local variables, called on `vargs`
    with an empty footprint: the body starts in `At L`, where `L` binds the
    parameters (the `function_entry2` side conditions are decided by the
    caller). -/
theorem satisfies_at (ge : CGenv) (f : Function) (S : FunSpec) (vargs : List Val)
    (L : TempEnv) (hvars : listNorepet (varNames f.fn_vars))
    (hpar : listNorepet (varNames f.fn_params))
    (hdisj : listDisjoint (varNames f.fn_params) (varNames f.fn_temps))
    (hnil : f.fn_vars = [])
    (hbind : bindParameterTemps f.fn_params vargs (createUndefTemps f.fn_temps) = some L)
    (hpre : ∀ hp, S.pre vargs hp → hp = Heap.emp)
    (body : Triple ge (FunctionEntry2 ge) f (At L) f.fn_body
        { normal := Assn.no, brk := Assn.no, cont := Assn.no, ret := S.post }) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f) S vargs :=
  satisfies_internal_noVars ge (FunctionEntry2 ge) f S vargs (At L)
    (fun _ => ⟨L, FunctionEntry2.intro hvars hpar hdisj (hnil ▸ AllocVariables.nil _ _) hbind,
      fun hp h => ⟨rfl, rfl, hpre hp h⟩⟩) body

end Sep
end CC
