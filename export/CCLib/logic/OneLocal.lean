/-
  Functions with one addressable local variable: entry and exit.

  VST's `semax_func` handles a function whose locals live in memory
  (`fn_vars ≠ []`) by giving the body the `data_at_ Tsh ty (v_x)` of every
  local on entry and taking it back on return (`stackframe_of`).  This file is
  that rule for the common case of a single local `x : ty`
  (`verif_stackframe_demo`, `verif_structcopy`):

  * `satisfies_oneLocal` — the body starts with the local bound to *some*
    fresh block `b` (`AtE (emptyEnv.set x (b, ty)) L _`), owning its
    `sizeof ty` undefined bytes at `Freeable` next to the caller's
    precondition.  The body must be verified for every `b`.
  * `triple_return_oneLocal` — `return a;` frees the block, which needs the
    local's bytes back (in whatever state the body left them, as a
    `bytesPtsTo` run of the right length), and hands the rest to the caller.

  The resource transfer itself is `CC.allocVariables_resources`
  (`CCLib.logic.Locals`); the free uses `Heap.Agrees_free_frame`.
-/
import CCLib.logic.Locals
import CCLib.logic.ExactTempsHeap

namespace CC
namespace Sep

open HProp

/-! ## The environment of one local -/

theorem elemsAux_set_leaf {A : Type} (v : A) :
    ∀ (i : Positive) (rp : List Bool) (acc : List (Positive × A)),
      ∃ k, PTree.elemsAux (PTree.set i v PTree.Leaf) rp acc = (k, v) :: acc := by
  intro i
  induction i with
  | xH => intro rp acc; exact ⟨_, rfl⟩
  | xO ii ih => intro rp acc; simp only [PTree.set, PTree.elemsAux]; exact ih _ _
  | xI ii ih => intro rp acc; simp only [PTree.set, PTree.elemsAux]; exact ih _ _

/-- An environment with one local frees exactly that local's block. -/
theorem blocksOfEnv_single (ce : CompositeEnv) (id : Ident) (b : Block) (ty : Ty) :
    blocksOfEnv ce (emptyEnv.set id (b, ty)) = [(b, 0, sizeof ce ty)] := by
  obtain ⟨k, hk⟩ := elemsAux_set_leaf (b, ty) id [] []
  show (PTree.elemsAux (PTree.set id (b, ty) PTree.Leaf) [] []).map (blockOfBinding ce) = _
  rw [hk]; rfl

/-! ## Entry -/

/-- **A function with one addressable local meets its specification** if its
    body does, started from the local bound to an arbitrary fresh block `b`
    whose `sizeof ty` bytes are owned (undefined, `Freeable`) next to the
    precondition.  The `function_entry2` side conditions are decided at the
    concrete function. -/
theorem satisfies_oneLocal (ge : CGenv) (f : Function) (S : FunSpec) (vargs : List Val)
    (L : TempEnv) (id : Ident) (ty : Ty)
    (hvars : f.fn_vars = [(id, ty)])
    (hpar : listNorepet (varNames f.fn_params))
    (hdisj : listDisjoint (varNames f.fn_params) (varNames f.fn_temps))
    (hbind : bindParameterTemps f.fn_params vargs (createUndefTemps f.fn_temps) = some L)
    (hsz : 0 ≤ sizeof ge.genv_cenv ty)
    (body : ∀ b, Triple ge (FunctionEntry2 ge) f
        (AtE (emptyEnv.set id (b, ty)) L
          (S.pre vargs ∗ undefBytes .Freeable b 0 (sizeof ge.genv_cenv ty).toNat)) f.fn_body
        { normal := Assn.no, brk := Assn.no, cont := Assn.no, ret := S.post }) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f) S vargs := by
  refine satisfies_internal ge _ f S vargs _ ?_ (triple_exists ge _ f _ _ _ body)
  intro m hp hf hpre hd hag
  let r := Mem.alloc m 0 (sizeof ge.genv_cenv ty)
  have hav : AllocVariables ge.genv_cenv emptyEnv m [(id, ty)] (emptyEnv.set id (r.2, ty)) r.1 :=
    AllocVariables.cons _ _ _ _ _ r.1 r.2 _ _ rfl (AllocVariables.nil _ _)
  obtain ⟨hl, hdl, hagl, hloc⟩ := allocVariables_resources hav
    (by simp [listNorepet, varNames]) (by simpa using hsz) (Heap.union hp hf) hag
  obtain ⟨h1, h2, _, rfl, ⟨b', hb'⟩, rfl⟩ := hloc
  obtain ⟨hpu, hu, hdpu, rfl, ⟨hget, rfl⟩, hub⟩ := hb'
  have hbb : b' = r.2 := by
    have := hget; rw [PTree.gss] at this; injection this with h; injection h with h; exact h.symm
  subst hbb
  simp only [Heap.emp_union, Heap.union_emp] at hdl hagl ⊢
  obtain ⟨hdpl, hdfl⟩ := Heap.disjoint_union_left.mp hdl
  refine ⟨_, L, r.1, hu, FunctionEntry2.intro (by rw [hvars]; simp [listNorepet, varNames])
    hpar hdisj (by rw [hvars]; exact hav) hbind, ?_, ?_, ⟨r.2, rfl, rfl,
      ⟨hp, hu, hdpl, rfl, hpre, hub⟩⟩⟩
  · rw [Heap.disjoint_union_left]; exact ⟨hd, Heap.disjoint_comm hdfl⟩
  · rw [Heap.union_assoc, Heap.union_comm (Heap.disjoint_comm hdfl), ← Heap.union_assoc]
    exact hagl

/-! ## Exit -/

/-- **`return a;` from a function with one local**: the local's block is freed,
    which consumes its bytes `vl` (of the local's size, in whatever state the
    body left them); the remaining fragment `Hr` goes back to the caller. -/
theorem triple_return_oneLocal (ge : CGenv) (fe : EntryRel) (f : Function) (id : Ident) (ty : Ty)
    (b : Block) (L : TempEnv) (Hr : HProp) (vl : List MemVal) (a : Expr) (v v' : Val)
    (hlen : (vl.length : _root_.Int) = sizeof ge.genv_cenv ty)
    (hev : ∀ m hp, (Hr ∗ bytesPtsTo b .Freeable 0 vl) hp → Heap.Agrees hp m →
      EvalExpr ge (emptyEnv.set id (b, ty)) L m a v)
    (hcast : ∀ m, Cop.semCast v (typeof a) f.fn_return m = some v') :
    Triple ge fe f (AtE (emptyEnv.set id (b, ty)) L (Hr ∗ bytesPtsTo b .Freeable 0 vl))
      (.Sreturn (some a))
      { normal := Assn.no, brk := Assn.no, cont := Assn.no,
        ret := fun r hp => r = v' ∧ Hr hp } := by
  refine triple_return ge fe f _ _ _ (fun e le hp m h hag => ?_)
  obtain ⟨rfl, rfl, hH⟩ := h
  have hev' := hev m hp hH hag
  obtain ⟨hr, hloc, hdrl, rfl, hHr, hb⟩ := hH
  have hown := bytesPtsTo_ownsRange b .Freeable vl 0 hloc hb
  have hrp := bytesPtsTo_rangePerm hb (Heap.Agrees_union_right hdrl hag)
  rw [show (0 : _root_.Int) + (vl.length : _root_.Int) = sizeof ge.genv_cenv ty by omega] at hrp
  have hfree := Mem.free_isSome hrp
  refine ⟨v, v', Mem.uncheckedFree m b 0 (sizeof ge.genv_cenv ty), hr, hev', hcast m, ?_, ⟨rfl, hHr⟩, fun hf hd hag' => ?_⟩
  · rw [blocksOfEnv_single, Mem.freeList, hfree]; rfl
  · obtain ⟨hdrf, hdlf⟩ := Heap.disjoint_union_left.mp hd
    refine ⟨hdrf, Heap.Agrees_free_frame ?_ (fun ofs h1 h2 => ?_)⟩
    · rw [Heap.union_assoc, Heap.union_comm hdlf, ← Heap.union_assoc] at hag'
      exact Heap.Agrees_union_left hag'
    · have hi : (ofs.toNat : Nat) < vl.length := by omega
      have hc := hown ofs.toNat hi
      rw [show (0 : _root_.Int) + (ofs.toNat : _root_.Int) = ofs by omega] at hc
      have hrn : hr b ofs = none := by
        rcases hdrl b ofs with h | h
        · exact h
        · rw [hc] at h; exact absurd h (by simp)
      have hfn : hf b ofs = none := by
        rcases hdlf b ofs with h | h
        · rw [hc] at h; exact absurd h (by simp)
        · exact h
      rw [Heap.union_of_right hrn]; exact hfn

/-! ## The local's address -/

/-- `&x`, for the local `x` at block `b`. -/
theorem eval_addrof_oneLocal {ge : CGenv} {le : TempEnv} {m : Mem} {id : Ident} {ty : Ty}
    {b : Block} (tp : Ty) :
    EvalExpr ge (emptyEnv.set id (b, ty)) le m (.Eaddrof (.Evar id ty) tp)
      (.Vptr b Integers.Ptrofs.zero) :=
  EvalExpr.Eaddrof _ _ b Integers.Ptrofs.zero (EvalLvalue.Evar_local id b ty (PTree.gss _ _ _))

/-- `x` as an l-value, for the local `x` at block `b`. -/
theorem eval_lvalue_oneLocal {ge : CGenv} {le : TempEnv} {m : Mem} {id : Ident} {ty : Ty}
    {b : Block} :
    EvalLvalue ge (emptyEnv.set id (b, ty)) le m (.Evar id ty) b Integers.Ptrofs.zero .Full :=
  EvalLvalue.Evar_local id b ty (PTree.gss _ _ _)

end Sep
end CC
