/-
  Branch tunneling — port of `backend/Tunneling.v` (an LTL → LTL
  optimisation): `record_branch(es)`, `record_cond`, `record_conds_1`,
  `record_conds` (with its termination argument), `record_gotos`,
  `tunnel_instr`, `tunnel_block`, `tunnel_function`, `tunnel_fundef`,
  `tunnel_program`.
-/
import CCLib.backend.LTL
import CCLib.lib.UnionFind
import CCLib.lib.Postorder
import CCLib.backend.Tailcall

namespace CC
namespace Tunneling

open LTL UnionFind

/-- `Tunneling.record_branch` -/
def recordBranch (uf : UF) (pc : Node) (b : Bblock) : UF :=
  match b with
  | .Lbranch s :: _ => uf.union pc s
  | _ => uf

/-- `Tunneling.record_branches` -/
def recordBranches (f : LTL.Function) : UF := PTree.fold recordBranch f.fn_code UF.empty

/-- `Tunneling.record_cond` -/
def recordCond (st : LTL.Code × UF × Bool) (pc : Node) (b : Bblock) : LTL.Code × UF × Bool :=
  match b with
  | .Lcond _ _ s1 s2 :: _ =>
      let (c, u, _) := st
      if u.repr s1 = u.repr s2 then (c.remove pc, u.union pc s1, true) else st
  | _ => st

/-- `Tunneling.record_conds_1` -/
def recordConds1 (cu : LTL.Code × UF) : LTL.Code × UF × Bool :=
  PTree.fold recordCond cu.1 (cu.1, cu.2, false)

/-- The invariant of the termination argument of `record_conds`. -/
theorem recordCond_foldl_card (N : Nat) :
    ∀ (L : List (Positive × Bblock)) (s : LTL.Code × UF × Bool),
      (L.map Prod.fst).Nodup →
      (∀ p ∈ L, s.1.get p.1 = some p.2) →
      PTree.cardinal s.1 + (if s.2.2 then 1 else 0) ≤ N →
      let s' := L.foldl (fun a p => recordCond a p.1 p.2) s
      PTree.cardinal s'.1 + (if s'.2.2 then 1 else 0) ≤ N
  | [], _, _, _, h => h
  | (pc, b) :: L, ⟨c, u, ch⟩, hnd, hget, hcard => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.foldl_cons]
    apply recordCond_foldl_card N L _ hnd.2
    · intro p hp
      have hne : p.1 ≠ pc := fun he => hnd.1 (he ▸ List.mem_map_of_mem hp)
      have hg := hget p (List.mem_cons_of_mem _ hp)
      simp only [recordCond]
      split
      · split
        · simp only
          rw [PTree.gro _ _ _ (Ne.symm hne)]; exact hg
        · exact hg
      · exact hg
    · have hpc : c.get pc = some b := hget (pc, b) List.mem_cons_self
      simp only [recordCond]
      split
      · split
        · simp only [if_true]
          have := PTree.cardinal_remove_lt pc c hpc
          simp only at hcard
          split at hcard <;> omega
        · exact hcard
      · exact hcard

theorem recordConds1_decreases (cu : LTL.Code × UF) {cu' : LTL.Code × UF}
    (h : recordConds1 cu = (cu'.1, cu'.2, true)) :
    PTree.cardinal cu'.1 < PTree.cardinal cu.1 := by
  have := recordCond_foldl_card (PTree.cardinal cu.1) (PTree.elements cu.1) (cu.1, cu.2, false)
    (PTree.elements_keys_norepet cu.1)
    (fun p hp => PTree.elements_complete cu.1 p.1 p.2 hp) (by simp)
  simp only at this
  rw [← PTree.fold_spec] at this
  change PTree.cardinal (recordConds1 cu).1 + (if (recordConds1 cu).2.2 then 1 else 0) ≤ _ at this
  rw [h] at this
  simp only [if_true] at this
  omega

/-- `Tunneling.record_conds` -/
def recordConds (cu : LTL.Code × UF) : UF :=
  match h : recordConds1 cu with
  | (c', u', changed) =>
      if hc : changed then
        have : PTree.cardinal c' < PTree.cardinal cu.1 :=
          recordConds1_decreases cu (cu' := (c', u')) (by rw [h, hc])
        recordConds (c', u')
      else cu.2
termination_by PTree.cardinal cu.1

/-- `Tunneling.record_gotos` -/
def recordGotos (f : LTL.Function) : UF := recordConds (f.fn_code, recordBranches f)

/-- `Tunneling.tunnel_instr` -/
def tunnelInstr (u : UF) (i : LTL.Instruction) : LTL.Instruction :=
  match i with
  | .Lbranch s => .Lbranch (u.repr s)
  | .Lcond cond args s1 s2 =>
      let s1' := u.repr s1
      let s2' := u.repr s2
      if s1' = s2' then .Lbranch s1' else .Lcond cond args s1' s2'
  | .Ljumptable arg tbl => .Ljumptable arg (tbl.map u.repr)
  | _ => i

/-- `Tunneling.tunnel_block` -/
def tunnelBlock (u : UF) (b : Bblock) : Bblock := b.map (tunnelInstr u)

/-- `Tunneling.tunnel_function` -/
def tunnelFunction (f : LTL.Function) : LTL.Function :=
  let u := recordGotos f
  { fn_sig := f.fn_sig, fn_stacksize := f.fn_stacksize,
    fn_code := PTree.map1 (tunnelBlock u) f.fn_code,
    fn_entrypoint := u.repr f.fn_entrypoint }

/-- `Tunneling.tunnel_fundef` -/
def tunnelFundef (f : LTL.Fundef) : LTL.Fundef := ASTFundef.transf tunnelFunction f

/-- `Tunneling.tunnel_program` -/
def tunnelProgram (p : LTL.Program) : LTL.Program := transformProgram tunnelFundef p

end Tunneling
end CC
