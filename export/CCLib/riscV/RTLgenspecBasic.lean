/-
  [RISC-V instance of `CCLib/backend/RTLgenspecBasic.lean`: the same development, in
  namespace `CC.RiscV`, over the RISC-V operators, registers and conventions.]

  Abstract specification of RTL generation — port of `backend/RTLgenspec.v`,
  part 1: reasoning about monadic computations (`bind_inversion`,
  `bind2_inversion`), monotonicity of the state (`instr_at_incr`), validity
  and freshness of registers (`reg_valid`, `reg_fresh`, `regs_valid`,
  `reg_in_map`, `map_valid`), properties of the basic state operations
  (`add_instr`, `update_instr`, `new_reg`, `find_var`, `find_letvar`,
  `add_var(s)`, `add_letvar`, `alloc_reg(s)`, `alloc_optreg`), the target
  register predicates (`target_reg_ok`, `target_regs_ok`) and
  `return_reg_ok`.

  Rocq's `monadInv` tactic is replaced by explicit uses of `bind_inv` /
  `bind2_inv`.
-/
import CCLib.riscV.RTLgen

namespace CC
namespace RiscV
namespace RTLgen

open Op CminorSel RTL

/-! ## Reasoning about monadic computations -/

/-- `RTLgenspec.bind_inversion` -/
theorem bind_inv {A B : Type} {f : Mon A} {g : A → Mon B} {y : B} {s1 s3 : State}
    {i : StateIncr s1 s3} (h : bind f g s1 = .OK y s3 i) :
    ∃ x s2 i1 i2, f s1 = .OK x s2 i1 ∧ g x s2 = .OK y s3 i2 := by
  unfold bind at h
  split at h
  · cases h
  · next a s' i' hf =>
    split at h
    · cases h
    · next b s'' i'' hg =>
      cases h
      exact ⟨a, s', i', i'', hf, hg⟩

/-- `RTLgenspec.bind2_inversion` -/
theorem bind2_inv {A B C : Type} {f : Mon (A × B)} {g : A → B → Mon C} {z : C} {s1 s3 : State}
    {i : StateIncr s1 s3} (h : bind2 f g s1 = .OK z s3 i) :
    ∃ x y s2 i1 i2, f s1 = .OK (x, y) s2 i1 ∧ g x y s2 = .OK z s3 i2 := by
  obtain ⟨⟨x, y⟩, s2, i1, i2, h1, h2⟩ := bind_inv h
  exact ⟨x, y, s2, i1, i2, h1, h2⟩

theorem ret_inv {A : Type} {x y : A} {s1 s2 : State} {i : StateIncr s1 s2}
    (h : ret x s1 = .OK y s2 i) : x = y ∧ s1 = s2 := by
  cases h; exact ⟨rfl, rfl⟩

theorem error_inv {A : Type} {msg : String} {y : A} {s1 s2 : State} {i : StateIncr s1 s2}
    (h : (error msg : Mon A) s1 = .OK y s2 i) : False := by
  cases h

/-! ## Monotonicity properties of the state -/

/-- `RTLgenspec.instr_at_incr` -/
theorem instr_at_incr {s1 s2 : State} {n : Node} {i : Instruction} (h : StateIncr s1 s2)
    (hi : s1.st_code.get n = some i) : s2.st_code.get n = some i := by
  cases h with
  | intro _ _ h3 =>
    rcases h3 n with h | h
    · rw [hi] at h; cases h
    · rw [h, hi]

/-! ## Validity and freshness of registers -/

/-- `RTLgenspec.reg_valid` -/
def RegValid (r : Reg) (s : State) : Prop := r < s.st_nextreg

/-- `RTLgenspec.reg_fresh` -/
def RegFresh (r : Reg) (s : State) : Prop := ¬ r < s.st_nextreg

theorem valid_fresh_absurd {r : Reg} {s : State} (h1 : RegValid r s) (h2 : RegFresh r s) :
    False := h2 h1

theorem valid_fresh_different {r1 r2 : Reg} {s : State} (h1 : RegValid r1 s)
    (h2 : RegFresh r2 s) : r1 ≠ r2 := by
  rintro rfl; exact h2 h1

theorem reg_valid_incr {r : Reg} {s1 s2 : State} (h : StateIncr s1 s2) (hv : RegValid r s1) :
    RegValid r s2 := by
  cases h with
  | intro _ h2 _ => exact Nat.lt_of_lt_of_le hv h2

theorem reg_fresh_decr {r : Reg} {s1 s2 : State} (h : StateIncr s1 s2) (hf : RegFresh r s2) :
    RegFresh r s1 := fun hv => hf (reg_valid_incr h hv)

/-- `RTLgenspec.regs_valid` -/
def RegsValid (rl : List Reg) (s : State) : Prop := ∀ r, r ∈ rl → RegValid r s

theorem regs_valid_nil (s : State) : RegsValid [] s := fun _ h => by cases h

theorem regs_valid_cons {r1 : Reg} {rl : List Reg} {s : State} (h1 : RegValid r1 s)
    (h2 : RegsValid rl s) : RegsValid (r1 :: rl) s := by
  intro r hr
  cases hr with
  | head => exact h1
  | tail _ h => exact h2 r h

theorem regs_valid_app {rl1 rl2 : List Reg} {s : State} (h1 : RegsValid rl1 s)
    (h2 : RegsValid rl2 s) : RegsValid (rl1 ++ rl2) s := by
  intro r hr
  rcases List.mem_append.mp hr with h | h
  · exact h1 r h
  · exact h2 r h

theorem regs_valid_incr {s1 s2 : State} {rl : List Reg} (h : StateIncr s1 s2)
    (hv : RegsValid rl s1) : RegsValid rl s2 := fun r hr => reg_valid_incr h (hv r hr)

/-- `RTLgenspec.reg_in_map` -/
def RegInMap (m : Mapping) (r : Reg) : Prop :=
  (∃ id, m.map_vars.get id = some r) ∨ r ∈ m.map_letvars

/-- `RTLgenspec.map_valid` -/
def MapValid (m : Mapping) (s : State) : Prop := ∀ r, RegInMap m r → RegValid r s

theorem map_valid_incr {s1 s2 : State} {m : Mapping} (h : StateIncr s1 s2) (hv : MapValid m s1) :
    MapValid m s2 := fun r hr => reg_valid_incr h (hv r hr)

/-! ## Properties of basic operations over the state -/

/-- `RTLgenspec.add_instr_at` -/
theorem add_instr_at {s1 s2 : State} {incr : StateIncr s1 s2} {i : Instruction} {n : Node}
    (h : addInstr i s1 = .OK n s2 incr) : s2.st_code.get n = some i := by
  cases h; exact PTree.gss _ _ _

/-- `RTLgenspec.update_instr_at` -/
theorem update_instr_at {n : Node} {i : Instruction} {s1 s2 : State} {incr : StateIncr s1 s2}
    {u : Unit} (h : updateInstr n i s1 = .OK u s2 incr) : s2.st_code.get n = some i := by
  unfold updateInstr at h
  split at h
  · split at h
    · cases h; exact PTree.gss _ _ _
    · cases h
  · cases h

/-- `RTLgenspec.new_reg_valid` -/
theorem new_reg_valid {s1 s2 : State} {r : Reg} {i : StateIncr s1 s2}
    (h : newReg s1 = .OK r s2 i) : RegValid r s2 := by
  cases h; exact Positive.lt_succ_self _

/-- `RTLgenspec.new_reg_fresh` -/
theorem new_reg_fresh {s1 s2 : State} {r : Reg} {i : StateIncr s1 s2}
    (h : newReg s1 = .OK r s2 i) : RegFresh r s1 := by
  cases h; exact Nat.lt_irrefl _

/-- `RTLgenspec.new_reg_not_in_map` -/
theorem new_reg_not_in_map {s1 s2 : State} {m : Mapping} {r : Reg} {i : StateIncr s1 s2}
    (h : newReg s1 = .OK r s2 i) (hm : MapValid m s1) : ¬ RegInMap m r :=
  fun hr => new_reg_fresh h (hm r hr)

/-! ## Properties of operations over compilation environments -/

/-- `RTLgenspec.init_mapping_valid` -/
theorem init_mapping_valid (s : State) : MapValid initMapping s := by
  intro r hr
  rcases hr with ⟨id, h⟩ | h
  · simp [initMapping] at h
  · simp [initMapping] at h

/-- `RTLgenspec.find_var_in_map` -/
theorem find_var_in_map {s1 s2 : State} {map : Mapping} {name : Ident} {r : Reg}
    {i : StateIncr s1 s2} (h : findVar map name s1 = .OK r s2 i) : RegInMap map r := by
  unfold findVar at h
  rcases hr : map.map_vars.get name with _ | r'
  · rw [hr] at h; cases h
  · rw [hr] at h; cases h; exact .inl ⟨name, hr⟩

theorem find_var_inv {s1 s2 : State} {map : Mapping} {name : Ident} {r : Reg}
    {i : StateIncr s1 s2} (h : findVar map name s1 = .OK r s2 i) :
    map.map_vars.get name = some r ∧ s1 = s2 := by
  unfold findVar at h
  rcases hr : map.map_vars.get name with _ | r'
  · rw [hr] at h; cases h
  · rw [hr] at h; cases h; exact ⟨rfl, rfl⟩

/-- `RTLgenspec.find_var_valid` -/
theorem find_var_valid {s1 s2 : State} {map : Mapping} {name : Ident} {r : Reg}
    {i : StateIncr s1 s2} (h : findVar map name s1 = .OK r s2 i) (hm : MapValid map s1) :
    RegValid r s1 := hm r (find_var_in_map h)

theorem find_letvar_inv {s1 s2 : State} {map : Mapping} {idx : Nat} {r : Reg}
    {i : StateIncr s1 s2} (h : findLetvar map idx s1 = .OK r s2 i) :
    map.map_letvars[idx]? = some r ∧ s1 = s2 := by
  unfold findLetvar at h
  rcases hr : map.map_letvars[idx]? with _ | r'
  · rw [hr] at h; cases h
  · rw [hr] at h; cases h; exact ⟨rfl, rfl⟩

/-- `RTLgenspec.find_letvar_in_map` -/
theorem find_letvar_in_map {s1 s2 : State} {map : Mapping} {idx : Nat} {r : Reg}
    {i : StateIncr s1 s2} (h : findLetvar map idx s1 = .OK r s2 i) : RegInMap map r :=
  .inr (List.mem_of_getElem? (find_letvar_inv h).1)

/-- `RTLgenspec.find_letvar_valid` -/
theorem find_letvar_valid {s1 s2 : State} {map : Mapping} {idx : Nat} {r : Reg}
    {i : StateIncr s1 s2} (h : findLetvar map idx s1 = .OK r s2 i) (hm : MapValid map s1) :
    RegValid r s1 := hm r (find_letvar_in_map h)

theorem new_reg_inv {s1 s2 : State} {r : Reg} {i : StateIncr s1 s2}
    (h : newReg s1 = .OK r s2 i) : r = s1.st_nextreg ∧ s2.st_nextreg = s1.st_nextreg.succ := by
  cases h; exact ⟨rfl, rfl⟩

theorem add_var_inv {s1 s2 : State} {map1 map2 : Mapping} {name : Ident} {r : Reg}
    {i : StateIncr s1 s2} (h : addVar map1 name s1 = .OK (r, map2) s2 i) :
    ∃ i', newReg s1 = .OK r s2 i' ∧ map2 = ⟨map1.map_vars.set name r, map1.map_letvars⟩ := by
  unfold addVar at h
  obtain ⟨x, s, i1, i2, h1, h2⟩ := bind_inv h
  cases h2
  exact ⟨i1, h1, rfl⟩

/-- `RTLgenspec.add_var_valid` -/
theorem add_var_valid {s1 s2 : State} {map1 map2 : Mapping} {name : Ident} {r : Reg}
    {i : StateIncr s1 s2} (h : addVar map1 name s1 = .OK (r, map2) s2 i)
    (hm : MapValid map1 s1) : RegValid r s2 ∧ MapValid map2 s2 := by
  obtain ⟨i', h1, rfl⟩ := add_var_inv h
  refine ⟨new_reg_valid h1, ?_⟩
  intro r' hr
  rcases hr with ⟨id, A⟩ | B
  · simp only at A
    rw [PTree.gsspec] at A
    split at A
    · cases A; exact new_reg_valid h1
    · exact reg_valid_incr i' (hm r' (.inl ⟨id, A⟩))
  · exact reg_valid_incr i' (hm r' (.inr B))

/-- `RTLgenspec.add_var_find` -/
theorem add_var_find {s1 s2 : State} {map map' : Mapping} {name : Ident} {r : Reg}
    {i : StateIncr s1 s2} (h : addVar map name s1 = .OK (r, map') s2 i) :
    map'.map_vars.get name = some r := by
  obtain ⟨_, _, rfl⟩ := add_var_inv h
  exact PTree.gss _ _ _

/-- `RTLgenspec.add_vars_valid` -/
theorem add_vars_valid :
    ∀ (namel : List Ident) {s1 s2 : State} {map1 map2 : Mapping} {rl : List Reg}
      {i : StateIncr s1 s2}, addVars map1 namel s1 = .OK (rl, map2) s2 i →
      MapValid map1 s1 → RegsValid rl s2 ∧ MapValid map2 s2
  | [], _, _, _, _, _, _, h, hm => by
    cases h; exact ⟨regs_valid_nil _, hm⟩
  | n1 :: nl, _, _, _, _, _, _, h, hm => by
    unfold addVars at h
    obtain ⟨rl1, map1', s, i1, i2, h1, h⟩ := bind2_inv h
    obtain ⟨r1, map2', s', i3, i4, h2, h⟩ := bind2_inv h
    cases h
    obtain ⟨A, B⟩ := add_vars_valid nl h1 hm
    obtain ⟨C, D⟩ := add_var_valid h2 B
    exact ⟨regs_valid_cons C (regs_valid_incr i3 A), D⟩

/-- `RTLgenspec.add_var_letenv` -/
theorem add_var_letenv {s1 s2 : State} {map1 map2 : Mapping} {id : Ident} {r : Reg}
    {i : StateIncr s1 s2} (h : addVar map1 id s1 = .OK (r, map2) s2 i) :
    map2.map_letvars = map1.map_letvars := by
  obtain ⟨_, _, rfl⟩ := add_var_inv h; rfl

/-- `RTLgenspec.add_vars_letenv` -/
theorem add_vars_letenv :
    ∀ (il : List Ident) {s1 s2 : State} {map1 map2 : Mapping} {rl : List Reg}
      {i : StateIncr s1 s2}, addVars map1 il s1 = .OK (rl, map2) s2 i →
      map2.map_letvars = map1.map_letvars
  | [], _, _, _, _, _, _, h => by cases h; rfl
  | n1 :: nl, _, _, _, _, _, _, h => by
    unfold addVars at h
    obtain ⟨rl1, map1', s, i1, i2, h1, h⟩ := bind2_inv h
    obtain ⟨r1, map2', s', i3, i4, h2, h⟩ := bind2_inv h
    cases h
    exact (add_var_letenv h2).trans (add_vars_letenv nl h1)

/-- `RTLgenspec.add_letvar_valid` -/
theorem add_letvar_valid {map : Mapping} {s : State} {r : Reg} (hm : MapValid map s)
    (hr : RegValid r s) : MapValid (addLetvar map r) s := by
  intro r' h
  rcases h with ⟨id, A⟩ | B
  · exact hm r' (.inl ⟨id, A⟩)
  · cases B with
    | head => exact hr
    | tail _ B => exact hm r' (.inr B)

/-! ## Properties of `alloc_reg` and `alloc_regs` -/

/-- `RTLgenspec.alloc_reg_valid` -/
theorem alloc_reg_valid {a : CminorSel.Expr} {s1 s2 : State} {map : Mapping} {r : Reg}
    {i : StateIncr s1 s2} (hm : MapValid map s1) (h : allocReg map a s1 = .OK r s2 i) :
    RegValid r s2 := by
  unfold allocReg at h
  split at h
  · obtain ⟨_, rfl⟩ := find_var_inv h; exact find_var_valid h hm
  · obtain ⟨_, rfl⟩ := find_letvar_inv h; exact find_letvar_valid h hm
  · exact new_reg_valid h

/-- `RTLgenspec.alloc_reg_fresh_or_in_map` -/
theorem alloc_reg_fresh_or_in_map {map : Mapping} {a : CminorSel.Expr} {s s' : State} {r : Reg}
    {i : StateIncr s s'} (h : allocReg map a s = .OK r s' i) :
    RegInMap map r ∨ RegFresh r s := by
  unfold allocReg at h
  split at h
  · exact .inl (find_var_in_map h)
  · exact .inl (find_letvar_in_map h)
  · exact .inr (new_reg_fresh h)

/-- `RTLgenspec.alloc_regs_valid` -/
theorem alloc_regs_valid :
    ∀ (al : Exprlist) {s1 s2 : State} {map : Mapping} {rl : List Reg} {i : StateIncr s1 s2},
    MapValid map s1 → allocRegs map al s1 = .OK rl s2 i → RegsValid rl s2
  | .Enil, _, _, _, _, _, _, h => by cases h; exact regs_valid_nil _
  | .Econs a bl, _, _, _, _, _, hm, h => by
    unfold allocRegs at h
    obtain ⟨r, s, i1, i2, h1, h⟩ := bind_inv h
    obtain ⟨rl, s', i3, i4, h2, h⟩ := bind_inv h
    cases h
    exact regs_valid_cons (reg_valid_incr i3 (alloc_reg_valid hm h1))
      (alloc_regs_valid bl (map_valid_incr i1 hm) h2)

/-- `RTLgenspec.alloc_regs_fresh_or_in_map` -/
theorem alloc_regs_fresh_or_in_map :
    ∀ (al : Exprlist) {map : Mapping} {s s' : State} {rl : List Reg} {i : StateIncr s s'},
    allocRegs map al s = .OK rl s' i → ∀ r, r ∈ rl → RegInMap map r ∨ RegFresh r s
  | .Enil, _, _, _, _, _, h => by cases h; intro r hr; cases hr
  | .Econs a bl, _, _, _, _, _, h => by
    unfold allocRegs at h
    obtain ⟨r1, s, i1, i2, h1, h⟩ := bind_inv h
    obtain ⟨rl, s', i3, i4, h2, h⟩ := bind_inv h
    cases h
    intro r hr
    cases hr with
    | head => exact alloc_reg_fresh_or_in_map h1
    | tail _ hr =>
      rcases alloc_regs_fresh_or_in_map bl h2 r hr with A | B
      · exact .inl A
      · exact .inr (reg_fresh_decr i1 B)

/-- `RTLgenspec.alloc_optreg_valid` -/
theorem alloc_optreg_valid {dest : Option Ident} {s1 s2 : State} {map : Mapping} {r : Reg}
    {i : StateIncr s1 s2} (hm : MapValid map s1) (h : allocOptreg map dest s1 = .OK r s2 i) :
    RegValid r s2 := by
  unfold allocOptreg at h
  split at h
  · obtain ⟨_, rfl⟩ := find_var_inv h; exact find_var_valid h hm
  · exact new_reg_valid h

/-- `RTLgenspec.alloc_optreg_fresh_or_in_map` -/
theorem alloc_optreg_fresh_or_in_map {map : Mapping} {dest : Option Ident} {s s' : State}
    {r : Reg} {i : StateIncr s s'} (h : allocOptreg map dest s = .OK r s' i) :
    RegInMap map r ∨ RegFresh r s := by
  unfold allocOptreg at h
  split at h
  · exact .inl (find_var_in_map h)
  · exact .inr (new_reg_fresh h)

/-! ## Target registers -/

/-- `RTLgenspec.target_reg_ok` -/
inductive TargetRegOk (map : Mapping) (pr : List Reg) : CminorSel.Expr → Reg → Prop where
  | var (id r) : map.map_vars.get id = some r → TargetRegOk map pr (.Evar id) r
  | letvar (idx r) : map.map_letvars[idx]? = some r → TargetRegOk map pr (.Eletvar idx) r
  | other (a r) : ¬ RegInMap map r → r ∉ pr → TargetRegOk map pr a r

/-- `RTLgenspec.target_regs_ok` -/
inductive TargetRegsOk (map : Mapping) : List Reg → Exprlist → List Reg → Prop where
  | nil (pr) : TargetRegsOk map pr .Enil []
  | cons (pr a1 al r1 rl) : TargetRegOk map pr a1 r1 → TargetRegsOk map (r1 :: pr) al rl →
      TargetRegsOk map pr (.Econs a1 al) (r1 :: rl)

/-- `RTLgenspec.target_reg_ok_append` -/
theorem target_reg_ok_append {map : Mapping} {pr : List Reg} {a : CminorSel.Expr} {r : Reg}
    (h : TargetRegOk map pr a r) (pr' : List Reg)
    (hpr : ∀ r', r' ∈ pr' → RegInMap map r' ∨ r' ≠ r) : TargetRegOk map (pr' ++ pr) a r := by
  cases h with
  | var id r h => exact .var _ _ h
  | letvar idx r h => exact .letvar _ _ h
  | other a r h1 h2 =>
    refine .other _ _ h1 ?_
    intro hin
    rcases List.mem_append.mp hin with A | B
    · rcases hpr r A with C | C
      · exact h1 C
      · exact C rfl
    · exact h2 B

/-- `RTLgenspec.target_reg_ok_cons` -/
theorem target_reg_ok_cons {map : Mapping} {pr : List Reg} {a : CminorSel.Expr} {r : Reg}
    (h : TargetRegOk map pr a r) (r' : Reg) (hr : RegInMap map r' ∨ r' ≠ r) :
    TargetRegOk map (r' :: pr) a r :=
  target_reg_ok_append h [r'] (fun r'' hin => by
    cases hin with
    | head => exact hr
    | tail _ h => cases h)

/-- `RTLgenspec.new_reg_target_ok` -/
theorem new_reg_target_ok {map : Mapping} {pr : List Reg} {s1 s2 : State} {a : CminorSel.Expr}
    {r : Reg} {i : StateIncr s1 s2} (hm : MapValid map s1) (hpr : RegsValid pr s1)
    (h : newReg s1 = .OK r s2 i) : TargetRegOk map pr a r :=
  .other _ _ (fun hin => new_reg_fresh h (hm r hin)) (fun hin => new_reg_fresh h (hpr r hin))

/-- `RTLgenspec.alloc_reg_target_ok` -/
theorem alloc_reg_target_ok {map : Mapping} {pr : List Reg} {s1 s2 : State}
    {a : CminorSel.Expr} {r : Reg} {i : StateIncr s1 s2} (hm : MapValid map s1)
    (hpr : RegsValid pr s1) (h : allocReg map a s1 = .OK r s2 i) : TargetRegOk map pr a r := by
  unfold allocReg at h
  split at h
  · exact .var _ _ (find_var_inv h).1
  · exact .letvar _ _ (find_letvar_inv h).1
  · exact new_reg_target_ok hm hpr h

/-- `RTLgenspec.alloc_regs_target_ok` -/
theorem alloc_regs_target_ok :
    ∀ (al : Exprlist) {map : Mapping} {pr : List Reg} {s1 s2 : State} {rl : List Reg}
      {i : StateIncr s1 s2}, MapValid map s1 → RegsValid pr s1 →
      allocRegs map al s1 = .OK rl s2 i → TargetRegsOk map pr al rl
  | .Enil, _, _, _, _, _, _, _, _, h => by cases h; exact .nil _
  | .Econs a bl, _, _, _, _, _, _, hm, hpr, h => by
    unfold allocRegs at h
    obtain ⟨r1, s, i1, i2, h1, h⟩ := bind_inv h
    obtain ⟨rl, s', i3, i4, h2, h⟩ := bind_inv h
    cases h
    exact .cons _ _ _ _ _ (alloc_reg_target_ok hm hpr h1)
      (alloc_regs_target_ok bl (map_valid_incr i1 hm)
        (regs_valid_cons (alloc_reg_valid hm h1) (regs_valid_incr i1 hpr)) h2)

/-! ## Return registers -/

/-- `RTLgenspec.return_reg_ok` -/
inductive ReturnRegOk : State → Mapping → Option Reg → Prop where
  | none (s map) : ReturnRegOk s map none
  | some (s map r) : ¬ RegInMap map r → RegValid r s → ReturnRegOk s map (some r)

/-- `RTLgenspec.return_reg_ok_incr` -/
theorem return_reg_ok_incr {s : State} {map : Mapping} {rret : Option Reg}
    (h : ReturnRegOk s map rret) {s' : State} (hi : StateIncr s s') : ReturnRegOk s' map rret := by
  cases h with
  | none => exact .none _ _
  | some _ h1 h2 => exact .some _ _ _ h1 (reg_valid_incr hi h2)

end RTLgen
end RiscV
end CC
