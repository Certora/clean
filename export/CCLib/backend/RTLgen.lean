/-
  Translation from CminorSel to RTL — port of `backend/RTLgen.v`
  (the state-and-error monad with its `state_incr` invariant, `add_instr`,
  `reserve_instr`, `update_instr`, `new_reg`, the compile-time mapping,
  `alloc_reg(s)`, `add_move`, `convert_builtin_arg(s)`/`_res`,
  `transl_expr`/`transl_exprlist`/`transl_condexpr`, `transl_exit`,
  `transl_jumptable`, `transl_exitexpr`, `transl_stmt`, `reserve_labels`,
  `transl_fun`, `transl_function`, `transl_fundef`, `transl_program`).

  Differences from Rocq:
  * The OCaml heuristic `more_likely` (a Rocq `Parameter`) is an explicit
    argument `moreLikely` of the statement translation.
  * The monad is the same dependent state-and-error monad as in Rocq (each
    successful result carries a proof of `state_incr`); it is not a Lean
    `Monad`, so the code uses `bind` explicitly.
  * Error messages are plain strings.
-/
import CCLib.backend.RTL
import CCLib.common.MemoryTheory

namespace CC
namespace RTLgen

open Op CminorSel RTL

theorem _root_.CC.Positive.lt_succ_self (p : Positive) : p < p.succ := by
  show p.toNat < p.succ.toNat; simp

theorem _root_.CC.Positive.le_succ_self (p : Positive) : p ≤ p.succ := by
  show p.toNat ≤ p.succ.toNat; simp

theorem _root_.CC.Positive.lt_succ_of_lt {p q : Positive} (h : p < q) : p < q.succ := by
  show p.toNat < q.succ.toNat; simp only [Positive.toNat_succ]; exact Nat.lt_succ_of_lt h

/-- `RTLgen.mapping` -/
structure Mapping where
  map_vars : PTree Reg
  map_letvars : List Reg

/-- `RTLgen.state` -/
structure State where
  st_nextreg : Positive
  st_nextnode : Positive
  st_code : Code
  st_wf : ∀ pc : Positive, pc < st_nextnode ∨ st_code.get pc = none

/-- `RTLgen.state_incr` -/
inductive StateIncr : State → State → Prop where
  | intro (s1 s2 : State) :
      s1.st_nextnode ≤ s2.st_nextnode →
      s1.st_nextreg ≤ s2.st_nextreg →
      (∀ pc, s1.st_code.get pc = none ∨ s2.st_code.get pc = s1.st_code.get pc) →
      StateIncr s1 s2

theorem stateIncr_refl (s : State) : StateIncr s s :=
  .intro s s (Nat.le_refl _) (Nat.le_refl _) (fun _ => .inr rfl)

theorem stateIncr_trans {s1 s2 s3 : State} (h1 : StateIncr s1 s2) (h2 : StateIncr s2 s3) :
    StateIncr s1 s3 := by
  cases h1 with
  | intro a1 b1 c1 =>
    cases h2 with
    | intro a2 b2 c2 =>
      refine .intro _ _ (Nat.le_trans a1 a2) (Nat.le_trans b1 b2) (fun pc => ?_)
      rcases c1 pc with h | h
      · exact .inl h
      · rcases c2 pc with h' | h'
        · exact .inl (h ▸ h')
        · exact .inr (h'.trans h)

/-- `RTLgen.res` -/
inductive Res (A : Type) (s : State) where
  | Error (msg : String)
  | OK (a : A) (s' : State) (i : StateIncr s s')

/-- `RTLgen.mon` -/
def Mon (A : Type) : Type := (s : State) → Res A s

/-- `RTLgen.ret` -/
def ret {A : Type} (x : A) : Mon A := fun s => .OK x s (stateIncr_refl s)

/-- `RTLgen.error` -/
def error {A : Type} (msg : String) : Mon A := fun _ => .Error msg

/-- `RTLgen.bind` -/
def bind {A B : Type} (f : Mon A) (g : A → Mon B) : Mon B := fun s =>
  match f s with
  | .Error msg => .Error msg
  | .OK a s' i =>
      match g a s' with
      | .Error msg => .Error msg
      | .OK b s'' i' => .OK b s'' (stateIncr_trans i i')

/-- `RTLgen.bind2` -/
def bind2 {A B C : Type} (f : Mon (A × B)) (g : A → B → Mon C) : Mon C :=
  bind f (fun xy => g xy.1 xy.2)

/-- `RTLgen.handle_error` -/
def handleError {A : Type} (f g : Mon A) : Mon A := fun s =>
  match f s with
  | .OK a s' i => .OK a s' i
  | .Error _ => g s

/-- `RTLgen.init_state` -/
def initState : State where
  st_nextreg := .xH
  st_nextnode := .xH
  st_code := PTree.empty
  st_wf := fun _ => .inr (PTree.gempty _)

private theorem addInstr_wf (s : State) (i : Instruction) (pc : Positive) :
    pc < s.st_nextnode.succ ∨ (s.st_code.set s.st_nextnode i).get pc = none := by
  by_cases h : pc = s.st_nextnode
  · subst h; left; exact Positive.lt_succ_self _
  · rw [PTree.gso _ _ _ _ (Ne.symm h)]
    rcases s.st_wf pc with h' | h'
    · left; exact Positive.lt_succ_of_lt h'
    · right; exact h'

private theorem addInstr_incr (s : State) (i : Instruction) :
    StateIncr s ⟨s.st_nextreg, s.st_nextnode.succ, s.st_code.set s.st_nextnode i,
      addInstr_wf s i⟩ := by
  refine .intro _ _ ?_ (Nat.le_refl _) (fun pc => ?_)
  · exact Positive.le_succ_self _
  · rcases s.st_wf pc with h | h
    · right
      show (s.st_code.set s.st_nextnode i).get pc = _
      rw [PTree.gso]
      intro he; subst he; exact Nat.lt_irrefl _ h
    · left; exact h

/-- `RTLgen.add_instr` -/
def addInstr (i : Instruction) : Mon Node := fun s =>
  .OK s.st_nextnode
    ⟨s.st_nextreg, s.st_nextnode.succ, s.st_code.set s.st_nextnode i, addInstr_wf s i⟩
    (addInstr_incr s i)

private theorem reserveInstr_wf (s : State) (pc : Positive) :
    pc < s.st_nextnode.succ ∨ s.st_code.get pc = none := by
  rcases s.st_wf pc with h | h
  · left; exact Positive.lt_succ_of_lt h
  · right; exact h

private theorem reserveInstr_incr (s : State) :
    StateIncr s ⟨s.st_nextreg, s.st_nextnode.succ, s.st_code, reserveInstr_wf s⟩ :=
  .intro _ _ (Positive.le_succ_self _) (Nat.le_refl _) (fun _ => .inr rfl)

/-- `RTLgen.reserve_instr` -/
def reserveInstr : Mon Node := fun s =>
  .OK s.st_nextnode ⟨s.st_nextreg, s.st_nextnode.succ, s.st_code, reserveInstr_wf s⟩
    (reserveInstr_incr s)

private theorem updateInstr_wf (s : State) (n : Node) (i : Instruction) (hlt : n < s.st_nextnode)
    (pc : Positive) : pc < s.st_nextnode ∨ (s.st_code.set n i).get pc = none := by
  by_cases h : pc = n
  · subst h; left; exact hlt
  · rw [PTree.gso _ _ _ _ (Ne.symm h)]; exact s.st_wf pc

private theorem updateInstr_incr (s : State) (n : Node) (i : Instruction) (hlt : n < s.st_nextnode)
    (hempty : s.st_code.get n = none) :
    StateIncr s ⟨s.st_nextreg, s.st_nextnode, s.st_code.set n i, updateInstr_wf s n i hlt⟩ := by
  refine .intro _ _ (Nat.le_refl _) (Nat.le_refl _) (fun pc => ?_)
  by_cases h : pc = n
  · subst h; left; exact hempty
  · right; show (s.st_code.set n i).get pc = _; rw [PTree.gso _ _ _ _ (Ne.symm h)]

/-- `RTLgen.update_instr` -/
def updateInstr (n : Node) (i : Instruction) : Mon Unit := fun s =>
  if hlt : n < s.st_nextnode then
    match hempty : s.st_code.get n with
    | none =>
        .OK () ⟨s.st_nextreg, s.st_nextnode, s.st_code.set n i, updateInstr_wf s n i hlt⟩
          (updateInstr_incr s n i hlt hempty)
    | some _ => .Error "RTLgen.update_instr"
  else .Error "RTLgen.update_instr"

private theorem newReg_incr (s : State) :
    StateIncr s ⟨s.st_nextreg.succ, s.st_nextnode, s.st_code, s.st_wf⟩ :=
  .intro _ _ (Nat.le_refl _) (Positive.le_succ_self _) (fun _ => .inr rfl)

/-- `RTLgen.new_reg` -/
def newReg : Mon Reg := fun s =>
  .OK s.st_nextreg ⟨s.st_nextreg.succ, s.st_nextnode, s.st_code, s.st_wf⟩ (newReg_incr s)

/-- `RTLgen.init_mapping` -/
def initMapping : Mapping := ⟨PTree.empty, []⟩

/-- `RTLgen.add_var` -/
def addVar (map : Mapping) (name : Ident) : Mon (Reg × Mapping) :=
  bind newReg fun r => ret (r, ⟨map.map_vars.set name r, map.map_letvars⟩)

/-- `RTLgen.add_vars` -/
def addVars (map : Mapping) : List Ident → Mon (List Reg × Mapping)
  | [] => ret ([], map)
  | n1 :: nl =>
      bind2 (addVars map nl) fun rl map1 =>
      bind2 (addVar map1 n1) fun r1 map2 =>
      ret (r1 :: rl, map2)

/-- `RTLgen.find_var` -/
def findVar (map : Mapping) (name : Ident) : Mon Reg :=
  match map.map_vars.get name with
  | none => error s!"RTLgen: unbound variable {name.toNat}"
  | some r => ret r

/-- `RTLgen.add_letvar` -/
def addLetvar (map : Mapping) (r : Reg) : Mapping := ⟨map.map_vars, r :: map.map_letvars⟩

/-- `RTLgen.find_letvar` -/
def findLetvar (map : Mapping) (idx : Nat) : Mon Reg :=
  match map.map_letvars[idx]? with
  | none => error "RTLgen: unbound let variable"
  | some r => ret r

/-- `RTLgen.alloc_reg` -/
def allocReg (map : Mapping) (a : CminorSel.Expr) : Mon Reg :=
  match a with
  | .Evar id => findVar map id
  | .Eletvar n => findLetvar map n
  | _ => newReg

/-- `RTLgen.alloc_regs` -/
def allocRegs (map : Mapping) : Exprlist → Mon (List Reg)
  | .Enil => ret []
  | .Econs a bl =>
      bind (allocReg map a) fun r =>
      bind (allocRegs map bl) fun rl =>
      ret (r :: rl)

/-- `RTLgen.alloc_optreg` -/
def allocOptreg (map : Mapping) (dest : Option Ident) : Mon Reg :=
  match dest with
  | some id => findVar map id
  | none => newReg

/-- `RTLgen.add_move` -/
def addMove (rs rd : Reg) (nd : Node) : Mon Node :=
  if rs = rd then ret nd else addInstr (.Iop .Omove [rs] rd nd)

/-- `RTLgen.exprlist_of_expr_list` -/
def exprlistOfExprList (l : List CminorSel.Expr) : Exprlist := l.foldr .Econs .Enil

/-- `RTLgen.convert_builtin_arg` -/
def convertBuiltinArg {A : Type} : BuiltinArg CminorSel.Expr → List A → BuiltinArg A × List A
  | .BA _, rl =>
      match rl with
      | r :: rs => (.BA r, rs)
      | [] => (.BA_int Integers.Int.zero, [])
  | .BA_int n, rl => (.BA_int n, rl)
  | .BA_long n, rl => (.BA_long n, rl)
  | .BA_float n, rl => (.BA_float n, rl)
  | .BA_single n, rl => (.BA_single n, rl)
  | .BA_loadstack chunk ofs, rl => (.BA_loadstack chunk ofs, rl)
  | .BA_addrstack ofs, rl => (.BA_addrstack ofs, rl)
  | .BA_loadglobal chunk id ofs, rl => (.BA_loadglobal chunk id ofs, rl)
  | .BA_addrglobal id ofs, rl => (.BA_addrglobal id ofs, rl)
  | .BA_splitlong hi lo, rl =>
      let (hi', rl1) := convertBuiltinArg hi rl
      let (lo', rl2) := convertBuiltinArg lo rl1
      (.BA_splitlong hi' lo', rl2)
  | .BA_addptr a1 a2, rl =>
      let (a1', rl1) := convertBuiltinArg a1 rl
      let (a2', rl2) := convertBuiltinArg a2 rl1
      (.BA_addptr a1' a2', rl2)

/-- `RTLgen.convert_builtin_args` -/
def convertBuiltinArgs {A : Type} : List (BuiltinArg CminorSel.Expr) → List A → List (BuiltinArg A)
  | [], _ => []
  | a1 :: al, rl =>
      let (a1', rl1) := convertBuiltinArg a1 rl
      a1' :: convertBuiltinArgs al rl1

/-- `RTLgen.convert_builtin_res` -/
def convertBuiltinRes (map : Mapping) (ty : XType) (r : BuiltinRes Ident) : Mon (BuiltinRes Reg) :=
  match r with
  | .BR id => bind (findVar map id) fun r => ret (.BR r)
  | .BR_none => if ty = .Xvoid then ret .BR_none else bind newReg fun r => ret (.BR r)
  | _ => error "RTLgen: bad builtin_res"

mutual
/-- `RTLgen.transl_expr` -/
def translExpr (map : Mapping) (a : CminorSel.Expr) (rd : Reg) (nd : Node) : Mon Node :=
  match a with
  | .Evar v => bind (findVar map v) fun r => addMove r rd nd
  | .Eop op al =>
      bind (allocRegs map al) fun rl =>
      bind (addInstr (.Iop op rl rd nd)) fun no =>
      translExprlist map al rl no
  | .Eload chunk addr al =>
      bind (allocRegs map al) fun rl =>
      bind (addInstr (.Iload chunk addr rl rd nd)) fun no =>
      translExprlist map al rl no
  | .Econdition a b c =>
      bind (translExpr map c rd nd) fun nfalse =>
      bind (translExpr map b rd nd) fun ntrue =>
      translCondexpr map a ntrue nfalse
  | .Elet b c =>
      bind newReg fun r =>
      bind (translExpr (addLetvar map r) c rd nd) fun nc =>
      translExpr map b r nc
  | .Eletvar n => bind (findLetvar map n) fun r => addMove r rd nd
  | .Ebuiltin ef al =>
      bind (allocRegs map al) fun rl =>
      bind (addInstr (.Ibuiltin ef (rl.map .BA) (.BR rd) nd)) fun no =>
      translExprlist map al rl no
  | .Eexternal id sg al =>
      bind (allocRegs map al) fun rl =>
      bind (addInstr (.Icall sg (.inr id) rl rd nd)) fun no =>
      translExprlist map al rl no

/-- `RTLgen.transl_exprlist` -/
def translExprlist (map : Mapping) (al : Exprlist) (rl : List Reg) (nd : Node) : Mon Node :=
  match al, rl with
  | .Enil, [] => ret nd
  | .Econs b bs, r :: rs => bind (translExprlist map bs rs nd) fun no => translExpr map b r no
  | _, _ => error "RTLgen.transl_exprlist"

/-- `RTLgen.transl_condexpr` -/
def translCondexpr (map : Mapping) (a : Condexpr) (ntrue nfalse : Node) : Mon Node :=
  match a with
  | .CEcond c al =>
      bind (allocRegs map al) fun rl =>
      bind (addInstr (.Icond c rl ntrue nfalse)) fun nt =>
      translExprlist map al rl nt
  | .CEcondition a b c =>
      bind (translCondexpr map c ntrue nfalse) fun nc =>
      bind (translCondexpr map b ntrue nfalse) fun nb =>
      translCondexpr map a nb nc
  | .CElet b c =>
      bind newReg fun r =>
      bind (translCondexpr (addLetvar map r) c ntrue nfalse) fun nc =>
      translExpr map b r nc
end

/-- `RTLgen.transl_exit` -/
def translExit (nexits : List Node) (n : Nat) : Mon Node :=
  match nexits[n]? with
  | none => error "RTLgen: wrong exit"
  | some ne => ret ne

/-- `RTLgen.transl_jumptable` -/
def translJumptable (nexits : List Node) : List Nat → Mon (List Node)
  | [] => ret []
  | t1 :: tl =>
      bind (translExit nexits t1) fun n1 =>
      bind (translJumptable nexits tl) fun nl =>
      ret (n1 :: nl)

/-- `RTLgen.transl_exitexpr` -/
def translExitexpr (map : Mapping) (a : Exitexpr) (nexits : List Node) : Mon Node :=
  match a with
  | .XEexit n => translExit nexits n
  | .XEjumptable a tbl =>
      bind (allocReg map a) fun r =>
      bind (translJumptable nexits tbl) fun tbl' =>
      bind (addInstr (.Ijumptable r tbl')) fun n1 =>
      translExpr map a r n1
  | .XEcondition a b c =>
      bind (translExitexpr map c nexits) fun nc =>
      bind (translExitexpr map b nexits) fun nb =>
      translCondexpr map a nb nc
  | .XElet a b =>
      bind newReg fun r =>
      bind (translExitexpr (addLetvar map r) b nexits) fun n1 =>
      translExpr map a r n1

/-- `RTLgen.labelmap` -/
abbrev Labelmap := PTree Node

/-- `RTLgen.transl_stmt` -/
def translStmt (moreLikely : Condexpr → CminorSel.Stmt → CminorSel.Stmt → Bool) (map : Mapping) (s : CminorSel.Stmt)
    (nd : Node) (nexits : List Node) (ngoto : Labelmap) (nret : Node) (rret : Option Reg) :
    Mon Node :=
  match s with
  | .Sskip => ret nd
  | .Sassign v b => bind (findVar map v) fun r => translExpr map b r nd
  | .Sstore chunk addr al b =>
      bind (allocRegs map al) fun rl =>
      bind (allocReg map b) fun r =>
      bind (addInstr (.Istore chunk addr rl r nd)) fun no =>
      bind (translExpr map b r no) fun ns =>
      translExprlist map al rl ns
  | .Scall optid sig (.inl b) cl =>
      bind (allocReg map b) fun rf =>
      bind (allocRegs map cl) fun rargs =>
      bind (allocOptreg map optid) fun r =>
      bind (addInstr (.Icall sig (.inl rf) rargs r nd)) fun n1 =>
      bind (translExprlist map cl rargs n1) fun n2 =>
      translExpr map b rf n2
  | .Scall optid sig (.inr id) cl =>
      bind (allocRegs map cl) fun rargs =>
      bind (allocOptreg map optid) fun r =>
      bind (addInstr (.Icall sig (.inr id) rargs r nd)) fun n1 =>
      translExprlist map cl rargs n1
  | .Stailcall sig (.inl b) cl =>
      bind (allocReg map b) fun rf =>
      bind (allocRegs map cl) fun rargs =>
      bind (addInstr (.Itailcall sig (.inl rf) rargs)) fun n1 =>
      bind (translExprlist map cl rargs n1) fun n2 =>
      translExpr map b rf n2
  | .Stailcall sig (.inr id) cl =>
      bind (allocRegs map cl) fun rargs =>
      bind (addInstr (.Itailcall sig (.inr id) rargs)) fun n1 =>
      translExprlist map cl rargs n1
  | .Sbuiltin res ef args =>
      let al := exprlistOfExprList (BuiltinArg.paramsList args)
      bind (allocRegs map al) fun rargs =>
      let args' := convertBuiltinArgs args rargs
      bind (convertBuiltinRes map ef.sig.sig_res res) fun res' =>
      bind (addInstr (.Ibuiltin ef args' res' nd)) fun n1 =>
      translExprlist map al rargs n1
  | .Sseq s1 s2 =>
      bind (translStmt moreLikely map s2 nd nexits ngoto nret rret) fun ns =>
      translStmt moreLikely map s1 ns nexits ngoto nret rret
  | .Sifthenelse c strue sfalse =>
      if moreLikely c strue sfalse then
        bind (translStmt moreLikely map sfalse nd nexits ngoto nret rret) fun nfalse =>
        bind (translStmt moreLikely map strue nd nexits ngoto nret rret) fun ntrue =>
        translCondexpr map c ntrue nfalse
      else
        bind (translStmt moreLikely map strue nd nexits ngoto nret rret) fun ntrue =>
        bind (translStmt moreLikely map sfalse nd nexits ngoto nret rret) fun nfalse =>
        translCondexpr map c ntrue nfalse
  | .Sloop sbody =>
      bind reserveInstr fun n1 =>
      bind (translStmt moreLikely map sbody n1 nexits ngoto nret rret) fun n2 =>
      bind (updateInstr n1 (.Inop n2)) fun _ =>
      addInstr (.Inop n2)
  | .Sblock sbody => translStmt moreLikely map sbody nd (nd :: nexits) ngoto nret rret
  | .Sexit n => translExit nexits n
  | .Sswitch a => translExitexpr map a nexits
  | .Sreturn opt_a =>
      match opt_a, rret with
      | none, _ => ret nret
      | some a, some r => translExpr map a r nret
      | _, _ => error "RTLgen: type mismatch on return"
  | .Slabel lbl s' =>
      bind (translStmt moreLikely map s' nd nexits ngoto nret rret) fun ns =>
      match ngoto.get lbl with
      | none => error "RTLgen: unbound label"
      | some n =>
          bind (handleError (updateInstr n (.Inop ns))
                  (error s!"Multiply-defined label {lbl.toNat}")) fun _ =>
          ret ns
  | .Sgoto lbl =>
      match ngoto.get lbl with
      | none => error s!"Undefined defined label {lbl.toNat}"
      | some n => ret n

/-- `RTLgen.alloc_label` -/
def allocLabel (lbl : Cminor.Label) (map : Labelmap) : Mon Labelmap :=
  bind reserveInstr fun n => ret (map.set lbl n)

/-- `RTLgen.reserve_labels` -/
def reserveLabels : CminorSel.Stmt → Labelmap → Mon Labelmap
  | .Sseq s1 s2, lm | .Sifthenelse _ s1 s2, lm =>
      bind (reserveLabels s2 lm) fun lm' => reserveLabels s1 lm'
  | .Sloop s1, lm | .Sblock s1, lm => reserveLabels s1 lm
  | .Slabel lbl s1, lm => bind (reserveLabels s1 lm) fun lm' => allocLabel lbl lm'
  | _, lm => ret lm

/-- `RTLgen.ret_reg` -/
def retReg (sig : Signature) (rd : Reg) : Option Reg :=
  if sig.sig_res = .Xvoid then none else some rd

/-- `RTLgen.transl_fun` -/
def translFun (moreLikely : Condexpr → CminorSel.Stmt → CminorSel.Stmt → Bool) (f : CminorSel.Function) :
    Mon (Node × List Reg) :=
  bind (reserveLabels f.fn_body PTree.empty) fun ngoto =>
  bind2 (addVars initMapping f.fn_params) fun rparams map1 =>
  bind2 (addVars map1 f.fn_vars) fun _ map2 =>
  bind newReg fun rret =>
  let orret := retReg f.fn_sig rret
  bind (addInstr (.Ireturn orret)) fun nret =>
  bind (translStmt moreLikely map2 f.fn_body nret [] ngoto nret orret) fun nentry =>
  ret (nentry, rparams)

/-- `RTLgen.transl_function` -/
def translFunction (moreLikely : Condexpr → CminorSel.Stmt → CminorSel.Stmt → Bool) (f : CminorSel.Function) :
    CC.Res RTL.Function :=
  match translFun moreLikely f initState with
  | .Error msg => .Error msg
  | .OK (nentry, rparams) s _ =>
      .OK { fn_sig := f.fn_sig, fn_params := rparams, fn_stacksize := f.fn_stackspace,
            fn_code := s.st_code, fn_entrypoint := nentry }

/-- `RTLgen.transl_fundef` -/
def translFundef (moreLikely : Condexpr → CminorSel.Stmt → CminorSel.Stmt → Bool) :
    CminorSel.Fundef → CC.Res RTL.Fundef :=
  ASTFundef.transfPartial (translFunction moreLikely)

/-- `RTLgen.transl_program` -/
def translProgram (moreLikely : Condexpr → CminorSel.Stmt → CminorSel.Stmt → Bool) (p : CminorSel.Program) :
    CC.Res RTL.Program :=
  transformPartialProgram (translFundef moreLikely) p

end RTLgen
end CC
