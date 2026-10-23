/-
  [RISC-V instance of `CCLib/backend/Debugvar.lean`: the same development, in
  namespace `CC.RiscV`, over the RISC-V operators, registers and conventions.]

  Live ranges of local variables carrying debug information — port of
  `backend/Debugvar.v` (a Linear → Linear pass), whole file:
  `safe_builtin_arg`, `debuginfo`, `normalize_debug_1`, `normalize_debug`,
  `avail`, `set_state`, `remove_state`, `set_debug_info`, `arg_no_overlap`,
  `kill`, `kill_res`, `arg_preserved`, `kill_at_call`, `eq_arg`,
  `eq_debuginfo`, `join`, `eq_state`, `top`, `labelmap`, `get_label`,
  `update_label(s)`, `is_debug_setvar`, `is_builtin_debug_setvar`,
  `transfer`, `ana_code`, `ana_iter`, `ana_function`, `diff`,
  `delta_state`, `add_start_range`, `add_end_range`, `add_delta_ranges`,
  `skip_debug_setvar`, `transf_code`, `transf_function`, `transf_fundef`,
  `transf_program`.

  Differences from Rocq: `eq_arg`, `eq_debuginfo`, `eq_state` are derived
  `DecidableEq` instances; the nested `fix join2` / `fix diff2` are
  separate structurally recursive functions `join2` / `diff2`, which take
  the outer recursive call as an argument;
  `Pos.compare` compares the `Nat` values of the identifiers.
-/
import CCLib.riscV.Linear
import CCLib.backend.Kildall

namespace CC
namespace RiscV


namespace Debugvar

open Linear Conventions1

/-- `Debugvar.safe_builtin_arg` -/
def SafeBuiltinArg {A : Type} : BuiltinArg A → Prop
  | .BA _ | .BA_int _ | .BA_long _ | .BA_float _ | .BA_single _ => True
  | .BA_splitlong hi lo => SafeBuiltinArg hi ∧ SafeBuiltinArg lo
  | _ => False

/-- `Debugvar.debuginfo` -/
abbrev Debuginfo := { a : BuiltinArg Loc // SafeBuiltinArg a }

/-- `Debugvar.normalize_debug_1` -/
def normalizeDebug1 (a : BuiltinArg Loc) : Option Debuginfo :=
  match a with
  | .BA x => some ⟨.BA x, trivial⟩
  | .BA_int n => some ⟨.BA_int n, trivial⟩
  | .BA_long n => some ⟨.BA_long n, trivial⟩
  | .BA_float n => some ⟨.BA_float n, trivial⟩
  | .BA_single n => some ⟨.BA_single n, trivial⟩
  | .BA_splitlong (.BA hi) (.BA lo) => some ⟨.BA_splitlong (.BA hi) (.BA lo), ⟨trivial, trivial⟩⟩
  | _ => none

/-- `Debugvar.normalize_debug` -/
def normalizeDebug : List (BuiltinArg Loc) → Option Debuginfo
  | [] => none
  | a :: l' =>
      match a with
      | .BA_int _ | .BA_long _ | .BA_float _ | .BA_single _ =>
          match normalizeDebug l' with
          | some i => some i
          | none => normalizeDebug1 a
      | _ => normalizeDebug1 a

/-- `Debugvar.avail` -/
abbrev Avail := List (Ident × Debuginfo)

/-- `Pos.compare` -/
def posCompare (p q : Positive) : Ordering := compare p.toNat q.toNat

/-- `Debugvar.set_state` -/
def setState (v : Ident) (i : Debuginfo) : Avail → Avail
  | [] => [(v, i)]
  | (v', i') :: s' =>
      match posCompare v v' with
      | .eq => (v, i) :: s'
      | .lt => (v, i) :: (v', i') :: s'
      | .gt => (v', i') :: setState v i s'

/-- `Debugvar.remove_state` -/
def removeState (v : Ident) : Avail → Avail
  | [] => []
  | (v', i') :: s' =>
      match posCompare v v' with
      | .eq => s'
      | .lt => (v', i') :: s'
      | .gt => (v', i') :: removeState v s'

/-- `Debugvar.set_debug_info` -/
def setDebugInfo (v : Ident) (info : List (BuiltinArg Loc)) (s : Avail) : Avail :=
  match normalizeDebug info with
  | some a => setState v a s
  | none => removeState v s

/-- `Debugvar.arg_no_overlap` -/
def argNoOverlap : BuiltinArg Loc → Loc → Bool
  | .BA l', l => decide (Loc.diff l' l)
  | .BA_splitlong hi lo, l => argNoOverlap hi l && argNoOverlap lo l
  | _, _ => true

/-- `Debugvar.kill` -/
def kill (l : Loc) (s : Avail) : Avail := s.filter (fun vi => argNoOverlap vi.2.1 l)

/-- `Debugvar.kill_res` -/
def killRes : BuiltinRes Mreg → Avail → Avail
  | .BR r, s => kill (.R r) s
  | .BR_none, s => s
  | .BR_splitlong hi lo, s => killRes hi (killRes lo s)

/-- `Debugvar.arg_preserved` -/
def argPreserved : BuiltinArg Loc → Bool
  | .BA (.R r) => !(Conventions1.destroyedAtCall.contains r)
  | .BA (.S _ _ _) => true
  | .BA_splitlong hi lo => argPreserved hi && argPreserved lo
  | _ => true

/-- `Debugvar.kill_at_call` -/
def killAtCall (s : Avail) : Avail := s.filter (fun vi => argPreserved vi.2.1)

/-- The inner loop `join2` of `Debugvar.join`, for a fixed head `(v1, i1)`;
    `rec` is `join s1'`. -/
def join2 (v1 : Ident) (i1 : Debuginfo) (rec : Avail → Avail) : Avail → Avail
  | [] => []
  | (v2, i2) :: s2' =>
      match posCompare v1 v2 with
      | .eq => if i1 = i2 then (v1, i1) :: rec s2' else rec s2'
      | .lt => rec ((v2, i2) :: s2')
      | .gt => join2 v1 i1 rec s2'

/-- `Debugvar.join` -/
def join : Avail → Avail → Avail
  | [] => fun _ => []
  | (v1, i1) :: s1' => join2 v1 i1 (join s1')

/-- `Debugvar.top` -/
def top : Avail := []

/-- `Debugvar.labelmap` -/
abbrev Labelmap := PTree Avail × Bool

/-- `Debugvar.get_label` -/
def getLabel (lbl : Label) (lm : Labelmap) : Option Avail := lm.1.get lbl

/-- `Debugvar.update_label` -/
def updateLabel (lbl : Label) (s1 : Avail) (lm : Labelmap) : Labelmap × Avail :=
  match getLabel lbl lm with
  | none => ((lm.1.set lbl s1, true), s1)
  | some s2 =>
      let s := join s1 s2
      if s = s2 then (lm, s2) else ((lm.1.set lbl s, true), s)

/-- `Debugvar.update_labels` -/
def updateLabels : List Label → Avail → Labelmap → Labelmap
  | [], _, lm => lm
  | lbl1 :: lbls, s, lm => updateLabels lbls s (updateLabel lbl1 s lm).1

/-- `Debugvar.is_debug_setvar` -/
def isDebugSetvar (ef : ExtFun) : Option Ident :=
  match ef with
  | .EF_debug k txt _ => if k = Positive.ofNat 2 then some txt else none
  | _ => none

/-- `Debugvar.is_builtin_debug_setvar` -/
def isBuiltinDebugSetvar (i : Instruction) : Option Ident :=
  match i with
  | .Lbuiltin ef _ .BR_none => isDebugSetvar ef
  | _ => none

/-- `Debugvar.transfer` -/
def transfer (lm : Labelmap) (before : Option Avail) (i : Instruction) : Labelmap × Option Avail :=
  match before with
  | none =>
      match i with
      | .Llabel lbl => (lm, getLabel lbl lm)
      | _ => (lm, none)
  | some s =>
      match i with
      | .Lgetstack _ _ _ rd => (lm, some (kill (.R rd) s))
      | .Lsetstack _ sl ofs ty => (lm, some (kill (.S sl ofs ty) s))
      | .Lop _ _ dst => (lm, some (kill (.R dst) s))
      | .Lload _ _ _ dst => (lm, some (kill (.R dst) s))
      | .Lstore _ _ _ _ => (lm, before)
      | .Lcall _ _ => (lm, some (killAtCall s))
      | .Ltailcall _ _ => (lm, none)
      | .Lbuiltin ef args res =>
          let s' := match isDebugSetvar ef with
            | some v => setDebugInfo v args s
            | none => s
          (lm, some (killRes res s'))
      | .Llabel lbl =>
          let (lm1, s1) := updateLabel lbl s lm
          (lm1, some s1)
      | .Lgoto lbl =>
          let (lm1, _) := updateLabel lbl s lm
          (lm1, none)
      | .Lcond _ _ lbl =>
          let (lm1, _) := updateLabel lbl s lm
          (lm1, before)
      | .Ljumptable _ lbls => (updateLabels lbls s lm, none)
      | .Lreturn => (lm, none)

/-- `Debugvar.ana_code` -/
def anaCode (lm : Labelmap) (before : Option Avail) : Code → Labelmap
  | [] => lm
  | i :: c =>
      let (lm1, after) := transfer lm before i
      anaCode lm1 after c

/-- `Debugvar.ana_iter` -/
def anaIter (c : Code) (lm : Labelmap) : Labelmap ⊕ Labelmap :=
  let lm' := anaCode (lm.1, false) (some top) c
  if lm'.2 then .inr lm' else .inl lm

/-- `Debugvar.ana_function` -/
def anaFunction (f : Linear.Function) : Option Labelmap :=
  PrimIter.iterate (anaIter f.fn_code) (PTree.empty, false)

/-- The inner loop `diff2` of `Debugvar.diff`, for a fixed head `(v1, i1)`
    of `s1 = (v1, i1) :: s1'`; `rec` is `diff s1'`. -/
def diff2 (v1 : Ident) (i1 : Debuginfo) (s1' : Avail) (rec : Avail → Avail) : Avail → Avail
  | [] => (v1, i1) :: s1'
  | (v2, i2) :: s2' =>
      match posCompare v1 v2 with
      | .eq => if i1 = i2 then rec s2' else (v1, i1) :: rec s2'
      | .lt => (v1, i1) :: rec ((v2, i2) :: s2')
      | .gt => diff2 v1 i1 s1' rec s2'

/-- `Debugvar.diff` -/
def diff : Avail → Avail → Avail
  | [] => fun _ => []
  | (v1, i1) :: s1' => diff2 v1 i1 s1' (diff s1')

/-- `Debugvar.delta_state` -/
def deltaState (before after : Option Avail) : Avail × Avail :=
  match before, after with
  | none, none => ([], [])
  | some b, none => (b, [])
  | none, some a => ([], a)
  | some b, some a => (diff b a, diff a b)

/-- `Debugvar.add_start_range` -/
def addStartRange (vi : Ident × Debuginfo) (c : Code) : Code :=
  .Lbuiltin (.EF_debug (Positive.ofNat 3) vi.1 []) [vi.2.1] .BR_none :: c

/-- `Debugvar.add_end_range` -/
def addEndRange (vi : Ident × Debuginfo) (c : Code) : Code :=
  .Lbuiltin (.EF_debug (Positive.ofNat 4) vi.1 []) [] .BR_none :: c

/-- `Debugvar.add_delta_ranges` -/
def addDeltaRanges (before after : Option Avail) (c : Code) : Code :=
  let (killed, born) := deltaState before after
  killed.foldr addEndRange (born.foldr addStartRange c)

/-- `Debugvar.skip_debug_setvar` -/
def skipDebugSetvar (lm : Labelmap) (before : Option Avail) : Code → Option Avail
  | [] => before
  | i :: c' =>
      match isBuiltinDebugSetvar i with
      | some _ => skipDebugSetvar lm (transfer lm before i).2 c'
      | none => before

/-- `Debugvar.transf_code` -/
def transfCode (lm : Labelmap) (before : Option Avail) : Code → Code
  | [] => []
  | .Lgoto lbl1 :: .Llabel lbl2 :: c' =>
      let after := getLabel lbl2 lm
      .Lgoto lbl1 :: .Llabel lbl2 :: addDeltaRanges before after (transfCode lm after c')
  | i :: c' =>
      let after := skipDebugSetvar lm (transfer lm before i).2 c'
      i :: addDeltaRanges before after (transfCode lm after c')

/-- `Debugvar.transf_function` -/
def transfFunction (f : Linear.Function) : Res Linear.Function :=
  match anaFunction f with
  | none => .Error "Debugvar: analysis diverges"
  | some lm => .OK { fn_sig := f.fn_sig, fn_stacksize := f.fn_stacksize,
                     fn_code := transfCode lm (some top) f.fn_code }

/-- `Debugvar.transf_fundef` -/
def transfFundef (fd : Linear.Fundef) : Res Linear.Fundef :=
  ASTFundef.transfPartial transfFunction fd

/-- `Debugvar.transf_program` -/
def transfProgram (p : Linear.Program) : Res Linear.Program :=
  transformPartialProgram transfFundef p

end Debugvar
end RiscV
end CC
