/-
  A faster implementation of the interpreter of `MenhirLib/Interpreter.v`,
  substituted for `parse` in compiled code.

  In `Interpreter.lean` the input buffer is a function `Nat → token`, and each
  shift replaces the buffer `b` by `buf_tail b = fun n => b (n + 1)`.  After
  `k` shifts, reading the next token goes through `k` nested closures, so
  parsing a word of length `n` costs `O(n²)`.  (Rocq uses a lazy stream, so it
  does not have this problem.)

  Here the parser works on the original buffer and an offset into it.  The
  theorem `parse_eq_parse_fast` shows that the two parsers agree, and the
  `@[csimp]` attribute makes the compiler use `parse_fast` whenever `parse` is
  called.  To get a linear-time parser, the input buffer itself should give
  constant-time access to its tokens (for instance `fun n => arr[n]?.getD eof`).
-/
import CCLib.MenhirLib.Interpreter

namespace CC
namespace MenhirLib

section InterpreterFast
variable [Alphs] [GrammarT] [AutInit] [AutomatonT]

/-- The buffer `buf` without its first `off` tokens. -/
def buf_shift (buf : Buffer) (off : Nat) : Buffer := fun n => buf (off + n)

omit [AutInit] [AutomatonT] in
theorem buf_shift_zero (buf : Buffer) : buf_shift buf 0 = buf := by
  funext n
  simp [buf_shift]

omit [AutInit] [AutomatonT] in
theorem buf_tail_shift (buf : Buffer) (off : Nat) :
    buf_tail (buf_shift buf off) = buf_shift buf (off + 1) := by
  funext n
  simp only [buf_tail, buf_shift]
  congr 1
  omega

variable (init : initstate) (Hsafe : safe)

/-- The result of a step of the fast interpreter: the buffers of `step_result`
are replaced by offsets. -/
inductive fast_result where
  | Fail_fr : State → token → fast_result
  | Accept_fr : symbol_semantic_type (.NT (start_nt init)) → Nat → fast_result
  | Progress_fr : Stack → Nat → fast_result

variable {init} in
/-- The step result represented by a fast result. -/
def fast_result.toStep (buf : Buffer) : fast_result init → step_result init
  | .Fail_fr st tok => .Fail_sr_full st tok
  | .Accept_fr sem off => .Accept_sr sem (buf_shift buf off)
  | .Progress_fr stk off => .Progress_sr stk (buf_shift buf off)

variable {init} in
/-- Replace the buffer of the result of a reduction (which is the input
buffer, see `reduce_step_spec`) by the offset `off`. -/
def fast_of_reduce (off : Nat) : step_result init → fast_result init
  | .Fail_sr_full st tok => .Fail_fr st tok
  | .Accept_sr sem _ => .Accept_fr sem off
  | .Progress_sr stk _ => .Progress_fr stk off

/-- One step of the fast interpreter, at offset `off` of `buf`. -/
def step_fast (stk : Stack) (buf : Buffer) (off : Nat) (Hi : stack_invariant init stk) :
    fast_result init :=
  match ha : action_table (state_of_stack init stk) with
  | .Default_reduce_act prod =>
    fast_of_reduce off
      (reduce_step stk prod (buf_shift buf off) (reduce_ok_of_default Hsafe ha) Hi)
  | .Lookahead_act awt =>
    match hl : awt (token_term (buf off)) with
    | .Shift_act state_new e =>
      .Progress_fr (⟨state_new, cast (congrArg symbol_semantic_type e) (token_sem (buf off))⟩ :: stk)
        (off + 1)
    | .Reduce_act prod =>
      fast_of_reduce off
        (reduce_step stk prod (buf_shift buf off) (reduce_ok_of_lookahead Hsafe ha hl) Hi)
    | .Fail_act => .Fail_fr (state_of_stack init stk) (buf off)

theorem fast_of_reduce_toStep {stk : Stack} {prod : production} {buf : Buffer} {off : Nat}
    {Hval : valid_for_reduce (state_of_stack init stk) prod} {Hi : stack_invariant init stk} :
    (fast_of_reduce off (reduce_step stk prod (buf_shift buf off) Hval Hi)).toStep buf =
      reduce_step stk prod (buf_shift buf off) Hval Hi := by
  rcases reduce_step_spec stk prod (buf_shift buf off) Hval Hi with
    ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;> rw [h] <;> rfl

/-- `step_fast` computes `step`. -/
theorem step_fast_spec (stk : Stack) (buf : Buffer) (off : Nat) (Hi : stack_invariant init stk) :
    (step_fast init Hsafe stk buf off Hi).toStep buf = step init Hsafe stk (buf_shift buf off) Hi := by
  unfold step_fast step
  split <;> rename_i ha
  · split <;> rename_i ha' <;> rw [ha] at ha' <;> cases ha'
    exact fast_of_reduce_toStep init
  · split <;> rename_i hl <;>
      (split <;> rename_i ha' <;> rw [ha] at ha' <;> cases ha') <;>
      (split <;> rename_i hl' <;> have h := hl.symm.trans hl' <;> cases h)
    · simp only [fast_result.toStep, buf_tail_shift]
      rfl
    · exact fast_of_reduce_toStep init
    · rfl

theorem step_fast_stack_invariant_preserved {stk : Stack} {buf : Buffer} {off : Nat} {Hi}
    {stk' : Stack} {off' : Nat} :
    step_fast init Hsafe stk buf off Hi = .Progress_fr stk' off' → stack_invariant init stk' := by
  intro h
  have := step_fast_spec init Hsafe stk buf off Hi
  rw [h] at this
  exact step_stack_invariant_preserved init Hsafe this.symm

/-- The main loop of the fast interpreter. -/
def parse_fix_fast : (stk : Stack) → (buf : Buffer) → (off : Nat) → (log_n_steps : Nat) →
    stack_invariant init stk →
    { r : fast_result init //
      ∀ stk' off', r = .Progress_fr stk' off' → stack_invariant init stk' }
  | stk, buf, off, 0, Hi =>
    ⟨step_fast init Hsafe stk buf off Hi, fun _ _ => step_fast_stack_invariant_preserved init Hsafe⟩
  | stk, buf, off, n + 1, Hi =>
    match parse_fix_fast stk buf off n Hi with
    | ⟨.Progress_fr stk' off', Hi'⟩ => parse_fix_fast stk' buf off' n (Hi' _ _ rfl)
    | r => r

/-- `parse_fix_fast` computes `parse_fix`. -/
theorem parse_fix_fast_spec (buf : Buffer) (log_n_steps : Nat) : ∀ (stk : Stack) (off : Nat)
    (Hi : stack_invariant init stk),
    (parse_fix_fast init Hsafe stk buf off log_n_steps Hi).1.toStep buf =
      (parse_fix init Hsafe stk (buf_shift buf off) log_n_steps Hi).1 := by
  induction log_n_steps with
  | zero => exact fun stk off Hi => step_fast_spec init Hsafe stk buf off Hi
  | succ n ih =>
    intro stk off Hi
    have ih1 := ih stk off Hi
    simp only [parse_fix_fast, parse_fix]
    revert ih1
    rcases parse_fix_fast init Hsafe stk buf off n Hi with ⟨r, Hr⟩
    rcases parse_fix init Hsafe stk (buf_shift buf off) n Hi with ⟨sr, Hsr⟩
    intro h
    simp only at h
    subst h
    cases r with
    | Fail_fr => rfl
    | Accept_fr => rfl
    | Progress_fr stk' off' => exact ih stk' off' _

/-- The fast parser. -/
def parse_fast (buffer : Buffer) (log_n_steps : Nat) :
    parse_result (symbol_semantic_type (.NT (start_nt init))) :=
  match (parse_fix_fast init Hsafe [] buffer 0 log_n_steps (stack_invariant_nil init)).1 with
  | .Fail_fr st tok => .Fail_pr_full st tok
  | .Accept_fr sem off => .Parsed_pr sem (buf_shift buffer off)
  | .Progress_fr _ _ => .Timeout_pr

end InterpreterFast

/-- The fast parser computes the same result as `parse`; the compiler uses it
in place of `parse`. -/
@[csimp] theorem parse_eq_parse_fast : @parse = @parse_fast := by
  funext _ _ _ _ init Hsafe buffer log_n_steps
  have h := parse_fix_fast_spec init Hsafe buffer log_n_steps [] 0 (stack_invariant_nil init)
  rw [buf_shift_zero] at h
  unfold parse parse_fast
  rw [← h]
  cases (parse_fix_fast init Hsafe [] buffer 0 log_n_steps (stack_invariant_nil init)).1 <;> rfl

end MenhirLib
end CC
