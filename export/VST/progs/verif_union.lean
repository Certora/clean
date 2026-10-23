/-
  Port of VST's `progs/verif_union.v`, function `g` of `vst/progs/union.c`:
  a value stored into a member of a local union is read back.

      union p_or_i { size_t choice_i; void *choice_p; };

      size_t g(size_t i) {
        union p_or_i x;
        x.choice_i = i;
        return x.choice_i;
      }

  VST's specification:

      DECLARE _g
       WITH i: Z
       PRE [ size_t ] PROP() PARAMS(Vptrofs (Ptrofs.repr i)) SEP()
       POST [ size_t ] PROP() RETURN (Vptrofs (Ptrofs.repr i)) SEP().

  On the 64-bit target `Vptrofs (Ptrofs.repr i)` is a `long` value; here it
  is any `Int64` `i`.  The local `x` lives in memory (it is a union): its
  entry and exit are `Sep.satisfies_oneLocal` / `Sep.triple_return_oneLocal`.
  `ge` must use the program's composite environment (`hcenv`), which gives the
  union its size (8) and the member its offset (0).
-/
import VST.progs.union
import CCLib
open CC CC.Sep CC.HProp
open Union

namespace VST.Verif.Union

/-! ## The layout of `union p_or_i` -/

abbrev tunion : Ty := .Tunion _p_or_i noattr

def coU : Composite :=
  match prog.prog_comp_env.get _p_or_i with
  | some co => co
  | none => { co_su := .Union, co_members := [], co_attr := noattr,
              co_sizeof := 0, co_alignof := 1, co_rank := 0 }

theorem get_u : prog.prog_comp_env.get _p_or_i = some coU := rfl
theorem sizeof_u : sizeof prog.prog_comp_env tunion = 8 := by decide
theorem offset_choice_i :
    unionFieldOffset prog.prog_comp_env _choice_i coU.co_members = .OK (0, .Full) := by decide

/-- `x.choice_i`, for the local `x` at block `b`, as an l-value. -/
theorem lvalue_choice_i {ge : CGenv} (hcenv : ge.genv_cenv = prog.prog_comp_env) {le : TempEnv}
    {m : Mem} {b : Block} :
    EvalLvalue ge (emptyEnv.set _x (b, tunion)) le m (.Efield (.Evar _x tunion) _choice_i tulong) b
      (Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.repr 0)) .Full :=
  EvalLvalue.Efield_union _ _choice_i tulong b Integers.Ptrofs.zero _p_or_i coU noattr 0 .Full
    (EvalExpr.Elvalue _ b Integers.Ptrofs.zero .Full _ eval_lvalue_oneLocal (DerefLoc.copy rfl))
    rfl (hcenv ▸ get_u) (hcenv ▸ offset_choice_i)

/-! ## The specification -/

/-- `g_spec` -/
def gSpec (i : Integers.Int64) : Sep.FunSpec where
  tyargs := [tulong]
  tyres := tulong
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vlong i] ∧ emp hp
  post := fun v hp => v = .Vlong i ∧ emp hp
  measure := fun _ => 0

theorem semCast_ulong (m : Mem) (x : Integers.Int64) :
    Cop.semCast (.Vlong x) tulong tulong m = some (.Vlong x) := rfl

/-- **`g` satisfies `g_spec`** (VST's `body_g`). -/
theorem g_satisfies (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (i : Integers.Int64) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_g) (gSpec i) [.Vlong i] := by
  let L : TempEnv := (createUndefTemps f_g.fn_temps).set _i (.Vlong i)
  refine satisfies_oneLocal ge f_g _ _ L _x tunion rfl (by decide) (by decide) rfl
    (by rw [hcenv, sizeof_u]; decide) fun b => ?_
  let E : Env := emptyEnv.set _x (b, tunion)
  have haddr : Integers.Ptrofs.unsigned
      (Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.repr 0)) = 0 := by decide
  -- the 8 undefined bytes of `x` are an undefined `size_t`
  refine triple_pre ge _ f_g (P := AtE E L (mapsto .Mint64 .Freeable b 0 .Vundef))
    (fun e le hp ⟨he, hl, hH⟩ => ⟨he, hl, by
      rw [hcenv, sizeof_u, show (8 : _root_.Int).toNat = sizeChunkNat .Mint64 from rfl,
        undefBytes_mapsto _ _ _ undefEncoded_Mint64 (by decide)] at hH
      obtain ⟨h1, h2, _, rfl, ⟨_, rfl⟩, hm⟩ := hH
      rwa [Heap.emp_union]⟩) ?_
  -- `x.choice_i = i;`
  refine triple_seq_only ge _ f_g
    (triple_assign_atE ge _ f_g E L _ _ .Mint64 .Freeable b _ 0 _ (.Vlong i) (.Vlong i) rfl rfl
      haddr (fun _ => lvalue_choice_i hcenv) (fun _ => EvalExpr.Etempvar _ _ _ rfl)
      (fun m => semCast_ulong m _)) ?_
  -- `t'1 = x.choice_i;`
  refine triple_seq_only ge _ f_g
    (triple_set_atE ge _ f_g E L _ _ _ (.Vlong i) fun m hp hm hag =>
      eval_lvalue_mapsto (chunk := .Mint64) (v := .Vlong i) rfl rfl (lvalue_choice_i hcenv)
        haddr hm hag) ?_
  -- `return t'1;` frees `x`
  refine triple_pre ge _ f_g (fun e le hp ⟨he, hl, hH⟩ => ⟨he, hl, by
    rw [emp_sep_eq, ← mapsto_eq_bytes (by decide)]; exact hH⟩)
    (triple_return_oneLocal ge _ f_g _x tunion b _ emp (encodeVal .Mint64 (.Vlong i)) _ (.Vlong i)
      (.Vlong i) (by rw [hcenv, sizeof_u]; rfl)
      (fun _ _ _ _ => EvalExpr.Etempvar _ _ _ (PTree.gss _ _ _)) (fun m => semCast_ulong m _))

end VST.Verif.Union
