/-
  A struct field read, proved with the separation logic.

  Validates the Phase-8 struct layer against a *real* `Efield` AST rather than an
  abstract one: `structAt` describes the object, `fieldsAt_split` pulls out the
  field being read (the rest of the struct becomes the frame), and
  `eval_field_scalar` discharges the composite-env lookup and `field_offset`
  computation `EvalLvalue.Efield_struct` demands.

  Shaped like the accesses zlib makes constantly (`strm->avail_out`, …).
-/
import GenStruct
import CCLib
open CC CC.Sep CC.HProp
open Structs2   -- the generated module now lives in its own namespace

namespace StructSep

/-! The three facts below are about the *generated program's* composite
environment: `fieldOffsetRec` compares field identifiers, so they need
`DecidableEq` on `Res`/`Member`/`Composite` (added for exactly this) *and* a
reducible `identOfString`.  They needed `native_decide` until `identOfString`
was rewritten to fold over `String.toList` (see `CCLib.lib.Positive`); kernel
`decide` now discharges them. -/

/-- `field_offset` for the two fields, computed from the generated composite. -/
theorem offset_x : fieldOffset prog.prog_comp_env _x
    [Member.Member_plain _x tuint, Member.Member_plain _y tuint] = .OK (0, .Full) := by
  decide

theorem offset_y : fieldOffset prog.prog_comp_env _y
    [Member.Member_plain _x tuint, Member.Member_plain _y tuint] = .OK (4, .Full) := by
  decide

theorem composite_st :
    prog.prog_comp_env.get _st = some
      { co_su := SU.Struct,
        co_members := [Member.Member_plain _x tuint, Member.Member_plain _y tuint],
        co_attr := noattr, co_sizeof := 8, co_alignof := 4, co_rank := 0 } := by
  decide

/-- **Reading `q->y` out of a `structAt`.**  The `x` field is never mentioned: it
    comes out of `fieldsAt_split` as the frame. -/
theorem read_y (ge : CGenv) (e : Env) (le : TempEnv) (m : Mem)
    (pm : Permission) (b : Block) (ofs : Integers.Ptrofs) (vx vy : Integers.Int)
    (h hy hrest : Heap)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hpr : permOrder pm .Readable = true)
    (hq : le.get _q = some (.Vptr b ofs))
    (hsplit : Heap.disjoint hy hrest ∧ h = Heap.union hy hrest
              ∧ fieldAt .Mint32 pm b (Integers.Ptrofs.unsigned ofs) 4 (.Vint vy) hy)
    (hag : Heap.Agrees h m)
    (hno : ofs.toNat + 4 < 18446744073709551616) :
    EvalExpr ge e le m
      (.Efield (.Ederef (.Etempvar _q (tptr (Ty.Tstruct _st noattr)))
                 (Ty.Tstruct _st noattr)) _y tuint) (.Vint vy) := by
  obtain ⟨hd, heq, hmy⟩ := hsplit
  subst heq
  have hlr : Val.loadResult .Mint32 (.Vint vy) = .Vint vy := by simp [Val.loadResult]
  rw [← hlr]
  refine eval_field_scalar (sid := _st) (att := noattr) (delta := 4)
    rfl hpr rfl (hcenv ▸ composite_st) (hcenv ▸ offset_y) hmy
    (Heap.Agrees_union_left hag)
    (EvalExpr.Elvalue _ b ofs .Full _
      (EvalLvalue.Ederef _ _ _ _
        (EvalExpr.Etempvar _q (tptr (Ty.Tstruct _st noattr)) _ hq)) ?_) ?_
  · -- a struct l-value is `By_copy`, so dereferencing yields the pointer itself
    exact DerefLoc.copy (by decide)
  · exact ptrofs_add_unsigned ofs 4 hno

end StructSep
