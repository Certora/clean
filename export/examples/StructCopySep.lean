/-
  **Acceptance test for `Sep.triple_assign_copy`** — the struct-copy assignment
  rule.

  `test/lean/structcopy.c` is the shape `inflate_table` writes its decoding
  tables with, cut down to one slot:

      struct code { unsigned char op; unsigned char bits; unsigned short val; };
      void put(struct code *dst) {
          struct code here;
          here.op = 0; here.bits = 5; here.val = 42;
          *dst = here;          /* accessMode = By_copy */
      }

  The last statement generates

      Sassign (Ederef (Etempvar _dst (tptr (Tstruct _code noattr)))
                      (Tstruct _code noattr))
              (Evar _here (Tstruct _code noattr))

  which is *literally* the shape at inftrees.c:130-131, 243, 304.  Because
  `accessMode (Tstruct …) = .By_copy`, it steps through `AssignLoc.copy` — a raw
  `loadbytes`/`storebytes` block copy — and `Sep.triple_assign` cannot touch it:
  that rule is hardwired to `AssignLoc.value`.  Before `triple_assign_copy` no
  rule in the logic could step over these statements at all.

  What this file exercises, in order:

  * the composite facts (`sizeof = 4`, `alignofBlockcopy = 2`, offsets 0/1/2) —
    one `decide` each, the `InflateMeasure` batching pattern;
  * `bytesPtsTo_append` twice, to assemble the 4-byte source out of the three
    field `mapsto`s (`mapsto` *is* `⌜align⌝ ∗ bytesPtsTo`, so the conversion is
    definitional);
  * **`Sep.triple_assign_copy`** on the real generated statement;
  * `anyBytes_split` / `anyBytes_of_bytesPtsTo`, the shapes a client actually
    owns on the destination side.
-/
import GenStructCopy
import CCLib
open CC CC.Sep CC.HProp
open Structcopy   -- the generated module lives in its own namespace

namespace StructCopySep

/-! ## 1. Layout facts

`struct code` is 1 + 1 + 2 = 4 bytes with no padding — the same layout as zlib's
`struct code` in inftrees.h, which is why the test is faithful. -/

def codeCo : Composite :=
  match prog.prog_comp_env.get _code with
  | some co => co
  | none => { co_su := .Struct, co_members := [], co_attr := noattr,
              co_sizeof := 0, co_alignof := 1, co_rank := 0 }

theorem hco : prog.prog_comp_env.get _code = some codeCo := rfl

theorem code_sizeof : sizeof prog.prog_comp_env (Ty.Tstruct _code noattr) = 4 := by
  decide

/-- The alignment `AssignLoc.copy` guards on — 2, because `val` is a `ushort`. -/
theorem code_alignblk :
    alignofBlockcopy prog.prog_comp_env (Ty.Tstruct _code noattr) = 2 := by decide

/-- `Tstruct` is copied, not loaded — this is the fact that makes
    `triple_assign` inapplicable and `triple_assign_copy` necessary. -/
theorem code_bycopy : accessMode (Ty.Tstruct _code noattr) = .By_copy := by decide

theorem hoff_op :
    fieldOffset prog.prog_comp_env _op codeCo.co_members = .OK (0, .Full) := by decide

theorem hoff_bits :
    fieldOffset prog.prog_comp_env _bits codeCo.co_members = .OK (1, .Full) := by
  decide

theorem hoff_val :
    fieldOffset prog.prog_comp_env _val codeCo.co_members = .OK (2, .Full) := by
  decide

/-- The `rfl` guard on the generated AST: the copy is the penultimate statement,
    followed by the `return`. -/
theorem body_shape :
    f_put.fn_body
      = .Ssequence
          (.Sassign (.Efield (.Evar _here (Ty.Tstruct _code noattr)) _op tuchar)
            (.Econst_int (Integers.Int.repr 0) tint))
          (.Ssequence
            (.Sassign (.Efield (.Evar _here (Ty.Tstruct _code noattr)) _bits tuchar)
              (.Econst_int (Integers.Int.repr 5) tint))
            (.Ssequence
              (.Sassign (.Efield (.Evar _here (Ty.Tstruct _code noattr)) _val tushort)
                (.Econst_int (Integers.Int.repr 42) tint))
              (.Ssequence
                (.Sassign
                  (.Ederef (.Etempvar _dst (tptr (Ty.Tstruct _code noattr)))
                    (Ty.Tstruct _code noattr))
                  (.Evar _here (Ty.Tstruct _code noattr)))
                (.Sreturn none)))) := rfl

theorem has_one_local : f_put.fn_vars = [(_here, Ty.Tstruct _code noattr)] := rfl

/-! ## 2. The source: three field `mapsto`s become a 4-byte run

`mapsto chunk p b ofs v` is *by definition* `⌜align⌝ ∗ bytesPtsTo b p ofs
(encodeVal chunk v)` (`SepLogic.lean:153`), so no conversion lemma is needed —
only `bytesPtsTo_append`, twice, and the observation that all three alignment
conjuncts are true (`0 % 1`, `1 % 1`, `2 % 2`). -/

/-- The three field encodings, named so their lengths can be rewritten. -/
def bOp : List MemVal := encodeVal .Mint8unsigned (.Vint (Integers.Int.repr 0))
def bBits : List MemVal := encodeVal .Mint8unsigned (.Vint (Integers.Int.repr 5))
def bVal : List MemVal := encodeVal .Mint16unsigned (.Vint (Integers.Int.repr 42))

theorem lOp : bOp.length = 1 := by decide
theorem lBits : bBits.length = 1 := by decide
theorem lVal : bVal.length = 2 := by decide

/-- The bytes `here` holds after the three field writes.  1 + 1 + 2 = 4, no
    padding — the same as zlib's `struct code`. -/
def hereBytes : List MemVal := bOp ++ (bBits ++ bVal)

theorem hereBytes_length : hereBytes.length = 4 := by decide

/-- **The assembly.**  An equality, so the same lemma takes the struct apart
    again — which a functional proof of `inflate_table` will want. -/
theorem here_assemble (p : Permission) (b : Block) :
    bytesPtsTo b p 0 hereBytes
      = mapsto .Mint8unsigned p b 0 (.Vint (Integers.Int.repr 0))
        ∗ (mapsto .Mint8unsigned p b 1 (.Vint (Integers.Int.repr 5))
           ∗ mapsto .Mint16unsigned p b 2 (.Vint (Integers.Int.repr 42))) := by
  rw [mapsto_eq_bytes (chunk := .Mint8unsigned) (by decide),
      mapsto_eq_bytes (chunk := .Mint8unsigned) (by decide),
      mapsto_eq_bytes (chunk := .Mint16unsigned) (by decide)]
  show bytesPtsTo b p 0 (bOp ++ (bBits ++ bVal))
        = bytesPtsTo b p 0 bOp ∗ (bytesPtsTo b p 1 bBits ∗ bytesPtsTo b p 2 bVal)
  rw [bytesPtsTo_append, bytesPtsTo_append, lOp, lBits,
      show (0 : _root_.Int) + ((1 : Nat) : _root_.Int) = 1 from by omega,
      show (1 : _root_.Int) + ((1 : Nat) : _root_.Int) = 2 from by omega]

/-! ## 3. The copy step — the point of the exercise

`triple_assign_copy` applied to the real generated statement.  Note what is
*not* a hypothesis: nothing says the `here` block and the `*dst` window do not
overlap.  That comes out of the `∗` between them, via
`Heap.disjoint_ranges_nonoverlap` inside the rule. -/

theorem ptrofs_zero_unsigned : Integers.Ptrofs.unsigned Integers.Ptrofs.zero = 0 := by
  simp [Integers.Ptrofs.unsigned, Integers.Ptrofs.zero, Integers.MI.unsigned,
        Integers.MI.zero]

/-- The state throughout `put`: the environment binds the local `here`, the
    parameter `dst` is in a temporary, and the heap satisfies `H`.  Only `H`
    changes from statement to statement. -/
def St (bHere bdst : Block) (odst : Integers.Ptrofs) (H : HProp) : Sep.Assn :=
  fun e le hp =>
    e.get _here = some (bHere, Ty.Tstruct _code noattr)
    ∧ le.get _dst = some (.Vptr bdst odst)
    ∧ H hp

/-- The heap before the copy: `here` holds its four bytes, `*dst` is a writable
    4-byte window of unknown contents, and the two are separate. -/
abbrev PreCopyH (phere pdst : Permission) (bHere bdst : Block)
    (odst : Integers.Ptrofs) (oldBytes : List MemVal) : HProp :=
  bytesPtsTo bHere phere 0 hereBytes
  ∗ bytesPtsTo bdst pdst (Integers.Ptrofs.unsigned odst) oldBytes

/-- …and after: the destination holds *the same bytes*, byte for byte.  The
    source is untouched, which is what lets the caller free `here`. -/
abbrev PostCopyH (phere pdst : Permission) (bHere bdst : Block)
    (odst : Integers.Ptrofs) : HProp :=
  bytesPtsTo bHere phere 0 hereBytes
  ∗ bytesPtsTo bdst pdst (Integers.Ptrofs.unsigned odst) hereBytes

/-- **The acceptance criterion.**  `*dst = here;` steps, in the separation logic,
    for the first time. -/
theorem copy_step (ge : CGenv) (fe : EntryRel) (phere pdst : Permission)
    (bHere bdst : Block) (odst : Integers.Ptrofs) (oldBytes : List MemVal)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hpr : permOrder phere .Readable = true)
    (hpw : permOrder pdst .Writable = true)
    (hold : oldBytes.length = 4)
    (haldst : Integers.Ptrofs.unsigned odst % 2 = 0) :
    Triple ge fe f_put
      (St bHere bdst odst (PreCopyH phere pdst bHere bdst odst oldBytes))
      (.Sassign
        (.Ederef (.Etempvar _dst (tptr (Ty.Tstruct _code noattr)))
          (Ty.Tstruct _code noattr))
        (.Evar _here (Ty.Tstruct _code noattr)))
      (.only (St bHere bdst odst (PostCopyH phere pdst bHere bdst odst))) := by
  refine triple_assign_copy ge fe f_put _ _ _ _ phere pdst
    bHere Integers.Ptrofs.zero bdst odst hereBytes oldBytes hpr hpw
    (by exact code_bycopy) ?_ (by rw [hold, hereBytes_length]) ?_ ?_ ?_
  · -- the size: 4 bytes, from the composite environment
    simp only [typeof]
    rw [hereBytes_length, hcenv, code_sizeof]
    omega
  · -- source alignment: `here` sits at offset 0 of its own block
    intro _
    simp only [typeof]
    rw [hcenv, code_alignblk, ptrofs_zero_unsigned]
    -- `alignofBlockcopy` returns `CC.Z`, where `omega` is blind (the standing
    -- trap); the goal is closed, not arithmetic
    decide
  · -- destination alignment: the caller's obligation
    intro _
    simp only [typeof]
    rw [hcenv, code_alignblk]
    exact haldst
  · -- the split, and the two evaluations
    intro e le hp m hP _
    obtain ⟨hbind, hdst, h1, h2, hd12, heq, hsm, hdm⟩ := hP
    refine ⟨h1, h2, Heap.emp, by simp, ?_, ?_, ?_, hdm, ?_, ?_, ?_, ?_⟩
    · rw [Heap.union_emp]; exact Heap.disjoint_comm hd12
    · rw [Heap.union_emp, heq]; exact Heap.union_comm hd12
    · rw [ptrofs_zero_unsigned]; exact hsm
    · -- the l-value `*dst`
      exact EvalLvalue.Ederef _ _ _ _
        (EvalExpr.Etempvar _dst (tptr (Ty.Tstruct _code noattr)) _ hdst)
    · -- the r-value `here`: a struct read is By_copy, so it yields its address
      exact EvalExpr.Elvalue _ bHere Integers.Ptrofs.zero .Full _
        (EvalLvalue.Evar_local _here bHere (Ty.Tstruct _code noattr) hbind)
        (DerefLoc.copy (by decide))
    · -- struct-to-same-struct cast is the identity
      simp only [typeof]
      exact semCast_struct_same _ _ _ _ _ _
    · -- reassemble the postcondition
      intro hDst' hdm' hd'
      rw [Heap.union_emp] at hd' ⊢
      exact ⟨hbind, hdst,
             h1, hDst', Heap.disjoint_comm hd', Heap.union_comm hd', hsm, hdm'⟩

/-! ## 4. Entry: the local's four bytes become three field slots

`allocVariables_resources` hands back `undefBytes .Freeable bHere 0 4`;
`undefBytes_split` carves it three times.  Every alignment is trivial here
(`0 % 1`, `1 % 1`, `2 % 2`) and the leftover runs are empty, because `struct
code` has no padding. -/

private theorem hwp : (2 : Nat) ^ Archi.ptrWordsize = 18446744073709551616 := by
  rw [Archi.ptrWordsize_eq]

theorem ptrofs_repr_unsigned (d : _root_.Int) (h0 : 0 ≤ d)
    (h : d < 18446744073709551616) :
    Integers.Ptrofs.unsigned (Integers.Ptrofs.repr d) = d := by
  show (((Integers.MI.repr d).toNat : _root_.Int)) = _
  simp only [Integers.MI.repr, BitVec.toNat_ofInt, hwp]
  omega

/-- **The carve.**  Four undefined bytes become `op`, `bits` and `val`. -/
theorem here_carve (p : Permission) (b : Block) :
    undefBytes p b 0 4
      = mapsto .Mint8unsigned p b 0 .Vundef
        ∗ (undefBytes p b 0 0
           ∗ (mapsto .Mint8unsigned p b 1 .Vundef
              ∗ (undefBytes p b 1 0
                 ∗ (mapsto .Mint16unsigned p b 2 .Vundef
                    ∗ (undefBytes p b 2 0 ∗ undefBytes p b 4 0))))) := by
  rw [undefBytes_split (chunk := .Mint8unsigned) p b 0 4 0
        undefEncoded_Mint8unsigned (by decide) (by decide),
      -- the COMPOUND offset first: rewriting `0 + ↑0 → 0` earlier would destroy
      -- the pattern `0 + ↑0 + ↑sizeChunkNat` this needs to match
      show (0 : _root_.Int) + ((0 : Nat) : _root_.Int)
             + ((sizeChunkNat .Mint8unsigned : Nat) : _root_.Int) = 1 from by decide,
      show (0 : _root_.Int) + ((0 : Nat) : _root_.Int) = 0 from by omega,
      show 4 - 0 - sizeChunkNat .Mint8unsigned = 3 from by decide,
      undefBytes_split (chunk := .Mint8unsigned) p b 1 3 0
        undefEncoded_Mint8unsigned (by decide) (by decide),
      show (1 : _root_.Int) + ((0 : Nat) : _root_.Int)
             + ((sizeChunkNat .Mint8unsigned : Nat) : _root_.Int) = 2 from by decide,
      show (1 : _root_.Int) + ((0 : Nat) : _root_.Int) = 1 from by omega,
      show 3 - 0 - sizeChunkNat .Mint8unsigned = 2 from by decide,
      undefBytes_split (chunk := .Mint16unsigned) p b 2 2 0
        undefEncoded_Mint16unsigned (by decide) (by decide),
      show (2 : _root_.Int) + ((0 : Nat) : _root_.Int)
             + ((sizeChunkNat .Mint16unsigned : Nat) : _root_.Int) = 4 from by decide,
      show (2 : _root_.Int) + ((0 : Nat) : _root_.Int) = 2 from by omega,
      show 2 - 0 - sizeChunkNat .Mint16unsigned = 0 from by decide]

/-- …and the leftovers are empty, so the three fields are the whole local. -/
theorem here_carve_exact (p : Permission) (b : Block) (h : Heap)
    (hu : undefBytes p b 0 4 h) :
    (mapsto .Mint8unsigned p b 0 .Vundef
     ∗ (mapsto .Mint8unsigned p b 1 .Vundef
        ∗ mapsto .Mint16unsigned p b 2 .Vundef)) h := by
  rw [here_carve] at hu
  simpa only [undefBytes_zero, emp_sep_eq, sep_emp_eq] using hu

/-! ## 5. Writing one field of `here`

`Efield (Evar _here …) fld` — an `Evar` of a *local* goes through
`EvalLvalue.Evar_local`, which is the only evaluation shape this needs beyond
what `StructSep` already covers. -/

theorem eval_field_here {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem}
    {b : Block} {fld : Ident} {delta : Z} {ty : Ty}
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hbind : e.get _here = some (b, Ty.Tstruct _code noattr))
    (hoff : fieldOffset prog.prog_comp_env fld codeCo.co_members
              = .OK (delta, .Full)) :
    EvalLvalue ge e le m (.Efield (.Evar _here (Ty.Tstruct _code noattr)) fld ty)
      b (Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.repr delta))
      .Full := by
  refine EvalLvalue.Efield_struct _ fld ty b Integers.Ptrofs.zero _code codeCo
    noattr delta .Full ?_ rfl (hcenv ▸ hco) (hcenv ▸ hoff)
  exact EvalExpr.Elvalue _ b Integers.Ptrofs.zero .Full _
    (EvalLvalue.Evar_local _here b (Ty.Tstruct _code noattr) hbind)
    (DerefLoc.copy (by decide))

/-- `Ptrofs.add 0 d = d`, so a field sits at its own offset. -/
theorem ptrofs_zero_add (d : Z) :
    Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.repr d)
      = Integers.Ptrofs.repr d := by
  apply BitVec.eq_of_toNat_eq
  simp only [Integers.Ptrofs.add, Integers.Ptrofs.zero, Integers.Ptrofs.repr,
             Integers.MI.add, Integers.MI.repr, Integers.MI.zero, BitVec.toNat_add,
             BitVec.toNat_ofInt]
  have hmod : ∀ x : _root_.Int, x % 18446744073709551616 < 18446744073709551616 := by
    intro x; omega
  simp [hmod d]

/-! ## 6. Writing one field, generically

One theorem covers all three writes: the field, its chunk, its offset and the
stored value are parameters.  `Rest` is whatever else the heap holds — the frame
that passes through. -/

theorem write_field (ge : CGenv) (fe : EntryRel) (phere : Permission)
    (bHere bdst : Block) (odst : Integers.Ptrofs)
    (fld : Ident) (delta : Z) (ty : Ty) (chunk : Chunk)
    (n : Integers.Int) (v : Val) (Rest : HProp)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hoff : fieldOffset prog.prog_comp_env fld codeCo.co_members
              = .OK (delta, .Full))
    (hd0 : 0 ≤ delta) (hdlt : delta < 18446744073709551616)
    (hpw : permOrder phere .Writable = true)
    (hacc : accessMode ty = .By_value chunk)
    (hcast : ∀ m : Mem, Cop.semCast (.Vint n) tint ty m = some v)
    (hw : Mem.ChunkNoWrap chunk delta := by exact Or.inl rfl) :
    Triple ge fe f_put
      (St bHere bdst odst (mapsto chunk phere bHere delta .Vundef ∗ Rest))
      (.Sassign (.Efield (.Evar _here (Ty.Tstruct _code noattr)) fld ty)
        (.Econst_int n tint))
      (.only (St bHere bdst odst (mapsto chunk phere bHere delta v ∗ Rest))) := by
  -- the field's address: `0 + delta` is `delta`
  have haddr : Integers.Ptrofs.unsigned
      (Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.repr delta))
        = delta := by
    rw [ptrofs_zero_add, ptrofs_repr_unsigned delta hd0 hdlt]
  refine triple_assign ge fe f_put _ _ _ _ chunk phere bHere
    (Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.repr delta))
    hpw (by simpa only [typeof] using hacc) ?_ (by rw [haddr]; exact hw)
  intro e le hp m hP _
  obtain ⟨hbind, hdst, h1, h2, hd12, heq, hm1, hrest⟩ := hP
  refine ⟨.Vundef, v, h1, h2, hd12, heq, by rw [haddr]; exact hm1, ?_, ?_, ?_⟩
  · exact eval_field_here hcenv hbind hoff
  · exact ⟨.Vint n, EvalExpr.Econst_int _ _, by simpa only [typeof] using hcast m⟩
  · intro h1' hm1' hd1'
    exact ⟨hbind, hdst, h1', h2, hd1', rfl, by rw [haddr] at hm1'; exact hm1', hrest⟩

/-! ## 7. The three writes, then the copy

The chain the brief asks for, end to end: three field writes leave three
`mapsto`s, `here_assemble` turns them into the 4-byte source, and
`triple_assign_copy` copies it.  The `here_assemble` step is the one that could
not be written before this PR. -/

/-! ### The field predicates, named

`set` is a Mathlib tactic and is not available here, so the four conjuncts of the
chain get names at the top level instead. -/

abbrev mOpU (phere : Permission) (bHere : Block) : HProp :=
  mapsto .Mint8unsigned phere bHere 0 .Vundef
abbrev mOp0 (phere : Permission) (bHere : Block) : HProp :=
  mapsto .Mint8unsigned phere bHere 0 (.Vint (Integers.Int.repr 0))
abbrev mBitsU (phere : Permission) (bHere : Block) : HProp :=
  mapsto .Mint8unsigned phere bHere 1 .Vundef
abbrev mBits5 (phere : Permission) (bHere : Block) : HProp :=
  mapsto .Mint8unsigned phere bHere 1 (.Vint (Integers.Int.repr 5))
abbrev mValU (phere : Permission) (bHere : Block) : HProp :=
  mapsto .Mint16unsigned phere bHere 2 .Vundef
abbrev mVal42 (phere : Permission) (bHere : Block) : HProp :=
  mapsto .Mint16unsigned phere bHere 2 (.Vint (Integers.Int.repr 42))
abbrev dstOld (pdst : Permission) (bdst : Block) (odst : Integers.Ptrofs)
    (oldBytes : List MemVal) : HProp :=
  bytesPtsTo bdst pdst (Integers.Ptrofs.unsigned odst) oldBytes

/-- `here.op = 0; here.bits = 5; here.val = 42; *dst = here;` — the whole body
    except the `return`.

    Each write needs its own field at the head of the `∗`-chain, so the three are
    separated by AC re-associations.  The last one folds the three field
    `mapsto`s into the 4-byte source with `here_assemble` — the step that could
    not be written before this PR — and then `copy_step` fires. -/
theorem body_upto_return (ge : CGenv) (fe : EntryRel) (phere pdst : Permission)
    (bHere bdst : Block) (odst : Integers.Ptrofs) (oldBytes : List MemVal)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hprh : permOrder phere .Readable = true)
    (hpwh : permOrder phere .Writable = true)
    (hpwd : permOrder pdst .Writable = true)
    (hold : oldBytes.length = 4)
    (haldst : Integers.Ptrofs.unsigned odst % 2 = 0) :
    Triple ge fe f_put
      (St bHere bdst odst
        (mOpU phere bHere ∗ (mBitsU phere bHere
           ∗ (mValU phere bHere ∗ dstOld pdst bdst odst oldBytes))))
      (.Ssequence
        (.Sassign (.Efield (.Evar _here (Ty.Tstruct _code noattr)) _op tuchar)
          (.Econst_int (Integers.Int.repr 0) tint))
        (.Ssequence
          (.Sassign (.Efield (.Evar _here (Ty.Tstruct _code noattr)) _bits tuchar)
            (.Econst_int (Integers.Int.repr 5) tint))
          (.Ssequence
            (.Sassign (.Efield (.Evar _here (Ty.Tstruct _code noattr)) _val tushort)
              (.Econst_int (Integers.Int.repr 42) tint))
            (.Sassign
              (.Ederef (.Etempvar _dst (tptr (Ty.Tstruct _code noattr)))
                (Ty.Tstruct _code noattr))
              (.Evar _here (Ty.Tstruct _code noattr))))))
      (.only (St bHere bdst odst (PostCopyH phere pdst bHere bdst odst))) := by
  -- `here.op = 0`
  refine triple_seq_fwd ge fe f_put _
    (St bHere bdst odst
      (mBitsU phere bHere ∗ (mOp0 phere bHere
         ∗ (mValU phere bHere ∗ dstOld pdst bdst odst oldBytes)))) _ _ _ ?_ ?_
  · rw [sep_left_comm_eq (mBitsU phere bHere) (mOp0 phere bHere)]
    exact write_field ge fe phere bHere bdst odst _op 0 tuchar .Mint8unsigned
      (Integers.Int.repr 0) (.Vint (Integers.Int.repr 0)) _
      hcenv hoff_op (by decide) (by decide) hpwh (by decide) (fun _ => rfl)
  -- `here.bits = 5`
  refine triple_seq_fwd ge fe f_put _
    (St bHere bdst odst
      (mValU phere bHere ∗ (mBits5 phere bHere
         ∗ (mOp0 phere bHere ∗ dstOld pdst bdst odst oldBytes)))) _ _ _ ?_ ?_
  · rw [show (mValU phere bHere ∗ (mBits5 phere bHere
               ∗ (mOp0 phere bHere ∗ dstOld pdst bdst odst oldBytes)))
           = mBits5 phere bHere ∗ (mOp0 phere bHere
               ∗ (mValU phere bHere ∗ dstOld pdst bdst odst oldBytes)) from by
          rw [sep_left_comm_eq (mOp0 phere bHere) (mValU phere bHere),
              sep_left_comm_eq (mValU phere bHere) (mBits5 phere bHere)]]
    exact write_field ge fe phere bHere bdst odst _bits 1 tuchar .Mint8unsigned
      (Integers.Int.repr 5) (.Vint (Integers.Int.repr 5)) _
      hcenv hoff_bits (by decide) (by decide) hpwh (by decide) (fun _ => rfl)
  -- `here.val = 42`
  refine triple_seq_fwd ge fe f_put _
    (St bHere bdst odst (PreCopyH phere pdst bHere bdst odst oldBytes)) _ _ _ ?_ ?_
  · rw [show PreCopyH phere pdst bHere bdst odst oldBytes
           = mVal42 phere bHere ∗ (mBits5 phere bHere
               ∗ (mOp0 phere bHere ∗ dstOld pdst bdst odst oldBytes)) from by
          show bytesPtsTo bHere phere 0 hereBytes
                ∗ dstOld pdst bdst odst oldBytes = _
          -- `here_assemble` lands as `(mOp0 ∗ (mBits5 ∗ mVal42)) ∗ dstOld`;
          -- two `assoc`s flatten it, then three `left_comm`s rotate `mVal42`
          -- to the head, where the next write needs it
          rw [here_assemble, sep_assoc_eq, sep_assoc_eq,
              sep_left_comm_eq (mOp0 phere bHere) (mBits5 phere bHere),
              sep_left_comm_eq (mOp0 phere bHere) (mVal42 phere bHere),
              sep_left_comm_eq (mBits5 phere bHere) (mVal42 phere bHere)]]
    exact write_field ge fe phere bHere bdst odst _val 2 tushort .Mint16unsigned
      (Integers.Int.repr 42) (.Vint (Integers.Int.repr 42)) _
      hcenv hoff_val (by decide) (by decide) hpwh (by decide) (fun _ => rfl)
  -- `*dst = here` — the new rule
  exact copy_step ge fe phere pdst bHere bdst odst oldBytes hcenv hprh hpwd hold
    haldst

end StructCopySep
