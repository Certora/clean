/-
  Global environments and program initialization — port of the definitional part
  of `common/Globalenvs.v` (the ~550 lines of proofs about `init_mem`, the
  `INITMEM_INJ` / `MATCH_PROGRAMS` machinery, and the pass-transformation
  sections are skipped; dropping the latter also removes any need for
  `common/Linking.v`).

  ## Documented deviation: `Genv` carries no invariants

  CompCert's `Genv.t` is proof-carrying, with three `Prop` fields maintained by
  `Program Definition add_global`:

      genv_symb_range : symbols point below `genv_next`
      genv_defs_range : definitions live below `genv_next`
      genv_vars_inj   : the symbol table is injective

  Nothing in `Clight.step` consumes them — they exist for CompCert's compiler
  proofs — so we keep only the data.  `genv_vars_inj` in particular is the
  awkward one to re-establish at each `add_global`; if a later phase needs these
  facts they are provable as lemmas about `globalenv p` rather than carried.

  `store_zeros` is a `Function … {wf (Zwf 0) n}` in Rocq (well-founded
  recursion); here it recurses structurally on a `Nat` count, which is
  equivalent for the non-negative sizes it is called with.
-/
import CCLib.cfrontend.Ctypes
import CCLib.common.Memory

namespace CC

/-- `Globalenvs.Genv.t`, minus the three `Prop` invariants (see header). -/
structure Genv (F V : Type) where
  genv_public : List Ident
  /-- symbol → block -/
  genv_symb : PTree Block
  /-- block → definition -/
  genv_defs : PTree (GlobDef F V)
  /-- next unused block -/
  genv_next : Block

namespace Genv
variable {F V : Type}

/-- `Genv.find_symbol` -/
def findSymbol (ge : Genv F V) (id : Ident) : Option Block := ge.genv_symb.get id

/-- `Genv.symbol_address` -/
def symbolAddress (ge : Genv F V) (id : Ident) (ofs : Integers.Ptrofs) : Val :=
  match findSymbol ge id with
  | some b => .Vptr b ofs
  | none => .Vundef

/-- `Genv.public_symbol` -/
def publicSymbol (ge : Genv F V) (id : Ident) : Bool :=
  match findSymbol ge id with
  | none => false
  | some _ => ge.genv_public.contains id

/-- `Genv.find_def` -/
def findDef (ge : Genv F V) (b : Block) : Option (GlobDef F V) := ge.genv_defs.get b

/-- `Genv.find_funct_ptr` -/
def findFunctPtr (ge : Genv F V) (b : Block) : Option F :=
  match findDef ge b with
  | some (.Gfun f) => some f
  | _ => none

/-- `Genv.find_funct` — the callee must be a pointer at offset 0. -/
def findFunct (ge : Genv F V) (v : Val) : Option F :=
  match v with
  | .Vptr b ofs =>
      if Integers.Ptrofs.eq ofs Integers.Ptrofs.zero then findFunctPtr ge b else none
  | _ => none

/-- `Genv.find_var_info` -/
def findVarInfo (ge : Genv F V) (b : Block) : Option (GlobVar V) :=
  match findDef ge b with
  | some (.Gvar v) => some v
  | _ => none

/-- `Genv.invert_symbol` — which identifier denotes this block? -/
def invertSymbol (ge : Genv F V) (b : Block) : Option Ident :=
  (ge.genv_symb.elements.find? (fun p => p.2 = b)).map (·.1)

/-- `Genv.block_is_volatile` — is this block a volatile global?  (`Senv`.) -/
def blockIsVolatile (ge : Genv F V) (b : Block) : Bool :=
  match findVarInfo ge b with
  | some gv => gv.gvar_volatile
  | none => false

/-- `Genv.add_global` -/
def addGlobal (ge : Genv F V) (idg : Ident × GlobDef F V) : Genv F V :=
  { genv_public := ge.genv_public
    genv_symb := ge.genv_symb.set idg.1 ge.genv_next
    genv_defs := ge.genv_defs.set ge.genv_next idg.2
    genv_next := ge.genv_next.succ }

/-- `Genv.add_globals` -/
def addGlobals (ge : Genv F V) (gl : List (Ident × GlobDef F V)) : Genv F V :=
  gl.foldl addGlobal ge

/-- `Genv.empty_genv` -/
def emptyGenv (pub : List Ident) : Genv F V :=
  { genv_public := pub, genv_symb := PTree.empty,
    genv_defs := PTree.empty, genv_next := Positive.xH }

/-! ## Initial memory state -/

/-- `Globalenvs.store_zeros`.  Rocq uses well-founded recursion on `n`; we
    recurse structurally on a `Nat` count, equivalent for `n ≥ 0`. -/
def storeZerosAux (m : Mem) (b : Block) (p : Z) : Nat → Option Mem
  | 0 => some m
  | n + 1 =>
      match Mem.store .Mint8unsigned m b p (.Vint Integers.Int.zero) with
      | none => none
      | some m' => storeZerosAux m' b (p + 1) n

def storeZeros (m : Mem) (b : Block) (p n : Z) : Option Mem :=
  storeZerosAux m b p n.toNat

/-- `Genv.store_init_data` -/
def storeInitData (ge : Genv F V) (m : Mem) (b : Block) (p : Z)
    (id : InitData) : Option Mem :=
  match id with
  | .Init_int8 n => Mem.store .Mint8unsigned m b p (.Vint n)
  | .Init_int16 n => Mem.store .Mint16unsigned m b p (.Vint n)
  | .Init_int32 n => Mem.store .Mint32 m b p (.Vint n)
  | .Init_int64 n => Mem.store .Mint64 m b p (.Vlong n)
  | .Init_float32 n => Mem.store .Mfloat32 m b p (.Vsingle n)
  | .Init_float64 n => Mem.store .Mfloat64 m b p (.Vfloat n)
  | .Init_addrof symb ofs =>
      match findSymbol ge symb with
      | none => none
      | some b' => Mem.store Mptr m b p (.Vptr b' ofs)
  | .Init_space _ => some m

/-- `Genv.store_init_data_list` -/
def storeInitDataList (ge : Genv F V) (m : Mem) (b : Block) (p : Z) :
    List InitData → Option Mem
  | [] => some m
  | id :: idl' =>
      match storeInitData ge m b p id with
      | none => none
      | some m' => storeInitDataList ge m' b (p + id.size) idl'

/-- `Genv.perm_globvar` — the final permission of a global. -/
def permGlobvar (gv : GlobVar V) : Permission :=
  if gv.gvar_volatile then .Nonempty
  else if gv.gvar_readonly then .Readable
  else .Writable

/-- `Genv.alloc_global` — allocate and initialize one global definition. -/
def allocGlobal (ge : Genv F V) (m : Mem) (idg : Ident × GlobDef F V) : Option Mem :=
  match idg.2 with
  | .Gfun _ =>
      let (m1, b) := Mem.alloc m 0 1
      Mem.dropPerm m1 b 0 1 .Nonempty
  | .Gvar v =>
      let init := v.gvar_init
      let sz := InitData.listSize init
      let (m1, b) := Mem.alloc m 0 sz
      match storeZeros m1 b 0 sz with
      | none => none
      | some m2 =>
          match storeInitDataList ge m2 b 0 init with
          | none => none
          | some m3 => Mem.dropPerm m3 b 0 sz (permGlobvar v)

/-- `Genv.alloc_globals` -/
def allocGlobals (ge : Genv F V) (m : Mem) :
    List (Ident × GlobDef F V) → Option Mem
  | [] => some m
  | g :: gl' =>
      match allocGlobal ge m g with
      | none => none
      | some m' => allocGlobals ge m' gl'

/-! ## The dropped `Genv` invariants, recovered as lemmas

The header explains why `Genv` carries no `Prop` fields: nothing in
`Clight.step` consumes them.  *Determinism* of that relation does — CompCert's
`Senv.t` exposes `genv_vars_inj` as `find_symbol_injective`, and
`Events.match_traces` needs it to pin the identifier recorded in a volatile
event: two identifiers naming one block would let a single step emit two
unrelated events.  So here are the two invariants, proved about `addGlobals`
rather than carried by the record, exactly as the header anticipated. -/

/-- CompCert's `genv_symb_range`: every symbol denotes an allocated block. -/
def SymbBelow (ge : Genv F V) : Prop :=
  ∀ id b, findSymbol ge id = some b → b < ge.genv_next

/-- CompCert's `genv_vars_inj`: distinct identifiers denote distinct blocks. -/
def SymbInjective (ge : Genv F V) : Prop :=
  ∀ id1 id2 b, findSymbol ge id1 = some b → findSymbol ge id2 = some b → id1 = id2

theorem symbBelow_emptyGenv (pub : List Ident) :
    SymbBelow (emptyGenv pub : Genv F V) := by
  intro id b h; simp [findSymbol, emptyGenv] at h

theorem symbInjective_emptyGenv (pub : List Ident) :
    SymbInjective (emptyGenv pub : Genv F V) := by
  intro id1 id2 b h _; simp [findSymbol, emptyGenv] at h

theorem symbBelow_addGlobal {ge : Genv F V} (idg : Ident × GlobDef F V)
    (h : SymbBelow ge) : SymbBelow (addGlobal ge idg) := by
  intro id b hb
  have hlt : b.toNat < ge.genv_next.toNat + 1 := by
    by_cases hid : idg.1 = id
    · subst hid
      simp only [findSymbol, addGlobal, PTree.gss] at hb
      injection hb with hb
      subst hb
      omega
    · simp only [findSymbol, addGlobal] at hb
      rw [PTree.gso _ _ _ _ hid] at hb
      have := (Positive.lt_iff _ _).1 (h id b hb)
      omega
  show b.toNat < (addGlobal ge idg).genv_next.toNat
  simpa [addGlobal] using hlt

theorem symbInjective_addGlobal {ge : Genv F V} (idg : Ident × GlobDef F V)
    (hb : SymbBelow ge) (h : SymbInjective ge) : SymbInjective (addGlobal ge idg) := by
  intro id1 id2 b h1 h2
  simp only [findSymbol, addGlobal] at h1 h2
  by_cases hd1 : idg.1 = id1
  · by_cases hd2 : idg.1 = id2
    · exact hd1.symm.trans hd2
    · rw [PTree.gso _ _ _ _ hd2] at h2
      subst hd1
      rw [PTree.gss] at h1
      injection h1 with h1
      subst h1
      exact absurd ((Positive.lt_iff _ _).1 (hb _ _ h2)) (Nat.lt_irrefl _)
  · by_cases hd2 : idg.1 = id2
    · rw [PTree.gso _ _ _ _ hd1] at h1
      subst hd2
      rw [PTree.gss] at h2
      injection h2 with h2
      subst h2
      exact absurd ((Positive.lt_iff _ _).1 (hb _ _ h1)) (Nat.lt_irrefl _)
    · rw [PTree.gso _ _ _ _ hd1] at h1
      rw [PTree.gso _ _ _ _ hd2] at h2
      exact h id1 id2 b h1 h2

theorem symbBelow_addGlobals {ge : Genv F V} (gl : List (Ident × GlobDef F V))
    (h : SymbBelow ge) : SymbBelow (addGlobals ge gl) := by
  induction gl generalizing ge with
  | nil => exact h
  | cons g gl' ih =>
      show SymbBelow (addGlobals (addGlobal ge g) gl')
      exact ih (symbBelow_addGlobal g h)

theorem symbInjective_addGlobals {ge : Genv F V} (gl : List (Ident × GlobDef F V))
    (hb : SymbBelow ge) (h : SymbInjective ge) : SymbInjective (addGlobals ge gl) := by
  induction gl generalizing ge with
  | nil => exact h
  | cons g gl' ih =>
      show SymbInjective (addGlobals (addGlobal ge g) gl')
      exact ih (symbBelow_addGlobal g hb) (symbInjective_addGlobal g hb h)

/-- The invariant CompCert's `Genv.t` carries, for an environment built the only
    way a program builds one (`Program.globalenv` is `addGlobals` over
    `emptyGenv`). -/
theorem symbInjective_globalenv (pub : List Ident) (gl : List (Ident × GlobDef F V)) :
    SymbInjective (addGlobals (emptyGenv pub) gl) :=
  symbInjective_addGlobals gl (symbBelow_emptyGenv pub) (symbInjective_emptyGenv pub)

end Genv
end CC
