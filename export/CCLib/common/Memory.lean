/-
  The memory model — port of `common/Memory.v` lines 36–608 (the operational
  core).  The remaining ~4000 lines of that file are the lemma library
  (`load_store_*`, `perm_alloc_*`, …) plus the memory-injection and
  memory-extension theories used only by CompCert's pass proofs; those are ported
  on demand.

  `Memtype.v` (1244 lines) is a pure `Module Type MEM` specification — nothing to
  port, but it is the best available spec document for what these operations
  guarantee.

  ## Proof-carrying record

  As in CompCert, `Mem` carries its three invariants as fields:

    * `access_max`         — current permissions never exceed maximal ones
    * `nextblock_noaccess` — blocks beyond `nextblock` have no permissions
    * `contents_default`   — the default content of every block is `Undef`

  In Rocq each constructor is a `Program Definition` discharging these as
  obligations (15 in total across the file), and record equality needs the
  classical `proof_irr` axiom from `lib/Axioms.v`.  In Lean `Prop` is
  definitionally proof-irrelevant, so equality of memories follows from equality
  of the three data fields with no axiom at all — see `Mem.ext`.

  Allocation never fails: CompCert models an infinite memory.
-/
import CCLib.lib.Maps
import CCLib.common.Memdata

namespace CC

/-! ## Permissions -/

/-- `Memtype.permission` -/
inductive Permission where
  | Freeable | Writable | Readable | Nonempty
  deriving DecidableEq, Repr, Inhabited

/-- `Memtype.perm_kind` -/
inductive PermKind where
  | Max | Cur
  deriving DecidableEq, Repr, Inhabited

/-- Numeric rank; `perm_order p q` iff `rank p ≥ rank q`.  This is exactly the
    reflexive-transitive closure of CompCert's `perm_order` constructors
    (`perm_refl`, `perm_F_any`, `perm_W_R`, `perm_any_N`). -/
def Permission.rank : Permission → Nat
  | .Freeable => 4 | .Writable => 3 | .Readable => 2 | .Nonempty => 1

/-- `Memtype.perm_order` (as a `Bool`). -/
def permOrder (p q : Permission) : Bool := q.rank ≤ p.rank

/-- `Memory.perm_order'` -/
def permOrder' : Option Permission → Permission → Bool
  | some p', p => permOrder p' p
  | none, _ => false

/-- `Memory.perm_order''` -/
def permOrder'' : Option Permission → Option Permission → Bool
  | some p1, some p2 => permOrder p1 p2
  | _, none => true
  | none, some _ => false

/-! ## The memory state -/

/-- `Memory.mem` — a proof-carrying record, as in CompCert. -/
structure Mem where
  contents : PMap (ZMap MemVal)
  access : PMap (Z → PermKind → Option Permission)
  nextblock : Block
  access_max : ∀ b ofs,
    permOrder'' (PMap.get b access ofs .Max) (PMap.get b access ofs .Cur) = true
  nextblock_noaccess : ∀ b ofs k,
    ¬ (b < nextblock) → PMap.get b access ofs k = none
  contents_default : ∀ b, (PMap.get b contents).dflt = MemVal.Undef

namespace Mem

/-- `Memory.mkmem_ext`.  In Rocq this needs the `proof_irr` axiom; in Lean
    proof irrelevance is definitional, so it is just `congr`. -/
theorem ext {m1 m2 : Mem}
    (hc : m1.contents = m2.contents) (ha : m1.access = m2.access)
    (hn : m1.nextblock = m2.nextblock) : m1 = m2 := by
  cases m1; cases m2; cases hc; cases ha; cases hn; rfl

/-! ## Validity and permissions -/

/-- `Memory.valid_block` -/
def validBlock (m : Mem) (b : Block) : Bool := b < m.nextblock

/-- `Memory.perm` (as a `Bool`; CompCert states it as a `Prop` with a separate
    `perm_dec`). -/
def perm (m : Mem) (b : Block) (ofs : Z) (k : PermKind) (p : Permission) : Bool :=
  permOrder' (PMap.get b m.access ofs k) p

/-- Number of offsets in `[lo, hi)`. -/
private def spanNat (lo hi : Z) : Nat := (hi - lo).toNat

private def rangePermAux (m : Mem) (b : Block) (ofs : Z) (n : Nat)
    (k : PermKind) (p : Permission) : Bool :=
  match n with
  | 0 => true
  | n + 1 => perm m b ofs k p && rangePermAux m b (ofs + 1) n k p

/-- `Memory.range_perm` (decided).  CompCert states it as a `∀` over the range,
    with `range_perm_dec` as the decision procedure; we give the decision
    procedure directly. -/
def rangePerm (m : Mem) (b : Block) (lo hi : Z) (k : PermKind) (p : Permission) : Bool :=
  rangePermAux m b lo (spanNat lo hi) k p

-- NOTE: these lemmas spell their numeric binders `Int` rather than the `Z`
-- abbreviation.  `omega` matches on the head symbol and does not see through
-- `abbrev Z := Int`, so a `Z`-typed hypothesis is invisible to it.  The two are
-- the same type, so the lemmas still apply to `Z`-typed arguments.

private theorem rangePermAux_perm (m : Mem) (b : Block) (k : PermKind)
    (p : Permission) :
    ∀ (n : Nat) (base ofs : Int), rangePermAux m b base n k p = true →
      base ≤ ofs → ofs < base + (n : Int) → perm m b ofs k p = true := by
  intro n
  induction n with
  | zero => intro base ofs _ h1 h2; omega
  | succ n ih =>
    intro base ofs h h1 h2
    rw [rangePermAux, Bool.and_eq_true] at h
    by_cases he : ofs = base
    · subst he; exact h.1
    · exact ih (base + 1) ofs h.2 (by omega) (by omega)

/-- Inversion for `rangePerm`: it really does give a permission at each offset.
    (CompCert gets this from the `∀`-shaped definition; we decide the range, so
    the inversion has to be proved.  Phase 4 needs it too.) -/
theorem rangePerm_perm (m : Mem) (b : Block) (lo hi : Int) (k : PermKind)
    (p : Permission) (h : rangePerm m b lo hi k p = true) (ofs : Int)
    (h1 : lo ≤ ofs) (h2 : ofs < hi) : perm m b ofs k p = true := by
  refine rangePermAux_perm m b k p (spanNat lo hi) lo ofs h h1 ?_
  simp only [spanNat]
  omega

/-- Converse of `rangePerm_perm`: build a `rangePerm` from pointwise permissions.
    Lives here because `rangePermAux`/`spanNat` are `private`; Phase-7 proofs
    outside this file need a way to *introduce* a `rangePerm`, not just use one. -/
theorem rangePerm_intro (m : Mem) (b : Block) (lo hi : Int) (k : PermKind)
    (p : Permission) (h : ∀ ofs : Int, lo ≤ ofs → ofs < hi → perm m b ofs k p = true) :
    rangePerm m b lo hi k p = true := by
  simp only [rangePerm]
  suffices hgen : ∀ (n : Nat) (lo' : Int),
      (∀ ofs : Int, lo' ≤ ofs → ofs < lo' + (n : Int) → perm m b ofs k p = true) →
      rangePermAux m b lo' n k p = true by
    refine hgen (spanNat lo hi) lo (fun ofs h1 h2 => h ofs h1 ?_)
    simp only [spanNat] at h2
    omega
  intro n
  induction n with
  | zero => intro lo' _; rfl
  | succ j ih =>
      intro lo' hall
      simp only [rangePermAux, Bool.and_eq_true]
      refine ⟨hall lo' (Int.le_refl _) (by omega), ih (lo' + 1) (fun ofs h1 h2 => ?_)⟩
      exact hall ofs (by omega) (by omega)

/-- A block carrying any permission is below `nextblock`. -/
theorem perm_valid_block (m : Mem) (b : Block) (ofs : Int) (k : PermKind)
    (p : Permission) (h : perm m b ofs k p = true) : b < m.nextblock := by
  match Nat.lt_or_ge b.toNat m.nextblock.toNat with
  | .inl hlt => exact hlt
  | .inr hge =>
      have hb : ¬ (b < m.nextblock) := by
        rw [Positive.lt_iff]; exact Nat.not_lt.mpr hge
      rw [perm, m.nextblock_noaccess b ofs k hb] at h
      simp [permOrder'] at h

/-- `Memory.valid_access` (decided): permissions over the whole chunk, plus
    natural alignment. -/
def validAccess (m : Mem) (chunk : Chunk) (b : Block) (ofs : Z)
    (p : Permission) : Bool :=
  rangePerm m b ofs (ofs + sizeChunk chunk) .Cur p && (ofs % alignChunk chunk == 0)

/-- `Memory.valid_pointer` -/
def validPointer (m : Mem) (b : Block) (ofs : Z) : Bool :=
  perm m b ofs .Cur .Nonempty

/-- `Memory.weak_valid_pointer` — valid at `ofs`, or just past the end at
    `ofs - 1` (C allows one-past-the-end pointers to be compared). -/
def weakValidPointer (m : Mem) (b : Block) (ofs : Z) : Bool :=
  validPointer m b ofs || validPointer m b (ofs - 1)

/-! ## Reading and writing byte sequences -/

/-- `Memory.getN` -/
def getN (n : Nat) (p : Z) (c : ZMap MemVal) : List MemVal :=
  match n with
  | 0 => []
  | n + 1 => ZMap.get p c :: getN n (p + 1) c

/-- `Memory.setN` -/
def setN (vl : List MemVal) (p : Z) (c : ZMap MemVal) : ZMap MemVal :=
  match vl with
  | [] => c
  | v :: vl' => setN vl' (p + 1) (ZMap.set p v c)

/-- `setN` preserves the default cell, which keeps `contents_default` true. -/
@[simp] theorem dflt_setN (vl : List MemVal) (p : Z) (c : ZMap MemVal) :
    (setN vl p c).dflt = c.dflt := by
  induction vl generalizing p c with
  | nil => rfl
  | cons v vl' ih => rw [setN, ih]; rfl

/-! ## The empty memory -/

/-- `Memory.empty` -/
def empty : Mem where
  contents := PMap.init (ZMap.init MemVal.Undef)
  access := PMap.init (fun _ _ => none)
  nextblock := Positive.xH
  access_max := by intro b ofs; rw [PMap.gi]; rfl
  nextblock_noaccess := by intro b ofs k _; rw [PMap.gi]
  contents_default := by intro b; rw [PMap.gi]; rfl

/-! ## Allocation -/

/-- `Memory.alloc` — returns the updated memory and the fresh block.  Never
    fails (infinite memory). -/
def alloc (m : Mem) (lo hi : Z) : Mem × Block :=
  ( { contents := PMap.set m.nextblock (ZMap.init MemVal.Undef) m.contents
      access := PMap.set m.nextblock
        (fun ofs _ => if lo ≤ ofs ∧ ofs < hi then some .Freeable else none)
        m.access
      nextblock := m.nextblock.succ
      access_max := by
        intro b ofs
        rw [PMap.gsspec]
        split
        · dsimp only; split <;> rfl
        · exact m.access_max b ofs
      nextblock_noaccess := by
        intro b ofs k hb
        rw [Positive.lt_iff, Positive.toNat_succ] at hb
        have hne : b ≠ m.nextblock := by intro h; subst h; omega
        have hlt : ¬ (b < m.nextblock) := by rw [Positive.lt_iff]; omega
        rw [PMap.gsspec, if_neg hne]
        exact m.nextblock_noaccess b ofs k hlt
      contents_default := by
        intro b
        rw [PMap.gsspec]
        split
        · rfl
        · exact m.contents_default b },
    m.nextblock )

/-! ## Freeing -/

/-- `Memory.unchecked_free` — drop permissions on `[lo, hi)` of block `b`. -/
def uncheckedFree (m : Mem) (b : Block) (lo hi : Z) : Mem where
  contents := m.contents
  access := PMap.set b
    (fun ofs k => if lo ≤ ofs ∧ ofs < hi then none else PMap.get b m.access ofs k)
    m.access
  nextblock := m.nextblock
  access_max := by
    intro b' ofs
    rw [PMap.gsspec]
    split
    · next h =>
        subst h
        dsimp only
        split
        · rfl
        · exact m.access_max b' ofs
    · exact m.access_max b' ofs
  nextblock_noaccess := by
    intro b' ofs k hb
    rw [PMap.gsspec]
    split
    · next h =>
        subst h
        dsimp only
        split
        · rfl
        · exact m.nextblock_noaccess b' ofs k hb
    · exact m.nextblock_noaccess b' ofs k hb
  contents_default := m.contents_default

/-- `Memory.free` — fails unless the whole range is `Freeable`. -/
def free (m : Mem) (b : Block) (lo hi : Z) : Option Mem :=
  if rangePerm m b lo hi .Cur .Freeable
  then some (uncheckedFree m b lo hi) else none

/-- `Memory.free_list` -/
def freeList (m : Mem) : List (Block × Z × Z) → Option Mem
  | [] => some m
  | (b, lo, hi) :: l' =>
      match free m b lo hi with
      | none => none
      | some m' => freeList m' l'

/-! ## Loads -/

/-- `Memory.load` -/
def load (chunk : Chunk) (m : Mem) (b : Block) (ofs : Z) : Option Val :=
  if validAccess m chunk b ofs .Readable
  then some (decodeVal chunk (getN (sizeChunkNat chunk) ofs (PMap.get b m.contents)))
  else none

/-- `Memory.loadv` — address given as a value.  As in CompCert, the access
    must not wrap around the end of the address space
    (`unsigned ofs + size_chunk chunk ≤ Ptrofs.modulus`). -/
def loadv (chunk : Chunk) (m : Mem) (addr : Val) : Option Val :=
  match addr with
  | .Vptr b ofs =>
      if Integers.Ptrofs.unsigned ofs + sizeChunk chunk ≤ Integers.Ptrofs.modulus
      then load chunk m b (Integers.Ptrofs.unsigned ofs) else none
  | _ => none

/-- `Memory.loadbytes` -/
def loadbytes (m : Mem) (b : Block) (ofs n : Z) : Option (List MemVal) :=
  if rangePerm m b ofs (ofs + n) .Cur .Readable
  then some (getN n.toNat ofs (PMap.get b m.contents))
  else none

/-! ## Stores -/

/-- Rebuild a memory with new contents, reusing the permission structure.
    Factors out the obligation proofs shared by `store` and `storebytes`
    (both leave `access` and `nextblock` untouched). -/
private def withContents (m : Mem) (b : Block) (c : ZMap MemVal)
    (hc : c.dflt = MemVal.Undef) : Mem where
  contents := PMap.set b c m.contents
  access := m.access
  nextblock := m.nextblock
  access_max := m.access_max
  nextblock_noaccess := m.nextblock_noaccess
  contents_default := by
    intro b'
    rw [PMap.gsspec]
    split
    · exact hc
    · exact m.contents_default b'

/-- The contents written by a store always have `Undef` as their default, so the
    `contents_default` invariant survives. -/
private theorem dflt_setN_block (m : Mem) (b : Block) (vl : List MemVal) (ofs : Z) :
    (setN vl ofs (PMap.get b m.contents)).dflt = MemVal.Undef := by
  rw [dflt_setN]; exact m.contents_default b

/-- `Memory.store` -/
def store (chunk : Chunk) (m : Mem) (b : Block) (ofs : Z) (v : Val) : Option Mem :=
  if validAccess m chunk b ofs .Writable
  then some (withContents m b (setN (encodeVal chunk v) ofs (PMap.get b m.contents))
              (dflt_setN_block m b _ ofs))
  else none

/-- `Memory.storev` (with the same no-wrap-around check as `loadv`). -/
def storev (chunk : Chunk) (m : Mem) (addr v : Val) : Option Mem :=
  match addr with
  | .Vptr b ofs =>
      if Integers.Ptrofs.unsigned ofs + sizeChunk chunk ≤ Integers.Ptrofs.modulus
      then store chunk m b (Integers.Ptrofs.unsigned ofs) v else none
  | _ => none

/-- `Memory.storebytes` -/
def storebytes (m : Mem) (b : Block) (ofs : Z) (bytes : List MemVal) : Option Mem :=
  if rangePerm m b ofs (ofs + (bytes.length : Z)) .Cur .Writable
  then some (withContents m b (setN bytes ofs (PMap.get b m.contents))
              (dflt_setN_block m b _ ofs))
  else none

/-! ## Dropping permissions (`Memory.drop_perm`)

Used by `Genv.alloc_global` to set the final permissions of a global. -/

/-- `Memory.drop_perm` — set permissions on `[lo, hi)` of `b` to exactly `p`.
    Fails unless the range is currently `Freeable`. -/
def dropPerm (m : Mem) (b : Block) (lo hi : Z) (p : Permission) : Option Mem :=
  if h : rangePerm m b lo hi .Cur .Freeable = true then
    some { contents := m.contents
           access := PMap.set b
             (fun ofs k => if lo ≤ ofs ∧ ofs < hi then some p
                           else PMap.get b m.access ofs k)
             m.access
           nextblock := m.nextblock
           access_max := by
             intro b' ofs
             rw [PMap.gsspec]
             split
             · next hb =>
                 subst hb
                 dsimp only
                 split
                 · simp [permOrder'', permOrder]
                 · exact m.access_max b' ofs
             · exact m.access_max b' ofs
           nextblock_noaccess := by
             intro b' ofs k hb
             rw [PMap.gsspec]
             split
             · next hbe =>
                 subst hbe
                 dsimp only
                 split
                 · next hr =>
                     -- in range, so the range is nonempty and `h` gives a
                     -- permission at `ofs`, forcing `b' < nextblock`
                     exact absurd (perm_valid_block m b' ofs .Cur .Freeable
                       (rangePerm_perm m b' lo hi .Cur .Freeable h ofs hr.1 hr.2)) hb
                 · exact m.nextblock_noaccess b' ofs k hb
             · exact m.nextblock_noaccess b' ofs k hb
           contents_default := m.contents_default }
  else none

end Mem
end CC
