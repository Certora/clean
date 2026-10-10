/-
  Finite and total maps — port of the parts of `lib/Maps.v` (2023 lines) that the
  semantics needs: `PTree` (finite map from `positive`), `PMap` (total map with a
  default), `ZMap` (total map keyed by `Z`).

  Used by: `Mem.mem` (`PMap.t (ZMap.t memval)` and `PMap.t (Z → perm_kind →
  option permission)`), `Clight.env`/`temp_env`, `Ctypes.composite_env`, `Genv`.

  ## Representation difference from CompCert 3.18

  CompCert ≥3.11 uses a *canonical* 7-constructor `tree'` representation
  precisely so that `PTree.extensionality` holds structurally (equal contents ⇒
  equal trees).  We use the classic 3-constructor trie instead:

      inductive PTree A | Leaf | Node (l) (o : Option A) (r)

  which is simpler but NOT canonical: `Node Leaf none Leaf` and `Leaf` have the
  same contents yet differ structurally.  Consequences, and why this is fine
  here: every lemma the semantics actually needs is about `get` results
  (`gss`, `gso`, `gempty`), which hold regardless.  Only proofs that conclude
  *tree* or *memory* equality from equal contents would need canonicity; if such
  a proof is needed later, either normalize on `set` or switch to the 7-ctor
  form.  This is recorded as a known deviation.
-/
import CCLib.Positive

namespace CC

/-! ## `PTree` — finite maps keyed by `positive` -/

inductive PTree (A : Type) where
  | Leaf
  | Node (l : PTree A) (o : Option A) (r : PTree A)
  deriving Inhabited

namespace PTree
variable {A B : Type}

/-- `PTree.empty` -/
def empty : PTree A := Leaf

/-- `PTree.get` -/
def get (i : Positive) (m : PTree A) : Option A :=
  match i, m with
  | _, Leaf => none
  | .xH, Node _ o _ => o
  | .xO ii, Node l _ _ => get ii l
  | .xI ii, Node _ _ r => get ii r

/-- `PTree.set` -/
def set (i : Positive) (v : A) (m : PTree A) : PTree A :=
  match i, m with
  | .xH, Leaf => Node Leaf (some v) Leaf
  | .xH, Node l _ r => Node l (some v) r
  | .xO ii, Leaf => Node (set ii v Leaf) none Leaf
  | .xO ii, Node l o r => Node (set ii v l) o r
  | .xI ii, Leaf => Node Leaf none (set ii v Leaf)
  | .xI ii, Node l o r => Node l o (set ii v r)

/-- `PTree.remove` (no re-normalization; see the header note on canonicity). -/
def remove (i : Positive) (m : PTree A) : PTree A :=
  match i, m with
  | _, Leaf => Leaf
  | .xH, Node l _ r => Node l none r
  | .xO ii, Node l o r => Node (remove ii l) o r
  | .xI ii, Node l o r => Node l o (remove ii r)

/-- `PTree.map1` — map a function over all bound values. -/
def map1 (f : A → B) (m : PTree A) : PTree B :=
  match m with
  | Leaf => Leaf
  | Node l o r => Node (map1 f l) (o.map f) (map1 f r)

/-- Key reached by a root-first path, stored deepest-first. -/
private def keyOfRevPath (revPath : List Bool) : Positive :=
  revPath.foldl (fun acc b => if b then Positive.xI acc else Positive.xO acc) Positive.xH

private def elemsAux (m : PTree A) (revPath : List Bool)
    (acc : List (Positive × A)) : List (Positive × A) :=
  match m with
  | Leaf => acc
  | Node l o r =>
      let acc := elemsAux r (true :: revPath) acc
      let acc := match o with
                 | some v => (keyOfRevPath revPath, v) :: acc
                 | none => acc
      elemsAux l (false :: revPath) acc

/-- `PTree.elements` — the bindings, as an association list.

    NOTE: the *order* need not match CompCert's `elements`.  The only consumer
    in the Clight semantics is `blocks_of_env` feeding `Mem.free_list`, whose
    result is order-independent (the blocks are pairwise distinct). -/
def elements (m : PTree A) : List (Positive × A) := elemsAux m [] []

@[simp] theorem get_leaf (i : Positive) : get i (Leaf : PTree A) = none := by
  cases i <;> rfl

@[simp] theorem gempty (i : Positive) : get i (empty : PTree A) = none := by
  cases i <;> rfl

/-- `PTree.gss` — reading back what was just written. -/
@[simp] theorem gss (i : Positive) (v : A) (m : PTree A) :
    get i (set i v m) = some v := by
  induction i generalizing m with
  | xH => cases m <;> rfl
  | xO ii ih => cases m <;> simp [get, set, ih]
  | xI ii ih => cases m <;> simp [get, set, ih]

/-- `PTree.gso` — writing one key does not disturb another. -/
theorem gso (i j : Positive) (v : A) (m : PTree A) (h : i ≠ j) :
    get j (set i v m) = get j m := by
  induction i generalizing j m with
  | xH =>
    cases j with
    | xH => exact absurd rfl h
    | xO jj => cases m <;> simp [get, set]
    | xI jj => cases m <;> simp [get, set]
  | xO ii ih =>
    cases j with
    | xH => cases m <;> simp [get, set]
    | xO jj =>
      have hne : ii ≠ jj := fun hh => h (by rw [hh])
      cases m <;> simp [get, set, ih jj _ hne]
    | xI jj => cases m <;> simp [get, set]
  | xI ii ih =>
    cases j with
    | xH => cases m <;> simp [get, set]
    | xO jj => cases m <;> simp [get, set]
    | xI jj =>
      have hne : ii ≠ jj := fun hh => h (by rw [hh])
      cases m <;> simp [get, set, ih jj _ hne]

end PTree

/-! ## `PMap` — total maps keyed by `positive` (a default plus a `PTree`) -/

structure PMap (A : Type) where
  dflt : A
  tree : PTree A
  deriving Inhabited

namespace PMap
variable {A : Type}

/-- `PMap.init` -/
def init (x : A) : PMap A := ⟨x, PTree.empty⟩
/-- `PMap.get` -/
def get (i : Positive) (m : PMap A) : A := (m.tree.get i).getD m.dflt
/-- `PMap.set` -/
def set (i : Positive) (v : A) (m : PMap A) : PMap A := ⟨m.dflt, m.tree.set i v⟩

@[simp] theorem gi (i : Positive) (x : A) : get i (init x) = x := by
  simp [get, init]

@[simp] theorem gss (i : Positive) (v : A) (m : PMap A) : get i (set i v m) = v := by
  simp [get, set]

theorem gso (i j : Positive) (v : A) (m : PMap A) (h : i ≠ j) :
    get j (set i v m) = get j m := by
  simp [get, set, PTree.gso i j v m.tree h]

/-- `PMap.gsspec` — the workhorse for reasoning about updated memories. -/
theorem gsspec (i j : Positive) (v : A) (m : PMap A) :
    get j (set i v m) = if j = i then v else get j m := by
  by_cases h : j = i
  · subst h; simp
  · simp [h, gso i j v m (Ne.symm h)]

/-- `set` preserves the default, which is what keeps `contents_default` true. -/
@[simp] theorem dflt_set (i : Positive) (v : A) (m : PMap A) :
    (set i v m).dflt = m.dflt := rfl

end PMap

/-! ## `ZMap` — total maps keyed by `Z`

`lib/Maps.v` builds this as `IMap(ZIndexed)`, i.e. a `PMap` under the injection
`ZIndexed.index : Z → positive`. -/

namespace ZIndexed

/-- `ZIndexed.index`: `0 ↦ xH`, `Zpos p ↦ xO p`, `Zneg p ↦ xI p`. -/
def index (z : Int) : Positive :=
  match z with
  | .ofNat 0 => .xH
  | .ofNat n => .xO (Positive.ofNat n)
  | .negSucc n => .xI (Positive.ofNat (n + 1))

end ZIndexed

/-- Total map keyed by `Z` (CompCert `ZMap.t`). -/
abbrev ZMap (A : Type) := PMap A

namespace ZMap
variable {A : Type}

def init (x : A) : ZMap A := PMap.init x
def get (i : Int) (m : ZMap A) : A := PMap.get (ZIndexed.index i) m
def set (i : Int) (v : A) (m : ZMap A) : ZMap A := PMap.set (ZIndexed.index i) v m

@[simp] theorem gi (i : Int) (x : A) : get i (init x) = x := by
  simp [get, init]

@[simp] theorem gss (i : Int) (v : A) (m : ZMap A) : get i (set i v m) = v := by
  simp [get, set]

end ZMap

end CC
