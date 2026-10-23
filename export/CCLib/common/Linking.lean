/-
  **Phase 9, Step 1 (Wave C) — cross-module linking.**

  `clightgen` emits one `.lean` per translation unit, and it rejects `-o` when
  given several inputs, so zlib arrives as nine separate `Program`s.  `compress`
  lives in compress.c and `deflate` in deflate.c, so the call appears in the
  first as `EF_external "deflate"` and the body only exists in the second.
  `Sep.closure` wants **one** program.

  Phase 0 deliberately dropped CompCert's `common/Linking.v` (936 lines) as an
  avoidable dependency.  This reverses that — but **ports the function, not the
  theory**.  Nothing here proves a compiler pass correct, so the linking
  *theorems* (`link_linkorder`, `match_program` transitivity, …) are not needed;
  only a merge that computes, plus the fact that `Genv.findFunct` then resolves,
  which is itself computation.

  What it does, following `link_fundef` / `link_def`:

  * an `External` **declaration** resolves against an `Internal` **definition**
    (either order), provided the declared signature matches;
  * two `External`s with the same shape merge to one;
  * two `Internal`s for the same identifier are a **conflict** (`none`) — that is
    a genuine duplicate-symbol error, not something to paper over;
  * globals merge when one side is an `extern` declaration (empty `gvar_init`);
  * composites merge by name, and the merged `prog_comp_env` is **rebuilt** with
    the existing `buildCompositeEnv`, so it is not stitched together by hand.

  A prerequisite discovered while implementing this (and not anticipated by the
  plan): every generated module used to declare `prog`, `composites`,
  `___builtin_fabsf`, … at the **root** namespace, so two of them could not be
  imported into one Lean file at all — `import` failed outright.  The exporter
  (`export/ExportLeanClight.ml`) now wraps each module in a namespace derived
  from its source basename (`deflate.c` -> `namespace Deflate`).  Without that,
  this file would have nothing to link.
-/
import CCLib.cfrontend.Clight

namespace CC
namespace Link

/-! ## Signatures and declarations -/

/-- Do two external declarations of the same function agree?  This is
    `link_fundef`'s side condition: same external function, same argument and
    result types, same calling convention. -/
def extMatches (ef1 : ExtFun) (targs1 : List Ty) (tres1 : Ty) (cc1 : CallConv)
    (ef2 : ExtFun) (targs2 : List Ty) (tres2 : Ty) (cc2 : CallConv) : Bool :=
  ef1 == ef2 && targs1 == targs2 && tres1 == tres2 && cc1 == cc2

/-- Does an `EF_external` declaration match an internal definition's own
    signature?  CompCert's `link_fundef` compares the *signature* of the external
    against `signature_of_function`; here the same check is expressed on the
    Clight function's parameter and return types.

    Note this deliberately ignores the `ExtFun`'s `Signature`: `clightgen` derives
    it from the very same C declaration, and comparing `ATyp` lists would reject
    nothing a type comparison accepts while adding a second failure mode. -/
def declMatchesDef (targs : List Ty) (tres : Ty) (cc : CallConv)
    (f : Function) : Bool :=
  targs == f.fn_params.map (fun p => p.2) && tres == f.fn_return
    && cc == f.fn_callconv

/-- `Linking.link_fundef`, specialised to Clight.

    An `External` **declaration** is subsumed by an `Internal` **definition**;
    two declarations merge if identical; two definitions of the same name are a
    duplicate-symbol error. -/
def linkFundef : FunDef → FunDef → Option FunDef
  | .Internal _, .Internal _ => none          -- duplicate symbol
  | .Internal f, .External _ targs tres cc =>
      if declMatchesDef targs tres cc f then some (.Internal f) else none
  | .External _ targs tres cc, .Internal f =>
      if declMatchesDef targs tres cc f then some (.Internal f) else none
  | .External ef1 ta1 tr1 cc1, .External ef2 ta2 tr2 cc2 =>
      if extMatches ef1 ta1 tr1 cc1 ef2 ta2 tr2 cc2
      then some (.External ef1 ta1 tr1 cc1) else none

/-- `Ctypes.link_type`, cut down to the case linking actually needs: an
    **incomplete array type** completes against a sized one.

    This is not a nicety.  zlib's deflate.h declares
    `extern const uch _dist_code[];` and trees.c defines
    `const uch _dist_code[512] = {…}`; `clightgen` renders the declaration as
    `tarray uchar 0` and the definition as `tarray uchar 512`, so **plain type
    equality rejects the link**.  Found by linking the real nine modules — the
    first four linked fine and trees.c was the first to fail.

    Restriction, stated rather than hidden: CompCert's `link_type` also recurses
    through pointers and function types and merges attributes.  This handles the
    top-level array case only, which is all the round-trip set needs; anything
    else must be equal. -/
def linkTy (t1 t2 : Ty) : Option Ty :=
  if t1 == t2 then some t1
  else
    match t1, t2 with
    | .Tarray e1 n1 a1, .Tarray e2 n2 a2 =>
        if e1 == e2 && a1 == a2 then
          if n1 == 0 then some (.Tarray e2 n2 a2)
          else if n2 == 0 then some (.Tarray e1 n1 a1)
          else none
        else none
    | _, _ => none

/-- A global variable declaration (C `extern int x;`) has no initializer.  Such a
    declaration is subsumed by a definition, as in `link_vardef`. -/
def isVarDecl (v : GlobVar Ty) : Bool := v.gvar_init.isEmpty

/-- `Linking.link_vardef`, specialised: types must *link* (not merely be equal —
    see `linkTy`), qualifiers must agree; a declaration yields to a definition;
    two initialised definitions conflict unless identical.

    The surviving variable carries the **linked** type, so an incomplete array in
    the declaring module does not leak a `tarray … 0` into the linked program —
    which would give `sizeof` the wrong answer for every access to it. -/
def linkVar (v1 v2 : GlobVar Ty) : Option (GlobVar Ty) :=
  match linkTy v1.gvar_info v2.gvar_info with
  | none => none
  | some ty =>
      if v1.gvar_readonly != v2.gvar_readonly
          || v1.gvar_volatile != v2.gvar_volatile then none
      else if isVarDecl v1 then some { v2 with gvar_info := ty }
      else if isVarDecl v2 then some { v1 with gvar_info := ty }
      else if v1.gvar_init == v2.gvar_init then some { v1 with gvar_info := ty }
      else none

/-- `Linking.link_def`. -/
def linkGlobdef : GlobDef FunDef Ty → GlobDef FunDef Ty →
    Option (GlobDef FunDef Ty)
  | .Gfun f1, .Gfun f2 => (linkFundef f1 f2).map .Gfun
  | .Gvar v1, .Gvar v2 => (linkVar v1 v2).map .Gvar
  | _, _ => none                              -- a function and a variable clash

/-! ## Merging the definition lists

The merge preserves the **first** module's order and appends whatever is new in
the second, so a linked program's `prog_defs` reads as a concatenation.  That
matters for `Genv`: `Genv.addGlobals` assigns block numbers in list order, so a
stable order makes the resulting `Genv` predictable. -/

/-! ### The merge, with an index

**Complexity matters here, unusually for this project.**  The obvious
list-based merge (`find?` then `map` per definition) is O(n²) in definitions with
a `Positive` comparison at every step, and zlib's linked program has ~300 of
them.  Measured: the naive version made a single 9-way link take minutes.  So the
accumulator carries a **`PTree` index** alongside the list — `PTree` is already
here for `prog_comp_env` — which makes lookup logarithmic while the list keeps
the order `Genv.addGlobals` needs. -/

/-- Definitions being accumulated: the ordered list, plus an index for lookup. -/
structure DefAcc where
  order : List Ident                              -- insertion order, first wins
  defs : PTree (GlobDef FunDef Ty)

def DefAcc.ofList (ds : List (Ident × GlobDef FunDef Ty)) : DefAcc :=
  ds.foldl (fun a d =>
    match a.defs.get d.1 with
    | some _ => a                                  -- a unit cannot define twice
    | none => { order := a.order ++ [d.1], defs := a.defs.set d.1 d.2 }) 
    { order := [], defs := PTree.empty }

def DefAcc.toList (a : DefAcc) : List (Ident × GlobDef FunDef Ty) :=
  a.order.filterMap (fun i => (a.defs.get i).map (fun g => (i, g)))

/-- Insert one definition, linking on collision. -/
def insertDef (a : DefAcc) (d : Ident × GlobDef FunDef Ty) : Option DefAcc :=
  match a.defs.get d.1 with
  | none => some { order := a.order ++ [d.1], defs := a.defs.set d.1 d.2 }
  | some g0 =>
      match linkGlobdef g0 d.2 with
      | none => none
      | some g => some { a with defs := a.defs.set d.1 g }

/-- Fold `insertDef` over a list. -/
def mergeInto : DefAcc → List (Ident × GlobDef FunDef Ty) → Option DefAcc
  | a, [] => some a
  | a, d :: ds =>
      match insertDef a d with
      | none => none
      | some a' => mergeInto a' ds

/-- Merge two definition lists, keeping the left one's order. -/
def mergeDefs (l1 l2 : List (Ident × GlobDef FunDef Ty)) :
    Option (List (Ident × GlobDef FunDef Ty)) :=
  (mergeInto (DefAcc.ofList l1) l2).map DefAcc.toList

/-- Structural equality of composite *definitions*.  `CompositeDef` has no
    derived `DecidableEq` (`Ty`'s is hand-written), but `Member`'s is derived, so
    a field-by-field comparison needs nothing new in `Ctypes`. -/
def compositeDefBeq : CompositeDef → CompositeDef → Bool
  | .Composite id1 su1 m1 a1, .Composite id2 su2 m2 a2 =>
      id1 == id2 && su1 == su2 && m1 == m2 && a1 == a2

/-- Composites merge by name: a name defined in both modules must be defined
    *identically* (it comes from the same header in practice).  Indexed like the
    definitions, for the same reason. -/
structure CoAcc where
  order : List CompositeDef
  index : PTree CompositeDef

def CoAcc.ofList (cs : List CompositeDef) : CoAcc :=
  cs.foldl (fun a c =>
    match a.index.get c.name with
    | some _ => a
    | none => { order := a.order ++ [c], index := a.index.set c.name c })
    { order := [], index := PTree.empty }

def insertComposite (a : CoAcc) (c : CompositeDef) : Option CoAcc :=
  match a.index.get c.name with
  | none => some { order := a.order ++ [c], index := a.index.set c.name c }
  | some q => if compositeDefBeq q c then some a else none

def mergeCoInto : CoAcc → List CompositeDef → Option CoAcc
  | a, [] => some a
  | a, c :: cs =>
      match insertComposite a c with
      | none => none
      | some a' => mergeCoInto a' cs

def mergeComposites (l1 l2 : List CompositeDef) : Option (List CompositeDef) :=
  (mergeCoInto (CoAcc.ofList l1) l2).map (fun a => a.order)

/-! ## Programs -/

/-- Link two programs.  `prog_main` comes from the first (the one that has a
    `main`, by convention); publics are unioned; the composite environment is
    **rebuilt** from the merged composite list by `mkprogram`, so it is never
    stitched together by hand. -/
def linkProgram (p1 p2 : Program) : Option Program :=
  match mergeComposites p1.prog_types p2.prog_types with
  | none => none
  | some types =>
      match mergeDefs p1.prog_defs p2.prog_defs with
      | none => none
      | some defs =>
          let pub := p1.prog_public ++ p2.prog_public.filter
            (fun i => !p1.prog_public.contains i)
          let p := mkprogram types defs pub p1.prog_main
          -- reject a merge whose composites do not build: `mkprogram` would
          -- silently fall back to the empty environment
          if compositesWellFormed p then some p else none

/-- Link a whole list, left to right.  `prog_main` is taken from the head. -/
def linkPrograms : List Program → Option Program
  | [] => none
  | p :: ps => ps.foldl (fun acc q => acc.bind (fun a => linkProgram a q)) (some p)


/-! ## Renaming file-local symbols

**The second thing the plan did not anticipate.**  `clightgen` names each
translation unit's string literals `__stringlit_1`, `__stringlit_2`, … — so
inflate.c and inffast.c both define `__stringlit_1`, with *different* contents
(23 bytes vs 22).  They are `static`, absent from `prog_public`, and a real
linker keeps them as distinct local symbols; but `prog_defs` is keyed by `Ident`,
so merging naively either fails (correctly, as a conflict) or silently drops one.

So a private definition whose name is already taken must be **renamed** before
merging.  A global is referenced only through `Evar id ty` — a called function is
`Evar f (Tfunction …)`, an address-taken global is `Eaddrof (Evar g ty)` — so
rewriting `Evar`'s identifier, plus the `prog_defs` keys, is complete.
Composite and member names are untouched, because they live inside `Ty`, not in
`Evar`'s identifier field: renaming can never disturb a struct layout.

Labels (`Slabel`/`Sgoto`) are also `Ident`s but are function-local and never
resolved against `prog_defs`, so they are deliberately left alone. -/

/-- Rewrite global references in an expression. -/
def renameExpr (σ : Ident → Ident) : Expr → Expr
  | .Econst_int n t => .Econst_int n t
  | .Econst_float n t => .Econst_float n t
  | .Econst_single n t => .Econst_single n t
  | .Econst_long n t => .Econst_long n t
  | .Evar id t => .Evar (σ id) t
  | .Etempvar id t => .Etempvar id t          -- temporaries are function-local
  | .Ederef a t => .Ederef (renameExpr σ a) t
  | .Eaddrof a t => .Eaddrof (renameExpr σ a) t
  | .Eunop op a t => .Eunop op (renameExpr σ a) t
  | .Ebinop op a1 a2 t => .Ebinop op (renameExpr σ a1) (renameExpr σ a2) t
  | .Ecast a t => .Ecast (renameExpr σ a) t
  | .Efield a f t => .Efield (renameExpr σ a) f t   -- `f` is a member name
  | .Esizeof t1 t => .Esizeof t1 t
  | .Ealignof t1 t => .Ealignof t1 t

mutual
def renameStmt (σ : Ident → Ident) : Stmt → Stmt
  | .Sskip => .Sskip
  | .Sassign a1 a2 => .Sassign (renameExpr σ a1) (renameExpr σ a2)
  | .Sset id a => .Sset id (renameExpr σ a)
  | .Scall optid a al => .Scall optid (renameExpr σ a) (al.map (renameExpr σ))
  | .Sbuiltin optid ef tyl al => .Sbuiltin optid ef tyl (al.map (renameExpr σ))
  | .Ssequence s1 s2 => .Ssequence (renameStmt σ s1) (renameStmt σ s2)
  | .Sifthenelse a s1 s2 =>
      .Sifthenelse (renameExpr σ a) (renameStmt σ s1) (renameStmt σ s2)
  | .Sloop s1 s2 => .Sloop (renameStmt σ s1) (renameStmt σ s2)
  | .Sbreak => .Sbreak
  | .Scontinue => .Scontinue
  | .Sreturn (some a) => .Sreturn (some (renameExpr σ a))
  | .Sreturn none => .Sreturn none
  | .Sswitch a ls => .Sswitch (renameExpr σ a) (renameLbl σ ls)
  | .Slabel lbl s => .Slabel lbl (renameStmt σ s)
  | .Sgoto lbl => .Sgoto lbl

def renameLbl (σ : Ident → Ident) : LStmts → LStmts
  | .LSnil => .LSnil
  | .LScons z s ls => .LScons z (renameStmt σ s) (renameLbl σ ls)
end

def renameFunction (σ : Ident → Ident) (f : Function) : Function :=
  { f with fn_body := renameStmt σ f.fn_body }

def renameFundef (σ : Ident → Ident) : FunDef → FunDef
  | .Internal f => .Internal (renameFunction σ f)
  | .External ef ta tr cc => .External ef ta tr cc

def renameGlobdef (σ : Ident → Ident) : GlobDef FunDef Ty → GlobDef FunDef Ty
  | .Gfun fd => .Gfun (renameFundef σ fd)
  | .Gvar v => .Gvar v            -- initializers hold no global references

/-- Apply a renaming to a whole program (definition keys, publics, and every
    `Evar` in every body).  `prog_types`/`prog_comp_env` are untouched. -/
def renameProgram (σ : Ident → Ident) (p : Program) : Program :=
  { p with
    prog_defs := p.prog_defs.map (fun d => (σ d.1, renameGlobdef σ d.2)),
    prog_public := p.prog_public.map σ,
    prog_main := σ p.prog_main }

/-- One past the largest identifier a program mentions as a definition — the
    start of a fresh-name supply. -/
def freshBase (p : Program) : Nat :=
  p.prog_defs.foldl (fun acc d => max acc d.1.toNat) 0 + 1

/-- Build the renaming for one module about to be merged into `acc`: every
    identifier that is **private** to the module (not in its `prog_public`) and
    **already used** in `acc` is moved to a fresh identifier.  Everything else,
    public or not, is left alone — so cross-module resolution still happens by
    name, which is the whole point of linking. -/
def privateRenaming (acc : Program) (q : Program) : Ident → Ident :=
  let taken : PTree Unit :=
    acc.prog_defs.foldl (fun t d => t.set d.1 ()) PTree.empty
  let pub : PTree Unit :=
    q.prog_public.foldl (fun t i => t.set i ()) PTree.empty
  let base := max (freshBase acc) (freshBase q)
  let σ : PTree Ident :=
    (q.prog_defs.filter (fun d =>
        (pub.get d.1).isNone && (taken.get d.1).isSome)).zipIdx.foldl
      (fun t (d, i) => t.set d.1 (Positive.ofNat (base + i))) PTree.empty
  fun id => (σ.get id).getD id

/-- Link with automatic renaming of colliding private symbols.  This is the
    entry point a real multi-module program should use; `linkProgram` is the raw
    merge. -/
def linkProgramRenaming (p1 p2 : Program) : Option Program :=
  linkProgram p1 (renameProgram (privateRenaming p1 p2) p2)

/-- Link a whole list left to right, renaming colliding private symbols at each
    step.  `prog_main` comes from the head. -/
def linkProgramsRenaming : List Program → Option Program
  | [] => none
  | p :: ps =>
      ps.foldl (fun acc q => acc.bind (fun a => linkProgramRenaming a q)) (some p)

/-! ## What a linked program is for

The only property needed downstream is that a call which was an `EF_external`
before linking now resolves to an `Internal` body — which is what
`Genv.findFunct` computes.  These two definitions name that check so a proof (or
a `decide`) can state it without unfolding `Genv`. -/

/-- Is `name` an `Internal` definition of `p`? -/
def hasInternal (p : Program) (name : Ident) : Bool :=
  match p.prog_defs.find? (fun d => d.1 == name) with
  | some (_, .Gfun (.Internal _)) => true
  | _ => false

/-- Is `name` still only an `External` declaration in `p`? -/
def hasExternal (p : Program) (name : Ident) : Bool :=
  match p.prog_defs.find? (fun d => d.1 == name) with
  | some (_, .Gfun (.External _ _ _ _)) => true
  | _ => false

/-! ### `linkFundef` behaves as intended

Three facts, each `rfl`-shaped, that pin the resolution direction.  They are the
reason `linkProgram` can be trusted without porting `Linking.v`'s theory: the
merge is a total function whose behaviour on each case is stated here. -/

theorem linkFundef_decl_def (ef : ExtFun) (targs : List Ty) (tres : Ty)
    (cc : CallConv) (f : Function) (h : declMatchesDef targs tres cc f = true) :
    linkFundef (.External ef targs tres cc) (.Internal f) = some (.Internal f) := by
  simp [linkFundef, h]

theorem linkFundef_def_decl (ef : ExtFun) (targs : List Ty) (tres : Ty)
    (cc : CallConv) (f : Function) (h : declMatchesDef targs tres cc f = true) :
    linkFundef (.Internal f) (.External ef targs tres cc) = some (.Internal f) := by
  simp [linkFundef, h]

/-- **Two definitions of one name never link.**  Deliberate: a duplicate symbol
    is an error, and silently preferring one would make the linked program
    depend on argument order. -/
theorem linkFundef_dup (f g : Function) :
    linkFundef (.Internal f) (.Internal g) = none := rfl

end Link
end CC
