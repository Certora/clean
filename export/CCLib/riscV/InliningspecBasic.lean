/-
  [RISC-V instance of `CCLib/backend/InliningspecBasic.lean`: the same development, in
  namespace `CC.RiscV`, over the RISC-V operators, registers and conventions.]

  RTL function inlining: relational specification — port of
  `backend/Inliningspec.v`, part 1: soundness of function environments
  (`fenv_compat`, `funenv_program_compat`), properties of shifting
  (`shiftpos_*`), the bounds `max_pc_function_sound`,
  `max_reg_function_def`, `max_reg_function_params` of `RTL.v`, the
  monotonicity of the state monad (`sincr`), and the specification of moves
  (`tr_moves`, `add_moves_unchanged`, `add_moves_spec`).

  The state monad of the port does not carry the proof `sincr s s'` that the
  state only grows; it is proved separately here (`*_incr` lemmas).
-/
import CCLib.riscV.Inlining
import CCLib.cfrontend.CtypesTheory
import CCLib.lib.MapsTheory

namespace CC
namespace RiscV
namespace Inlining

open Op RTL

/-! ## Positive arithmetic -/

theorem toNat_add (p q : Positive) : (Positive.add p q).toNat = p.toNat + q.toNat := by
  unfold Positive.add
  have := Positive.toNat_pos p
  exact Positive.toNat_ofNat _ (by omega)

/-- `Inliningspec.shiftpos_eq` -/
theorem shiftpos_eq (x y : Positive) : (shiftpos x y).toNat = x.toNat + y.toNat - 1 := by
  unfold shiftpos
  have := Positive.toNat_pos x
  have := Positive.toNat_pos y
  exact Positive.toNat_ofNat _ (by omega)

/-- `Inliningspec.shiftpos_inj` -/
theorem shiftpos_inj {x y n : Positive} (h : shiftpos x n = shiftpos y n) : x = y := by
  have h1 := congrArg Positive.toNat h
  rw [shiftpos_eq, shiftpos_eq] at h1
  have := Positive.toNat_pos x
  have := Positive.toNat_pos y
  have := Positive.toNat_pos n
  exact Positive.toNat_inj (by omega)

/-- `Inliningspec.shiftpos_diff` -/
theorem shiftpos_diff {x y : Positive} (n : Positive) (h : x ≠ y) : shiftpos x n ≠ shiftpos y n :=
  fun he => h (shiftpos_inj he)

/-- `Inliningspec.shiftpos_above` -/
theorem shiftpos_above (x n : Positive) : n ≤ shiftpos x n := by
  show n.toNat ≤ (shiftpos x n).toNat
  rw [shiftpos_eq]; have := Positive.toNat_pos x; omega

/-- `Inliningspec.shiftpos_not_below` -/
theorem shiftpos_not_below (x n : Positive) (h : shiftpos x n < n) : False := by
  have := shiftpos_above x n
  have h' : (shiftpos x n).toNat < n.toNat := h
  have : n.toNat ≤ (shiftpos x n).toNat := this
  omega

/-- `Inliningspec.shiftpos_below` -/
theorem shiftpos_below (x n : Positive) : shiftpos x n < Positive.add x n := by
  show (shiftpos x n).toNat < (Positive.add x n).toNat
  rw [shiftpos_eq, toNat_add]; have := Positive.toNat_pos n; omega

/-- `Inliningspec.shiftpos_le` -/
theorem shiftpos_le {x y : Positive} (n : Positive) (h : x ≤ y) : shiftpos x n ≤ shiftpos y n := by
  show (shiftpos x n).toNat ≤ (shiftpos y n).toNat
  have h' : x.toNat ≤ y.toNat := h
  rw [shiftpos_eq, shiftpos_eq]; omega

/-! ## Bounds on program points and registers (`RTL.v`) -/

theorem le_max_left (p q : Positive) : p ≤ Positive.max p q := by
  show p.toNat ≤ (Positive.max p q).toNat
  unfold Positive.max; split <;> omega

theorem le_max_right (p q : Positive) : q ≤ Positive.max p q := by
  show q.toNat ≤ (Positive.max p q).toNat
  unfold Positive.max; split <;> omega

theorem foldl_mono {A B : Type} (F : Positive → A → Positive) (G : B → A)
    (hF : ∀ a x, a ≤ F a x) : ∀ (l : List B) (a : Positive),
    a ≤ l.foldl (fun a p => F a (G p)) a
  | [], a => Nat.le_refl a.toNat
  | p :: l, a => by
    show a.toNat ≤ (l.foldl (fun a p => F a (G p)) (F a (G p))).toNat
    have h1 : a.toNat ≤ (F a (G p)).toNat := hF a (G p)
    have h2 := foldl_mono F G hF l (F a (G p))
    have h2' : (F a (G p)).toNat ≤ _ := h2
    omega

theorem foldl_mem {A B : Type} (F : Positive → A → Positive) (G : B → A)
    (hF : ∀ a x, a ≤ F a x) {r : Positive} {p : B} (hr : ∀ a, r ≤ F a (G p)) :
    ∀ (l : List B) (a : Positive), p ∈ l → r ≤ l.foldl (fun a p => F a (G p)) a
  | [], _, h => by cases h
  | q :: l, a, h => by
    cases h with
    | head =>
      simp only [List.foldl]
      have h1 : r.toNat ≤ (F a (G p)).toNat := hr a
      have h2 : (F a (G p)).toNat ≤ _ := foldl_mono F G hF l (F a (G p))
      show r.toNat ≤ _
      omega
    | tail _ h => exact foldl_mem F G hF hr l _ h


/-- `RTL.max_pc_function_sound` -/
theorem max_pc_function_sound {f : RTL.Function} {pc : Node} {i : Instruction}
    (h : f.fn_code.get pc = some i) : pc ≤ maxPcFunction f := by
  unfold maxPcFunction
  rw [PTree.fold_spec]
  exact foldl_mem (fun m (p : Positive × Instruction) => Positive.max m p.1) id
    (fun a x => le_max_left _ _) (p := (pc, i)) (fun a => le_max_right a pc) _ _
    (PTree.elements_correct _ _ _ h)

theorem foldl_max_ge_init : ∀ (l : List Positive) (n : Positive), n ≤ l.foldl Positive.max n
  | [], n => Nat.le_refl _
  | a :: l, n => by
    show n.toNat ≤ (l.foldl Positive.max (Positive.max n a)).toNat
    have h1 : n.toNat ≤ (Positive.max n a).toNat := le_max_left n a
    have h2 : (Positive.max n a).toNat ≤ _ := foldl_max_ge_init l (Positive.max n a)
    omega

theorem foldl_max_ge {r : Positive} : ∀ (l : List Positive) (n : Positive),
    (r ∈ l ∨ r ≤ n) → r ≤ l.foldl Positive.max n
  | [], n, h => by
    rcases h with h | h
    · cases h
    · exact h
  | a :: l, n, h => by
    apply foldl_max_ge l (Positive.max n a)
    rcases h with h | h
    · cases h with
      | head => exact .inr (le_max_right _ _)
      | tail _ h => exact .inl h
    · right
      have h1 : r.toNat ≤ n.toNat := h
      have h2 : n.toNat ≤ (Positive.max n a).toNat := le_max_left n a
      show r.toNat ≤ _
      omega

theorem le_trans' {a b c : Positive} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  have h1' : a.toNat ≤ b.toNat := h1
  have h2' : b.toNat ≤ c.toNat := h2
  show a.toNat ≤ c.toNat
  omega

/-- `RTL.max_reg_instr_ge` -/
theorem max_reg_instr_ge (m : Positive) (pc : Node) (i : Instruction) : m ≤ maxRegInstr m pc i := by
  cases i with
  | Inop => exact Nat.le_refl _
  | Iop _ args res _ => exact le_trans' (le_max_right _ _) (foldl_max_ge_init _ _)
  | Iload _ _ args dst _ => exact le_trans' (le_max_right _ _) (foldl_max_ge_init _ _)
  | Istore _ _ args src _ => exact le_trans' (le_max_right _ _) (foldl_max_ge_init _ _)
  | Icall _ ros args res _ =>
    cases ros with
    | inl r =>
      exact le_trans' (le_trans' (le_max_right _ _) (le_max_right _ _)) (foldl_max_ge_init _ _)
    | inr _ => exact le_trans' (le_max_right _ _) (foldl_max_ge_init _ _)
  | Itailcall _ ros args =>
    cases ros with
    | inl r => exact le_trans' (le_max_right _ _) (foldl_max_ge_init _ _)
    | inr _ => exact foldl_max_ge_init _ _
  | Ibuiltin _ args res _ =>
    exact le_trans' (foldl_max_ge_init _ _) (foldl_max_ge_init _ _)
  | Icond _ args _ _ => exact foldl_max_ge_init _ _
  | Ijumptable arg _ => exact le_max_right _ _
  | Ireturn or =>
    cases or with
    | none => exact Nat.le_refl _
    | some a => exact le_max_right _ _

/-- `RTL.max_reg_instr_def` -/
theorem max_reg_instr_def (m : Positive) (pc : Node) {i : Instruction} {r : Reg}
    (h : instrDefs i = some r) : r ≤ maxRegInstr m pc i := by
  cases i with
  | Iop _ args res _ =>
    cases h; exact foldl_max_ge _ _ (.inr (le_max_left _ _))
  | Iload _ _ args dst _ =>
    cases h; exact foldl_max_ge _ _ (.inr (le_max_left _ _))
  | Icall _ ros args res _ =>
    cases h
    cases ros with
    | inl r' => exact foldl_max_ge _ _ (.inr (le_trans' (le_max_left _ _) (le_max_right _ _)))
    | inr _ => exact foldl_max_ge _ _ (.inr (le_max_left _ _))
  | Ibuiltin _ args res _ =>
    cases res with
    | BR x =>
      obtain rfl : x = r := Option.some.inj h
      exact le_trans' (foldl_max_ge [x] _ (.inl (.head _))) (foldl_max_ge_init _ _)
    | _ => cases h
  | _ => cases h

/-- `RTL.max_reg_function_def` -/
theorem max_reg_function_def {f : RTL.Function} {pc : Node} {i : Instruction} {r : Reg}
    (h : f.fn_code.get pc = some i) (hd : instrDefs i = some r) : r ≤ maxRegFunction f := by
  unfold maxRegFunction
  refine le_trans' ?_ (le_max_left _ _)
  rw [PTree.fold_spec]
  exact foldl_mem (fun m (p : Positive × Instruction) => maxRegInstr m p.1 p.2) id
    (fun a x => max_reg_instr_ge _ _ _) (p := (pc, i)) (fun a => max_reg_instr_def a pc hd) _ _
    (PTree.elements_correct _ _ _ h)

/-- `RTL.max_reg_function_params` -/
theorem max_reg_function_params {f : RTL.Function} {r : Reg} (h : r ∈ f.fn_params) :
    r ≤ maxRegFunction f :=
  le_trans' (foldl_max_ge _ _ (.inl h)) (le_max_right _ _)

/-! ## Soundness of function environments -/

/-- `Inliningspec.fenv_compat` -/
def FenvCompat (p : RTL.Program) (fenv : Funenv) : Prop :=
  ∀ id f, fenv.get id = some f → p.defmap.get id = some (.Gfun (.Internal f))

/-! ## Working with the state monad -/

theorem pos_le_iff (p q : Positive) : p ≤ q ↔ p.toNat ≤ q.toNat := Iff.rfl

/-- Linear arithmetic over `Positive`, through `toNat`. -/
macro "pos_omega" : tactic =>
  `(tactic| ((try simp only [CC.Positive.lt_iff, CC.RiscV.Inlining.pos_le_iff, CC.RiscV.Inlining.toNat_add,
      CC.RiscV.Inlining.shiftpos_eq, CC.Positive.toNat_succ] at *); omega))

/-- `Inlining.sincr`: the state only grows. -/
structure Sincr (s1 s2 : State) : Prop where
  nextnode : s1.st_nextnode ≤ s2.st_nextnode
  nextreg : s1.st_nextreg ≤ s2.st_nextreg
  stksize : s1.st_stksize ≤ s2.st_stksize

theorem Sincr.refl (s : State) : Sincr s s := ⟨Nat.le_refl _, Nat.le_refl _, Int.le_refl _⟩

theorem Sincr.trans {s1 s2 s3 : State} (h1 : Sincr s1 s2) (h2 : Sincr s2 s3) : Sincr s1 s3 := by
  obtain ⟨a1, b1, c1⟩ := h1
  obtain ⟨a2, b2, c2⟩ := h2
  exact ⟨by pos_omega, by pos_omega, Int.le_trans c1 c2⟩

/-- A computation of the state monad whose final state extends its initial one. -/
def IncrM {A : Type} (m : Mon A) : Prop := ∀ s, Sincr s (m s).2

theorem incrM_bind {A B : Type} {f : Mon A} {g : A → Mon B} (hf : IncrM f)
    (hg : ∀ a, IncrM (g a)) : IncrM (f >>= g) :=
  fun s => (hf s).trans (hg _ _)

theorem incrM_pure {A : Type} (a : A) : IncrM (pure a : Mon A) := fun s => Sincr.refl s

/-- `Inliningspec.bind_inversion` -/
theorem bind_inv {A B : Type} {f : Mon A} {g : A → Mon B} {s : State} {y : B} {s' : State}
    (h : (f >>= g) s = (y, s')) : ∃ x s1, f s = (x, s1) ∧ g x s1 = (y, s') :=
  ⟨(f s).1, (f s).2, rfl, h⟩

theorem setInstr_incr (pc : Node) (i : Instruction) : IncrM (setInstr pc i) :=
  fun s => ⟨Nat.le_refl _, Nat.le_refl _, Int.le_refl _⟩

theorem addInstr_incr (i : Instruction) : IncrM (addInstr i) :=
  fun s => ⟨by show s.st_nextnode.toNat ≤ s.st_nextnode.succ.toNat; pos_omega,
    Nat.le_refl _, Int.le_refl _⟩

theorem reserveNodes_incr (n : Positive) : IncrM (reserveNodes n) :=
  fun s => ⟨by show s.st_nextnode.toNat ≤ (s.st_nextnode.add n).toNat; pos_omega,
    Nat.le_refl _, Int.le_refl _⟩

theorem reserveRegs_incr (n : Positive) : IncrM (reserveRegs n) :=
  fun s => ⟨Nat.le_refl _, by show s.st_nextreg.toNat ≤ (s.st_nextreg.add n).toNat; pos_omega,
    Int.le_refl _⟩

theorem requestStack_incr (sz : Z) : IncrM (requestStack sz) :=
  fun s => ⟨Nat.le_refl _, Nat.le_refl _, by
    show s.st_stksize ≤ Max.max s.st_stksize sz; exact Int.le_max_left _ _⟩

theorem addMoves_incr : ∀ (srcs dsts : List Reg) (succ : Node), IncrM (addMoves srcs dsts succ)
  | [], _, _ => incrM_pure _
  | _ :: _, [], _ => incrM_pure _
  | _ :: sl, _ :: dl, _ =>
    incrM_bind (addInstr_incr _) (fun n => addMoves_incr sl dl n)

theorem foldl_incr {B : Type} (F : State → B → State) (hF : ∀ s b, Sincr s (F s b)) :
    ∀ (l : List B) (s : State), Sincr s (l.foldl F s)
  | [], s => Sincr.refl s
  | b :: l, s => (hF s b).trans (foldl_incr F hF l (F s b))

theorem ptreeMfold_incr {A : Type} {f : Positive → A → Mon Unit} (hf : ∀ k v, IncrM (f k v))
    (t : PTree A) : IncrM (ptreeMfold f t) := by
  intro s
  show Sincr s (PTree.fold (fun s1 k v => ((f k v).run s1).2) t s)
  rw [PTree.fold_spec]
  exact foldl_incr _ (fun s1 (p : Positive × A) => hf p.1 p.2 s1) _ _

/-! ## Relational specification of the translation of moves -/

/-- `Inliningspec.tr_moves` -/
inductive TrMoves (c : Code) : Node → List Reg → List Reg → Node → Prop where
  | cons (pc1 src srcs dst dsts pc2 pc3) :
      TrMoves c pc1 srcs dsts pc2 →
      c.get pc2 = some (.Iop .Omove [src] dst pc3) →
      TrMoves c pc1 (src :: srcs) (dst :: dsts) pc3
  | nil (srcs dsts pc) : srcs = [] ∨ dsts = [] → TrMoves c pc srcs dsts pc

/-- `Inliningspec.add_moves_unchanged` -/
theorem add_moves_unchanged : ∀ (srcs dsts : List Reg) (pc2 : Node) {s : State} {pc1 : Node}
    {s' : State} {pc : Node}, addMoves srcs dsts pc2 s = (pc1, s') →
    (pc < s.st_nextnode ∨ s'.st_nextnode ≤ pc) → s'.st_code.get pc = s.st_code.get pc
  | [], _, _, _, _, _, _, h, _ => by cases h; rfl
  | _ :: _, [], _, _, _, _, _, h, _ => by cases h; rfl
  | a :: sl, d :: dl, pc2, s, pc1, s', pc, h, hp => by
    have h' : addMoves sl dl s.st_nextnode
        { s with st_nextnode := s.st_nextnode.succ,
                 st_code := s.st_code.set s.st_nextnode (.Iop .Omove [a] d pc2) } = (pc1, s') := h
    have I := addMoves_incr sl dl s.st_nextnode
      { s with st_nextnode := s.st_nextnode.succ,
               st_code := s.st_code.set s.st_nextnode (.Iop .Omove [a] d pc2) }
    rw [h'] at I
    have I1 := I.nextnode
    simp only at I1
    rw [add_moves_unchanged sl dl _ h' (by
      rcases hp with hp | hp
      · left; simp only; pos_omega
      · right; exact hp)]
    simp only
    rw [PTree.gso]
    rintro rfl
    rcases hp with hp | hp <;> pos_omega

/-- `Inliningspec.add_moves_spec` -/
theorem add_moves_spec {c : Code} : ∀ (srcs dsts : List Reg) (pc2 : Node) {s : State} {pc1 : Node}
    {s' : State}, addMoves srcs dsts pc2 s = (pc1, s') →
    (∀ pc, s.st_nextnode ≤ pc → pc < s'.st_nextnode → c.get pc = s'.st_code.get pc) →
    TrMoves c pc1 srcs dsts pc2
  | [], _, _, _, _, _, h, _ => by cases h; exact .nil _ _ _ (.inl rfl)
  | _ :: _, [], _, _, _, _, h, _ => by cases h; exact .nil _ _ _ (.inr rfl)
  | a :: sl, d :: dl, pc2, s, pc1, s', h, hc => by
    have h' : addMoves sl dl s.st_nextnode
        { s with st_nextnode := s.st_nextnode.succ,
                 st_code := s.st_code.set s.st_nextnode (.Iop .Omove [a] d pc2) } = (pc1, s') := h
    have I := addMoves_incr sl dl s.st_nextnode
      { s with st_nextnode := s.st_nextnode.succ,
               st_code := s.st_code.set s.st_nextnode (.Iop .Omove [a] d pc2) }
    rw [h'] at I
    have I1 := I.nextnode
    simp only at I1
    refine .cons _ _ _ _ _ s.st_nextnode _ (add_moves_spec sl dl _ h' (fun pc h1 h2 => hc pc
      (by simp only at h1; pos_omega) h2)) ?_
    rw [hc _ (Nat.le_refl _) (by pos_omega), add_moves_unchanged sl dl _ h'
      (.inl (by simp only; pos_omega))]
    simp

end Inlining
end RiscV
end CC
