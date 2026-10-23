/-
  First part of the port of `lib/Parmov.v` (split from `CCLib.lib.Parmov`): `clos_refl_trans`, moves, the non-deterministic specification of parallel-move compilation, well-formedness of states and its preservation by the transitions.
-/

namespace CC
namespace Parmov

/-! ### Reflexive-transitive closure (`clos_refl_trans`) -/

/-- Reflexive-transitive closure of a relation (`clos_refl_trans`). -/
inductive Star {α : Type _} (R : α → α → Prop) : α → α → Prop where
  | refl (x : α) : Star R x x
  | step {x y z : α} : R x y → Star R y z → Star R x z

theorem Star.single {α : Type _} {R : α → α → Prop} {x y : α} (h : R x y) : Star R x y :=
  .step h (.refl y)

theorem Star.trans {α : Type _} {R : α → α → Prop} {x y z : α}
    (h1 : Star R x y) (h2 : Star R y z) : Star R x z := by
  induction h1 with
  | refl => exact h2
  | step h _ ih => exact .step h (ih h2)

section PARMOV

variable {reg : Type _}

/-! ## Registers, moves, and their semantics -/

/-- `is_temp r`: `r` is one of the temporaries. -/
def is_temp (temp : reg → reg) (r : reg) : Prop := ∃ s, r = temp s

/-- A set of moves: a list of `(source, destination)` pairs. -/
abbrev moves (reg : Type _) := List (reg × reg)

/-- Sources of a list of moves. -/
def srcs (m : moves reg) : List reg := m.map Prod.fst
/-- Destinations of a list of moves. -/
def dests (m : moves reg) : List reg := m.map Prod.snd

@[simp] theorem srcs_nil : srcs ([] : moves reg) = [] := rfl
@[simp] theorem srcs_cons (s d : reg) (m : moves reg) : srcs ((s, d) :: m) = s :: srcs m := rfl
@[simp] theorem dests_nil : dests ([] : moves reg) = [] := rfl
@[simp] theorem dests_cons (s d : reg) (m : moves reg) : dests ((s, d) :: m) = d :: dests m := rfl

/-! ## Specification of the non-deterministic algorithm -/

/-- States `(mu, sigma, tau)` of the algorithm. -/
structure state (reg : Type _) where
  mu : moves reg
  sigma : moves reg
  tau : moves reg

/-- `no_read mu d`: `d` is not a source of `mu`. -/
def no_read (mu : moves reg) (d : reg) : Prop := d ∉ srcs mu

/-- The non-deterministic rewriting rules. -/
inductive transition (temp : reg → reg) : state reg → state reg → Prop where
  | tr_nop (mu1 : moves reg) (r : reg) (mu2 sigma tau : moves reg) :
      transition temp ⟨mu1 ++ (r, r) :: mu2, sigma, tau⟩ ⟨mu1 ++ mu2, sigma, tau⟩
  | tr_start (mu1 : moves reg) (s d : reg) (mu2 tau : moves reg) :
      transition temp ⟨mu1 ++ (s, d) :: mu2, [], tau⟩ ⟨mu1 ++ mu2, [(s, d)], tau⟩
  | tr_push (mu1 : moves reg) (d r : reg) (mu2 : moves reg) (s : reg) (sigma tau : moves reg) :
      transition temp ⟨mu1 ++ (d, r) :: mu2, (s, d) :: sigma, tau⟩
                      ⟨mu1 ++ mu2, (d, r) :: (s, d) :: sigma, tau⟩
  | tr_loop (mu sigma : moves reg) (s d : reg) (tau : moves reg) :
      transition temp ⟨mu, sigma ++ [(s, d)], tau⟩
                      ⟨mu, sigma ++ [(temp s, d)], (s, temp s) :: tau⟩
  | tr_pop (mu : moves reg) (s0 d0 s1 d1 : reg) (sigma tau : moves reg) :
      no_read mu d1 → d1 ≠ s0 →
      transition temp ⟨mu, (s1, d1) :: sigma ++ [(s0, d0)], tau⟩
                      ⟨mu, sigma ++ [(s0, d0)], (s1, d1) :: tau⟩
  | tr_last (mu : moves reg) (s d : reg) (tau : moves reg) :
      no_read mu d →
      transition temp ⟨mu, [(s, d)], tau⟩ ⟨mu, [], (s, d) :: tau⟩

/-- Reflexive-transitive closure of `transition`. -/
def transitions (temp : reg → reg) : state reg → state reg → Prop := Star (transition temp)

/-! ### Well-formedness of states -/

/-- No destination appears twice. -/
def is_mill (m : moves reg) : Prop := (dests m).Nodup

/-- `r` is not a temporary. -/
def is_not_temp (temp : reg → reg) (r : reg) : Prop := ∀ d, r ≠ temp d

/-- No temporary appears in `m`. -/
def move_no_temp (temp : reg → reg) (m : moves reg) : Prop :=
  ∀ s d, (s, d) ∈ m → is_not_temp temp s ∧ is_not_temp temp d

/-- No temporary appears in `m`, except possibly as the last source. -/
def temp_last (temp : reg → reg) (m : moves reg) : Prop :=
  match m.reverse with
  | [] => True
  | (_, d) :: m' => is_not_temp temp d ∧ move_no_temp temp m'

/-- `d` is the destination of the first move of `m` (if any). -/
def is_first_dest (m : moves reg) (d : reg) : Prop :=
  match m with
  | [] => True
  | (_, d0) :: _ => d = d0

/-- `m` is a path: the source of each move is the destination of the next. -/
inductive is_path : moves reg → Prop where
  | nil : is_path []
  | cons (s d : reg) (m : moves reg) : is_first_dest m s → is_path m → is_path ((s, d) :: m)

/-- Well-formed states. -/
inductive state_wf (temp : reg → reg) : state reg → Prop where
  | intro (mu sigma tau : moves reg) :
      is_mill (mu ++ sigma) → move_no_temp temp mu → temp_last temp sigma → is_path sigma →
      state_wf temp ⟨mu, sigma, tau⟩

/-! ### Properties of `srcs` and `dests` -/

@[simp] theorem dests_append (m1 m2 : moves reg) : dests (m1 ++ m2) = dests m1 ++ dests m2 := by
  simp [dests]

theorem dests_decomp (m1 : moves reg) (s d : reg) (m2 : moves reg) :
    dests (m1 ++ (s, d) :: m2) = dests m1 ++ d :: dests m2 := by simp

@[simp] theorem srcs_append (m1 m2 : moves reg) : srcs (m1 ++ m2) = srcs m1 ++ srcs m2 := by
  simp [srcs]

theorem srcs_decomp (m1 : moves reg) (s d : reg) (m2 : moves reg) :
    srcs (m1 ++ (s, d) :: m2) = srcs m1 ++ s :: srcs m2 := by simp

theorem srcs_dests_combine (s d : List reg) (h : s.length = d.length) :
    srcs (s.zip d) = s ∧ dests (s.zip d) = d := by
  induction s generalizing d with
  | nil => cases d <;> simp_all
  | cons a s ih =>
    cases d with
    | nil => simp at h
    | cons b d =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      have := ih d h
      simp [List.zip_cons_cons, this]

theorem mem_srcs_of_mem {s d : reg} {m : moves reg} (h : (s, d) ∈ m) : s ∈ srcs m :=
  List.mem_map.2 ⟨_, h, rfl⟩

theorem mem_dests_of_mem {s d : reg} {m : moves reg} (h : (s, d) ∈ m) : d ∈ dests m :=
  List.mem_map.2 ⟨_, h, rfl⟩

/-- Destinations of `m1` and `m2` are disjoint (`dests_disjoint`). -/
def dests_disjoint (m1 m2 : moves reg) : Prop :=
  ∀ x y, x ∈ dests m1 → y ∈ dests m2 → x ≠ y

theorem dests_disjoint_sym (m1 m2 : moves reg) :
    dests_disjoint m1 m2 ↔ dests_disjoint m2 m1 := by
  unfold dests_disjoint
  exact ⟨fun h x y hx hy e => h y x hy hx e.symm, fun h x y hx hy e => h y x hy hx e.symm⟩

theorem dests_disjoint_cons_left (m1 : moves reg) (s d : reg) (m2 : moves reg) :
    dests_disjoint ((s, d) :: m1) m2 ↔ dests_disjoint m1 m2 ∧ d ∉ dests m2 := by
  unfold dests_disjoint
  constructor
  · intro h
    exact ⟨fun x y hx hy => h x y (by simp [hx]) hy, fun hd => h d d (by simp) hd rfl⟩
  · rintro ⟨h1, h2⟩ x y hx hy
    simp at hx
    rcases hx with rfl | hx
    · rintro rfl; exact h2 hy
    · exact h1 x y hx hy

theorem dests_disjoint_cons_right (m1 : moves reg) (s d : reg) (m2 : moves reg) :
    dests_disjoint m1 ((s, d) :: m2) ↔ dests_disjoint m1 m2 ∧ d ∉ dests m1 := by
  rw [dests_disjoint_sym, dests_disjoint_cons_left, dests_disjoint_sym]

theorem dests_disjoint_append_left (m1 m2 m3 : moves reg) :
    dests_disjoint (m1 ++ m2) m3 ↔ dests_disjoint m1 m3 ∧ dests_disjoint m2 m3 := by
  unfold dests_disjoint
  simp only [dests_append, List.mem_append]
  constructor
  · intro h
    exact ⟨fun x y hx hy => h x y (.inl hx) hy, fun x y hx hy => h x y (.inr hx) hy⟩
  · rintro ⟨h1, h2⟩ x y (hx | hx) hy
    · exact h1 x y hx hy
    · exact h2 x y hx hy

theorem dests_disjoint_append_right (m1 m2 m3 : moves reg) :
    dests_disjoint m1 (m2 ++ m3) ↔ dests_disjoint m1 m2 ∧ dests_disjoint m1 m3 := by
  rw [dests_disjoint_sym, dests_disjoint_append_left, dests_disjoint_sym m2,
    dests_disjoint_sym m3]

theorem is_mill_cons (s d : reg) (m : moves reg) :
    is_mill ((s, d) :: m) ↔ is_mill m ∧ d ∉ dests m := by
  simp [is_mill, List.nodup_cons, And.comm]

theorem is_mill_append (m1 m2 : moves reg) :
    is_mill (m1 ++ m2) ↔ is_mill m1 ∧ is_mill m2 ∧ dests_disjoint m1 m2 := by
  simp only [is_mill, dests_disjoint, dests_append, List.nodup_append]
  exact ⟨fun ⟨a, b, c⟩ => ⟨a, b, fun x y hx hy => c x hx y hy⟩,
    fun ⟨a, b, c⟩ => ⟨a, b, fun x hx y hy => c x y hx hy⟩⟩

theorem notin_dests_cons (x s d : reg) (m : moves reg) :
    x ∉ dests ((s, d) :: m) ↔ x ≠ d ∧ x ∉ dests m := by
  simp

theorem notin_dests_append (d : reg) (m1 m2 : moves reg) :
    d ∉ dests (m1 ++ m2) ↔ d ∉ dests m1 ∧ d ∉ dests m2 := by
  simp

/-! ### Properties of `move_no_temp`, `temp_last` and `is_path` -/

theorem move_no_temp_append {temp : reg → reg} {m1 m2 : moves reg}
    (h1 : move_no_temp temp m1) (h2 : move_no_temp temp m2) : move_no_temp temp (m1 ++ m2) := by
  intro s d h
  rcases List.mem_append.1 h with h | h
  · exact h1 s d h
  · exact h2 s d h

theorem move_no_temp_rev {temp : reg → reg} {m : moves reg}
    (h : move_no_temp temp m.reverse) : move_no_temp temp m := by
  intro s d hm; exact h s d (List.mem_reverse.2 hm)

theorem temp_last_change_last_source {temp : reg → reg} (s d s' : reg) (sigma : moves reg)
    (h : temp_last temp (sigma ++ [(s, d)])) : temp_last temp (sigma ++ [(s', d)]) := by
  unfold temp_last at *
  simpa using h

theorem temp_last_push {temp : reg → reg} (s1 d1 s2 d2 : reg) (sigma : moves reg)
    (h : temp_last temp ((s2, d2) :: sigma))
    (hs1 : is_not_temp temp s1) (hd1 : is_not_temp temp d1) :
    temp_last temp ((s1, d1) :: (s2, d2) :: sigma) := by
  unfold temp_last at *
  simp only [List.reverse_cons] at *
  rcases hr : sigma.reverse with _ | ⟨⟨sN, dN⟩, m'⟩ <;> rw [hr] at h <;> simp only [List.nil_append,
    List.cons_append] at h ⊢
  · refine ⟨h.1, ?_⟩
    intro s d hm
    simp at hm
    rcases hm with ⟨rfl, rfl⟩
    exact ⟨hs1, hd1⟩
  · refine ⟨h.1, ?_⟩
    intro s d hm
    simp only [List.append_assoc, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.cons_append, List.nil_append] at hm
    rcases hm with hm | hm | hm
    · exact h.2 s d (List.mem_append.2 (.inl hm))
    · exact h.2 s d (List.mem_append.2 (.inr (List.mem_singleton.2 hm)))
    · cases hm; exact ⟨hs1, hd1⟩

theorem temp_last_pop {temp : reg → reg} (s1 d1 : reg) (sigma : moves reg) (s2 d2 : reg)
    (h : temp_last temp ((s1, d1) :: sigma ++ [(s2, d2)])) :
    temp_last temp (sigma ++ [(s2, d2)]) := by
  unfold temp_last at *
  simp only [List.cons_append, List.reverse_cons, List.reverse_append] at *
  refine ⟨h.1, fun s d hm => h.2 s d (List.mem_append.2 (.inl hm))⟩

theorem is_path_pop {s d : reg} {m : moves reg} (h : is_path ((s, d) :: m)) : is_path m := by
  cases h; assumption

theorem is_path_change_last_source (s s' d : reg) (sigma : moves reg)
    (h : is_path (sigma ++ [(s, d)])) : is_path (sigma ++ [(s', d)]) := by
  induction sigma with
  | nil => exact .cons _ _ _ trivial .nil
  | cons a sigma ih =>
    obtain ⟨a1, a2⟩ := a
    cases h with
    | cons _ _ _ hf hp =>
      refine .cons _ _ _ ?_ (ih hp)
      rcases sigma with _ | ⟨⟨s1, d1⟩, sigma'⟩ <;> simpa [is_first_dest] using hf

theorem path_sources_dests (s0 d0 : reg) (sigma : moves reg)
    (h : is_path (sigma ++ [(s0, d0)])) :
    ∀ x, x ∈ srcs (sigma ++ [(s0, d0)]) → x ∈ s0 :: dests (sigma ++ [(s0, d0)]) := by
  induction sigma with
  | nil => intro x hx; simp at hx; simp [hx]
  | cons a sigma ih =>
    obtain ⟨s, d⟩ := a
    cases h with
    | cons _ _ _ hf hp =>
      have hs : s ∈ dests (sigma ++ [(s0, d0)]) := by
        rcases sigma with _ | ⟨⟨s1, d1⟩, sigma'⟩ <;> simp_all [is_first_dest]
      intro x hx
      simp only [List.cons_append, srcs_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · simp at hs ⊢; grind
      · have := ih hp x hx
        simp only [List.mem_cons, List.cons_append, dests_cons] at this ⊢
        grind

theorem no_read_path (d1 : reg) (sigma : moves reg) (s0 d0 : reg) (hne : d1 ≠ s0)
    (hp : is_path (sigma ++ [(s0, d0)])) (hnd : d1 ∉ dests (sigma ++ [(s0, d0)])) :
    no_read (sigma ++ [(s0, d0)]) d1 := by
  intro hin
  rcases List.mem_cons.1 (path_sources_dests _ _ _ hp _ hin) with h | h
  · exact hne h
  · exact hnd h

/-! ### Transitions preserve well-formedness -/

theorem list_in_insert {a : reg × reg} {m1 m2 : moves reg} {x : reg × reg}
    (h : a ∈ m1 ++ m2) : a ∈ m1 ++ x :: m2 := by
  simp only [List.mem_append, List.mem_cons] at h ⊢; grind

theorem transition_preserves_wf {temp : reg → reg} {st st' : state reg}
    (ht : transition temp st st') (hwf : state_wf temp st) : state_wf temp st' := by
  cases hwf with
  | intro mu sigma tau A B C D =>
  cases ht with
  | tr_nop mu1 r mu2 =>
    refine .intro _ _ _ ?_ (fun s d h => B s d (list_in_insert h)) C D
    simp only [is_mill, dests_append, dests_cons, List.nodup_append, List.nodup_cons,
      List.mem_append, List.mem_cons] at A ⊢
    grind
  | tr_start mu1 s d mu2 =>
    have hsd := B s d (by simp)
    refine .intro _ _ _ ?_ (fun s d h => B s d (list_in_insert h)) ?_ (.cons _ _ _ trivial .nil)
    · simp only [is_mill, dests_append, dests_cons, List.nodup_append, List.nodup_cons,
        List.mem_append, List.mem_cons, dests_nil, List.append_nil] at A ⊢
      grind
    · simp [temp_last, hsd.2, move_no_temp]
  | tr_push mu1 d r mu2 s sigma =>
    have hdr := B d r (by simp)
    refine .intro _ _ _ ?_ (fun s d h => B s d (list_in_insert h))
      (temp_last_push _ _ _ _ _ C hdr.1 hdr.2) (.cons _ _ _ rfl D)
    simp only [is_mill, dests_append, dests_cons, List.nodup_append, List.nodup_cons,
      List.mem_append, List.mem_cons] at A ⊢
    grind
  | tr_loop mu sigma s d =>
    refine .intro _ _ _ ?_ B (temp_last_change_last_source _ _ _ _ C)
      (is_path_change_last_source _ _ _ _ D)
    simpa [is_mill] using A
  | tr_pop mu s0 d0 s1 d1 sigma _ _ =>
    refine .intro _ _ _ ?_ B (temp_last_pop _ _ _ _ _ C) (is_path_pop D)
    simp only [is_mill, dests_append, dests_cons, List.nodup_append, List.nodup_cons,
      List.mem_append, List.mem_cons, List.cons_append] at A ⊢
    grind
  | tr_last mu s d _ =>
    refine .intro _ _ _ ?_ B (by simp [temp_last]) .nil
    simp only [is_mill, dests_append, List.nodup_append] at A ⊢
    simp [A.1]

theorem transitions_preserve_wf {temp : reg → reg} {st st' : state reg}
    (ht : transitions temp st st') (hwf : state_wf temp st) : state_wf temp st' := by
  induction ht with
  | refl => exact hwf
  | step h _ ih => exact ih (transition_preserves_wf h hwf)

end PARMOV
end Parmov
end CC
