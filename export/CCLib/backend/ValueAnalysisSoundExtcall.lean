/-
  Soundness of the value analysis, part 3 — port of `external_call_match`
  from `backend/ValueAnalysis.v`.

  An external call, viewed through the memory injection `inj_of_bc bc`,
  produces a new block classification `bc'` that agrees with `bc` on the
  old blocks and classifies the freshly mapped blocks as `BCother`.

  Differences from Rocq: the properties of external calls that CompCert
  states as axioms for uninterpreted externals (`ec_mem_inject` and the
  memory fields of `extcall_properties`) are hypotheses, discharged for the
  interpreted ones by `externalCall_memInject` / `externalCall_memProps`.
-/
import CCLib.backend.ValueAnalysisSoundBC
import CCLib.common.EventsInject
import CCLib.common.EventsMem

namespace CC
namespace ValueAnalysis

open ValueDomain RTL

/-- `inj_of_bc bc` injects the symbol environment of a matching `ge` into itself. -/
theorem symbolsInject_of_bc {F V : Type} {bc : BlockClassification} {ge : Genv F V}
    (hg : GenvMatch bc ge) : SymbolsInject (injOfBc bc) (Genv.toSenv ge) (Genv.toSenv ge) where
  public_eq _ := rfl
  find_mapped id b1 b2 delta hf h := by
    obtain ⟨_, rfl, rfl⟩ := inj_of_bc_inv bc hf
    exact ⟨rfl, h⟩
  find_public id b1 _ h :=
    ⟨b1, inj_of_bc_valid bc (by rw [(hg.1 id b1).1 h]; simp), h⟩
  volatile_eq b1 b2 delta hf := by
    obtain ⟨_, rfl, rfl⟩ := inj_of_bc_inv bc hf
    rfl

/-- `ValueAnalysis.external_call_match` -/
theorem external_call_match {F V : Type} (ef : ExtFun) (ge : Genv F V) {vargs : List Val}
    {m : Mem} {t : Trace} {vres : Val} {m' : Mem} {bc : BlockClassification} {rm : Romem}
    {am : Amem}
    (hinj : ExtcallMemInject (externalCall ef))
    (hprops : ExtcallMemProps (externalCall ef) (Genv.toSenv ge))
    (EC : externalCall ef (Genv.toSenv ge) vargs m t vres m')
    (GENV : GenvMatch bc ge) (ARGS : ∀ v, v ∈ vargs → Vmatch bc v Vtop)
    (RO : Romatch bc m rm) (MM : Mmatch bc m am) (NOSTACK : BcNostack bc) :
    ∃ bc', bcIncr bc bc' ∧ (∀ b, b < m.nextblock → bc' b = bc b) ∧
      Vmatch bc' vres Vtop ∧ GenvMatch bc' ge ∧ Romatch bc' m' rm ∧
      Mmatch bc' m' mtop ∧ BcNostack bc' ∧
      (∀ b ofs n, Mem.validBlock m b = true → bc b = .BCinvalid →
        Mem.loadbytes m' b ofs n = Mem.loadbytes m b ofs n) := by
  -- Part 1: using `ec_mem_inject`
  have ARGS' : Val.InjectList (injOfBc bc) vargs vargs := by
    clear EC
    induction vargs with
    | nil => exact .nil
    | cons v vl ih =>
      exact .cons (vmatch_inj (ARGS v (List.mem_cons_self ..)))
        (ih (fun v h => ARGS v (List.mem_cons_of_mem _ h)))
  obtain ⟨j', vres', m'', _, IRES, IMEM, UNCH1, _, IINCR, ISEP⟩ :=
    hinj _ _ _ _ _ _ _ _ _ _ (symbolsInject_of_bc GENV) EC (mmatch_inj MM) ARGS'
  have JBELOW : ∀ b, b < m.nextblock → j' b = injOfBc bc b := by
    intro b hb
    cases e : injOfBc bc b with
    | some p => obtain ⟨b', d⟩ := p; exact IINCR _ _ _ e
    | none =>
      cases e' : j' b with
      | none => rfl
      | some p =>
        obtain ⟨b'', d'⟩ := p
        have := (ISEP _ _ _ e e').1
        rw [(Mem.validBlock_iff m b).2 hb] at this; cases this
  -- Part 2: constructing `bc'` from `j'`
  let f : Block → BlockClass := fun b =>
    if b < m.nextblock then bc b
    else match j' b with
      | none => .BCinvalid
      | some _ => .BCother
  have F_bc : ∀ b c, f b = c → c = .BCstack ∨ (∃ id, c = .BCglob id) → bc b = c := by
    intro b c h hc
    by_cases hb : b < m.nextblock
    · simpa [f, hb] using h
    · simp only [f, hb, if_false] at h
      split at h <;> (subst h; rcases hc with hc | ⟨_, hc⟩ <;> cases hc)
  let bc' : BlockClassification :=
    { bc_img := f
      bc_stack := fun b1 b2 h1 h2 =>
        bc.bc_stack b1 b2 (F_bc _ _ h1 (.inl rfl)) (F_bc _ _ h2 (.inl rfl))
      bc_glob := fun b1 b2 id h1 h2 =>
        bc.bc_glob b1 b2 id (F_bc _ _ h1 (.inr ⟨id, rfl⟩)) (F_bc _ _ h2 (.inr ⟨id, rfl⟩)) }
  have BELOW : ∀ b, b < m.nextblock → bc' b = bc b := fun b hb => by
    show f b = bc b; simp [f, hb]
  have INCR : bcIncr bc bc' := fun b hb => BELOW b (MM.mmatch_below b hb)
  have ABOVE : ∀ b, ¬ b < m.nextblock → bc' b = match j' b with
      | none => .BCinvalid
      | some _ => .BCother := fun b hb => by
    show f b = _; simp only [f, hb, if_false]
  have BC'INV : ∀ b, bc' b ≠ .BCinvalid → ∃ b' delta, j' b = some (b', delta) := by
    intro b hb
    by_cases h : b < m.nextblock
    · rw [BELOW b h] at hb
      exact ⟨b, 0, by rw [JBELOW b h]; exact inj_of_bc_valid bc hb⟩
    · rw [ABOVE b h] at hb
      cases e : j' b with
      | none => rw [e] at hb; exact absurd rfl hb
      | some p => exact ⟨p.1, p.2, rfl⟩
  -- Part 3: injection wrt `j'` implies matching with top wrt `bc'`
  have PMTOP : ∀ b b' delta ofs, j' b = some (b', delta) → Pmatch bc' b ofs .Ptop := by
    intro b b' delta ofs hj
    refine .top ?_
    by_cases h : b < m.nextblock
    · rw [BELOW b h]; rw [JBELOW b h] at hj; exact (inj_of_bc_inv bc hj).1
    · rw [ABOVE b h, hj]; simp
  have VMTOP : ∀ v v', Val.Inject j' v v' → Vmatch bc' v Vtop := by
    intro v v' h
    cases h with
    | ptr delta hf _ => exact .ifptr_p _ _ _ (PMTOP _ _ _ _ hf)
    | _ => constructor
  have SMTOP : ∀ b, bc' b ≠ .BCinvalid → Smatch bc' m' b .Ptop := by
    intro b hb
    obtain ⟨b', delta, J'⟩ := BC'INV b hb
    refine ⟨fun chunk ofs v hl => ?_, fun ofs b2 ofs' q i hl => ?_⟩
    · obtain ⟨v', _, B⟩ := Mem.load_inject IMEM hl J'
      exact VMTOP _ _ B
    · obtain ⟨bytes', _, B⟩ := Mem.loadbytes_inject IMEM hl J'
      cases B with
      | cons hmv _ =>
        cases hmv with
        | frag _ _ hv =>
          cases hv with
          | ptr delta hf _ => exact PMTOP _ _ _ _ hf
  have NB : m.nextblock.toNat ≤ m'.nextblock.toNat := UNCH1.nextblock_le
  -- Conclusions
  refine ⟨bc', INCR, BELOW, VMTOP _ _ IRES, ?_, ?_, ?_, ?_, ?_⟩
  · -- genv match
    refine genv_match_exten GENV (fun b id => ⟨fun h => ?_, fun h => ?_⟩) (fun b h => ?_)
    · rw [INCR b (by rw [h]; simp)]; exact h
    · by_cases hb : b < m.nextblock
      · rw [BELOW b hb] at h; exact h
      · rw [ABOVE b hb] at h; split at h <;> cases h
    · rw [INCR b (by rw [h]; simp)]; exact h
  · -- romatch m'
    intro b id ab hb hrm
    by_cases h : b < m.nextblock
    · rw [BELOW b h] at hb
      obtain ⟨R, P, Q⟩ := RO b id ab hb hrm
      have hv : Mem.validBlock m b = true := (Mem.validBlock_iff m b).2 h
      refine ⟨R, bmatch_incr INCR (bmatch_ext P fun ofs n bytes hl _ => ?_), fun ofs => ?_⟩
      · rw [← (hprops.readonly _ _ _ _ _ EC).loadbytes_1 hv (fun i _ _ => by
          simp [locNotWritable, Q i])]
        exact hl
      · cases e : Mem.perm m' b ofs .Max .Writable
        · rfl
        · have := hprops.maxPerm _ _ _ _ _ _ _ _ EC hv e
          rw [Q ofs] at this; cases this
    · rw [ABOVE b h] at hb; split at hb <;> cases hb
  · -- mmatch top
    refine ⟨fun b hb => ?_, fun id ab b _ hg => ?_, fun b _ h2 => SMTOP b h2,
      fun b hb => SMTOP b hb, fun b hb => ?_⟩
    · exact ablock_init_sound (SMTOP b (by rw [hb]; simp))
    · simp [mtop, minit] at hg
    · by_cases h : b < m.nextblock
      · exact Nat.lt_of_lt_of_le h NB
      · obtain ⟨b', delta, J'⟩ := BC'INV b hb
        exact (Mem.validBlock_iff m' b).1 (Mem.validBlock_inject_1 J' IMEM)
  · -- nostack
    intro b hb
    by_cases h : b < m.nextblock
    · rw [BELOW b h] at hb; exact NOSTACK b hb
    · rw [ABOVE b h] at hb; split at hb <;> cases hb
  · -- unmapped blocks are invariant
    intro b ofs n hv hb
    exact UNCH1.loadbytes_1 hv (fun _ _ _ => by
      show injOfBc bc b = none
      unfold injOfBc; rw [hb])

end ValueAnalysis
end CC
