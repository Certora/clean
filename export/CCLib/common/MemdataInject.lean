/-
  Compatibility of the byte-level encoding with memory injections — port of
  the "Compatibility with memory injections" section of `common/Memdata.v`
  (`memval_inject`, `decode_val_inject`, `encode_val_inject`,
  `memval_inject_compose`) together with the value-level facts it needs from
  `common/Values.v` (`load_result_inject`, `val_inject_compose`).

  Rocq's `list_forall2 (memval_inject f)` is the inductive `MemvalInjectList`.
-/
import CCLib.common.ValuesLemmas
import CCLib.lib.IntegersPtrofs
import CCLib.common.Memdata

namespace CC

namespace Val

/-- `Values.val_inject_compose` -/
theorem inject_compose {f f' : Meminj} {v1 v2 v3 : Val} (h1 : Inject f v1 v2)
    (h2 : Inject f' v2 v3) : Inject (compose_meminj f f') v1 v3 := by
  cases h1 with
  | int => cases h2; exact .int _
  | long => cases h2; exact .long _
  | float => cases h2; exact .float _
  | single => cases h2; exact .single _
  | undef => exact .undef _
  | ptr d hf ho =>
    cases h2 with
    | ptr d' hf' ho' =>
      refine .ptr (d + d') (by simp [compose_meminj, hf, hf']) ?_
      rw [ho', ho, Integers.Ptrofs.add_assoc, ← Integers.Ptrofs.repr_add]

/-- `Values.Val.load_result_inject` -/
theorem loadResult_inject {f : Meminj} (chunk : Chunk) {v1 v2 : Val} (h : Inject f v1 v2) :
    Inject f (loadResult chunk v1) (loadResult chunk v2) := by
  cases h with
  | undef => cases chunk <;> exact .undef _
  | int n =>
    cases chunk <;> simp only [loadResult] <;> first | exact .int _ | exact .undef _ | skip
    simp only [normBool]; split <;> first | exact .int _ | exact .undef _
  | long => cases chunk <;> simp only [loadResult] <;> first | exact .long _ | exact .undef _
  | float => cases chunk <;> simp only [loadResult] <;> first | exact .float _ | exact .undef _
  | single => cases chunk <;> simp only [loadResult] <;> first | exact .single _ | exact .undef _
  | ptr d hf ho =>
    cases chunk <;> simp only [loadResult, Archi.ptr64] <;>
      first | exact .undef _ | exact .ptr d hf ho

end Val

/-! ## `memval_inject` -/

/-- `Memdata.memval_inject` -/
inductive MemvalInject (f : Val.Meminj) : MemVal → MemVal → Prop where
  | byte (n : Byte) : MemvalInject f (.Byte n) (.Byte n)
  | frag {v1 v2 : Val} (q : Quantity) (n : Nat) :
      Val.Inject f v1 v2 → MemvalInject f (.Fragment v1 q n) (.Fragment v2 q n)
  | undef (mv : MemVal) : MemvalInject f .Undef mv

/-- `list_forall2 (memval_inject f)` -/
inductive MemvalInjectList (f : Val.Meminj) : List MemVal → List MemVal → Prop where
  | nil : MemvalInjectList f [] []
  | cons {a b l l'} : MemvalInject f a b → MemvalInjectList f l l' →
      MemvalInjectList f (a :: l) (b :: l')

/-- `Memdata.memval_inject_incr` -/
theorem MemvalInject.incr {f f' : Val.Meminj} {v1 v2 : MemVal} (h : MemvalInject f v1 v2)
    (hi : Val.inject_incr f f') : MemvalInject f' v1 v2 := by
  cases h with
  | byte => exact .byte _
  | frag q n hv => exact .frag q n (Val.inject_incr_inject hi hv)
  | undef => exact .undef _

/-- `Memdata.memval_inject_compose` -/
theorem MemvalInject.compose {f f' : Val.Meminj} {v1 v2 v3 : MemVal}
    (h1 : MemvalInject f v1 v2) (h2 : MemvalInject f' v2 v3) :
    MemvalInject (Val.compose_meminj f f') v1 v3 := by
  cases h1 with
  | byte => cases h2; exact .byte _
  | frag q n hv => cases h2 with | frag _ _ hv' => exact .frag q n (Val.inject_compose hv hv')
  | undef => exact .undef _

/-- `Memdata.memval_lessdef` -/
def MemvalLessdef : MemVal → MemVal → Prop := MemvalInject Val.inject_id

/-- `Memdata.memval_lessdef_refl` -/
theorem memvalLessdef_refl (mv : MemVal) : MemvalLessdef mv mv := by
  cases mv with
  | Undef => exact .undef _
  | Byte b => exact .byte b
  | Fragment v q n => exact .frag q n (Val.lessdef_inject_id.mp (.refl v))

/-! ## Decoding -/

section
variable {f : Val.Meminj}

/-- `Memdata.proj_bytes_inject` -/
theorem projBytes_inject {vl vl' : List MemVal} (h : MemvalInjectList f vl vl') {bl}
    (hp : projBytes vl = some bl) : projBytes vl' = some bl := by
  induction h generalizing bl with
  | nil => exact hp
  | @cons a b l l' ha _ ih =>
    cases ha with
    | byte n =>
      simp only [projBytes] at hp ⊢
      cases hq : projBytes l with
      | none => rw [hq] at hp; cases hp
      | some l0 => rw [hq] at hp; rw [ih hq]; exact hp
    | frag => simp [projBytes] at hp
    | undef => simp [projBytes] at hp

/-- `Memdata.check_value_inject` -/
theorem checkValue_inject {vl vl' : List MemVal} (h : MemvalInjectList f vl vl') :
    ∀ {n v v' q}, checkValue n v q vl = true → Val.Inject f v v' → v ≠ .Vundef →
      checkValue n v' q vl' = true := by
  induction h with
  | nil => intro n v v' q hc _ _; cases n <;> simp_all [checkValue]
  | cons ha _ ih =>
    intro n v v' q hc hv hne
    cases n with
    | zero => simp [checkValue] at hc
    | succ n =>
      cases ha with
      | byte => simp [checkValue] at hc
      | undef => simp [checkValue] at hc
      | @frag v1 v2 q0 n0 hv12 =>
        simp only [checkValue, Bool.and_eq_true, beq_iff_eq] at hc ⊢
        obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hc⟩ := hc
        refine ⟨⟨⟨?_, rfl⟩, rfl⟩, ih hc hv hne⟩
        cases hv with
        | undef => exact absurd rfl hne
        | int => cases hv12; rfl
        | long => cases hv12; rfl
        | float => cases hv12; rfl
        | single => cases hv12; rfl
        | ptr d hf ho =>
          cases hv12 with
          | ptr d' hf' ho' =>
            rw [hf] at hf'; cases hf'; rw [ho, ho']

/-- `Memdata.proj_value_inject` -/
theorem projValue_inject (q : Quantity) {vl1 vl2 : List MemVal}
    (h : MemvalInjectList f vl1 vl2) : Val.Inject f (projValue q vl1) (projValue q vl2) := by
  cases h with
  | nil => exact .undef _
  | @cons a b l l' ha hl =>
    cases ha with
    | byte => exact .undef _
    | undef => exact .undef _
    | @frag v1 v2 q0 n hv =>
      simp only [projValue]
      split
      · rename_i hc
        by_cases hu : v1 = .Vundef
        · subst hu; exact .undef _
        · rw [checkValue_inject (.cons (.frag q0 n hv) hl) hc hv hu]
          exact hv
      · exact .undef _

/-- `Memdata.proj_bytes_not_inject` -/
theorem projBytes_not_inject {vl vl' : List MemVal} (h : MemvalInjectList f vl vl')
    (h1 : projBytes vl = none) (h2 : projBytes vl' ≠ none) : MemVal.Undef ∈ vl := by
  induction h with
  | nil => simp [projBytes] at h1
  | cons ha _ ih =>
    cases ha with
    | byte n =>
      apply List.mem_cons_of_mem
      apply ih
      · simp only [projBytes] at h1
        cases hq : projBytes _ with
        | none => rfl
        | some _ => rw [hq] at h1; cases h1
      · intro hn; apply h2; simp [projBytes, hn]
    | frag => simp [projBytes] at h2
    | undef => exact List.mem_cons_self

/-- `Memdata.check_value_undef` -/
theorem checkValue_undef : ∀ (n : Nat) (q : Quantity) (v : Val) (vl : List MemVal),
    MemVal.Undef ∈ vl → checkValue n v q vl = false := by
  intro n
  induction n with
  | zero => intro q v vl h; cases vl with
    | nil => simp at h
    | cons a l => rfl
  | succ n ih =>
    intro q v vl h
    cases vl with
    | nil => rfl
    | cons a l =>
      cases a with
      | Undef => rfl
      | Byte _ => rfl
      | Fragment v' q' m' =>
        simp only [List.mem_cons, reduceCtorEq, false_or] at h
        simp [checkValue, ih q v l h]

/-- `Memdata.proj_value_undef` -/
theorem projValue_undef (q : Quantity) (vl : List MemVal) (h : MemVal.Undef ∈ vl) :
    projValue q vl = .Vundef := by
  unfold projValue
  split
  · rw [checkValue_undef _ _ _ _ h]; rfl
  · rfl

/-- `Memdata.decode_val_inject` -/
theorem decodeVal_inject (chunk : Chunk) {vl1 vl2 : List MemVal}
    (h : MemvalInjectList f vl1 vl2) :
    Val.Inject f (decodeVal chunk vl1) (decodeVal chunk vl2) := by
  unfold decodeVal
  cases hp1 : projBytes vl1 with
  | some bl1 =>
    rw [projBytes_inject h hp1]
    cases chunk <;> simp only <;>
      (first | exact .int _ | exact .long _ | exact .float _ | exact .single _ | exact .undef _ | skip)
    simp only [Val.normBool]; split <;> first | exact .int _ | exact .undef _
  | none =>
    have hA : ∀ (q : Quantity) (g : List Byte → Val),
        Val.Inject f (Val.loadResult chunk (projValue q vl1))
          (match projBytes vl2 with
           | some bl => g bl
           | none => Val.loadResult chunk (projValue q vl2)) := by
      intro q g
      cases hp2 : projBytes vl2 with
      | some bl2 =>
        rw [projValue_undef q vl1 (projBytes_not_inject h hp1 (by simp [hp2]))]
        cases chunk <;> exact .undef _
      | none => exact Val.loadResult_inject chunk (projValue_inject q h)
    cases chunk <;> simp only [Archi.ptr64, ite_true] <;>
      first | exact .undef _ | skip
    · cases hp2 : projBytes vl2 with
      | some bl2 =>
        simp only
        rw [projValue_undef _ vl1 (projBytes_not_inject h hp1 (by simp [hp2]))]
        exact .undef _
      | none => exact Val.loadResult_inject _ (projValue_inject _ h)
    · cases hp2 : projBytes vl2 with
      | some bl2 =>
        simp only
        rw [projValue_undef _ vl1 (projBytes_not_inject h hp1 (by simp [hp2]))]
        exact .undef _
      | none => exact Val.loadResult_inject _ (projValue_inject _ h)
    · cases hp2 : projBytes vl2 with
      | some bl2 =>
        simp only
        rw [projValue_undef _ vl1 (projBytes_not_inject h hp1 (by simp [hp2]))]
        exact .undef _
      | none => exact Val.loadResult_inject _ (projValue_inject _ h)

/-! ## Encoding -/

/-- `Memdata.inj_bytes_inject` -/
theorem injBytes_inject (bl : List Byte) : MemvalInjectList f (injBytes bl) (injBytes bl) := by
  induction bl with
  | nil => exact .nil
  | cons b bl ih => exact .cons (.byte b) ih

/-- `Memdata.repeat_Undef_inject_any` -/
theorem replicate_Undef_inject_any (vl : List MemVal) :
    MemvalInjectList f (List.replicate vl.length .Undef) vl := by
  induction vl with
  | nil => exact .nil
  | cons a l ih => exact .cons (.undef a) ih

/-- `Memdata.repeat_Undef_inject_self` -/
theorem replicate_Undef_inject_self (n : Nat) :
    MemvalInjectList f (List.replicate n .Undef) (List.replicate n .Undef) := by
  have := replicate_Undef_inject_any (f := f) (List.replicate n .Undef)
  rwa [List.length_replicate] at this

/-- `Memdata.repeat_Undef_inject_encode_val` -/
theorem replicate_Undef_inject_encodeVal (chunk : Chunk) (v : Val) :
    MemvalInjectList f (List.replicate (sizeChunkNat chunk) .Undef) (encodeVal chunk v) := by
  have := replicate_Undef_inject_any (f := f) (encodeVal chunk v)
  rwa [length_encodeVal] at this

/-- `Memdata.inj_value_inject` -/
theorem injValue_inject {v1 v2 : Val} (q : Quantity) (h : Val.Inject f v1 v2) :
    MemvalInjectList f (injValue q v1) (injValue q v2) := by
  unfold injValue
  generalize sizeQuantityNat q = n
  induction n with
  | zero => exact .nil
  | succ n ih => exact .cons (.frag q n h) ih

/-- `Memdata.encode_val_inject` -/
theorem encodeVal_inject (chunk : Chunk) {v1 v2 : Val} (h : Val.Inject f v1 v2) :
    MemvalInjectList f (encodeVal chunk v1) (encodeVal chunk v2) := by
  cases h with
  | int n => cases chunk <;> simp only [encodeVal] <;>
      (first | exact injBytes_inject _ | exact replicate_Undef_inject_self _
             | exact injValue_inject _ (.int n))
  | long n => cases chunk <;> simp only [encodeVal] <;>
      (first | exact injBytes_inject _ | exact replicate_Undef_inject_self _
             | exact injValue_inject _ (.long n))
  | float x => cases chunk <;> simp only [encodeVal] <;>
      (first | exact injBytes_inject _ | exact replicate_Undef_inject_self _
             | exact injValue_inject _ (.float x))
  | single x => cases chunk <;> simp only [encodeVal] <;>
      (first | exact injBytes_inject _ | exact replicate_Undef_inject_self _
             | exact injValue_inject _ (.single x))
  | ptr d hf ho => cases chunk <;> simp only [encodeVal, Archi.ptr64, ite_true] <;>
      (first | exact replicate_Undef_inject_self _ | exact injValue_inject _ (.ptr d hf ho))
  | undef v =>
    cases chunk <;> simp only [encodeVal] <;>
      (first
        | exact replicate_Undef_inject_encodeVal _ _
        | exact injValue_inject _ (.undef _)
        | (cases v <;> simp only [encodeVal] <;>
            (first
              | exact replicate_Undef_inject_encodeVal _ _
              | exact injValue_inject _ (.undef _))))

end

end CC
