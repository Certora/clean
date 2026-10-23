/-
  Semantic correctness of the operations over the initialization state — port
  of the "Semantic correctness of state operations" and "Total size
  properties" parts of `cfrontend/Initializersproof.v`.

  `MatchState ge s m b` says that the abstract initialization state `s`
  describes the contents of block `b` of memory `m`: the first `s.curr` bytes
  are the bytes denoted by the initialization data of `s`, and the bytes from
  `s.curr` to `s.total_size` read as zeros.  The operations `pad_to`,
  `load_int`, `store_data`, `store_int` and `init_data_list_of_state` are
  proved correct with respect to this interpretation.
-/
import CCLib.cfrontend.InitializersproofState
import CCLib.common.MemdataTheory

namespace CC
namespace Initializersproof

open Initializers Mem

local macro "zomega" : tactic => `(tactic| ((try dsimp only [CC.Z] at *) <;> omega))

private theorem res_bind_eq_OK {A B : Type} {x : Res A} {f : A → Res B} {b : B} :
    (bind x f = Res.OK b) ↔ ∃ a, x = .OK a ∧ f a = .OK b := by
  cases x <;> simp [bind, Res.bind]

private theorem assertion_eq_OK {A : Type} {c : Bool} {k : Res A} {a : A}
    (h : assertion c k = .OK a) : c = true ∧ k = .OK a := by
  unfold assertion at h
  split at h
  · exact ⟨by assumption, h⟩
  · cases h

section MATCH

variable {F V : Type} (ge : Genv F V)

local notation "boid" => Genv.bytesOfInitData ge
local notation "boidl" => Genv.bytesOfInitDataList ge

/-! ## Semantic interpretation of states -/

/-- `Initializersproof.match_state` -/
structure MatchState (s : Initializers.State) (m : Mem) (b : Block) : Prop where
  range : 0 ≤ s.curr ∧ s.curr ≤ s.total_size
  contents : Mem.loadbytes m b 0 s.curr = some (boidl s.init.reverse)
  valid : IdlValid ge 0 s.init.reverse
  uninitialized : ReadsAsZeros m b s.curr s.total_size

variable {ge}

/-- `Initializersproof.match_size` -/
theorem match_size {s : Initializers.State} {m : Mem} {b : Block} (h : MatchState ge s m b) :
    InitData.listSize s.init.reverse = s.curr := by
  rw [initDataListSize_boidl ge, loadbytes_length h.contents]
  have := h.range.1
  zomega

/-- `Initializersproof.curr_pad_to` -/
theorem curr_padTo (s : Initializers.State) (pos : Z) :
    s.curr ≤ (padTo s pos).curr ∧ pos ≤ (padTo s pos).curr := by
  unfold padTo
  split
  · exact ⟨Int.le_refl _, by assumption⟩
  · exact ⟨by zomega, Int.le_refl _⟩

/-- `Initializersproof.total_size_pad_to` -/
theorem totalSize_padTo (s : Initializers.State) (pos : Z) : (padTo s pos).total_size = s.total_size := by
  unfold padTo; split <;> rfl

/-- `Initializersproof.pad_to_correct` -/
theorem padTo_correct {pos : Z} {s : Initializers.State} {m : Mem} {b : Block} (h : MatchState ge s m b)
    (hp : pos ≤ s.total_size) : MatchState ge (padTo s pos) m b := by
  unfold padTo
  split
  · exact h
  · next hlt =>
    have r := h.range
    refine ⟨⟨by zomega, hp⟩, ?_, ?_, ?_⟩
    · show Mem.loadbytes m b 0 pos = some (boidl (InitData.Init_space (pos - s.curr) :: s.init).reverse)
      rw [boidl_reverse_cons]
      have := loadbytes_concat h.contents
        (readsAsZeros_loadbytes' h.uninitialized (pos - s.curr) (0 + s.curr) (by zomega)
          (by zomega) (by zomega)) r.1 (by zomega)
      rw [show s.curr + (pos - s.curr) = pos by zomega] at this
      exact this
    · show IdlValid ge 0 (InitData.Init_space (pos - s.curr) :: s.init).reverse
      rw [List.reverse_cons, idlValid_app]
      exact ⟨h.valid, idlValid_space ge _ _⟩
    · exact readsAsZeros_mono h.uninitialized (by zomega) (Int.le_refl _)

/-- `Initializersproof.trisection_correct` -/
theorem trisection_correct {s : Initializers.State} {m : Mem} {b : Block} {pos sz : Z}
    {bytes1 bytes2 : List Integers.Byte} {il : List InitData} (h : MatchState ge s m b)
    (ht : trisection s.init (s.curr - (pos + sz)) sz = .OK (bytes1, bytes2, il))
    (h0 : 0 ≤ pos) (h1 : pos + sz ≤ s.curr) (h2 : 0 ≤ sz) :
    Mem.loadbytes m b 0 pos = some (boidl il.reverse) ∧
      Mem.loadbytes m b pos sz = some (injBytes bytes2) ∧
      Mem.loadbytes m b (pos + sz) (s.curr - (pos + sz)) = some (injBytes bytes1) := by
  obtain ⟨A, B, C⟩ := trisection_boidl ge ht
  have D := h.contents
  rw [show s.curr = (pos + sz) + (s.curr - (pos + sz)) by zomega] at D
  obtain ⟨bytes0, bytes1', LB0, LB1, E1⟩ := loadbytes_split D (by zomega) (by zomega)
  have LB0' : Mem.loadbytes m b 0 (pos + sz) = some bytes0 := LB0
  rw [show (0 : _root_.Int) + (pos + sz) = pos + sz by zomega] at LB1
  obtain ⟨bytes3, bytes2', LB3, LB2, E2⟩ := loadbytes_split LB0' h0 h2
  rw [show (0 : _root_.Int) + pos = pos by zomega] at LB2
  rw [A] at E1
  obtain ⟨E3, E4⟩ := List.append_inj' E1 (by
    rw [length_injBytes, loadbytes_length LB1, B])
  rw [E2] at E3
  obtain ⟨E5, E6⟩ := List.append_inj' E3 (by
    rw [length_injBytes, loadbytes_length LB2, C])
  refine ⟨?_, ?_, ?_⟩
  · rw [LB3, E5]
  · rw [LB2, E6]
  · rw [LB1, E4]

/-- `Initializersproof.decode_int_zero_ext`, for 1-byte carriers. -/
private theorem zeroExt8_repr {x : _root_.Int} (h0 : 0 ≤ x) (h1 : x < 256) :
    Integers.Int.zero_ext 8 (Integers.Int.repr x) = Integers.Int.repr x := by
  apply BitVec.eq_of_toNat_eq
  show (Integers.MI.zero_ext 8 (BitVec.ofInt 32 x)).toNat = (BitVec.ofInt 32 x).toNat
  rw [toNat_zero_ext_8, BitVec.toNat_ofInt]
  omega

/-- `Initializersproof.decode_int_zero_ext`, for 2-byte carriers. -/
private theorem zeroExt16_repr {x : _root_.Int} (h0 : 0 ≤ x) (h1 : x < 65536) :
    Integers.Int.zero_ext 16 (Integers.Int.repr x) = Integers.Int.repr x := by
  apply BitVec.eq_of_toNat_eq
  show (Integers.MI.zero_ext 16 (BitVec.ofInt 32 x)).toNat = (BitVec.ofInt 32 x).toNat
  rw [toNat_zero_ext_16, BitVec.toNat_ofInt]
  omega

private theorem decodeInt_range (bl : List Integers.Byte) :
    0 ≤ decodeInt bl ∧ decodeInt bl < 2 ^ (bl.length * 8) := by
  simp only [decodeInt, revIfBe_id]
  exact intOfBytes_range bl

/-- `Initializersproof.load_int_correct` -/
theorem loadInt_correct {s : Initializers.State} {m : Mem} {b : Block} {pos : Z} {isz : IntSize}
    {i : Integers.Int} {v : Val} (h : MatchState ge s m b) (hr : loadInt s pos isz = .OK i)
    (hl : Mem.load (Cop.chunkForCarrier isz) m b pos = some v) : v = .Vint i := by
  have hva := load_valid_access hl
  simp only [validAccess, Bool.and_eq_true, beq_iff_eq] at hva
  unfold loadInt at hr
  obtain ⟨hc, hr⟩ := assertion_eq_OK hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨b1, b2, il⟩, ET, hr⟩ := res_bind_eq_OK.mp hr
  cases hr
  have hsz := sizeChunk_pos (Cop.chunkForCarrier isz)
  have MS' := padTo_correct h hc.2
  have hcp := (curr_padTo s (pos + sizeChunk (Cop.chunkForCarrier isz))).2
  obtain ⟨-, L2, -⟩ := trisection_correct MS' ET hc.1 hcp (by zomega)
  have LD := loadbytes_load L2 (Int.dvd_of_emod_eq_zero hva.2)
  rw [hl] at LD
  cases LD
  have LEN := loadbytes_length L2
  rw [length_injBytes] at LEN
  have R := decodeInt_range b2
  rw [LEN] at R
  cases isz with
  | I8 =>
    simp only [Cop.chunkForCarrier, decodeVal, projBytes_injBytes]
    exact congrArg Val.Vint (zeroExt8_repr R.1 R.2)
  | IBool =>
    simp only [Cop.chunkForCarrier, decodeVal, projBytes_injBytes]
    exact congrArg Val.Vint (zeroExt8_repr R.1 R.2)
  | I16 =>
    simp only [Cop.chunkForCarrier, decodeVal, projBytes_injBytes]
    exact congrArg Val.Vint (zeroExt16_repr R.1 R.2)
  | I32 =>
    simp only [Cop.chunkForCarrier, decodeVal, projBytes_injBytes]

/-- `Initializersproof.loadbytes_concat_3` -/
theorem loadbytes_concat_3 {m : Mem} {b : Block} {ofs1 len1 ofs2 len2 ofs3 len3 len : _root_.Int}
    {l1 l2 l3 : List MemVal}
    (H1 : Mem.loadbytes m b ofs1 len1 = some l1) (H2 : Mem.loadbytes m b ofs2 len2 = some l2)
    (H3 : Mem.loadbytes m b ofs3 len3 = some l3)
    (e2 : ofs2 = ofs1 + len1) (e3 : ofs3 = ofs2 + len2) (h1 : 0 ≤ len1) (h2 : 0 ≤ len2)
    (h3 : 0 ≤ len3) (e : len = len1 + len2 + len3) :
    Mem.loadbytes m b ofs1 len = some (l1 ++ l2 ++ l3) := by
  subst e2 e3 e
  exact loadbytes_concat (loadbytes_concat H1 H2 h1 h2)
    (by rw [← Int.add_assoc]; exact H3) (by omega) h3

/-- `Initializersproof.store_data_correct` -/
theorem storeData_correct {s : Initializers.State} {m : Mem} {b : Block} {pos : Z} {i : InitData}
    {s' : Initializers.State} {m' : Mem} (h : MatchState ge s m b)
    (hst : storeData s pos i = .OK s') (hsi : Genv.storeInitData ge m b pos i = some m')
    (hns : NotSpace i) : MatchState ge s' m' b := by
  have ALIGN := Genv.storeInitData_aligned ge hsi
  have VALID : IdValid ge i := by
    cases i with
    | Init_addrof id ofs =>
      simp only [Genv.storeInitData] at hsi
      split at hsi
      · cases hsi
      · next b0 hb => exact ⟨b0, hb⟩
    | _ => trivial
  have hsz := Genv.InitData.size_nonneg i
  unfold storeData at hst
  obtain ⟨hc, hst⟩ := assertion_eq_OK hst
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  have U : UnchangedOn (fun _ o => ¬(pos ≤ o ∧ o < pos + i.size)) m m' :=
    Genv.storeInitData_unchanged ge _ hsi (fun o h1 h2 hn => hn ⟨h1, h2⟩)
  have D := storeInitData_loadbytes' ge hsi hns
  have r := h.range
  split at hst
  · next hle =>
    cases hst
    have key : ∀ il : List InitData,
        (il = if s.curr < pos then InitData.Init_space (pos - s.curr) :: s.init else s.init) →
        MatchState ge ⟨i :: il, pos + i.size, s.total_size⟩ m' b := by
      intro il hil
      have IL : boidl il.reverse =
          boidl s.init.reverse ++ List.replicate (pos - s.curr).toNat (MemVal.Byte Integers.Byte.zero) := by
        subst hil
        split
        · rw [boidl_reverse_cons]; rfl
        · rw [show (pos - s.curr).toNat = 0 by zomega, List.replicate_zero, List.append_nil]
      have ILS : InitData.listSize il.reverse = pos := by
        subst hil
        split
        · rw [List.reverse_cons, initDataListSize_app, match_size h]
          show s.curr + (max (pos - s.curr) 0 + 0) = pos
          zomega
        · rw [match_size h]; zomega
      have ILV : IdlValid ge 0 il.reverse := by
        subst hil
        split
        · rw [List.reverse_cons, idlValid_app]; exact ⟨h.valid, idlValid_space ge _ _⟩
        · exact h.valid
      refine ⟨⟨by zomega, hc.2⟩, ?_, ?_, ?_⟩
      · show Mem.loadbytes m' b 0 (pos + i.size) = some (boidl (i :: il).reverse)
        rw [boidl_reverse_cons, IL]
        refine loadbytes_concat_3 (len1 := s.curr) (len2 := pos - s.curr) (len3 := i.size)
          (U.loadbytes (fun j a c => by intro hh; zomega) h.contents)
          (U.loadbytes (fun j a c => by intro hh; zomega)
            (readsAsZeros_loadbytes' h.uninitialized (pos - s.curr) s.curr (Int.le_refl _)
              (by zomega) (by zomega)))
          D (by zomega) (by zomega) r.1 (by zomega) hsz (by zomega)
      · show IdlValid ge 0 (i :: il).reverse
        rw [List.reverse_cons, idlValid_app, ILS]
        exact ⟨ILV, by rw [Int.zero_add]; exact ALIGN, VALID, trivial⟩
      · exact readsAsZeros_unchanged (readsAsZeros_mono h.uninitialized (by zomega) (Int.le_refl _))
          U (fun j a c => by intro hh; zomega)
    exact key _ rfl
  · next hlt =>
    obtain ⟨⟨b1, b2, il2⟩, ET, hst⟩ := res_bind_eq_OK.mp hst
    cases hst
    have hcp := (curr_padTo s (pos + i.size)).2
    have MS' := padTo_correct h hc.2
    obtain ⟨L1, L2, L3⟩ := trisection_correct MS' ET hc.1 hcp hsz
    have r' := MS'.range
    refine ⟨r', ?_, ?_, ?_⟩
    · show Mem.loadbytes m' b 0 (padTo s (pos + i.size)).curr =
        some (boidl (addRevBytes b1 (i :: il2)).reverse)
      rw [addRevBytes_spec', boidl_app, boidl_reverse_cons, boidl_init_bytes]
      exact loadbytes_concat_3 (U.loadbytes (fun j a c => by intro hh; zomega) L1) D
        (U.loadbytes (fun j a c => by intro hh; zomega) L3) (by zomega) rfl hc.1 hsz
        (by zomega) (by zomega)
    · show IdlValid ge 0 (addRevBytes b1 (i :: il2)).reverse
      apply addRevBytes_valid
      rw [List.reverse_cons, idlValid_app]
      have ILS : InitData.listSize il2.reverse = pos := by
        rw [initDataListSize_boidl ge, loadbytes_length L1]; zomega
      rw [ILS]
      exact ⟨trisection_valid ge ET MS'.valid, by rw [Int.zero_add]; exact ALIGN, VALID, trivial⟩
    · exact readsAsZeros_unchanged MS'.uninitialized U (fun j a c => by intro hh; zomega)

/-- `Initializersproof.store_int_correct` -/
theorem storeInt_correct {s : Initializers.State} {m : Mem} {b : Block} {pos : Z} {isz : IntSize}
    {n : Integers.Int} {s' : Initializers.State} {m' : Mem} (h : MatchState ge s m b)
    (hst : storeInt s pos isz n = .OK s')
    (hs : Mem.store (Cop.chunkForCarrier isz) m b pos (.Vint n) = some m') :
    MatchState ge s' m' b := by
  refine storeData_correct h hst ?_ ?_ <;> cases isz <;> first | exact hs | trivial

/-- `Genv.init_data_list_aligned` follows from validity. -/
theorem aligned_of_idlValid : ∀ (l : List InitData) (p : Z),
    IdlValid ge p l → Genv.initDataListAligned p l
  | [], _, _ => trivial
  | _ :: l, _, ⟨a, _, h⟩ => ⟨a, aligned_of_idlValid l _ h⟩

/-- The symbols of valid initialization data are defined. -/
theorem symbols_of_idlValid : ∀ (l : List InitData) (p : Z), IdlValid ge p l →
    ∀ id ofs, InitData.Init_addrof id ofs ∈ l → ∃ b, Genv.findSymbol ge id = some b
  | [], _, _, _, _, hin => by cases hin
  | _ :: l, _, ⟨_, hv, h⟩, id, ofs, hin => by
    cases hin with
    | head => exact hv
    | tail _ hin => exact symbols_of_idlValid l _ h id ofs hin

/-- `Initializersproof.init_data_list_of_state_correct` -/
theorem initDataListOfState_correct {s : Initializers.State} {m : Mem} {b : Block}
    {il : List InitData} {b' : Block} {m1 : Mem} (h : MatchState ge s m b)
    (hi : initDataListOfState s = .OK il)
    (hp : Mem.rangePerm m1 b' 0 s.total_size .Cur .Writable = true)
    (hz : ReadsAsZeros m1 b' 0 s.total_size) :
    ∃ m2, Genv.storeInitDataList ge m1 b' 0 il = some m2 ∧
      Mem.loadbytes m2 b' 0 (InitData.listSize il) = Mem.loadbytes m b 0 s.total_size := by
  unfold initDataListOfState at hi
  obtain ⟨hc, hi⟩ := assertion_eq_OK hi
  simp only [decide_eq_true_eq] at hc
  cases hi
  have MS1 := padTo_correct h (pos := s.total_size) (Int.le_refl _)
  have C : (padTo s s.total_size).curr = s.total_size := by
    unfold padTo; split
    · zomega
    · rfl
  have SZ : InitData.listSize (padTo s s.total_size).init.reverse = s.total_size := by
    rw [match_size MS1, C]
  obtain ⟨m2, ST⟩ := Genv.storeInitDataList_exists ge b' _ m1 0
    (by rw [SZ, Int.zero_add]; exact hp) (aligned_of_idlValid _ _ MS1.valid)
    (symbols_of_idlValid _ _ MS1.valid)
  refine ⟨m2, ST, ?_⟩
  have hz' := (readsAsZeros_equiv m1 b' 0 s.total_size).mp hz
  rw [Int.sub_zero, ← SZ] at hz'
  rw [Genv.storeInitDataList_loadbytes ge b' _ ST hz']
  have := MS1.contents
  rw [C] at this
  rw [this]

/-! ## Total size properties -/

/-- `Initializersproof.total_size_store_data` -/
theorem totalSize_storeData {s : Initializers.State} {pos : Z} {i : InitData}
    {s' : Initializers.State} (h : storeData s pos i = .OK s') : s'.total_size = s.total_size := by
  unfold storeData at h
  obtain ⟨_, h⟩ := assertion_eq_OK h
  split at h
  · cases h; rfl
  · obtain ⟨⟨b1, b2, il2⟩, _, h⟩ := res_bind_eq_OK.mp h
    cases h
    exact totalSize_padTo _ _

end MATCH

end Initializersproof
end CC
