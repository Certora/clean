/-
  Correctness of the operations over the initialization state — port of the
  part of `cfrontend/Initializersproof.v` from "Correctness of operations over
  the initialization state" to the end of "Total size properties":

  * the bytes denoted by initialization data (`boidl_*`), and the effect of
    `add_rev_bytes`, `add_zeros`, `decompose`, `normalize` and `trisection` on
    them;
  * validity (`idvalid`, `idlvalid`) and size of initialization data;
  * memory areas that read as zeros (`ReadsAsZeros`);
  * the interpretation `MatchState s m b` of an abstract initialization state
    `s` as the contents of block `b` of memory `m`, and the correctness of
    `pad_to`, `trisection`, `load_int`, `store_data`, `store_int` and
    `init_data_list_of_state` with respect to it;
  * `total_size` is preserved by the translation functions.

  CompCert states these lemmas for a C global environment `ge`; only its
  symbol table is used, so here they are stated for any `Genv F V`.
-/
import CCLib.cfrontend.Initializers
import CCLib.common.GlobalenvsBytes

namespace CC
namespace Initializersproof

open Initializers Mem

/-- `omega` after unfolding the `Z` abbreviation, whose arithmetic instances
    `omega` does not recognise (see the header of `CCLib/common/MemdataLemmas.lean`). -/
local macro "zomega" : tactic => `(tactic| ((try dsimp only [CC.Z] at *) <;> omega))

private theorem res_bind_eq_OK {A B : Type} {x : Res A} {f : A → Res B} {b : B} :
    (bind x f = Res.OK b) ↔ ∃ a, x = .OK a ∧ f a = .OK b := by
  cases x <;> simp [bind, Res.bind]

section BYTES

variable {F V : Type} (ge : Genv F V)

/-! ## Properties of the in-memory bytes denoted by initialization data -/

local notation "boid" => Genv.bytesOfInitData ge
local notation "boidl" => Genv.bytesOfInitDataList ge

/-- `Initializersproof.boidl_app` -/
theorem boidl_app (il1 il2 : List InitData) : boidl (il1 ++ il2) = boidl il1 ++ boidl il2 := by
  induction il1 with
  | nil => rfl
  | cons i il1 ih =>
    show boid i ++ boidl (il1 ++ il2) = (boid i ++ boidl il1) ++ boidl il2
    rw [ih, List.append_assoc]

/-- `Initializersproof.boidl_rev_cons` -/
theorem boidl_rev_cons (i : InitData) (il : List InitData) :
    boidl (il.reverse ++ [i]) = boidl il.reverse ++ boid i := by
  rw [boidl_app]
  show _ ++ (boid i ++ []) = _
  rw [List.append_nil]

theorem boidl_reverse_cons (i : InitData) (il : List InitData) :
    boidl (i :: il).reverse = boidl il.reverse ++ boid i := by
  rw [List.reverse_cons, boidl_rev_cons]

/-- `Initializersproof.byte_of_int` -/
def byteOfInt (n : Integers.Int) : Integers.Byte := Integers.Byte.repr (Integers.Int.unsigned n)

/-- `Initializersproof.byte_of_int_of_byte` -/
theorem byteOfInt_intOfByte (b : Integers.Byte) : byteOfInt (intOfByte b) = b := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofInt 8 ((BitVec.ofInt 32 (b.toNat : _root_.Int)).toNat : _root_.Int)).toNat = b.toNat
  have hb := b.isLt
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofInt]
  simp only [Nat.reducePow] at hb ⊢
  omega

/-- `Initializersproof.inj_bytes_1` -/
theorem injBytes_1 (n : Z) :
    injBytes (encodeInt 1 n) = [MemVal.Byte (Integers.Byte.repr n)] := by
  simp [encodeInt, bytesOfInt, injBytes]

/-- `Initializersproof.inj_bytes_byte` -/
theorem injBytes_byte (b : Integers.Byte) :
    injBytes (encodeInt 1 (Integers.Int.unsigned (intOfByte b))) = [MemVal.Byte b] := by
  rw [injBytes_1]
  exact congrArg (fun x => [MemVal.Byte x]) (byteOfInt_intOfByte b)

/-- `Initializersproof.boidl_init_ints8` -/
theorem boidl_init_ints8 (l : List Integers.Int) :
    boidl (l.map .Init_int8) = injBytes (l.map byteOfInt) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    show injBytes (encodeInt 1 (Integers.Int.unsigned i)) ++ boidl (l.map .Init_int8) = _
    rw [injBytes_1, ih]; rfl

/-- `Initializersproof.boidl_init_bytes` -/
theorem boidl_init_bytes (l : List Integers.Byte) :
    boidl (l.map initByte) = injBytes l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    show injBytes (encodeInt 1 (Integers.Int.unsigned (intOfByte b))) ++ boidl (l.map initByte) = _
    rw [injBytes_byte, ih]; rfl

/-- `Initializersproof.boidl_ints8` -/
theorem boidl_ints8 (i : Integers.Int) (n : Nat) :
    boidl (List.replicate n (.Init_int8 i)) = List.replicate n (MemVal.Byte (byteOfInt i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show injBytes (encodeInt 1 (Integers.Int.unsigned i)) ++ boidl (List.replicate n (.Init_int8 i)) = _
    rw [injBytes_1, ih]; rfl

theorem byteOfInt_zero : byteOfInt Integers.Int.zero = Integers.Byte.zero := by decide

/-! ## Properties of operations over list of initialization data -/

/-- `Initializersproof.add_rev_bytes_spec` -/
theorem addRevBytes_spec (l : List Integers.Byte) (il : List InitData) :
    addRevBytes l il = l.reverse.map initByte ++ il := by
  induction l generalizing il with
  | nil => rfl
  | cons b l ih =>
    rw [addRevBytes, ih, List.reverse_cons, List.map_append, List.append_assoc]; rfl

/-- `Initializersproof.add_rev_bytes_spec'` -/
theorem addRevBytes_spec' (l : List Integers.Byte) (il : List InitData) :
    (addRevBytes l il).reverse = il.reverse ++ l.map initByte := by
  rw [addRevBytes_spec, List.reverse_append, List.map_reverse, List.reverse_reverse]

/-- `Initializersproof.add_zeros_spec` (in the port, `add_zeros` is defined
    by this equation). -/
theorem addZeros_spec (n : Z) (il : List InitData) :
    addZeros n il = List.replicate n.toNat (.Init_int8 Integers.Int.zero) ++ il := rfl

/-- `Initializersproof.decompose_spec` -/
theorem decomposeRec_spec : ∀ (il : List InitData) (accu : List Integers.Byte) (depth : Z)
    (bl : List Integers.Byte) (il' : List InitData),
    decomposeRec accu il depth = .OK (bl, il') →
    ∃ nl : List Integers.Int, il = nl.map .Init_int8 ++ il' ∧
      bl = nl.reverse.map byteOfInt ++ accu ∧ nl.length = depth.toNat
  | il, accu, depth, bl, il', h => by
    unfold decomposeRec at h
    by_cases hd : depth ≤ 0
    · rw [if_pos hd] at h
      cases h
      exact ⟨[], rfl, rfl, by simp; zomega⟩
    · rw [if_neg hd] at h
      match il, h with
      | .Init_int8 n :: il, h =>
        obtain ⟨nl, P, Q, R⟩ := decomposeRec_spec il _ _ bl il' h
        refine ⟨n :: nl, by rw [P]; rfl, ?_, ?_⟩
        · rw [Q, List.reverse_cons, List.map_append, List.append_assoc]; rfl
        · rw [List.length_cons, R]; zomega

/-- `Initializersproof.decompose_spec` -/
theorem decompose_spec {il : List InitData} {depth : Z} {bl : List Integers.Byte}
    {il' : List InitData} (h : decompose il depth = .OK (bl, il')) :
    ∃ nl : List Integers.Int, il = nl.map .Init_int8 ++ il' ∧
      bl = nl.reverse.map byteOfInt ∧ nl.length = depth.toNat := by
  obtain ⟨nl, P, Q, R⟩ := decomposeRec_spec il [] depth bl il' h
  exact ⟨nl, P, by rw [Q, List.append_nil], R⟩

/-- `Initializersproof.normalize_boidl` -/
theorem normalize_boidl : ∀ (il : List InitData) (depth : Z) (il' : List InitData),
    normalize il depth = .OK il' → boidl il'.reverse = boidl il.reverse
  | il, depth, il', h => by
    unfold normalize at h
    by_cases hd : depth ≤ 0
    · rw [if_pos hd] at h; cases h; rfl
    · rw [if_neg hd] at h
      match il, h with
      | .Init_int8 n :: il, h =>
        obtain ⟨il'', E, h⟩ := res_bind_eq_OK.mp h
        cases h
        rw [boidl_reverse_cons, boidl_reverse_cons, normalize_boidl il _ il'' E]
      | .Init_int16 n :: il, h =>
        obtain ⟨il'', E, h⟩ := res_bind_eq_OK.mp h
        cases h
        rw [addRevBytes_spec', boidl_app, boidl_init_bytes, boidl_reverse_cons,
          normalize_boidl il _ il'' E]; rfl
      | .Init_int32 n :: il, h =>
        obtain ⟨il'', E, h⟩ := res_bind_eq_OK.mp h
        cases h
        rw [addRevBytes_spec', boidl_app, boidl_init_bytes, boidl_reverse_cons,
          normalize_boidl il _ il'' E]; rfl
      | .Init_int64 n :: il, h =>
        obtain ⟨il'', E, h⟩ := res_bind_eq_OK.mp h
        cases h
        rw [addRevBytes_spec', boidl_app, boidl_init_bytes, boidl_reverse_cons,
          normalize_boidl il _ il'' E]; rfl
      | .Init_float32 n :: il, h =>
        obtain ⟨il'', E, h⟩ := res_bind_eq_OK.mp h
        cases h
        rw [addRevBytes_spec', boidl_app, boidl_init_bytes, boidl_reverse_cons,
          normalize_boidl il _ il'' E]; rfl
      | .Init_float64 n :: il, h =>
        obtain ⟨il'', E, h⟩ := res_bind_eq_OK.mp h
        cases h
        rw [addRevBytes_spec', boidl_app, boidl_init_bytes, boidl_reverse_cons,
          normalize_boidl il _ il'' E]; rfl
      | .Init_space z :: il, h =>
        simp only at h
        by_cases hn : max 0 z ≤ depth
        · rw [if_pos hn] at h
          obtain ⟨il'', E, h⟩ := res_bind_eq_OK.mp h
          cases h
          rw [addZeros_spec, List.reverse_append, boidl_app, normalize_boidl il _ il'' E,
            List.reverse_replicate, boidl_ints8, boidl_reverse_cons, byteOfInt_zero]
          show _ ++ List.replicate _ _ = _ ++ List.replicate _ _
          rw [show (max 0 z).toNat = z.toNat by zomega]
        · rw [if_neg hn] at h
          cases h
          rw [addZeros_spec, List.reverse_append, boidl_app, List.reverse_replicate, boidl_ints8,
            boidl_reverse_cons, boidl_reverse_cons, byteOfInt_zero, List.append_assoc]
          show _ ++ (List.replicate _ _ ++ List.replicate _ _) = _ ++ List.replicate _ _
          rw [List.replicate_append_replicate, show (max 0 z - depth).toNat + depth.toNat = z.toNat by zomega]

/-- `Initializersproof.trisection_boidl` -/
theorem trisection_boidl {il : List InitData} {depth sz : Z} {bytes1 bytes2 : List Integers.Byte}
    {il' : List InitData} (h : trisection il depth sz = .OK (bytes1, bytes2, il')) :
    boidl il.reverse = boidl il'.reverse ++ injBytes bytes2 ++ injBytes bytes1 ∧
      bytes1.length = depth.toNat ∧ bytes2.length = sz.toNat := by
  unfold trisection at h
  obtain ⟨il0, E0, h⟩ := res_bind_eq_OK.mp h
  obtain ⟨⟨b1, il1⟩, E1, h⟩ := res_bind_eq_OK.mp h
  obtain ⟨⟨b2, il2⟩, E2, h⟩ := res_bind_eq_OK.mp h
  cases h
  obtain ⟨nl1, A1, B1, C1⟩ := decompose_spec E1
  obtain ⟨nl2, A2, B2, C2⟩ := decompose_spec E2
  refine ⟨?_, ?_, ?_⟩
  · rw [← normalize_boidl ge il _ il0 E0, A1, A2, List.reverse_append, List.reverse_append,
      boidl_app, boidl_app, ← List.map_reverse, ← List.map_reverse, boidl_init_ints8,
      boidl_init_ints8, ← B1, ← B2, List.append_assoc]
  · rw [B1, List.length_map, List.length_reverse, C1]
  · rw [B2, List.length_map, List.length_reverse, C2]

/-- The side condition `match i with Init_space _ => False | _ => True` of
    several lemmas of `Initializersproof.v`. -/
def NotSpace : InitData → Prop
  | .Init_space _ => False
  | _ => True

/-- `Initializersproof.store_init_data_loadbytes` -/
theorem storeInitData_loadbytes' {m : Mem} {b : Block} {p : Z} {i : InitData} {m' : Mem}
    (h : Genv.storeInitData ge m b p i = some m')
    (hns : NotSpace i) :
    Mem.loadbytes m' b p i.size = some (boid i) := by
  cases i with
  | Init_int8 n => exact loadbytes_store_same h
  | Init_int16 n => exact loadbytes_store_same h
  | Init_int32 n => exact loadbytes_store_same h
  | Init_int64 n => exact loadbytes_store_same h
  | Init_float32 n => exact loadbytes_store_same h
  | Init_float64 n => exact loadbytes_store_same h
  | Init_space n => exact hns.elim
  | Init_addrof id ofs =>
    simp only [Genv.storeInitData] at h
    split at h
    · cases h
    · next b' hb =>
      rw [Genv.initDataSize_addrof, loadbytes_store_same h]
      simp only [Genv.bytesOfInitData, hb]
      rfl

/-! ## Validity and size of initialization data -/

/-- `Initializersproof.idvalid` -/
def IdValid : InitData → Prop
  | .Init_addrof symb _ => ∃ b, Genv.findSymbol ge symb = some b
  | _ => True

/-- `Initializersproof.idlvalid` -/
def IdlValid : Z → List InitData → Prop
  | _, [] => True
  | p, i1 :: il => Genv.initDataAlignment i1 ∣ p ∧ IdValid ge i1 ∧ IdlValid (p + i1.size) il

/-- `Initializersproof.init_data_list_size_app` -/
theorem initDataListSize_app (l1 l2 : List InitData) :
    InitData.listSize (l1 ++ l2) = InitData.listSize l1 + InitData.listSize l2 := by
  induction l1 with
  | nil => show InitData.listSize l2 = 0 + InitData.listSize l2; rw [Int.zero_add]
  | cons i l1 ih =>
    show i.size + InitData.listSize (l1 ++ l2) = (i.size + InitData.listSize l1) + _
    rw [ih, Int.add_assoc]

/-- `Initializersproof.idlvalid_app` -/
theorem idlValid_app (l2 : List InitData) : ∀ (l1 : List InitData) (pos : Z),
    IdlValid ge pos (l1 ++ l2) ↔
      IdlValid ge pos l1 ∧ IdlValid ge (pos + InitData.listSize l1) l2
  | [], pos => by
    show _ ↔ True ∧ IdlValid ge (pos + 0) l2
    rw [Int.add_zero]; exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | d :: l1, pos => by
    show (_ ∧ _ ∧ IdlValid ge (pos + d.size) (l1 ++ l2)) ↔
      (_ ∧ _ ∧ IdlValid ge (pos + d.size) l1) ∧ IdlValid ge (pos + (d.size + InitData.listSize l1)) l2
    rw [idlValid_app l2 l1, Int.add_assoc]
    exact ⟨fun ⟨a, b, c, d⟩ => ⟨⟨a, b, c⟩, d⟩, fun ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩⟩

theorem idlValid_bytes (l : List Integers.Int) : ∀ (pos : Z), IdlValid ge pos (l.map .Init_int8) := by
  induction l with
  | nil => intro _; trivial
  | cons i l ih => intro pos; exact ⟨Int.one_dvd _, trivial, ih _⟩

/-- `Initializersproof.add_rev_bytes_valid` -/
theorem addRevBytes_valid {il : List InitData} (bl : List Integers.Byte)
    (h : IdlValid ge 0 il.reverse) : IdlValid ge 0 (addRevBytes bl il).reverse := by
  rw [addRevBytes_spec, List.reverse_append, idlValid_app]
  refine ⟨h, ?_⟩
  rw [List.map_reverse, List.reverse_reverse]
  have e : bl.map initByte = (bl.map intOfByte).map InitData.Init_int8 := by
    rw [List.map_map]; rfl
  rw [e]; exact idlValid_bytes ge _ _

/-- `Initializersproof.add_zeros_valid` -/
theorem addZeros_valid {il : List InitData} (n : Z) (h : IdlValid ge 0 il.reverse) :
    IdlValid ge 0 (addZeros n il).reverse := by
  rw [addZeros_spec, List.reverse_append, idlValid_app, List.reverse_replicate]
  refine ⟨h, ?_⟩
  have := idlValid_bytes ge (List.replicate n.toNat Integers.Int.zero)
    (0 + InitData.listSize il.reverse)
  rwa [List.map_replicate] at this

theorem idlValid_space (p n : Z) : IdlValid ge p [.Init_space n] :=
  ⟨Int.one_dvd _, trivial, trivial⟩

/-- `Initializersproof.normalize_valid` -/
theorem normalize_valid : ∀ (il : List InitData) (depth : Z) (il' : List InitData),
    normalize il depth = .OK il' → IdlValid ge 0 il.reverse → IdlValid ge 0 il'.reverse
  | il, depth, il', h, hv => by
    unfold normalize at h
    by_cases hd : depth ≤ 0
    · rw [if_pos hd] at h; cases h; exact hv
    · rw [if_neg hd] at h
      match il, h with
      | .Init_int8 n :: il, h =>
        obtain ⟨il'', E, h⟩ := res_bind_eq_OK.mp h
        cases h
        rw [List.reverse_cons, idlValid_app] at hv ⊢
        exact ⟨normalize_valid il _ il'' E hv.1, ⟨Int.one_dvd _, trivial, trivial⟩⟩
      | .Init_int16 n :: il, h =>
        obtain ⟨il'', E, h⟩ := res_bind_eq_OK.mp h
        cases h
        rw [List.reverse_cons, idlValid_app] at hv
        exact addRevBytes_valid ge _ (normalize_valid il _ il'' E hv.1)
      | .Init_int32 n :: il, h =>
        obtain ⟨il'', E, h⟩ := res_bind_eq_OK.mp h
        cases h
        rw [List.reverse_cons, idlValid_app] at hv
        exact addRevBytes_valid ge _ (normalize_valid il _ il'' E hv.1)
      | .Init_int64 n :: il, h =>
        obtain ⟨il'', E, h⟩ := res_bind_eq_OK.mp h
        cases h
        rw [List.reverse_cons, idlValid_app] at hv
        exact addRevBytes_valid ge _ (normalize_valid il _ il'' E hv.1)
      | .Init_float32 n :: il, h =>
        obtain ⟨il'', E, h⟩ := res_bind_eq_OK.mp h
        cases h
        rw [List.reverse_cons, idlValid_app] at hv
        exact addRevBytes_valid ge _ (normalize_valid il _ il'' E hv.1)
      | .Init_float64 n :: il, h =>
        obtain ⟨il'', E, h⟩ := res_bind_eq_OK.mp h
        cases h
        rw [List.reverse_cons, idlValid_app] at hv
        exact addRevBytes_valid ge _ (normalize_valid il _ il'' E hv.1)
      | .Init_space z :: il, h =>
        simp only at h
        rw [List.reverse_cons, idlValid_app] at hv
        by_cases hn : max 0 z ≤ depth
        · rw [if_pos hn] at h
          obtain ⟨il'', E, h⟩ := res_bind_eq_OK.mp h
          cases h
          exact addZeros_valid ge _ (normalize_valid il _ il'' E hv.1)
        · rw [if_neg hn] at h
          cases h
          refine addZeros_valid ge _ ?_
          rw [List.reverse_cons, idlValid_app]
          exact ⟨hv.1, idlValid_space ge _ _⟩

/-- `Initializersproof.trisection_valid` -/
theorem trisection_valid {il : List InitData} {depth sz : Z} {bytes1 bytes2 : List Integers.Byte}
    {il' : List InitData} (h : trisection il depth sz = .OK (bytes1, bytes2, il'))
    (hv : IdlValid ge 0 il.reverse) : IdlValid ge 0 il'.reverse := by
  unfold trisection at h
  obtain ⟨il0, E0, h⟩ := res_bind_eq_OK.mp h
  obtain ⟨⟨b1, il1⟩, E1, h⟩ := res_bind_eq_OK.mp h
  obtain ⟨⟨b2, il2⟩, E2, h⟩ := res_bind_eq_OK.mp h
  cases h
  obtain ⟨nl1, A1, -, -⟩ := decompose_spec E1
  obtain ⟨nl2, A2, -, -⟩ := decompose_spec E2
  have := normalize_valid ge il _ il0 E0 hv
  rw [A1, A2, List.reverse_append, List.reverse_append, idlValid_app, idlValid_app] at this
  exact this.1.1

/-- `Initializersproof.init_data_size_boid` -/
theorem initDataSize_boid (i : InitData) : i.size = ((boid i).length : Z) := by
  cases i with
  | Init_space n =>
    simp only [InitData.size, Genv.bytesOfInitData, List.length_replicate]; zomega
  | Init_addrof id ofs =>
    simp only [InitData.size, Genv.bytesOfInitData]
    split <;> split <;> rfl
  | _ => rfl

/-- `Initializersproof.init_data_list_size_boidl` -/
theorem initDataListSize_boidl (il : List InitData) :
    InitData.listSize il = ((boidl il).length : Z) := by
  induction il with
  | nil => rfl
  | cons i il ih =>
    show i.size + InitData.listSize il = ((boid i ++ boidl il).length : Z)
    rw [List.length_append, ih, initDataSize_boid ge i]
    zomega

end BYTES

/-! ## Memory areas that are initialized to zeros -/

/-- `Initializersproof.reads_as_zeros` -/
def ReadsAsZeros (m : Mem) (b : Block) (from_ to : Z) : Prop :=
  ∀ i : _root_.Int, from_ ≤ i → i < to →
    Mem.loadbytes m b i 1 = some [MemVal.Byte Integers.Byte.zero]

/-- `Initializersproof.reads_as_zeros_mono` -/
theorem readsAsZeros_mono {m : Mem} {b : Block} {from1 from2 to1 to2 : _root_.Int}
    (h : ReadsAsZeros m b from1 to1) (h1 : from1 ≤ from2) (h2 : to2 ≤ to1) :
    ReadsAsZeros m b from2 to2 := fun i a c => h i (by zomega) (by zomega)

/-- `Initializersproof.reads_as_zeros_unchanged` -/
theorem readsAsZeros_unchanged {P : Block → Z → Prop} {m : Mem} {b : Block}
    {from_ to : _root_.Int} {m' : Mem}
    (h : ReadsAsZeros m b from_ to) (hu : UnchangedOn P m m')
    (hP : ∀ i : _root_.Int, from_ ≤ i → i < to → P b i) : ReadsAsZeros m' b from_ to :=
  fun i h1 h2 => hu.loadbytes (fun j a c => hP j (by zomega) (by zomega)) (h i h1 h2)

/-- `Initializersproof.reads_as_zeros_loadbytes` -/
theorem readsAsZeros_loadbytes {m : Mem} {b : Block} {from_ to : _root_.Int}
    (h : ReadsAsZeros m b from_ to) : ∀ (n : Nat) (pos : _root_.Int),
    from_ ≤ pos → pos + n ≤ to →
    Mem.loadbytes m b pos n = some (List.replicate n (MemVal.Byte Integers.Byte.zero))
  | 0, pos, _, _ => loadbytes_empty _ _ _ (by simp)
  | n + 1, pos, h1, h2 => by
    rw [List.replicate_succ, ← List.singleton_append,
      show ((n + 1 : Nat) : _root_.Int) = 1 + (n : _root_.Int) by omega]
    exact loadbytes_concat (h pos h1 (by omega))
      (readsAsZeros_loadbytes h n (pos + 1) (by omega) (by omega)) (by omega) (by omega)

/-- `Initializersproof.reads_as_zeros_loadbytes`, with an integer length. -/
theorem readsAsZeros_loadbytes' {m : Mem} {b : Block} {from_ to : _root_.Int}
    (h : ReadsAsZeros m b from_ to) (len pos : _root_.Int) (h1 : from_ ≤ pos)
    (h2 : pos + len ≤ to) (h3 : 0 ≤ len) :
    Mem.loadbytes m b pos len = some (List.replicate len.toNat (MemVal.Byte Integers.Byte.zero)) := by
  have := readsAsZeros_loadbytes h len.toNat pos h1 (by omega)
  rwa [show ((len.toNat : Nat) : _root_.Int) = len by omega] at this

/-- `Initializersproof.reads_as_zeros_equiv` -/
theorem readsAsZeros_equiv (m : Mem) (b : Block) (from_ to : _root_.Int) :
    ReadsAsZeros m b from_ to ↔ Genv.ReadbytesAsZero m b from_ (to - from_) := by
  constructor
  · intro h p n h1 h2
    exact readsAsZeros_loadbytes h n p h1 (by omega)
  · intro h i h1 h2
    exact h i 1 h1 (by omega)

end Initializersproof
end CC
