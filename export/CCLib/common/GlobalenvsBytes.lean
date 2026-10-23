/-
  The in-memory bytes denoted by initialization data — port of the
  "Properties related to `loadbytes`" part of `common/Globalenvs.v`
  (`readbytes_as_zero`, `bytes_of_init_data`, `bytes_of_init_data_list`,
  `store_init_data_loadbytes`, `store_init_data_list_loadbytes`,
  `store_zeros_loadbytes`), plus `store_init_data_aligned` from the
  `INITMEM_INVERSION` section.
-/
import CCLib.common.GlobalenvsInitMem
import CCLib.common.MemoryBytes

namespace CC
namespace Genv
variable {F V : Type}

open Mem

private theorem eq_of_range_one {x q : _root_.Int} (h1 : q ≤ x) (h2 : x < q + 1) : x = q := by
  omega

/-- `Genv.readbytes_as_zero`: every byte in `[ofs, ofs + len)` reads as zero. -/
def ReadbytesAsZero (m : Mem) (b : Block) (ofs len : _root_.Int) : Prop :=
  ∀ (p : _root_.Int) (n : Nat), ofs ≤ p → p + (n : _root_.Int) ≤ ofs + len →
    Mem.loadbytes m b p (n : _root_.Int) = some (List.replicate n (MemVal.Byte Integers.Byte.zero))

section Bytes
variable (ge : Genv F V)

/-- `Genv.bytes_of_init_data` -/
def bytesOfInitData : InitData → List MemVal
  | .Init_int8 n => injBytes (encodeInt 1 (Integers.Int.unsigned n))
  | .Init_int16 n => injBytes (encodeInt 2 (Integers.Int.unsigned n))
  | .Init_int32 n => injBytes (encodeInt 4 (Integers.Int.unsigned n))
  | .Init_int64 n => injBytes (encodeInt 8 (Integers.Int64.unsigned n))
  | .Init_float32 n => injBytes (encodeInt 4 (Integers.Int.unsigned (Floats.Float32.toBits n)))
  | .Init_float64 n => injBytes (encodeInt 8 (Integers.Int64.unsigned (Floats.Float.toBits n)))
  | .Init_space n => List.replicate n.toNat (MemVal.Byte Integers.Byte.zero)
  | .Init_addrof id ofs =>
      match findSymbol ge id with
      | some b => injValue (if Archi.ptr64 then .Q64 else .Q32) (.Vptr b ofs)
      | none => List.replicate (if Archi.ptr64 then 8 else 4) .Undef

/-- `Genv.bytes_of_init_data_list` -/
def bytesOfInitDataList : List InitData → List MemVal
  | [] => []
  | i :: il => bytesOfInitData ge i ++ bytesOfInitDataList il

/-- `Genv.init_data_size_addrof` -/
theorem initDataSize_addrof (id : Ident) (ofs : Integers.Ptrofs) :
    (InitData.Init_addrof id ofs).size = sizeChunk Mptr := rfl

/-- `Genv.store_init_data_loadbytes` -/
theorem storeInitData_loadbytes {m : Mem} {b : Block} {p : _root_.Int} {i : InitData} {m' : Mem}
    (h : storeInitData ge m b p i = some m') (hz : ReadbytesAsZero m b p i.size) :
    Mem.loadbytes m' b p i.size = some (bytesOfInitData ge i) := by
  cases i with
  | Init_int8 n => exact loadbytes_store_same h
  | Init_int16 n => exact loadbytes_store_same h
  | Init_int32 n => exact loadbytes_store_same h
  | Init_int64 n => exact loadbytes_store_same h
  | Init_float32 n => exact loadbytes_store_same h
  | Init_float64 n => exact loadbytes_store_same h
  | Init_space n =>
    simp only [storeInitData, Option.some.injEq] at h
    subst h
    have := hz p n.toNat (Int.le_refl _) (by simp only [InitData.size]; omega)
    simp only [InitData.size, bytesOfInitData]
    rwa [show ((n.toNat : Nat) : _root_.Int) = max n 0 by omega] at this
  | Init_addrof id ofs =>
    simp only [storeInitData] at h
    split at h
    · cases h
    · next b' hb =>
      rw [initDataSize_addrof, loadbytes_store_same h]
      simp only [bytesOfInitData, hb]
      rfl

/-- `Genv.store_init_data_list_loadbytes` -/
theorem storeInitDataList_loadbytes (b : Block) : ∀ (il : List InitData) {m : Mem} {p : _root_.Int} {m' : Mem},
    storeInitDataList ge m b p il = some m' →
    ReadbytesAsZero m b p (InitData.listSize il) →
    Mem.loadbytes m' b p (InitData.listSize il) = some (bytesOfInitDataList ge il)
  | [], m, p, m', _, _ => loadbytes_empty _ _ _ (by simp [InitData.listSize])
  | i1 :: il, m, p, m', h, hz => by
    have P1 := InitData.size_nonneg i1
    have PL := InitData.listSize_nonneg il
    rw [InitData.listSize_cons] at hz ⊢
    simp only [storeInitDataList] at h
    split at h
    · cases h
    · next m1 hs =>
      refine loadbytes_concat ?_ ?_ P1 PL
      · refine (storeInitDataList_unchanged ge (fun _ ofs1 => ofs1 < p + i1.size) il h
          (fun o h1 h2 => Int.lt_irrefl _ (Int.lt_of_le_of_lt h1 h2))).loadbytes (fun _ _ h2 => h2) ?_
        exact storeInitData_loadbytes ge hs (fun q n h1 h2 => hz q n h1 (by omega))
      · refine storeInitDataList_loadbytes b il h (fun q n h1 h2 => ?_)
        refine (storeInitData_unchanged ge (fun _ ofs1 => p + i1.size ≤ ofs1) hs
          (fun o h1 h2 h3 => by omega)).loadbytes (fun _ h1 _ => by omega) ?_
        exact hz q n (by omega) (by omega)

/-- `Genv.store_init_data_aligned` -/
theorem storeInitData_aligned {m : Mem} {b : Block} {p : _root_.Int} {i : InitData} {m' : Mem}
    (h : storeInitData ge m b p i = some m') : initDataAlignment i ∣ p := by
  have dfl : ∀ (chunk : Chunk) (v : Val), store chunk m b p v = some m' →
      alignChunk chunk = initDataAlignment i → initDataAlignment i ∣ p := by
    intro chunk v hs ha
    have hva := store_valid_access hs
    simp only [validAccess, Bool.and_eq_true, beq_iff_eq] at hva
    rw [← ha]
    exact Int.dvd_of_emod_eq_zero hva.2
  cases i with
  | Init_int8 n => exact dfl _ _ h rfl
  | Init_int16 n => exact dfl _ _ h rfl
  | Init_int32 n => exact dfl _ _ h rfl
  | Init_int64 n => exact dfl _ _ h rfl
  | Init_float32 n => exact dfl _ _ h rfl
  | Init_float64 n => exact dfl _ _ h rfl
  | Init_space n => exact Int.one_dvd p
  | Init_addrof id ofs =>
    simp only [storeInitData] at h
    split at h
    · cases h
    · exact dfl _ _ h rfl

end Bytes

/-- `Genv.store_zeros_loadbytes` -/
theorem storeZerosAux_loadbytes : ∀ (k : Nat) {m : Mem} {b : Block} {p : _root_.Int} {m' : Mem},
    storeZerosAux m b p k = some m' → ReadbytesAsZero m' b p k
  | 0, m, b, p, m', _, q, n, h1, h2 => by
    have : n = 0 := by omega
    subst this
    exact loadbytes_empty _ _ _ (by simp)
  | k + 1, m, b, p, m', h, q, n, h1, h2 => by
    simp only [storeZerosAux] at h
    split at h
    · cases h
    · next m1 hs =>
      by_cases hq : q = p
      · subst hq
        cases n with
        | zero => exact loadbytes_empty _ _ _ (by simp)
        | succ n =>
          rw [show ((n + 1 : Nat) : _root_.Int) = 1 + (n : _root_.Int) by omega,
            List.replicate_succ, ← List.singleton_append]
          refine loadbytes_concat ?_ ?_ (by omega) (by omega)
          · refine (storeZerosAux_unchanged (fun _ ofs1 => ofs1 = q) k h
              (fun o h1 _ h3 => by subst h3; exact absurd h1 (Int.not_le.mpr (Int.lt_succ _)))).loadbytes (fun _ h1 h2 => eq_of_range_one h1 h2) ?_
            exact loadbytes_store_same hs
          · exact storeZerosAux_loadbytes k h (q + 1) n (by omega) (by omega)
      · exact storeZerosAux_loadbytes k h q n (by omega) (by omega)

/-- `Genv.store_zeros_loadbytes` -/
theorem storeZeros_loadbytes {m : Mem} {b : Block} {p n : _root_.Int} {m' : Mem}
    (h : storeZeros m b p n = some m') : ReadbytesAsZero m' b p n := fun q k h1 h2 =>
  storeZerosAux_loadbytes n.toNat h q k h1 (by omega)

end Genv
end CC
