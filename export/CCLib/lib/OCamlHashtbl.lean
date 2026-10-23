/-
  A model of OCaml's standard `Hashtbl` (generic, non-randomized tables),
  used by the ports whose output depends on the iteration order of an OCaml
  hash table (`debug/DebugInformation.lean`, `debug/Dwarfgen.lean`).

  This is not a CompCert source file: it reproduces the behaviour of the
  OCaml standard library (OCaml ≥ 4.04) that CompCert relies on.
  * `Hashtbl.create n` allocates `max 16 (next power of two ≥ n)` buckets;
  * `add` pushes the binding at the head of its bucket and doubles the
    number of buckets (keeping the relative order of the bindings) once the
    number of bindings exceeds twice the number of buckets;
  * `replace` overwrites the most recent binding of the key in place, or
    adds a new binding;
  * `remove` removes the most recent binding of the key;
  * `fold`/`iter` visit the buckets in increasing index order and each
    bucket from its head (most recent binding first);
  * `reset` goes back to the initial number of buckets.

  The bucket of a key is `Hashtbl.hash key land (buckets - 1)`, where
  `Hashtbl.hash` is OCaml's `caml_hash` (MurmurHash3-based).  The class
  `OCamlHash` gives `caml_hash` for OCaml `int`s (`Int`) and `string`s
  (`String`, hashed on its UTF-8 bytes), exactly as the OCaml runtime on a
  64-bit host computes it.  For other key types (pairs, Coq `positive`s)
  the instances below are *not* OCaml's hash: they are only used for tables
  that CompCert never iterates over, where the hash only affects
  efficiency.
-/
import CCLib.lib.Positive

namespace CC
namespace OCamlHashtbl

/-! ## `caml_hash` -/

def rotl32 (x : UInt32) (n : UInt32) : UInt32 := (x <<< n) ||| (x >>> (32 - n))

/-- `MIX(h, d)` of `runtime/hash.c` -/
def mix (h d : UInt32) : UInt32 :=
  let d := d * 0xcc9e2d51
  let d := rotl32 d 15
  let d := d * 0x1b873593
  let h := h ^^^ d
  let h := rotl32 h 13
  h * 5 + 0xe6546b64

/-- `FINAL_MIX(h)` of `runtime/hash.c` -/
def finalMix (h : UInt32) : UInt32 :=
  let h := h ^^^ (h >>> 16)
  let h := h * 0x85ebca6b
  let h := h ^^^ (h >>> 13)
  let h := h * 0xc2b2ae35
  h ^^^ (h >>> 16)

/-- The low 32 bits of an integer (two's complement). -/
def low32 (x : Int) : UInt32 := UInt32.ofNat (x % (2 ^ 32 : Int)).toNat

/-- `caml_hash_mix_intnat` on a 64-bit host. -/
def mixIntnat (h : UInt32) (d : Int) : UInt32 :=
  let hi := d / (2 ^ 32 : Int)   -- `d >> 32` (arithmetic shift)
  let sign : Int := if d < 0 then -1 else 0   -- `d >> 63`
  mix h (low32 hi ^^^ low32 sign ^^^ low32 d)

/-- `caml_hash_mix_string` -/
def mixString (h : UInt32) (s : String) : UInt32 := Id.run do
  let b := s.toUTF8
  let len := b.size
  let mut h := h
  let mut i := 0
  while i + 4 ≤ len do
    let w : UInt32 := b[i]!.toUInt32 ||| (b[i+1]!.toUInt32 <<< 8) |||
      (b[i+2]!.toUInt32 <<< 16) ||| (b[i+3]!.toUInt32 <<< 24)
    h := mix h w
    i := i + 4
  let r := len % 4
  if r != 0 then
    let mut w : UInt32 := 0
    if r == 3 then w := b[i+2]!.toUInt32 <<< 16
    if r ≥ 2 then w := w ||| (b[i+1]!.toUInt32 <<< 8)
    w := w ||| b[i]!.toUInt32
    h := mix h w
  return h ^^^ UInt32.ofNat len

/-- The final step of `caml_hash`: `FINAL_MIX(h); h & 0x3FFFFFFF`. -/
def finish (h : UInt32) : Nat := (finalMix h &&& 0x3FFFFFFF).toNat

/-- `Hashtbl.hash` on the keys of a table. -/
class OCamlHash (α : Type) where
  hash : α → Nat

/-- `Hashtbl.hash (n : int)`: an immediate value is hashed through its
    tagged representation `2n+1`. -/
instance : OCamlHash Int := ⟨fun n => finish (mixIntnat 0 (2 * n + 1))⟩

/-- `Hashtbl.hash (s : string)` -/
instance : OCamlHash String := ⟨fun s => finish (mixString 0 s)⟩

/-- Not OCaml's hash (see the header): only for tables that are never
    iterated. -/
instance {α β : Type} [OCamlHash α] [OCamlHash β] : OCamlHash (α × β) :=
  ⟨fun (a, b) => finish (mix (UInt32.ofNat (OCamlHash.hash a)) (UInt32.ofNat (OCamlHash.hash b)))⟩

/-- Not OCaml's hash (see the header): only for tables that are never
    iterated. -/
instance : OCamlHash Positive := ⟨fun p => OCamlHash.hash (Int.ofNat p.toNat)⟩

#guard OCamlHash.hash (0 : Int) = 129913994
#guard OCamlHash.hash ("" : String) = 0

end OCamlHashtbl

open OCamlHashtbl in
/-- An OCaml hash table `('a, 'b) Hashtbl.t` (see the header). -/
structure OHashtbl (α β : Type) where
  data : Array (List (α × β)) := Array.replicate 16 []
  size : Nat := 0
  initialSize : Nat := 16

namespace OHashtbl

open OCamlHashtbl

variable {α β : Type} [BEq α] [OCamlHash α]

instance : Inhabited (OHashtbl α β) := ⟨{}⟩

/-- `power_2_above 16 n` -/
def power2Above (x n : Nat) (fuel : Nat := 64) : Nat :=
  match fuel with
  | 0 => x
  | fuel + 1 => if x ≥ n then x else power2Above (2 * x) n fuel

/-- `Hashtbl.create n` -/
def create (n : Nat) : OHashtbl α β :=
  let s := power2Above 16 n
  { data := Array.replicate s [], size := 0, initialSize := s }

/-- `key_index h key` -/
def keyIndex (h : OHashtbl α β) (k : α) : Nat :=
  OCamlHash.hash k % h.data.size

/-- `resize`: double the number of buckets, keeping the order of the
    bindings inside each new bucket. -/
def resize (h : OHashtbl α β) : OHashtbl α β := Id.run do
  let nsize := 2 * h.data.size
  let mut nd : Array (List (α × β)) := Array.replicate nsize []
  for b in h.data do
    for (k, v) in b do
      let i := OCamlHash.hash k % nsize
      nd := nd.modify i ((k, v) :: ·)
  return { h with data := nd.map List.reverse }

/-- `Hashtbl.add` -/
def add (h : OHashtbl α β) (k : α) (v : β) : OHashtbl α β :=
  let i := h.keyIndex k
  let h := { h with data := h.data.modify i ((k, v) :: ·), size := h.size + 1 }
  if h.size > 2 * h.data.size then h.resize else h

/-- `Hashtbl.find_opt` (the most recent binding) -/
def find? (h : OHashtbl α β) (k : α) : Option β :=
  if h.data.size = 0 then none else
  (h.data[h.keyIndex k]!.find? (fun p => p.1 == k)).map (·.2)

/-- `Hashtbl.mem` -/
def mem (h : OHashtbl α β) (k : α) : Bool := (h.find? k).isSome

/-- Replace the first binding of `k` in a bucket. -/
def replaceBucket (k : α) (v : β) : List (α × β) → Option (List (α × β))
  | [] => none
  | (k', v') :: rest =>
    if k' == k then some ((k, v) :: rest)
    else (replaceBucket k v rest).map ((k', v') :: ·)

/-- `Hashtbl.replace` -/
def replace (h : OHashtbl α β) (k : α) (v : β) : OHashtbl α β :=
  let i := h.keyIndex k
  match replaceBucket k v h.data[i]! with
  | some b => { h with data := h.data.set! i b }
  | none =>
    let h := { h with data := h.data.modify i ((k, v) :: ·), size := h.size + 1 }
    if h.size > 2 * h.data.size then h.resize else h

/-- Remove the first binding of `k` in a bucket. -/
def removeBucket (k : α) : List (α × β) → Option (List (α × β))
  | [] => none
  | (k', v') :: rest =>
    if k' == k then some rest
    else (removeBucket k rest).map ((k', v') :: ·)

/-- `Hashtbl.remove` -/
def remove (h : OHashtbl α β) (k : α) : OHashtbl α β :=
  let i := h.keyIndex k
  match removeBucket k h.data[i]! with
  | some b => { h with data := h.data.set! i b, size := h.size - 1 }
  | none => h

/-- `Hashtbl.fold` -/
def fold {γ : Type} (f : α → β → γ → γ) (h : OHashtbl α β) (init : γ) : γ :=
  h.data.foldl (fun acc b => b.foldl (fun acc (k, v) => f k v acc) acc) init

/-- `Hashtbl.iter`, with a monadic function. -/
def iterM {m : Type → Type} [Monad m] (f : α → β → m Unit) (h : OHashtbl α β) : m Unit := do
  for b in h.data do
    for (k, v) in b do
      f k v

/-- The bindings in iteration order. -/
def toList (h : OHashtbl α β) : List (α × β) := (h.fold (fun k v acc => (k, v) :: acc) []).reverse

/-- `Hashtbl.reset` -/
def reset (h : OHashtbl α β) : OHashtbl α β :=
  { data := Array.replicate h.initialSize [], size := 0, initialSize := h.initialSize }

end OHashtbl

end CC
