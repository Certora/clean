(* Differential test ORACLE for CCLib/common/Memory.lean.

   Why OCaml and not Coq: CompCert's `Mem.store`/`load`/`free` cannot be
   evaluated by Coq's `Compute`.  They branch on `valid_access_dec`, which goes
   through `range_perm_dec`, which is defined by well-founded recursion over an
   accessibility proof that is not reduction-transparent.  So the memory model is
   unevaluable inside Coq — but its OCaml *extraction* is precisely what
   CompCert's own reference interpreter runs (there the `Prop` invariants are
   erased), so we use that as the oracle.

   Must stay in lockstep with MemDiff.lean: same scenarios, same order.  Each
   value observation prints TWO lines (tag, then payload) to avoid needing
   bignum arithmetic here. *)

open Camlcoq
open AST
open Values
open Memory

(* ---- output helpers, matching MemDiff.lean ---- *)

let outi (i : int) = print_string (string_of_int i); print_newline ()
let outz (z : BinNums.coq_Z) = print_string (Z.to_string z); print_newline ()

let vtag (v : coq_val) : int =
  match v with
  | Vundef -> 0
  | Vint _ -> 1
  | Vlong _ -> 2
  | Vfloat _ -> 3
  | Vsingle _ -> 4
  | Vptr (_, _) -> 5

(* payload: for pointers we print the block number, then the offset, so a
   pointer observation is (tag, block, offset) = 3 lines; every other value is
   (tag, payload, 0). *)
let outv (v : coq_val) =
  outi (vtag v);
  (match v with
   | Vundef -> outi 0; outi 0
   | Vint n -> outz (Integers.Int.unsigned n); outi 0
   | Vlong n -> outz (Integers.Int64.unsigned n); outi 0
   | Vfloat f -> outz (Integers.Int64.unsigned (Floats.Float.to_bits f)); outi 0
   | Vsingle f -> outz (Integers.Int.unsigned (Floats.Float32.to_bits f)); outi 0
   | Vptr (b, ofs) -> outi (P.to_int b); outz (Integers.Ptrofs.unsigned ofs))

let outov = function
  | None -> outi (-1); outi 0; outi 0
  | Some v -> outv v

let bcode b = if b then 1 else 0
let omcode = function None -> -1 | Some _ -> 1

let zi = Z.of_sint

let ld chunk om b ofs =
  match om with
  | None -> outi (-2); outi 0; outi 0
  | Some m -> outov (Mem.load chunk m b (zi ofs))

let vp om b ofs =
  match om with
  | None -> outi (-2)
  | Some m -> outi (bcode (Mem.valid_pointer m b (zi ofs)))

let nb = function
  | None -> outi (-2)
  | Some m -> outi (P.to_int (Mem.nextblock m))

let vint k = Vint (Integers.Int.repr (zi k))
let vlong64 (k : int64) = Vlong (Integers.Int64.repr (Z.of_sint64 k))
let ptrofs k = Integers.Ptrofs.repr (zi k)

let () =
  (* ---- scenario setup ---- *)
  let m0 = Mem.empty in
  let (m1, bb) = Mem.alloc m0 (zi 0) (zi 16) in

  (* nextblock and freshness *)
  outi (P.to_int (Mem.nextblock m0));
  outi (P.to_int (Mem.nextblock m1));
  outi (P.to_int bb);
  outi (bcode (P.lt bb (Mem.nextblock m0)));
  outi (bcode (P.lt bb (Mem.nextblock m1)));

  (* permissions on a fresh block *)
  outi (bcode (Mem.valid_pointer m1 bb (zi 0)));
  outi (bcode (Mem.valid_pointer m1 bb (zi 15)));
  outi (bcode (Mem.valid_pointer m1 bb (zi 16)));
  outi (bcode (Mem.valid_pointer m1 bb (zi (-1))));
  outi (bcode (Mem.weak_valid_pointer m1 bb (zi 16)));
  outi (bcode (Mem.weak_valid_pointer m1 bb (zi 17)));

  (* fresh memory reads as Undef *)
  ld Mint32 (Some m1) bb 0;
  ld Mint8unsigned (Some m1) bb 3;

  (* ---- stores and loads ---- *)
  let s32 = Mem.store Mint32 m1 bb (zi 0) (vint 1234567) in
  outi (omcode s32);
  ld Mint32 s32 bb 0;
  ld Mint8unsigned s32 bb 0;
  ld Mint8unsigned s32 bb 1;
  ld Mint8signed s32 bb 0;
  ld Mint16unsigned s32 bb 0;
  ld Mint64 s32 bb 0;

  outi (omcode (Mem.store Mint32 m1 bb (zi 1) (vint 1)));
  outi (omcode (Mem.store Mint32 m1 bb (zi 2) (vint 1)));
  outi (omcode (Mem.store Mint32 m1 bb (zi 16) (vint 1)));
  outi (omcode (Mem.store Mint32 m1 bb (zi (-4)) (vint 1)));
  outi (omcode (Mem.store Mint64 m1 bb (zi 0) (vlong64 42L)));
  outi (omcode (Mem.store Mint64 m1 bb (zi 8) (vlong64 42L)));

  let s64 = Mem.store Mint64 m1 bb (zi 0) (vlong64 1234567890123L) in
  ld Mint64 s64 bb 0;
  ld Mint32 s64 bb 0;
  ld Mint32 s64 bb 4;

  (* float round trip through memory *)
  let dbl = Vfloat (Floats.Float.of_bits
              (Integers.Int64.repr (Z.of_sint64 4611686018427387904L))) in
  let sf = Mem.store Mfloat64 m1 bb (zi 0) dbl in
  ld Mfloat64 sf bb 0;
  ld Mint64 sf bb 0;
  let sgl = Vsingle (Floats.Float32.of_bits (Integers.Int.repr (zi 1065353216))) in
  let sfs = Mem.store Mfloat32 m1 bb (zi 0) sgl in
  ld Mfloat32 sfs bb 0;
  ld Mint32 sfs bb 0;

  (* ---- pointers in memory: the Fragment machinery ---- *)
  let sp = Mem.store Mint64 m1 bb (zi 0) (Vptr (bb, ptrofs 8)) in
  ld Mint64 sp bb 0;
  let sp' = match sp with
            | None -> None
            | Some m -> Mem.store Mint8unsigned m bb (zi 3) (vint 0) in
  ld Mint64 sp' bb 0;
  ld Mint32 sp bb 0;
  let sany = Mem.store Many64 m1 bb (zi 0) (Vptr (bb, ptrofs 8)) in
  ld Many64 sany bb 0;

  (* ---- storebytes ---- *)
  let bytes = Memdata.encode_val Mint32 (vint 7) in
  let sb = Mem.storebytes m1 bb (zi 0) bytes in
  outi (omcode sb);
  ld Mint32 sb bb 0;
  outi (omcode (Mem.storebytes m1 bb (zi 1) bytes));
  outi (omcode (Mem.storebytes m1 bb (zi 13) bytes));

  (* ---- freeing ---- *)
  let f1 = Mem.free m1 bb (zi 0) (zi 16) in
  outi (omcode f1);
  vp f1 bb 0;
  ld Mint32 f1 bb 0;
  nb f1;
  let f2 = Mem.free m1 bb (zi 0) (zi 8) in
  outi (omcode f2);
  vp f2 bb 0;
  vp f2 bb 8;
  outi (omcode (Mem.free m1 bb (zi 0) (zi 32)));
  outi (omcode (Mem.free m0 bb (zi 0) (zi 16)));
  outi (omcode (match f1 with None -> None | Some m -> Mem.free m bb (zi 0) (zi 16)));

  (* ---- two blocks are independent ---- *)
  let (m2, bb2) = Mem.alloc m1 (zi 0) (zi 8) in
  outi (P.to_int bb2);
  let t1 = Mem.store Mint32 m2 bb (zi 0) (vint 111) in
  let t2 = match t1 with
           | None -> None
           | Some m -> Mem.store Mint32 m bb2 (zi 0) (vint 222) in
  ld Mint32 t2 bb 0;
  ld Mint32 t2 bb2 0;
  let t3 = match t2 with None -> None | Some m -> Mem.free m bb2 (zi 0) (zi 8) in
  ld Mint32 t3 bb 0;
  ld Mint32 t3 bb2 0;

  (* ---- free_list ---- *)
  let l1 = [ ((bb, zi 0), zi 16); ((bb2, zi 0), zi 8) ] in
  let l2 = [ ((bb2, zi 0), zi 8); ((bb, zi 0), zi 16) ] in
  let l3 = [ ((bb, zi 0), zi 16); ((bb, zi 0), zi 16) ] in
  outi (omcode (Mem.free_list m2 l1));
  outi (omcode (Mem.free_list m2 l2));
  outi (omcode (Mem.free_list m2 l3));
  outi (omcode (Mem.free_list m2 []))
