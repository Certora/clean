/-
  Executable sanity checks for `CCLib.lib.FSetAVL` and `CCLib.lib.FSetAVLplus`
  (sets of integers).
-/
import CCLib.lib.FSetAVLplus

open CC

private def s0 : FSetAVL.t Int :=
  [5, 3, 9, 1, 7, 3, 12, -4, 8].foldl (fun s x => FSetAVL.add x s) FSetAVL.empty

-- elements are sorted and deduplicated
#guard FSetAVL.elements s0 = [-4, 1, 3, 5, 7, 8, 9, 12]
#guard FSetAVL.cardinal s0 = 8
#guard FSetAVL.mem 7 s0 && !FSetAVL.mem 6 s0
#guard FSetAVL.elements (FSetAVL.remove 5 s0) = [-4, 1, 3, 7, 8, 9, 12]
#guard FSetAVL.min_elt s0 = some (-4) && FSetAVL.max_elt s0 = some 12

private def s1 : FSetAVL.t Int :=
  [2, 3, 4, 5, 6].foldl (fun s x => FSetAVL.add x s) FSetAVL.empty

#guard FSetAVL.elements (FSetAVL.union s0 s1) = [-4, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12]
#guard FSetAVL.elements (FSetAVL.inter s0 s1) = [3, 5]
#guard FSetAVL.elements (FSetAVL.diff s0 s1) = [-4, 1, 7, 8, 9, 12]

-- the interval `[3, 8]`
private def above (x : Int) : Bool := decide (3 ≤ x)
private def below (x : Int) : Bool := decide (x ≤ 8)

#guard FSetAVLplus.mem_between above below s0
#guard !FSetAVLplus.mem_between (fun x => decide (10 ≤ x)) (fun x => decide (x ≤ 11)) s0
#guard FSetAVL.elements (FSetAVLplus.elements_between above below s0) = [3, 5, 7, 8]
#guard FSetAVLplus.for_all_between (fun x => decide (x ≠ 4)) above below s0
#guard !FSetAVLplus.for_all_between (fun x => decide (x ≠ 7)) above below s0
#guard FSetAVL.elements (FSetAVLplus.partition_between above below s0).1 = [3, 5, 7, 8]
#guard FSetAVL.elements (FSetAVLplus.partition_between above below s0).2 = [-4, 1, 9, 12]
