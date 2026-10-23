/-
  Binary positive numbers — Coq's `positive`, plus the string↔ident encoding
  from `export/Ctypesdefs.v`.

  Moved here from `Clightdefs.lean` because the maps (`CCLib.lib.Maps`) and the
  memory model need it too: CompCert's `block`, `ident`, and every `PTree` key
  is a `positive`.  Names are unchanged (`CC.Positive`, `CC.identOfString`), so
  files emitted by `clightgen -lean` are unaffected.
-/
namespace CC

/-- Coq's `positive` (strictly-positive binary numbers, LSB-first spine). -/
inductive Positive where
  | xH                    -- 1
  | xO (p : Positive)     -- 2*p
  | xI (p : Positive)     -- 2*p + 1
  deriving DecidableEq, Repr

instance : Inhabited Positive := ⟨Positive.xH⟩

/-- CompCert's `ident` (`AST.ident := positive`). -/
abbrev Ident := Positive
/-- CompCert's `block` (`Values.block := positive`). -/
abbrev Block := Positive

namespace Positive

/-- Build a `Positive` from a `Nat`.  Total (structural on `fuel`) so that it
    reduces in the kernel; `0` maps to `1` since `positive` has no zero. -/
def ofNatAux : Nat → Nat → Positive
  | 0, _ => Positive.xH
  | _, 0 => Positive.xH
  | _, 1 => Positive.xH
  | fuel + 1, n =>
      if n % 2 == 0
      then Positive.xO (ofNatAux fuel (n / 2))
      else Positive.xI (ofNatAux fuel (n / 2))

def ofNat (n : Nat) : Positive := ofNatAux n n

/-- Numeric value of a `Positive` (always ≥ 1). -/
def toNat : Positive → Nat
  | .xH => 1
  | .xO p => 2 * p.toNat
  | .xI p => 2 * p.toNat + 1

/-- Coq's `Pos.succ`. -/
def succ : Positive → Positive
  | .xH => .xO .xH
  | .xO p => .xI p
  | .xI p => .xO (succ p)

theorem toNat_pos (p : Positive) : 0 < p.toNat := by
  induction p with
  | xH => decide
  | xO q ih => simp only [toNat]; omega
  | xI q _ => simp only [toNat]; omega

@[simp] theorem toNat_succ (p : Positive) : (succ p).toNat = p.toNat + 1 := by
  induction p with
  | xH => rfl
  | xO q _ => rfl
  | xI q ih => simp only [succ, toNat, ih]; omega

/-- Coq's `Pos.lt`, via numeric value. -/
def lt (p q : Positive) : Bool := p.toNat < q.toNat
/-- Coq's `Pos.le`. -/
def le (p q : Positive) : Bool := p.toNat ≤ q.toNat

instance : LT Positive := ⟨fun p q => p.toNat < q.toNat⟩
instance : LE Positive := ⟨fun p q => p.toNat ≤ q.toNat⟩

/-- Bridge `<` on `Positive` to `<` on `Nat`, so `omega` can be used. -/
theorem lt_iff (p q : Positive) : p < q ↔ p.toNat < q.toNat := Iff.rfl
instance (p q : Positive) : Decidable (p < q) :=
  inferInstanceAs (Decidable (p.toNat < q.toNat))
instance (p q : Positive) : Decidable (p ≤ q) :=
  inferInstanceAs (Decidable (p.toNat ≤ q.toNat))

end Positive

/-! ## Encoding character strings as identifiers

Mirror of `ident_of_string` / `append_char_pos` in `export/Ctypesdefs.v`.  We
use the general 8-bit encoding for every character (Rocq special-cases the
common ones for shorter numbers); it is injective and self-consistent, which is
all a standalone Lean mirror needs. -/

private def appendBit (b : Bool) (p : Positive) : Positive :=
  if b then Positive.xI p else Positive.xO p

private def nthBit (n i : Nat) : Bool := (n >>> i) &&& 1 == 1

private def appendCharPos (c : Char) (p : Positive) : Positive :=
  let n := c.toNat
  let p := appendBit (nthBit n 7) p
  let p := appendBit (nthBit n 6) p
  let p := appendBit (nthBit n 5) p
  let p := appendBit (nthBit n 4) p
  let p := appendBit (nthBit n 3) p
  let p := appendBit (nthBit n 2) p
  let p := appendBit (nthBit n 1) p
  let p := appendBit (nthBit n 0) p
  .xI (.xI (.xI (.xI (.xI (.xI p)))))

/-- Encode a character string as an identifier (`ident_of_string`).

    Folds over `s.toList` rather than calling `String.foldr` directly.  The two
    are equal — `identOfString_eq_foldr` below, from core's
    `String.foldr_eq_foldr_toList` — but only this form **reduces in the
    kernel**: `String.foldr` goes through the opaque UTF-8 iterator, so `decide`
    got stuck on every identifier disequality and the program logic had to reach
    for `native_decide`.  Folding over the character list makes identifier facts
    kernel-decidable, which is why `Distinct`-style hypotheses are no longer
    needed. -/
def identOfString (s : String) : Ident :=
  s.toList.foldr appendCharPos Positive.xH

/-- The `toList` fold above is exactly `String.foldr`, so nothing about the
    encoding changed — only its reducibility. -/
theorem identOfString_eq_foldr (s : String) :
    identOfString s = s.foldr appendCharPos Positive.xH := by
  -- Recent Lean cores (the `export/` toolchain) provide
  -- `String.foldr_eq_foldr_toList`.  Older ones (e.g. Lean 4.28, used when the
  -- port is built from the repository root) lack it, so the second branch
  -- proves the same fact directly from the definitions of `String.foldr` and
  -- `String.Slice.Pos.prev`; it is only elaborated if the first branch fails.
  first
  | exact (String.foldr_eq_foldr_toList ..).symm
  | open String in (
    show s.toList.foldr appendCharPos Positive.xH = s.foldr appendCharPos Positive.xH
    symm
    have prevAuxGo_max {s : Slice} (off : Nat) (h₁ : off < s.utf8ByteSize) (r : Nat)
        (hlt : (Slice.Pos.prevAux.go off h₁).byteIdx < r) (hle : r ≤ off) (hr : r < s.utf8ByteSize) :
        ¬ (s.getUTF8Byte ⟨r⟩ (by simpa [Pos.Raw.lt_iff] using hr)).IsUTF8FirstByte := by
      induction off with
      | zero =>
        rw [Slice.Pos.prevAux.go] at hlt
        split at hlt
        · simp at hlt; omega
        · omega
      | succ off ih =>
        rw [Slice.Pos.prevAux.go] at hlt
        split at hlt
        · simp at hlt; omega
        · rename_i hb
          by_cases hro : r = off + 1
          · subst hro; exact hb
          · exact ih _ hlt (by omega)
    have prev_max {s : Slice} (p q : s.Pos) (h : p ≠ s.startPos) (h1 : p.prev h < q) (h2 : q < p) : False := by
      have hv := q.isValidForSlice
      rw [Pos.Raw.isValidForSlice_iff_isUTF8FirstByte] at hv
      have hpe := p.isValidForSlice.le_rawEndPos
      simp only [Slice.Pos.lt_iff, Pos.Raw.lt_iff, Pos.Raw.le_iff] at h1 h2 hpe
      rcases hv with hv | ⟨hlt, hb⟩
      · rw [hv] at h2; omega
      · simp only [Slice.Pos.prev, Slice.Pos.prevAux] at h1
        have hr : q.offset.byteIdx < s.utf8ByteSize := by
          simpa [Pos.Raw.lt_iff] using hlt
        exact prevAuxGo_max _ _ q.offset.byteIdx h1 (by omega) hr hb
    have next_prev {s : Slice} (p : s.Pos) (h : p ≠ s.startPos) :
        (p.prev h).next Slice.Pos.prev_ne_endPos = p := by
      have h1 : (p.prev h).next Slice.Pos.prev_ne_endPos ≤ p := Slice.Pos.next_le_of_lt Slice.Pos.prev_lt
      have h2 : p.prev h < (p.prev h).next Slice.Pos.prev_ne_endPos := Slice.Pos.lt_next
      by_cases h3 : (p.prev h).next Slice.Pos.prev_ne_endPos < p
      · exact (prev_max p _ h h2 h3).elim
      · simp only [Slice.Pos.lt_iff, Slice.Pos.le_iff, Pos.Raw.lt_iff, Pos.Raw.le_iff] at h1 h3
        apply Slice.Pos.ext; apply Pos.Raw.ext; omega
    have sliceTo_prev_append {s : Slice} (p : s.Pos) (h : p ≠ s.startPos) :
        (s.sliceTo p).copy = (s.sliceTo (p.prev h)).copy ++ singleton ((p.prev h).get Slice.Pos.prev_ne_endPos) := by
      have hs := Slice.Pos.splits_next (p.prev h) Slice.Pos.prev_ne_endPos
      rw [next_prev] at hs
      exact (Slice.Pos.splits p).eq_left hs
    have foldRev {s : Slice} {α : Type} (f : Char → α → α) (n : Nat) : ∀ (p : s.Pos) (acc : α),
        p.offset.byteIdx = n →
        Std.Iter.fold (fun d (b : { p : s.Pos // p ≠ s.endPos }) => flip f d (b.val.get b.property)) acc
            ({ internalState := { currPos := p } } : Std.Iter (α := Slice.RevPosIterator s) { p : s.Pos // p ≠ s.endPos }) =
          (s.sliceTo p).copy.toList.foldr f acc := by
      induction n using Nat.strongRecOn with
      | _ n ih =>
      intro p acc hn
      rw [Std.Iter.fold_eq_match_step]
      by_cases h : p = s.startPos
      · subst h
        have e : (s.sliceTo s.startPos).copy = "" :=
          (Slice.Pos.splits s.startPos).eq_left (Slice.splits_startPos s)
        rw [e]
        simp [Std.Iter.step, Std.IterM.step, Std.Iterator.step, Std.Iter.toIterM]
      · simp [Std.Iter.step, Std.IterM.step, Std.Iterator.step, Std.Iter.toIterM, h]
        have hlt : (p.prev h).offset.byteIdx < n := by
          have := @Slice.Pos.prev_lt s p h
          simp only [Slice.Pos.lt_iff, Pos.Raw.lt_iff] at this; omega
        rw [sliceTo_prev_append p h]
        have := ih _ hlt (p.prev h) (flip f acc ((p.prev h).get Slice.Pos.prev_ne_endPos)) rfl
        simp only [String.toList_append, List.foldr_append]
        simpa [flip] using this
    rw [String.foldr, String.Slice.foldr, String.Slice.revChars, Std.Iter.fold_map]
    rw [String.Slice.revPositions, foldRev appendCharPos _ _ Positive.xH rfl]
    have e : (s.toSlice.sliceTo s.toSlice.endPos).copy = s.toSlice.copy :=
      (String.Slice.Pos.splits _).eq_left (String.Slice.splits_endPos _)
    rw [e, String.copy_toSlice])

end CC
