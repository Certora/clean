/-
  `CCLibMathlib` — the part of the port that imports Mathlib.  It is kept out
  of the `CCLib` root (which depends on Lean core only), so that importing
  `CCLib` does not load Mathlib.

  * `CCLib.lib.MathlibEquiv` — definitions of the port that duplicate Mathlib,
    Batteries or core ones, with the proofs that they agree (see
    `MATHLIB_DUPLICATION.md`).

  (The former `CCLibReal` root collected the real-number side of the Flocq
  port; Flocq is not part of the Lean port any more, see `MODULE_AUDIT.md`.)
-/
import CCLib.lib.MathlibEquiv
