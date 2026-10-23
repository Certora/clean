/-
  Enumeration of the nodes of an LTL function for linearization — the
  Rocq-layout entry point for `backend/Linearizeaux.ml`.

  The transcription itself lives in `backend/Linearize.lean` (as
  `Linearize.joinPoints`, `Linearize.basicBlocks`, `Linearize.flattenBlocks`
  and `Linearize.enumerateAuxDefault`), because the extracted compiler
  (`extraction/extraction.lean`) uses it as the default value of the
  parameter `Linearize.enumerate_aux`.  This module gives these functions
  their OCaml names in the namespace `Linearizeaux`.
-/
import CCLib.backend.Linearize

namespace CC
namespace Linearizeaux

/-- `Linearizeaux.join_points`: reachable nodes with more than one
    predecessor. -/
abbrev join_points := @Linearize.joinPoints

/-- `Linearizeaux.basic_blocks`: the reachable basic blocks, each with its
    smallest node. -/
abbrev basic_blocks := @Linearize.basicBlocks

/-- `Linearizeaux.flatten_blocks`: concatenation of the blocks in
    decreasing order of their smallest node. -/
abbrev flatten_blocks := @Linearize.flattenBlocks

/-- `Linearizeaux.enumerate_aux` -/
abbrev enumerate_aux := @Linearize.enumerateAuxDefault

end Linearizeaux
end CC
