/-
  Port of `lib/Printlines.ml`: printing lines of a source file (used by the
  assembly printers to show the C source next to `.loc` directives).

  Differences from OCaml: the OCaml version keeps an input channel and seeks
  forward/backward to the requested line; here the file is read once
  (`FileBuf.openFile`) and `copy` is a pure function of its contents, with the
  same output: the lines `first … last`, each prefixed by `pref`, with `\r`,
  `\t` (`\011`) and form feeds (`\012`) printed as spaces, and a final newline
  supplied if the file ends inside the range.  Nothing is printed if line
  `first` does not exist.
-/

namespace CC
namespace Printlines

/-- The contents of a source file, as the segments between newlines
    (segment `i` is line `i + 1`; the last segment is what follows the last
    newline). -/
structure FileBuf where
  segments : Array String

/-- `Printlines.openfile` -/
def FileBuf.openFile (f : System.FilePath) : IO FileBuf := do
  let s ← IO.FS.readFile f
  return ⟨(s.splitOn "\n").toArray⟩

/-- The characters `copy` prints as a space. -/
def blank (c : Char) : Char :=
  if c = '\r' || c = '\t' || c = '\x0c' then ' ' else c

/-- `Printlines.copy`: lines `first … last` (1-based) of `b`, each prefixed by
    `pref`. -/
def copy (pref : String) (b : FileBuf) (first last : Nat) : String :=
  if first = 0 ∨ b.segments.size < first then "" else
    let rec go (l : Nat) (fuel : Nat) (acc : String) : String :=
      match fuel with
      | 0 => acc
      | fuel + 1 =>
        if last < l then acc
        else
          let seg := (b.segments[l - 1]!).map blank
          if l < b.segments.size then
            -- a complete line, followed by a newline
            let acc := acc ++ seg ++ "\n"
            go (l + 1) fuel (if l + 1 ≤ last then acc ++ pref else acc)
          else
            -- the end of the file
            acc ++ seg ++ "\n"
    go first (last + 1 - first) pref

-- A line in the middle, a range running past the end of a file without a
-- final newline, and a line that does not exist.
#guard copy "# " ⟨#["int x;", "\treturn x;", ""]⟩ 2 2 == "#  return x;\n"
#guard copy "# " ⟨#["a", "b"]⟩ 1 5 == "# a\n# b\n"
#guard copy "# " ⟨#["a", ""]⟩ 3 3 == ""

end Printlines
end CC
