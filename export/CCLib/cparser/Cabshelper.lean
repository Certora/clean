/-
  Port of `cparser/Cabshelper.ml`: helper functions on the parse tree
  `Cabs` (storage-class and specifier tests, locations).
-/
import CCLib.cparser.Cabs

namespace CC
namespace Cabshelper

open Cabs

def isStatic : List SpecElem → Bool
  | [] => false
  | .SpecStorage .STATIC :: _ => true
  | _ :: rest => isStatic rest

def isExtern : List SpecElem → Bool
  | [] => false
  | .SpecStorage .EXTERN :: _ => true
  | _ :: rest => isExtern rest

def isInline : List SpecElem → Bool
  | [] => false
  | .SpecFunction .INLINE :: _ => true
  | _ :: rest => isInline rest

def isTypedef : List SpecElem → Bool
  | [] => false
  | .SpecStorage .TYPEDEF :: _ => true
  | _ :: rest => isTypedef rest

def get_definitionloc : Definition → Loc
  | .FUNDEF _ _ _ _ l => l
  | .DECDEF _ l => l
  | .PRAGMA _ l => l
  | .STATIC_ASSERT _ _ _ _ l => l

def get_statementloc : Statement → Loc
  | .NOP loc => loc
  | .COMPUTATION _ loc => loc
  | .BLOCK _ loc => loc
  | .If _ _ _ loc => loc
  | .WHILE _ _ loc => loc
  | .DOWHILE _ _ loc => loc
  | .FOR _ _ _ _ loc => loc
  | .BREAK loc => loc
  | .CONTINUE loc => loc
  | .RETURN _ loc => loc
  | .SWITCH _ _ loc => loc
  | .CASE _ _ loc => loc
  | .DEFAULT _ loc => loc
  | .LABEL _ _ loc => loc
  | .GOTO _ loc => loc
  | .DEFINITION d => get_definitionloc d
  | .ASM _ _ _ _ _ _ loc => loc

def string_of_loc (l : Loc) : String := s!"{l.filename}:{l.lineno}"

def format_loc := string_of_loc

end Cabshelper
end CC
