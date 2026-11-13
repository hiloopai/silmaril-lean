module

public import Silmaril.Wasi.Versions.WitImport.KLex.Defs
public import Silmaril.Wasi.Versions.WitImport.Select.Defs

@[expose] public section

/-!
# The WIT importer, kernel-reducible

`importK sel cs` is `WitImport.importPkg` (`sel = false`) or `WitImport.importIfaces`
(`sel = true`: worlds dropped before elaboration) on the characters `cs` of the glued source
texts (`wit_src%`), with the fuelled lexer `lexK` in place of the well-founded `lex`
(`parseCharsK`, equal to the parser of `Silmaril.Wasm.Wit.Text` by `parseCharsK_eq`). The rest is
the importer's own code: `mergeDocs`, `dropWorlds`, `Elab.elaborate`, `table`, `drops`. The
kernel evaluates all of it (`WitImport/KTables/*`).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasm.Wit

/-- The importer on glued source characters. -/
def importK (sel : Bool) (srcs : List (List Char)) : Except String Binary.Package := do
  let ds ← srcs.mapM fun cs =>
    match parseCharsK cs with
    | some d => .ok d
    | none => .error "not WIT text this parser accepts"
  let U := if sel then (mergeDocs ds).map dropWorlds else mergeDocs ds
  let P ← U.head?.elim (.error "no package") pure
  let (B, _) ← Elab.elaborate U P.name []
  pure B

/-- The signature table the importer gives, if it succeeds. -/
def kTable (ver sel : Bool) (srcs : List (List Char)) : Option Table :=
  match importK sel srcs with
  | .ok P => some (table ver P)
  | .error _ => none

/-- The resource drops the importer gives, if it succeeds. -/
def kDrops (ver : Bool) (srcs : List (List Char)) : Option (List FnName) :=
  match importK false srcs with
  | .ok P => some (drops ver P)
  | .error _ => none

end Silmaril.Wasi.Versions.WitImport
