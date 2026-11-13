module

public import Silmaril.Project.CompilesTo.Defs
public import Silmaril.Cerberus.Codec.File.Defs

/-!
# Probe: the Core elaboration of a C text, as a canonical document

`docText text` runs the Lean Cerberus frontend (`FrontendAil`) and elaborator (`ElabAil`) on
`text` and prints the typed Ail (the text `ail_program%` reads) and the Core, a canonical `cerb-export` document (`Codec.encodeDocument`, `printTagged`), the text
that `core_document%` (`Silmaril.Cerberus.Core.Quote`) turns back into a `Codec.Document` literal.
`tools/c-tv` runs it at elaboration time (`run_cmd logWarning …` in a scratch module, with
`meta import` of this module) and reads the document between the markers. The output is
untrusted: a generated header states `ElaboratesTo` about the quoted literal, and Lean checks it.
-/

@[expose] public section

namespace Silmaril.Project.CompilesTo.Probe

open Silmaril.Cerberus
open Silmaril.Project.Shapes.C (FrontendAil ElabAil)

/-- The commit field of the probe's documents. -/
def commit : String := "silmaril-lean Lean Cerberus port (Project.Shapes.C.ElabAil)"

/-- The implementation field of the probe's documents. -/
def implementation : String :=
  "TargetCoherence.linuxLP64; ParameterCallReturn.Example.runtime (constructed)"

/-- The canonical document of the elaborated bindings. -/
def document (b : Codec.FileBindings) : String :=
  Silmaril.Formats.SExpEncoding.printTagged
    (Codec.encodeDocument ⟨commit, implementation, b, b.toFile, rfl, none⟩) ++ "\n"

/-- The canonical wire text of a typed Ail program (what `ail_program%` reads). -/
def ailText (p : Ail.TypedProgram) : String :=
  Ail.Codec.emitProgram Ail.Codec.emitGenTypeCategory p ""

/-- **The probe**: the typed Ail of the C text between `BEGIN-TYPED-AIL`/`END-TYPED-AIL`, then
its Core between `BEGIN-CORE-DOCUMENT`/`END-CORE-DOCUMENT`; or `FRONTEND-ERROR: …`,
`CORE-ELAB-ERROR: …`. -/
def docText (text : String) : String :=
  match FrontendAil text with
  | .error e => "FRONTEND-ERROR: " ++ e
  | .ok ail =>
    "BEGIN-TYPED-AIL\n" ++ ailText ail ++ "\nEND-TYPED-AIL\n" ++
    match ElabAil ail with
    | .ok b => "BEGIN-CORE-DOCUMENT\n" ++ document b ++ "END-CORE-DOCUMENT"
    | .error e => "CORE-ELAB-ERROR: " ++ (reprStr e)

end Silmaril.Project.CompilesTo.Probe

end
