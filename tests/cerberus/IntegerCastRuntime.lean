import Silmaril.Cerberus.Elaboration.Conversion.Defs
import Silmaril.Cerberus.Codec.WellFormed.Defs
import Silmaril.Cerberus.Core.Outcome.Defs

/-! Execute the actual captured runtime's loaded-integer conversion in the
imported Core LTS. Expected values are comparison outputs only. This is external
fixture evidence, not a general C conversion or runtime adequacy theorem. -/
open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Elaboration
open Construction

private def checked {α : Type} (context : String) : Except String α → IO α
  | .ok value => pure value
  | .error why => throw <| IO.userError s!"{context}: {why}"

private def load (path : System.FilePath) : IO Codec.Document := do
  let result ← IO.Process.output {cmd := "gzip", args := #["-dc", path.toString]}
  unless result.exitCode == 0 do
    throw <| IO.userError s!"{path}: gzip failed: {result.stderr}"
  match Codec.WellFormed.parseDocument result.stdout with
  | .ok document => pure document
  | .error why => throw <| IO.userError s!"{path}: actual Core document: {repr why}"

private def specifiedCase (document : Codec.Document) (destination : Ctype)
    (input expected : Int) : IO Unit := do
  let expression ← checked "actual conv_loaded_int call" <|
    Conversion.loadedArithmetic document.bindings.stdlib
      (.mk [] (.basic (.integer (.signed .int)))) destination (specified (integer input))
  let start : State := {control := .pureExpr expression ∅}
  let execution := run document.file ∅ 10000 start
  match execution.ending with
  | some (.defined (.loaded (.specified (.integer value)))) =>
      unless value == expected do
        throw <| IO.userError s!"specified conversion: expected {expected}, actual {value}"
  | ending => throw <| IO.userError s!"specified conversion: {(observation ending).json.compress}"
  IO.println s!"actual runtime specified({input}) -> specified({expected}); transitions={execution.actions.length}"

private def unspecifiedCase (document : Codec.Document) (source destination : Ctype) : IO Unit := do
  let expression ← checked "actual conv_loaded_int unspecified call" <|
    Conversion.loadedArithmetic document.bindings.stdlib source destination (unspecified source)
  let start : State := {control := .pureExpr expression ∅}
  let execution := run document.file ∅ 10000 start
  match execution.ending with
  | some (.defined (.loaded (.unspecified actual))) =>
      unless decide (actual = destination) do
        throw <| IO.userError "unspecified conversion discarded or changed the destination CType"
  | ending => throw <| IO.userError s!"unspecified conversion: {(observation ending).json.compress}"
  IO.println s!"actual runtime unspecified -> unspecified(exact destination CType); transitions={execution.actions.length}"

def main (args : List String) : IO UInt32 := do
  let [directory] := args
    | throw <| IO.userError "expected actual Cerberus fixture directory"
  let document ← load (System.FilePath.mk directory / "cast-narrow" / "core.sexp.gz")
  let signedInt : Ctype := .mk [] (.basic (.integer (.signed .int)))
  let unsignedChar : Ctype := .mk [] (.basic (.integer (.unsigned .ichar)))
  let signedLong : Ctype := .mk [] (.basic (.integer (.signed .long)))
  specifiedCase document unsignedChar 257 1
  specifiedCase document signedLong (-1) (-1)
  unspecifiedCase document signedInt (.mk [.std "preserved cast destination"]
    (.basic (.integer (.unsigned .ichar))))
  unspecifiedCase document signedInt (.mk [.std "preserved bool destination"]
    (.basic (.integer .bool)))
  return 0
