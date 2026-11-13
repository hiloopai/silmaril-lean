import Silmaril.Compiler.Core.ParameterCallReturn.Thms

/-! Executable receipt: check the exact existing runtime recognizers both on
our constructed runtime and on a canonical genuine Core capture. The generic
length_one_eval, nth_zero_eval and convLoadedInt_eval theorems explain these
finite branches. This is not whole-runtime equivalence or parser adequacy. -/
open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Compile.Core.Verified
open Silmaril.Cerberus.Elaboration
open Silmaril.Compiler.Core.ParameterCallReturn

private def checked {α : Type} (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error why => throw <| IO.userError why

private def check (name : String) (runtime : List Runtime.Binding) (program : Dynamics.Program) : IO Unit := do
  let length ← checked <| Runtime.fetchSymbol (runtime.map Prod.fst) "params_length"
  let nth ← checked <| Runtime.fetchSymbol (runtime.map Prod.fst) "params_nth"
  let convert ← checked <| Runtime.fetchSymbol (runtime.map Prod.fst) "conv_loaded_int"
  unless CallArg.isParamsLength program length do throw <| IO.userError s!"{name}: length branch rejected"
  unless CallArg.isParamsNth program nth do throw <| IO.userError s!"{name}: nth0 branch rejected"
  unless ConvInt.isConvLoadedInt program convert do throw <| IO.userError s!"{name}: conversion branch rejected"
  IO.println s!"{name}: actual length-singleton/nth-zero/specified-int recognizers all true"

def main (args : List String) : IO UInt32 := do
  let [path] := args | throw <| IO.userError "expected genuine canonical Core capture"
  let text ← if path.endsWith ".gz" then do
    let result ← IO.Process.output {cmd := "gzip", args := #["-dc", path]}
    unless result.exitCode == 0 do throw <| IO.userError result.stderr
    pure result.stdout
  else IO.FS.readFile path
  let document ← match Codec.WellFormed.parseDocument text with
    | .ok value => pure value
    | .error why => throw <| IO.userError s!"Core capture decoding: {repr why}"
  unless (Silmaril.Formats.SExpEncoding.printTagged (Codec.encodeDocument document) ++ "\n") == text do throw <| IO.userError "noncanonical Core capture"
  check "constructed" Example.runtime.stdlib file
  check "captured upstream" document.bindings.stdlib document.file
  pure 0
