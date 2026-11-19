module

public import Silmaril.Containers.Adapter.Examples.Thms
meta import Silmaril.Containers.Adapter.Examples.Defs
meta import Silmaril.Containers.Events.Defs
meta import Silmaril.Containers.Signals.Defs

open Silmaril.Containers Silmaril.Containers.Adapter.Examples

public def main : IO Unit := do
  IO.println s!"abstract store load: {repr (abstractRuntime.load manifest)}"
  IO.println s!"checked stdio: {repr (stdioCodec.trace [.stdout [111, 107]])}"
  IO.println s!"unsupported stdio: {repr (stdioCodec.trace [.stdout [111], .clock 0])}"
  IO.println s!"SIGINT cleanup: {repr cancelled.effects}; {repr cancelled.stop}"
  IO.println s!"buggy handler: {repr buggy.stop}"
  IO.println "Lean proofs: abstract_safe, unsupported_stdio, alias_offset, partial_write_effect,"
  IO.println "cancel_cleanup, buggy_handler, toy_certificate. No layout hashing in this example."
