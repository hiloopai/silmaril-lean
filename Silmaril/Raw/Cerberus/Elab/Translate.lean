module

public import Silmaril.Cerberus.Ail.Codec.Defs
public import Silmaril.Cerberus.Codec.WellFormed.Defs

/-! # Elaboration of typed Ail into Cerberus Core (part 1)

The port of Cerberus's `frontend/model/translation.lem` (`Translation.translate_program`, about 5-8k lines with
its helpers in `translation_aux.lem`, `translation_effect.lem`), followed by the Core passes that the exporter
applies (`core_passes`: `Core_indet.hackish_order`, the sequentialisation used by the driver, ...) and the
linking with `std.core` and the implementation file, at Cerberus `b3e11ea3`.

`elaborate tail` maps the typed-Ail output of `cerb-oracle --level tail` to the wire bindings of the linked
Core file that `cerb-oracle --level core` prints for the same program; `printDocument` prints it in the
canonical dialect (`Codec.WellFormed`), so the measure of the port is byte equality with the oracle's document.

Status: a stub. Every program is rejected; the selected cases are ported constructor by constructor in `Silmaril.Cerberus.Elaboration`.

## Notes for the port

* Symbols: Core documents carry Cerberus's raw fresh numbers (std.core first, then the program), while
  `--level tail` documents are renumbered canonically by the oracle (`--raw-fresh` keeps the raw numbers). Either
  take raw-fresh tail input and replay Cerberus's counter, or compare modulo a canonical renumbering; the
  evaluator reports both `core_exact` (bytes) and `core_alpha_exact` (symbol numbers renamed by first occurrence).
* std.core and the implementation are constant: their part of the document can be taken from any oracle
  document (`stdlib`, `impl`, and the std.core symbols' locations with their absolute paths) until the Core
  parser is ported.
-/

@[expose] public section

namespace Silmaril.Cerberus.Elab

open Silmaril.Cerberus

/-- Elaborate a typed-Ail output to the bindings of the linked Core file. -/
def elaborate (_tail : Ail.Codec.TailOutput) : Except String Codec.FileBindings :=
  .error "unsupported: the elaboration (translation.lem) is not ported yet"

/-- The canonical text of a Core document with these bindings. -/
def printDocument (b : Codec.FileBindings) : String :=
  let doc : Codec.Document :=
    { commit := "b3e11ea334e95359907d4abf9194f0e7fedc6c6a",
      implementation := "gcc_4.9.0_x86_64-apple-darwin10.8.0",
      bindings := b, file := b.toFile, file_eq := rfl }
  Formats.SExpEncoding.printTagged (Codec.document.enc doc) ++ "\n"

end Silmaril.Cerberus.Elab
