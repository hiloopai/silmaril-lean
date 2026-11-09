module
public import Silmaril.Project.Defs
public import Silmaril.Formats.SExp.Parser
public import Silmaril.Formats.SExp.Printer
public import Silmaril.Formats.SExp.Rivest

/-!
# Formats `sexp.text` and `sexp.canonical`

Thin adapters over silmaril-lean's S-expression code (`Silmaril/Formats/SExp`);
no parser is changed.

* `sexp.text`: UTF-8 text to a proper Lisp-style S-expression,
  `Silmaril.Formats.SExpParser.parseSExp?`. Printer: the checked printer
  `SExpPrinter.printSExp?`, encoded as UTF-8.
* `sexp.canonical`: the canonical representation of draft-rivest-sexp-04
  (`3:abc`-style verbatim atoms) to `RivestSExp`, `RivestSExp.parseCanonical?`.
  Printer: the checked `RivestSExp.printCanonical?`.

Both printers are *checked* (they reparse their output), so both round-trip laws
hold; they are proved in `Silmaril.Project.Formats.SExp.Thms`.
-/

@[expose] public section
namespace Silmaril.Project.Formats

open Silmaril.Formats

/-- Lisp-style S-expressions in UTF-8 text, proper lists only. -/
def sexp : Format blob (SExp String) where
  parse b := String.fromUTF8? b.data >>= SExpParser.parseSExp?
  print := some fun v => (SExpPrinter.printSExp? v).map fun s => ⟨s.toUTF8⟩

/-- Rivest canonical S-expressions (octet-string atoms). -/
def sexpCanonical : Format blob RivestSExp where
  parse := RivestSExp.parseCanonical?
  print := some RivestSExp.printCanonical?

end Silmaril.Project.Formats

silmaril format sexp.text := Silmaril.Project.Formats.sexp
  (doc := "UTF-8 Lisp-style S-expressions, proper lists (Silmaril.Formats.SExpParser.parseSExp?)")
silmaril format sexp.canonical := Silmaril.Project.Formats.sexpCanonical
  (doc := "Canonical Rivest S-expressions, draft-rivest-sexp-04 (RivestSExp.parseCanonical?)")
silmaril format_default sexp := sexp.text
