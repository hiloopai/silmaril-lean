module
public import Silmaril.Project.Formats.SExp.Defs
public import Silmaril.Data.IncludeBytes
import Silmaril.Proofs.Project.Formats.SExp

/-!
# Formats `sexp.text` and `sexp.canonical`: laws and examples

* `sexp_roundtrip`, `sexpCanonical_roundtrip`: whatever the registered printer
  produces parses back, from silmaril-lean's `printSExp?_sound` and
  `printCanonical?_sound` (the printers are checked).
* Examples on `examples/project-formats/example.{sexp,csexp}`, decided by the kernel.
-/

@[expose] public section
namespace Silmaril.Project.Formats

open Silmaril.Formats

theorem fromUTF8?_toUTF8 (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  simp [String.fromUTF8?, String.fromUTF8, s.isValidUTF8]

theorem sexp_roundtrip : sexp.RoundTrip := Silmaril.Proofs.Project.Formats.sexp_roundtrip

theorem sexpCanonical_roundtrip : sexpCanonical.RoundTrip := by
  rintro p hp v a ha
  cases hp
  exact RivestSExp.printCanonical?_sound ha

/-- `examples/project-formats/example.sexp`. -/
def exampleSExp : Silmaril.Formats.Bytes := ⟨include_bytes "../../../../examples/project-formats/example.sexp"⟩

/-- `examples/project-formats/example.csexp`. -/
def exampleCSExp : Silmaril.Formats.Bytes := ⟨include_bytes "../../../../examples/project-formats/example.csexp"⟩

theorem exampleSExp_parses : (sexp.parse exampleSExp).isSome = true := by decide +kernel

theorem exampleCSExp_parses : (sexpCanonical.parse exampleCSExp).isSome = true := by decide +kernel

end Silmaril.Project.Formats

silmaril format_law sexp.text roundtrip := Silmaril.Project.Formats.sexp_roundtrip
silmaril format_law sexp.canonical roundtrip := Silmaril.Project.Formats.sexpCanonical_roundtrip
