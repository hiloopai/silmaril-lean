module
public import Silmaril.Project.Formats.SExpWat.Defs
public import Silmaril.Data.IncludeBytes
import Silmaril.Proofs.Project.Formats.SExpWat

/-!
# Format `sexp.wat`: law and example

* `sexpWat_sound`: the parser is sound for `SExpWatRel`, from silmaril-lean's
  `Wat.sexpWat_of_fullExec`.
* An example on `examples/project-formats/example-wat.sexp`.
-/

@[expose] public section
namespace Silmaril.Project.Formats

open Silmaril.Formats.SExpEncoding

theorem sexpWat_sound : sexpWat.SoundFor SExpWatRel :=
  Silmaril.Proofs.Project.Formats.sexpWat_sound

/-- `examples/project-formats/example-wat.sexp`. -/
def exampleSExpWat : Silmaril.Formats.Bytes :=
  ⟨include_bytes "../../../../examples/project-formats/example-wat.sexp"⟩

theorem exampleSExpWat_parses : (sexpWat.parse exampleSExpWat).isSome = true := by decide +kernel

end Silmaril.Project.Formats

silmaril format_law sexp.wat sound := Silmaril.Project.Formats.sexpWat_sound
  (rel := Silmaril.Project.Formats.SExpWatRel)
