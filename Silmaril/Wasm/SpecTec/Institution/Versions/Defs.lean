module

public import Silmaril.Wasm.SpecTec.Institution.Defs

/-!
# Versions of a SpecTec specification as theories: definitions

`relFree d` says that the top-level definition `d` declares no relation (it is a syntax type, a
function, a grammar or a group). An erratum whose corrected definition is `relFree` changes no
rule, so it leaves the theory of a script unchanged (`Versions.Thms`). That is the Lean check of
the `theory-diff` rows "wasm-3.0 original → Binary51, Text6x, fixed" and "wasm-2.0 original →
fixed" (`docs/projects/spectec/README.md`). `relFreeExcept X d` allows relations named in `X`: such
errata change the theory only at the relations `X` (the wasm-1.0 row, where erratum 680 corrects
`Module_ok`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod

/-- `d` declares no relation. -/
def relFree (d : Def) : Bool :=
  match declKind? d with
  | some (.rel, _) => false
  | _ => true

/-- `d` declares no relation outside the names `X`. -/
def relFreeExcept (X : List IL.Id) (d : Def) : Bool :=
  match declKind? d with
  | some (.rel, y) => y ∈ X
  | _ => true

/-- No erratum of the list corrects a relation outside the names `X`. -/
def ErrataRelFreeExcept (X : List IL.Id) (es : List Erratum) : Prop :=
  ∀ e ∈ es, relFreeExcept X e.corrected = true

/-- No erratum of the list corrects a relation. -/
def ErrataRelFree (es : List Erratum) : Prop := ∀ e ∈ es, relFree e.corrected = true

end Silmaril.Wasm.SpecTec.Institution
