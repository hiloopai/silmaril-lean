module

public import Silmaril.Formats.LeanNDJSON.Validate.Defs
import Silmaril.Proofs.Formats.LeanNDJSON.Basic

/-!
# Lean-NDJSON validation: the checkers decide the specification

* `serialValid?_iff`: `serialValid?` decides `SerialValid`.
* `validate?_iff`: `validate?` decides `Valid` (serial validity and distinct declared names).
-/

@[expose] public section

namespace Silmaril.Formats.LeanNDJSON

theorem serialValid?_iff (c : Counters) (es : List Event) :
    serialValid? c es = true ↔ SerialValid c es :=
  Proofs.Formats.LeanNDJSON.serialValid?_iff c es

theorem validate?_iff (es : List Event) : validate? es = true ↔ Valid es :=
  Proofs.Formats.LeanNDJSON.validate?_iff es

end Silmaril.Formats.LeanNDJSON
