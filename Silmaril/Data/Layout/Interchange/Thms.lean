module

public import Silmaril.Data.Layout.Interchange.Defs
import Silmaril.Proofs.Data.Layout.Interchange

/-!
# The v1 report codec round-trips

PROVED in `Silmaril.Proofs.Data.Layout.Interchange`: UTF-16 encoding of strings is inverted
by the JSON reader's decoding (`unitsString_stringUnits`), and decoding inverts encoding on
JSON trees (`decode_encode`). The byte level (`decodeText`, the RFC 8259 reader) is not
covered: `Silmaril.Formats.JsonWire` has no printer/reader round-trip theorem.
-/

@[expose] public section

namespace Silmaril.Data.Layout.Interchange

theorem unitsString_stringUnits (s : String) :
    Formats.JsonWire.unitsString? (Formats.JsonWire.stringUnits s) = some s :=
  Silmaril.Proofs.Data.Layout.Interchange.unitsString?_stringUnits s

/-- Decoding inverts encoding, for every report. -/
theorem decode_encode (r : Report) : decode (encode r) = .ok r :=
  Silmaril.Proofs.Data.Layout.Interchange.decode_encode r

end Silmaril.Data.Layout.Interchange
