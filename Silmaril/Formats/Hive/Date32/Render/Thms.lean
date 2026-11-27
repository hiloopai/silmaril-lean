module

public import Silmaril.Formats.Hive.Date32.Render.Defs
import Silmaril.Proofs.Formats.Hive.Date32.Render

public section

namespace Silmaril.Formats.Hive.Date32

open DateInterop.Date32 (Payload)

/-- Printing and parsing agree on the exact canonical text and signed day. -/
theorem encodeText_ok_iff (day : Payload) (text : String) :
    encodeText day = .ok text ↔ decodeText text = .ok day :=
  Proofs.Formats.Hive.Date32.Render.encodeText_ok_iff day text

/-- The write planner can restore every successfully encoded present cell. -/
theorem encode_convert_leftInverse (key : String) :
    WritePlan.CellLeftInverse (partition key) encode convert :=
  fun _ day text printed => (encodeText_ok_iff day text).mp printed

/-- Every day in the four-digit calendar range has printable text. -/
theorem encodeText_outside (day : Payload) :
    encodeText day = .error (.outsideDateProfile day) ↔ ¬ Csv.Typed.Codecs.Date32.Admitted day :=
  Proofs.Formats.Hive.Date32.Render.encodeText_outside day

/-- Use the same key and options to recover the exact typed cell, including null. -/
theorem decodeDirectory_renderDirectory (key : String) (options : PartitionPath.Options)
    (day : Option Payload) (directory : String) (written : renderDirectory key options day = .ok directory) :
    WritePlan.decodeDirectory (partition key) options convert directory = .ok (fun _ => day) :=
  Proofs.Formats.Hive.Date32.Render.decodeDirectory_renderDirectory key options day directory written

/-- An otherwise admitted present value equal to the decoded marker is refused. -/
theorem renderDirectory_markerCollision (key : String) (options : PartitionPath.Options)
    (day : Payload) (printed : encodeText day = .ok options.nullMarker)
    (marker : options.nullMarker.isEmpty = false)
    (valid : PartitionPath.validate options [(key, some options.nullMarker)] = .ok ()) :
    renderDirectory key options (some day) = .error (.path (.nullMarkerCollision key)) :=
  Proofs.Formats.Hive.Date32.Render.renderDirectory_markerCollision key options day printed marker valid

end Silmaril.Formats.Hive.Date32
