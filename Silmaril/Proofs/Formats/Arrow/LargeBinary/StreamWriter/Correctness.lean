module

public import Silmaril.Formats.Arrow.LargeBinary.StreamWriter.Defs
import Silmaril.Formats.Arrow.Binary.StreamWriter.Thms
import Silmaril.Formats.Arrow.LargeBinary.Stream.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.LargeBinary.StreamWriter

open Silmaril.Formats.Arrow
open LargeBinary.StreamWriter

theorem emit_readback {limits : Limits} {field : LargeBinary.Field}
    {batches : List LargeBinary.Column} {wire : KBytes}
    (written : emit limits field batches = .ok wire) :
    ∃ decoded, LargeBinary.Stream.read limits .modern wire = .ok decoded ∧
      Agrees field batches decoded ∧ LargeBinary.Stream.StreamWire limits .modern wire decoded ∧
      Binary.StreamWriter.SerializedWire .i64 limits field.name field.nullable batches wire := by
  cases serialized : serialize limits field batches with
  | error => simp [emit, serialized, Bind.bind, Except.bind] at written
  | ok actual =>
    cases decoded : LargeBinary.Stream.read limits .modern actual with
    | error =>
      simp [emit, serialized, decoded, Bind.bind, Except.bind, Except.mapError] at written
    | ok result =>
      by_cases agrees : Agrees field batches result
      · have same : actual = wire := by
          simpa [emit, serialized, decoded, agrees, Bind.bind, Except.bind, Except.mapError] using written
        subst wire
        exact ⟨result, decoded, agrees, LargeBinary.Stream.read_sound decoded,
          Binary.StreamWriter.serializeFor_exact serialized⟩
      · simp [emit, serialized, decoded, agrees, Bind.bind, Except.bind, Except.mapError] at written

end Silmaril.Proofs.Formats.Arrow.LargeBinary.StreamWriter
