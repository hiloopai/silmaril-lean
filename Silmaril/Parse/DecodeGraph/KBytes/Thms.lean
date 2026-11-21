module

public import Silmaril.Parse.DecodeGraph.KBytes.Defs
import Silmaril.Proofs.Parse.DecodeGraph.KBytes

public section

namespace Silmaril.Parse.DecodeGraph

/-- On a well-formed rope, the existing `ByteArray` parser and the direct rope
parser agree at the same window and cursor, including EOF diagnostics. -/
theorem kbyte_eq_byte (bytes : KBytes) (valid : bytes.wf = true) (stop pos : Nat) :
    kbyte bytes stop pos = ByteParse.byte bytes.toByteArray stop pos :=
  Proofs.kbyte_eq_byte bytes valid stop pos

end Silmaril.Parse.DecodeGraph
