module

public import Silmaril.ProofFormats.LeanNDJSON.Arithmetic.Defs
public import Silmaril.Formats.LeanNDJSON.Validate.Thms
import Silmaril.Proofs.ProofFormats.LeanNDJSON.Arithmetic

/-!
# PA proofs from Lean-NDJSON: soundness

* `importCheckFrom_sound`: a declaration accepted from decoded records is a derivation
  (`Seq.Derivable`, the existing natural deduction) of the reported judgment.
* `importCheck_sound`: the same from bytes; moreover the file decoded and is `Valid` (serially
  valid references, distinct declared names).

Nothing else is claimed: in particular the declared type of the declaration and the file's
metadata are not evidence, and decoding and translation are not trusted.
-/

@[expose] public section

namespace Silmaril.ProofFormats.LeanNDJSON.Arithmetic

open Silmaril.Formats.LeanNDJSON Silmaril.Consequence.Arithmetic.ND

/-- **An imported, checked declaration is a derivation.** -/
theorem importCheckFrom_sound {T : Theory} {es : List Event} {decl : String} {s : Seq}
    (h : importCheckFrom T es decl = .ok s) : s.Derivable T :=
  Proofs.ProofFormats.LeanNDJSON.Arithmetic.importCheckFrom_sound h

/-- **An imported, checked declaration from bytes is a derivation, from a valid file.** -/
theorem importCheck_sound {T : Theory} {bytes : List UInt8} {decl : String} {s : Seq}
    (h : importCheck T bytes decl = .ok s) :
    s.Derivable T ∧ ∃ es, readFile bytes = .ok es ∧ Valid es :=
  Proofs.ProofFormats.LeanNDJSON.Arithmetic.importCheck_sound h

end Silmaril.ProofFormats.LeanNDJSON.Arithmetic
