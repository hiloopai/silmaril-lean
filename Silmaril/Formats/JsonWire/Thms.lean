module

public import Silmaril.Formats.JsonWire.Defs
public import Silmaril.Formats.JsonWire.Concrete.Thms
import Silmaril.Proofs.Formats.JsonWire.Parse

/-! # JSON on the wire: lemmas

* `parseCst?_sound`: a lossless CST the reader returns has the input as its source and is the
  reader's parse of it (`IsCst`);
* the concrete-syntax lemmas of `Silmaril.Formats.JsonWire.Concrete.Thms`.
-/

@[expose] public section

namespace Silmaril.Formats.JsonWire

theorem parseCst?_sound {dialect : Dialect} {bytes : Bytes} {cst : Cst}
    (h : parseCst? dialect bytes = some cst) : cst.source = bytes ∧ IsCst dialect cst :=
  Silmaril.Proofs.Formats.JsonWire.Parse.parseCst?_sound h

end Silmaril.Formats.JsonWire

end
