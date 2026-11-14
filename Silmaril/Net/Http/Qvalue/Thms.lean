module

public import Silmaril.Net.Http.Qvalue.Defs
import Silmaril.Proofs.Net.Http.Qvalue

/-!
# Quality values: laws

* `parseQvalue_le`: a weight is at most `1000` (thousandths of `1`).
-/

@[expose] public section

namespace Silmaril.Net.Http.Qvalue

theorem parseQvalue_le {v : List UInt8} {q : Nat} (h : parseQvalue v = some q) : q ≤ 1000 :=
  Proofs.Net.Http.Qvalue.parseQvalue_le h

end Silmaril.Net.Http.Qvalue
