module

public import Silmaril.Wasm.Tools.FastPaths.Defs
public import Silmaril.Wasm.Tools.FastFrame.Thms
import Silmaril.Proofs.Wasm.Tools.FastPaths

/-!
# The fast paths compute the specification functions

* **`checkFast_eq`**: `checkFast F b = Validate.check F b` (so `check_ok_iff`, `check_sound`
  and `check_complete` hold of the fast validator);
* **`stripFast_eq`**: `stripFast rm b` gives the bytes `Strip.strip rm` gives on the list;
* **`objdumpFast_eq`**: `objdumpFast b = Objdump.objdump b.data.toList`.

The proofs are in `Silmaril.Proofs.Wasm.Tools.FastPaths`.

New theorems.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.FastPaths

open Silmaril.Wasm.Tools.Features

/-- **The fast validator is the validator.** -/
theorem checkFast_eq (F : WFeatures) (b : ByteArray) : checkFast F b = Validate.check F b :=
  Silmaril.Proofs.Wasm.Tools.FastPaths.checkFast_eq F b

/-- **The fast `strip` is `strip`.** -/
theorem stripFast_eq (rm : String → Bool) (b : ByteArray) :
    (stripFast rm b).map (·.data.toList) = Strip.strip rm b.data.toList :=
  Silmaril.Proofs.Wasm.Tools.FastPaths.stripFast_eq rm b

/-- **The fast `objdump` is `objdump`.** -/
theorem objdumpFast_eq (b : ByteArray) : objdumpFast b = Objdump.objdump b.data.toList :=
  Silmaril.Proofs.Wasm.Tools.FastPaths.objdumpFast_eq b

end Silmaril.Wasm.Tools.FastPaths

end
