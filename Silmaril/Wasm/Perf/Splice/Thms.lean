module

public import Silmaril.Wasm.Perf.Splice.Defs
import Silmaril.Proofs.Wasm.Perf.Splice.Eq

/-!
# `spliceF` is `Splice.splice`

`rawSecF_eq`, `rawSecsF_eq`, and `splice_eq_spliceF : Splice.splice = spliceF`, registered with
`@[csimp]`. The proofs are in `Silmaril.Proofs.Wasm.Perf.Splice.Eq`.
-/

@[expose] public section

namespace Silmaril.Wasm.Perf.Splice

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wac.Splice (RawTable rawSec rawSecs splice)

theorem toBA_append (l l' : List UInt8) : toBA (l ++ l') = toBA l ++ toBA l' :=
  Silmaril.Proofs.Wasm.Perf.Splice.toBA_append l l'

theorem rawSecF_eq (raw : RawTable) (acc : ByteArray) (s : Section) :
    rawSecF raw acc s = (rawSec raw s).map (acc ++ toBA ·) :=
  Silmaril.Proofs.Wasm.Perf.Splice.rawSecF_eq raw acc s

theorem rawSecsF_eq (raw : RawTable) (ss : List Section) (acc : ByteArray) :
    rawSecsF raw ss acc = (rawSecs raw ss).map (acc ++ toBA ·) :=
  Silmaril.Proofs.Wasm.Perf.Splice.rawSecsF_eq raw ss acc

/-- **`spliceF` is `Splice.splice`**, used by the compiler in its place. -/
@[csimp] theorem splice_eq_spliceF : @splice = @spliceF :=
  Silmaril.Proofs.Wasm.Perf.Splice.splice_eq_spliceF

/-- `splice_eq_spliceF` the other way round, for the definitions that call `spliceF`
(`Wac.Emit.composeWasmRaw`). -/
theorem spliceF_eq : @spliceF = @splice := splice_eq_spliceF.symm

end Silmaril.Wasm.Perf.Splice
