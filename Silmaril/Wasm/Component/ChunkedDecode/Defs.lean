module

public import Silmaril.Wasm.Component.Chunked.Defs

/-!
# Chunked decode certificates for `decode?`: the extra check

`Silmaril.Wasm.Component.Chunked` checks a core module in slices (sections, code groups,
instruction plans) with silmaril's readers and proves the grammar `Encodes`. To get
`decode? b = some m` from the same checks (`Silmaril.Wasm.Component.ChunkedDecode.Thms`), one more
fact is needed that the grammar does not ask for: `readCode` rejects a function with more than
`maxLocals` (`50000`) locals. `chkLocals` checks it on the plans of a code group, reading only the
size and the locals vector of each entry (not the body), so it is cheap in the kernel.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.ChunkedDecode

open Silmaril.Wasm.Component.Chunked

/-- The locals of each code entry of the plans `ps`, on the bytes `r`, number at most
`maxLocals`. -/
def chkLocals : List CPlan → List UInt8 → Bool
  | [], _ => true
  | p :: ps, r =>
    match runAll (Silmaril.Wasm.Binary.Core.Decode.readU 32) (r.take p.kSize) with
    | some len =>
      (match runAll (Silmaril.Wasm.Binary.Core.Decode.readVec readLocalsGroup)
          (((r.drop p.kSize).take len).take p.kLocals) with
        | some lss => decide (lss.flatten.length ≤ Silmaril.Wasm.Binary.Core.Decode.maxLocals)
        | none => false) && chkLocals ps ((r.drop p.kSize).drop len)
    | none => false

end Silmaril.Wasm.Component.ChunkedDecode

end
