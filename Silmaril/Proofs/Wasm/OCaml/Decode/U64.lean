module

public import Silmaril.Wasm.OCaml.Decode.Defs

/-! Kernel runs of `decode.ml`'s `u64` (header: `Silmaril.Wasm.OCaml.Decode.Thms`). -/

@[expose] public section
namespace Silmaril.Wasm.OCaml.Decode

set_option maxRecDepth 100000

/-- `u64` agrees with `Silmaril.Wasm.Binary.RefInterp.refU64` on every case of `u64Cases`. -/
theorem u64_agrees :
    u64Cases.all (fun (bs, p) => agreesU 64 asU64 (out (run .u64 [] bs p)) bs p) = true := by
  decide +kernel

end Silmaril.Wasm.OCaml.Decode
