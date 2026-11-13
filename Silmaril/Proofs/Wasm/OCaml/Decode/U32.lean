module

public import Silmaril.Wasm.OCaml.Decode.Defs

/-! Kernel runs of `decode.ml`'s `u32` (header: `Silmaril.Wasm.OCaml.Decode.Thms`). -/

@[expose] public section
namespace Silmaril.Wasm.OCaml.Decode

set_option maxRecDepth 100000

/-- `u32` agrees with `Silmaril.Wasm.Binary.RefInterp.refU32` on every case of `u32Cases`. -/
theorem u32_agrees :
    u32Cases.all (fun (bs, p) => agreesU 32 asU32 (out (run .u32 [] bs p)) bs p) = true := by
  decide +kernel

end Silmaril.Wasm.OCaml.Decode
