module

public import Silmaril.Wasm.OCaml.Decode.Defs

/-! Kernel runs of `decode.ml`'s `s32` (header: `Silmaril.Wasm.OCaml.Decode.Thms`). -/

@[expose] public section
namespace Silmaril.Wasm.OCaml.Decode

set_option maxRecDepth 100000

/-- `s32` agrees with `Silmaril.Wasm.Binary.RefInterp.refS32` on every case of `s32Cases`. -/
theorem s32_agrees :
    s32Cases.all (fun (bs, p) => agreesS 32 asS32 (out (run .s32 [] bs p)) bs p) = true := by
  decide +kernel

end Silmaril.Wasm.OCaml.Decode
