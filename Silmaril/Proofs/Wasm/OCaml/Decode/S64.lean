module

public import Silmaril.Wasm.OCaml.Decode.Defs

/-! Kernel runs of `decode.ml`'s `s64` (header: `Silmaril.Wasm.OCaml.Decode.Thms`). -/

@[expose] public section
namespace Silmaril.Wasm.OCaml.Decode

set_option maxRecDepth 100000

/-- `s64` agrees with `Silmaril.Wasm.Binary.RefInterp.refS64` on every case of `s64Cases`. -/
theorem s64_agrees :
    s64Cases.all (fun (bs, p) => agreesS 64 asS64 (out (run .s64 [] bs p)) bs p) = true := by
  decide +kernel

end Silmaril.Wasm.OCaml.Decode
