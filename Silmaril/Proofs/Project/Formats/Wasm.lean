module

public import Silmaril.Project.Formats.Wasm.Defs
public import Silmaril.Wasm.Binaryen.Exe.EncodeSound

/-! # Proof of the `wasm.binary.core` printer lemma (restated in `Silmaril.Project.Formats.Wasm.Thms`) -/

@[expose] public section

namespace Silmaril.Proofs.Project.Formats

open Silmaril.Wasm Silmaril.Project Silmaril.Project.Formats

theorem wasm_print_sound {p} (hp : wasm.print = some p) {m : Silmaril.Wasm.Module}
    {b : Silmaril.Formats.Bytes} (h : p m = some b) : WasmRel b m := by
  cases hp
  cases he : Binaryen.Exe.encodeModule? m with
  | error => simp [he] at h
  | ok bs =>
    simp only [he] at h
    cases h
    simpa [WasmRel, Silmaril.Formats.Bytes.toList] using Binaryen.Exe.encodeModule?_sound he

end Silmaril.Proofs.Project.Formats
