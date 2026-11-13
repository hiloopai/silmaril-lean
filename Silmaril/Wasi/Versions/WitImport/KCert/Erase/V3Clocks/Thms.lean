module

public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V3Clocks.Thms
public import Silmaril.Wasi.Versions.WitImport.KErase.Defs

@[expose] public section

/-!
# Doc comments only fill `docs` fields: `V3Clocks`

For each file, `KF.….parseEr`: the verified parser on the glued text with its doc comments
(`KF.….full`, `wit_src%`), with every `docs` field then erased (`Document.erase`), gives the
document of the text without doc comments (`KF.….src`, `wit_srcnd%`). Checked by the kernel
(`kernel_rfl`); the kernel never evaluates the doc strings, which the erasure discards.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

/-- `specs/wasi/0.3.2/clocks/monotonic-clock.wit`: its parse with doc comments, erased, is the parse without them. -/
theorem KF.v3.clocks.monotonic_clock.parseEr :
    (parseCharsK KF.v3.clocks.monotonic_clock.full).map Silmaril.Wasm.Wit.Document.erase = parseCharsK KF.v3.clocks.monotonic_clock.src :=
  (show (parseCharsK KF.v3.clocks.monotonic_clock.full).map Silmaril.Wasm.Wit.Document.erase = some (KF.v3.clocks.monotonic_clock.d String.ofList) by
    kernel_rfl).trans KF.v3.clocks.monotonic_clock.parse.symm

/-- `specs/wasi/0.3.2/clocks/system-clock.wit`: its parse with doc comments, erased, is the parse without them. -/
theorem KF.v3.clocks.system_clock.parseEr :
    (parseCharsK KF.v3.clocks.system_clock.full).map Silmaril.Wasm.Wit.Document.erase = parseCharsK KF.v3.clocks.system_clock.src :=
  (show (parseCharsK KF.v3.clocks.system_clock.full).map Silmaril.Wasm.Wit.Document.erase = some (KF.v3.clocks.system_clock.d String.ofList) by
    kernel_rfl).trans KF.v3.clocks.system_clock.parse.symm

/-- `specs/wasi/0.3.2/clocks/timezone.wit`: its parse with doc comments, erased, is the parse without them. -/
theorem KF.v3.clocks.timezone.parseEr :
    (parseCharsK KF.v3.clocks.timezone.full).map Silmaril.Wasm.Wit.Document.erase = parseCharsK KF.v3.clocks.timezone.src :=
  (show (parseCharsK KF.v3.clocks.timezone.full).map Silmaril.Wasm.Wit.Document.erase = some (KF.v3.clocks.timezone.d String.ofList) by
    kernel_rfl).trans KF.v3.clocks.timezone.parse.symm

/-- `specs/wasi/0.3.2/clocks/types.wit`: its parse with doc comments, erased, is the parse without them. -/
theorem KF.v3.clocks.types.parseEr :
    (parseCharsK KF.v3.clocks.types.full).map Silmaril.Wasm.Wit.Document.erase = parseCharsK KF.v3.clocks.types.src :=
  (show (parseCharsK KF.v3.clocks.types.full).map Silmaril.Wasm.Wit.Document.erase = some (KF.v3.clocks.types.d String.ofList) by
    kernel_rfl).trans KF.v3.clocks.types.parse.symm

end Silmaril.Wasi.Versions.WitImport
