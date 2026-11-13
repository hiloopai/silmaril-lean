module

public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V3Cli.Thms
public import Silmaril.Wasi.Versions.WitImport.KErase.Defs

@[expose] public section

/-!
# Doc comments only fill `docs` fields: `V3Cli`

For each file, `KF.….parseEr`: the verified parser on the glued text with its doc comments
(`KF.….full`, `wit_src%`), with every `docs` field then erased (`Document.erase`), gives the
document of the text without doc comments (`KF.….src`, `wit_srcnd%`). Checked by the kernel
(`kernel_rfl`); the kernel never evaluates the doc strings, which the erasure discards.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

/-- `specs/wasi/0.3.2/cli/environment.wit`: its parse with doc comments, erased, is the parse without them. -/
theorem KF.v3.cli.environment.parseEr :
    (parseCharsK KF.v3.cli.environment.full).map Silmaril.Wasm.Wit.Document.erase = parseCharsK KF.v3.cli.environment.src :=
  (show (parseCharsK KF.v3.cli.environment.full).map Silmaril.Wasm.Wit.Document.erase = some (KF.v3.cli.environment.d String.ofList) by
    kernel_rfl).trans KF.v3.cli.environment.parse.symm

/-- `specs/wasi/0.3.2/cli/exit.wit`: its parse with doc comments, erased, is the parse without them. -/
theorem KF.v3.cli.exit.parseEr :
    (parseCharsK KF.v3.cli.exit.full).map Silmaril.Wasm.Wit.Document.erase = parseCharsK KF.v3.cli.exit.src :=
  (show (parseCharsK KF.v3.cli.exit.full).map Silmaril.Wasm.Wit.Document.erase = some (KF.v3.cli.exit.d String.ofList) by
    kernel_rfl).trans KF.v3.cli.exit.parse.symm

/-- `specs/wasi/0.3.2/cli/run.wit`: its parse with doc comments, erased, is the parse without them. -/
theorem KF.v3.cli.run.parseEr :
    (parseCharsK KF.v3.cli.run.full).map Silmaril.Wasm.Wit.Document.erase = parseCharsK KF.v3.cli.run.src :=
  (show (parseCharsK KF.v3.cli.run.full).map Silmaril.Wasm.Wit.Document.erase = some (KF.v3.cli.run.d String.ofList) by
    kernel_rfl).trans KF.v3.cli.run.parse.symm

/-- `specs/wasi/0.3.2/cli/stdio.wit`: its parse with doc comments, erased, is the parse without them. -/
theorem KF.v3.cli.stdio.parseEr :
    (parseCharsK KF.v3.cli.stdio.full).map Silmaril.Wasm.Wit.Document.erase = parseCharsK KF.v3.cli.stdio.src :=
  (show (parseCharsK KF.v3.cli.stdio.full).map Silmaril.Wasm.Wit.Document.erase = some (KF.v3.cli.stdio.d String.ofList) by
    kernel_rfl).trans KF.v3.cli.stdio.parse.symm

/-- `specs/wasi/0.3.2/cli/terminal.wit`: its parse with doc comments, erased, is the parse without them. -/
theorem KF.v3.cli.terminal.parseEr :
    (parseCharsK KF.v3.cli.terminal.full).map Silmaril.Wasm.Wit.Document.erase = parseCharsK KF.v3.cli.terminal.src :=
  (show (parseCharsK KF.v3.cli.terminal.full).map Silmaril.Wasm.Wit.Document.erase = some (KF.v3.cli.terminal.d String.ofList) by
    kernel_rfl).trans KF.v3.cli.terminal.parse.symm

end Silmaril.Wasi.Versions.WitImport
