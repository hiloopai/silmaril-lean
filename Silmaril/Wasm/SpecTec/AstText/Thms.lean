module

public import Silmaril.Wasm.SpecTec.AstText.Defs
public import Silmaril.Proofs.Wasm.SpecTec.AstText.Compose
public import Silmaril.Proofs.Wasm.SpecTec.AstText.Streams
public import Silmaril.Proofs.Wasm.SpecTec.AstText.Slices

/-!
# SpecTec `--ast` text to IL scripts: results

Proved in `Silmaril.Proofs.Wasm.SpecTec.AstText.*`, in namespace `Silmaril.Wasm.SpecTec.AstText`; progress and scope in
`docs/projects/spectec/README.md`.

* `importAstText?_sound`, `importAstText?_complete`: the verified reader followed by the
  decoder is a sound and complete decoder for `AstTextRel`; `astTextRel_functional`: a text
  spells at most one script.
* `importAstText?_astFile`: printing any script at any `--ast-width` and reading it back gives
  the script, under the decidable side condition `AllToken (realsScript sc)` (every `realN`
  payload is a token). The condition is necessary (`IL.exists_decodeDef?_not_printable`) and
  holds for everything the reader returns (`allToken_of_importAstText?`).
* The pinned streams (`Streams`): `importAstText?_wasm30Text : importAstText? wasm30Text =
  some Specs.wasm30`, where `wasm30Text := astFile 80 (scriptS Specs.wasm30)`; likewise for
  wasm-1.0 and wasm-2.0. **That `wasm30Text` is the contents of `specs/spectec/wasm-3.0.ast` is
  a compiled build-time check (`spectec_check_stream`), not a kernel fact.** The same check runs
  the verified reader on each file and requires the result to be `scriptS Specs.wasmNN`.
* Literal slices (`Slices`): the kernel lexes the first 26 lines of `wasm-3.0.ast` and the
  `Bi32` definition (lines 47339-47347): `parse_prefix5`, `import_prefix5 : importAstText?
  prefix5 = some (Specs.wasm30.take 5)`, `parse_bi32`, `import_bi32`. That the literals are those
  lines is again a compiled check (`spectec_check_slice`).
-/
