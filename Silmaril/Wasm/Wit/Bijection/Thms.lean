module

public import Silmaril.Proofs.Wasm.Wit.Bijection

/-!
# WIT packages and type-only components: the end-to-end correspondence

Proofs in `Silmaril.Proofs.Wasm.Wit.Bijection`:

* `surface_decode`, `surface_injective`: elaborated surface packages are determined
  by their bytes up to the normal form `canon`;
* `encode_injective`, `image_roundtrip`: `encodePackage`/`decodePackage` are
  inverse bijections between canonical valid packages with distinct names and
  their bytes;
* `text_to_component`: for a valid document, text ↔ AST is exact, `elaborate`
  succeeds or reports a wit-parser world error, and the bytes decode to the
  normal form.

See `tools/wasm-tools/README.md` (section *The end-to-end correspondence*).
-/
