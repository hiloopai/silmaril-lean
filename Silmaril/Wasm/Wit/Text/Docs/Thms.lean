module

public import Silmaril.Wasm.Wit.Text.Docs.Defs
public import Silmaril.Proofs.Wasm.Wit.Text.Docs

/-!
# WIT text with `wit-parser`'s doc comments: theorems

Proofs in `Silmaril.Proofs.Wasm.Wit.Text.Docs`:

* `normDocs_clean`: on `///` comments of one space and a clean line each,
  `wit-parser`'s normalisation is the plain reading (the lines joined with
  newlines, as `Parse.mkDocs` gives them), so `parseWP` and `parse` agree on such
  documentation;
* `normDocs_block`, `normDocs_dedent`, `normDocs_plain_block`: examples of where they
  differ (block comments, indentation, plain block comments).

Tested, not proved: `parseWP` against `wit-parser` 0.263.0 through elaboration and
encoding (`tests/wit-text/docs.sh`): the seven WASI 0.2.12 packages and the fixture
`tests/wit-text/docs.wit` (block comments, `//` docs, dedent, comments in parameter
lists, after gates and at the end of lists) give exactly the bytes of
`wasm-tools component wit --wasm` 1.263.0, `package-docs` included. That `docPos`
matches the call sites of `parse_docs` is a transcription.
-/
