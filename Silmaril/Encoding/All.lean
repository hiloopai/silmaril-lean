module

public import Silmaril.Encoding.Relation
public import Silmaril.Encoding.Lattice
public import Silmaril.Encoding.Codec
public import Silmaril.Encoding.Per
public import Silmaril.Encoding.Category
public import Silmaril.Encoding.Fibration
public import Silmaril.Encoding.Encoded
public import Silmaril.Encoding.Carriers
public import Silmaril.Encoding.Unicode
public import Silmaril.Encoding.Base64
public import Silmaril.Encoding.Syntax
public import Silmaril.Encoding.FunctionalCat
public import Silmaril.Encoding.SyntaxCarriers

/-!
# Encoding theory

Encodings as values `EncRel σ α`, their lattice, induced partial
equivalences, categories `EncCat σ` / `EncCat₂`, encoded values, and carrier
functors (bytes, Unicode text, base64, naturals), and text/binary syntaxes
(`WithText`, `WithBinary`).  See `Silmaril.Encoding.Relation`.
Format instances live in `Silmaril.Formats.Json.Encoding`,
`Silmaril.Formats.Cbor.Encoding` and `Silmaril.Formats.Cbor.EncodingJson`
(and their `EncodingSyntax` companions).  `Silmaril.Encoding.Wasm` (`WasmText`,
`WasmBinary`) is not imported here, since it depends on the Wasm syntax.
-/
