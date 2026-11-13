module

public import Silmaril.Wasm.Wit.Binary.Custom.Defs
public import Silmaril.Proofs.Wasm.Wit.Binary.Sim.Items
public import Silmaril.Proofs.Wasm.Wit.Binary.Names
public import Silmaril.Proofs.Wasm.Wit.Binary.Json
public import Silmaril.Proofs.Wasm.Wit.Binary.Bytes
public import Silmaril.Proofs.Wasm.Wit.Binary.Canon
public import Silmaril.Proofs.Wasm.Wit.Binary.Producers
public import Silmaril.Proofs.Wasm.Wit.Binary.Roundtrip
public import Silmaril.Proofs.Wasm.Wit.Binary.NameSec

/-!
# WIT packages as type-only components: theorems

Proofs in `Silmaril/Proofs/Wasm/Wit/Binary/`:

* `decodeItems_encodeItems : p.Valid deps → encodeItems deps p = .ok ss →
  decodeItems ss = .ok p.normalize` — the item sections wit-component writes
  for a package (`Silmaril.Wasm.Wit.Binary.Encode`) decode
  (`Silmaril.Wasm.Wit.Binary.Decode`) to the package's normal form
  (`Silmaril.Wasm.Wit.Binary.Normal`). The proof is a simulation between the
  encoder's type tables and the decoder's slots (`Sim/*`): `valType_sim`
  (value types, with anonymous types shared by structure), `typeDefIdx_sim`
  (named types: the definition is claimed by the name), `funcType_sim`,
  `encodeInstance_item`, `decWorld_encodeWorld`, `decTop_encodeIface`.
* `decodePackage_encodePackage : p.Valid deps → encodePackage deps p = .ok b →
  decodePackage b = .ok (p.normalize.inject p.docsJson)` — at the byte level, with
  the `package-docs` metadata put back; uses `parse_encode` of component binaries,
  `JVal.parse_print` (the JSON of `package-docs` reads back) and
  `readDocsSection_docsSection`.
* `encodeItems_normalize : encodeItems deps p.normalize = encodeItems deps p` (the
  item encoder ignores docs; `sortFuncs_idem`) and `encodeItems_decodeItems`:
  **encode ∘ decode is the identity on the image** of the item encoder.
* `decodeWorldType_encodeWorldType`: a world embedded in a core module (the
  `component-type` payload) reads back in normal form with its string encoding.
* `Producers.parse_encode`: the `producers` section reads back;
  `parseNameSec_encode`: the `component-name` section reads back.
* `inject_docsJson : p.NamesUnique → p.normalize.inject p.docsJson = p.canon`
  (docs injection inverts docs extraction), hence
  `decodePackage_encodePackage_canon` (the bytes of a valid package with distinct
  names decode to `p.canon`: functions in wit-component's order, docs kept) and
  `encodePackage_decodePackage` (encode ∘ decode = id on the bytes of packages
  already in that order; false without that order, see `Golden.reorderCounter`).
* `demangle_mangled`, `parseIfaceName_id`, `nameKey_id`: names parse back.

See `docs/projects/wasm-components.md` for the status of the byte-level statements.
-/
