# Strict and Ultrastrict modules

Import `Silmaril.Wasm.Sublanguages.Strict.Thms`. In the new `Sublanguages` API,
**Strict allows function imports**. **Ultrastrict has no imports**. The
previous `Profiles.Strict` name and its proofs still refer to the earlier
closed guard; `Ultrastrict.legacyEquiv` is an exact, computable bridge.

| Type | What it guarantees |
| --- | --- |
| `LocalSections` | Type groups, function definitions, start, and function-only exports. These can refer to imports; this is section data, not a standalone validation judgment. |
| `FunctionModule` | Those sections plus an ordered list of `FunctionImport` declarations. No memory, table, global, tag, data, or element fields. Imports have one constructor: a named function type use. |
| `Strict` | `FunctionModule` plus the existing immutable-GC, no-exception feature guard over the entire assembled Core module, including nested bodies. Still not necessarily valid. |
| `Ultrastrict` | Guarded `LocalSections` assembled with no imports. There is no import field. |
| `Strict.Checked iface` | `Strict` plus the actual Core validation judgment at the given import/export interface. |

## Move between these and Core

- `FunctionModule.ofCore?` rejects resource sections, any other import kind
  (even a constant global), and any non-function export. It doesn't drop
  unwanted sections, silently filter imports, or renumber references.
  `ofCore?_toCore` and `toCore_ofCore?` prove both directions of exact
  projection for the represented shape. `Strict.ofCore?` also checks the
  features, and `Ultrastrict.ofCore?` also checks import absence.
- `functionTypes` lists import type uses before local type uses. Both that
  list and `functionSignature?` agree with the actual Core queries. This is
  source lookup; `Strict.validate?` runs the existing Core validator to
  resolve type uses and check the whole module. `validate?_ofChecked` gives
  the result for any module inhabiting `Strict.Checked iface`.
- `strictLanguage`, `ultrastrictLanguage`, and `ultrastrictIntoStrict` plug
  into the existing [sublanguage API](wasm-sublanguages.md).
  The `functional gc exn` objects retain their closed-module meaning.
  `strictReadback` and `ultrastrictReadback` plug into its actual Core linker
  adapter. This doesn't make the linker total or establish image closure.

The [regression](../../tests/wasm/profiles/OpenStrict.lean) validates
`env.read : [] → [i32]` and `env.next : [i32] → [i32]`, calls both by index,
and re-exports one under a different name. It checks that a provider supplying
the two functions links through Core and the result reads back as Ultrastrict.
It also checks rejection of resource imports and sections, forbidden
instructions, and an unresolved import type index (which passes the shape and
feature checks, but fails validation).

## Seam for host effects

`Strict.Checked.imports_ok` aligns each named declaration with the
corresponding closed Core interface port, in the same resolved type context
as the validated module. `FunctionImport.port_type` proves that a validated
port is a function port resolved from the declaration's type index. A
denotational client could use the validated position and signature to index
a request in a free monad; an operational client can supply its host and
initialization policy separately. These are interfaces for future semantics,
not new execution rules. A type-correct host can still have effects, trap, or
diverge. Immutable GC allocation is not claimed to be observationally pure.

The current reusable pieces are explicit embeddings, read-back, and checked
interfaces. No universal typeclass or global semantics instance is introduced.

Reproduce with `make check CHECK_TARGETS=+Silmaril.Wasm.Sublanguages.Strict.Thms`.
