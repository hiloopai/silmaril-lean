# Owner-scoped parsed Prolly roots and local collection

`Silmaril.Formats.Dasl.Arena.Prolly.Surface.{Defs,Thms}` gives a mounted,
typed surface over an immutable indexed lineage. A public local token has
an owner, kind and numeric index. Resolution checks owner first, then kind,
then distinguishes never allocated, stale and resident. A backing name is a
different target constructor. An internal `Handle.local` belongs to the
mount's pinned lineage, while `.external` delegates by name and has no
local index. The external reader only returns blocks with external names;
the bridge does not guess local pointers from unavailable backing data.

Registration declares roots to preserve, not memory ownership. Duplicate
registration does not acquire a second pin; unregister removes all
occurrences. `register_spec` and `unregister_spec` preserve the checked
view invariant and leave slots unchanged. Local registration requires a
resident, correctly scoped token; external registration does not imply
availability or byte verification. Callers must declare every root whose
lifetime should survive collection. Holding an unregistered token does not
pin anything (although it can survive as a descendant of a registered root).

`collect` reuses the finite marker and checked sweep over the pinned index
snapshot. It rejects an unchecked closure or any attempt to grow the
retained index set. On a valid view with resident backward local edges in
the rooted closure the operation succeeds (`collect_exists`). For every
registered root, `lookup_registered` preserves the entire result with the
same backing reader, including a successful miss and route faults.
`Layer.collect` leaves its separate authority field exactly unchanged;
`layer_lookup_registered` derives reader equality when reads are a fixed
function of that authority. IO may change its availability despite an
unchanged authority handle; compare reads under one snapshot or separately
establish adequate backing observations. Collection never deletes,
revalidates or rewrites authoritative bytes. Byte-cache eviction is a
separate policy from this structural local sweep.

On the same mount a reclaimed index does not move or refill;
`collect_stale` and `stale_persists` classify rejected token reads after
collection. Registers and unregisters never rewrite a slot. This slice
does not grow or remount a surface in place: an adapter must issue a fresh
owner on a new lifetime and keep previously issued token fields opaque.
The proofs compare checked identities, not adversarial identities or Rust
references. Reuse would need an optional distinct policy: compare
`(owner, kind, index, generation)` on every public and local edge/root
read, preserve live edge and pin targets, and prove generation monotonicity
with no wraparound or revival. No such reuse is implemented. The pinned
basis is explicit; no physical memory saving, incremental marking, pin
delivery, concurrent read lease, or durable transaction is claimed.

## Internal map and consumers

The map order is `LinearOrder Key`; chunking uses `Semantics.Prolly.Policy`
(`width`, minimum width proof, level/key bucketer). Native queries use
`Block Ref Key Payload` and `Reader.lookup` and do not need serialization
or naming. The separate by-name boundary can use `BlockCodec Name Key
Payload`, a wire profile, and selected CAS names. Ordinary keys and
`Dasl.Prolly.LinkKey.Mixed` instantiate the same block/reader API; mixed
link equality is tagged name identity, not resolved payload equality.
Local collection preserves results, not map well-formedness; the existing
rooted, binding-store proofs establish semantics under their stronger
hypotheses.

The Git filesystem adapter's `DirBlock` is one specialization (byte-key
directory components, entry mode and CID, with separate blob reads).
`Git.Object` is a different kind-indexed carrier for arbitrary Git
blob/tree/commit objects and unresolved refs, while `Git.Arena.Id` separates
native Git OID algorithms from raw/object CAS lanes. A filesystem map is
neither a general Git payload nor a Git wire codec. This slice does not
localize all arbitrary Git objects or implement a filesystem writer.

```sh
lake build --wfail +Silmaril.Formats.Dasl.Arena.Prolly.Surface.Examples
make check CHECK_TARGETS='+Silmaril.Formats.Dasl.Arena.Prolly.Surface.Examples'
```
