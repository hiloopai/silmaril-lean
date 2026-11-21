# Synchronous Arena and CasArena language handoff

This is a contract for a local implementation, not production bindings.
The checked reference uses pure, exclusive state passing. On failure there
is no successor to commit. Rust borrow checking, physical IO rollback,
durability, concurrent mutable snapshots, and slot reuse are not proved.

## Operation and law index

The `Traits` modules below are under `Silmaril.Semantics.Arena`. `Step.Refines`
compares exact successful observations and semantic failures; a backend failure
can preempt either. `Step.rollback` is a state law, not a progress or IO law.

| Operation | Checked boundary and law |
| --- | --- |
| Ordinary read, reserve, insert, replace, remove | `Traits.ArenaApi`: hole, occupied reservation, or resident. `ArenaApi.raw_refines`, `ArenaApi.dense_refines`, and `CasArena.Refines.plain_slots` relate sparse/dense/shared-state views. Reserve and insert require a hole, replace and remove require occupancy. Plain replacement drops the local name; all plain edits leave authoritative bytes unchanged (`CasArena.Refines.plain_valid`). |
| Optional fresh allocation | `Traits.Allocate.Fresh` (`append_fresh`): a fresh slot and other reads unchanged; it is not a frame for authoritative bytes or a fresh-key publication theorem. |
| `get`, probe, raw `put` | `Traits.CasArena`: `get` returns exact snapshot bytes or authoritative absence on a successful read. `Parsed.CasArena.probe_agrees` keeps unavailable separate. `putBytes.graph_eq`, `putBytes.collision_iff` and `CasArena.Refines.put_readback`: select a name for exact bytes, admit without overwriting, return those bytes on successful readback. |
| Key name, aliases, verified attach, stable-key replacement | `keyName` and `CasArena.claimKeys` include name-only claims. `attachedKeys` contains every co-present resident key; no uniqueness premise. `CasArena.Refines.attach_effect` specifies exact attachment and `Refines.replace_valid` preserves prior binding validity through `replaceAndAttach`. No resident edit rebinds an old name to different bytes. Optional interning changes the policy, not these default alias laws. |
| Named reservation, insert-and-publish, fulfill | `Traits.Publish.reserve_effect`: adds only a local claim. `run_refines` and `run_effect`: atomic, explicit-key typed commit, exact slot frame and byte graph union. Fulfill distinguishes no reservation, not reserved and wrong claim. `rollback` applies to failed slot/backend operations, encoding, naming/validation, and collision. `reattach_idempotent` concerns exact existing model attachments, not a second insert or fulfill. |
| Optional checked ingress | `Traits.Parsed.put_agrees`, `attach_agrees`, and `Traits.Publish.checked_agrees`: on a validated exact fact, observe the trusted operation with injected errors. `checked_rejects` rolls back invalid facts; `checked_get` gives exact bytes if a post-commit authoritative read succeeds. A validated upstream fact does not authorize overwriting the target's prior binding. |
| Positive byte cache and eviction | `Traits.Cache.withCache_refines` keeps the same authority contract under binding-preserving transitions. `Layer.evict_get_exact` preserves read-through results when backing is readable; a failed backing can lose a hot hit. Cold cache probes never claim absence. |
| Parsed map reads, scoped roots and collection | `Dasl.Arena.Prolly.Reader.ofSlots_refines` needs local/fallback read agreement. `Surface.resolve_local_iff`, `register_spec`, `unregister_spec`, `lookup_registered`, `stale_persists`, and `layer_collect_spec` cover owner/kind checks, changed root registration, fixed-reader preservation and no authority mutation. The rooted representation invariant is separate from query preservation. |

## Rust trait sketch

Associated error types below stand for the classified Lean enums in the index,
not a flattened string error. Preserve semantic versus backend failures;
gate/attachment rejections are not absence. `is_attached_key` observes membership
in the entire reverse set; a finite backend may also enumerate all aliases.

```rust
pub enum Cell<'arena, Obj> { Hole, Reserved, Resident(&'arena Obj) }
pub enum Failure<Semantic, Backend> { Semantic(Semantic), Backend(Backend) }
pub enum Probe<Backend> { Present(Vec<u8>), Absent, Unavailable(Backend) }

pub trait Arena<Key, Obj> {
    type Backend;
    type SlotFault;
    fn read(&self, key: &Key) -> Cell<'_, Obj>;
    fn reserve(&mut self, key: Key) -> Result<(), Failure<Self::SlotFault, Self::Backend>>;
    fn insert(&mut self, key: Key, obj: Obj) -> Result<(), Failure<Self::SlotFault, Self::Backend>>;
    fn replace(&mut self, key: &Key, obj: Obj) -> Result<(), Failure<Self::SlotFault, Self::Backend>>;
    fn remove(&mut self, key: &Key) -> Result<(), Failure<Self::SlotFault, Self::Backend>>;
}

pub trait CasProfile<Name, Obj> {
    fn encode(&self, obj: &Obj) -> Option<Vec<u8>>;
    fn select_name(&self, bytes: &[u8]) -> Option<Name>;
}

pub trait MutableCas<Name> {
    type Backend;
    type PutFault;
    fn get(&self, name: &Name) -> Result<Option<Vec<u8>>, Self::Backend>;
    fn probe(&self, name: &Name) -> Probe<Self::Backend> {
        match self.get(name) {
            Ok(Some(bytes)) => Probe::Present(bytes),
            Ok(None) => Probe::Absent,
            Err(reason) => Probe::Unavailable(reason),
        }
    }
    fn put(&mut self, bytes: &[u8]) -> Result<Name, Failure<Self::PutFault, Self::Backend>>;
}

pub trait CasArena<Key, Obj, Name>:
    Arena<Key, Obj> + MutableCas<Name, Backend = <Self as Arena<Key, Obj>>::Backend>
{
    type AttachError;
    type ReplaceAndAttachError;
    type PublishError;
    fn profile(&self) -> &dyn CasProfile<Name, Obj>;
    fn key_name(&self, key: &Key) -> Option<&Name>;
    fn is_attached_key(&self, key: &Key, name: &Name) -> bool;
    fn attach(&mut self, key: &Key, name: &Name) -> Result<(), Self::AttachError>;
    fn replace_and_attach(&mut self, key: &Key, obj: Obj, name: &Name)
        -> Result<(), Self::ReplaceAndAttachError>;
    fn insert_and_publish(&mut self, key: Key, obj: Obj, name: &Name)
        -> Result<(), Self::PublishError>;
    fn fulfill_named(&mut self, key: &Key, obj: Obj, claim: &Name)
        -> Result<(), Self::PublishError>;
}

pub trait Allocate<Key, Obj>: Arena<Key, Obj> {
    fn allocate(&mut self, obj: Option<Obj>) -> Result<Key, Failure<Self::SlotFault, Self::Backend>>;
}

pub trait NamedReserve<Key, Obj, Name>: CasArena<Key, Obj, Name> {
    type ReserveError;
    fn reserve_named(&mut self, key: Key, claim: Name) -> Result<(), Self::ReserveError>;
}
```

These are signatures, not default `&mut` implementations of transactions:
calling a mutating method then propagating a later `Err` does not undo the
first mutation. Stage both effects together. Do not export a mutable alias to
an attached resident. Borrowed results end before a conflicting edit; an owned
copy may outlive the borrow but is not live authority. Consumed arguments are
not returned on error by this sketch. Add the checked ingress as a separate
wrapper, not a requirement for plain parsed inserts and reads.

## Python and JavaScript examples

Use synchronous calls, opaque tokens and owned values or copies, not escaping
`&mut` emulation. Python uses classified edit exceptions; JavaScript uses
classified tagged results. Successful map absence is returned normally, not
for an unreadable child or exhausted fuel.

```python
arena.reserve_named(key, name)              # None on success; classified exception otherwise
assert arena.read_owned(key).tag == "reserved"
arena.fulfill_named(key, value, name)        # failed edit leaves the original state
probe = arena.probe(name)                   # Present(bytes) | Absent | Unavailable(error)
roots.register(root)                       # set-like; no second pin for a duplicate
result = roots.lookup(root, query, fuel=8)   # Found | Absent; faults raise
```

```javascript
const reserve = arena.reserveNamed(key, name); // {tag:'ok'} | {tag:'error', error}
if (reserve.tag === 'ok') {
  const cell = arena.readOwned(key);             // hole | reserved | resident
  const commit = arena.fulfillNamed(key, value, name);
}
const probe = arena.probe(name);                // present | absent | unavailable
const result = roots.lookup(root, query, {fuel: 8}); // found | absent | error
```

Never collapse hole, reservation, authoritative absence, a failed backing
read, or a rejected token into a single `None`/`null`. Return immutable Python
`bytes` and caller-owned JS `Uint8Array` snapshots. Keep owner/kind checks at
runtime even when the host has typed or branded handles. If numeric IDs cross
JS, use `bigint` or a lossless encoding, not `Number`.

## Indexing, trust, and storage policies

- **Separate or tagged.** Start with separate typed `Vec<Option<Slot>>` or
  sparse tables and opaque owner-scoped handles. `Traits.Tagged.equiv`,
  `change_pack` and `arena_refines` justify a coherent tagged table if shared
  storage is useful. A wrong tag is not a hole; storage kind does not certify
  owner identity or act as a CAS name. See [typed spaces](arena-tagged-spaces.md).
- **Authority and Fact.** The checked Lean code uses `Parsed.Fact ... : Prop`,
  not a general CAS `Fact` object or a certificate synthesized from a digest.
  The repo's unrelated `Wasm.Resource.Client.Fact` tracks static handle facts,
  not evidence for CAS admission.
  `Fact` pins the actual source observation, profile, name and exact bytes;
  `AttachmentFact` and `Publish.ValueFact` additionally check encoding of the
  resident or submitted typed value. The trusted default means the backend's
  observations refine one authoritative `Cas.State` and its ready states
  satisfy `Profile.Valid`. It does not give arbitrary IO global trust. An
  observed source fact needs `Source.Agrees` to describe a reference store;
  the receiving profile revalidates instead of importing a different
  profile's witness. A gate failure, including unavailable source, does not
  establish absence in the receiving store. Neither serializer nor name
  selection is assumed injective. Nameless native Prolly residency calls neither.
- **Surface, backing and GC.** Internal handles are local indices or external
  names; the external lane yields no inferred local edges. Register all live
  roots (duplicate registration adds no extra pin). The checked collector
  retains the reachable local closure in a fixed indexed lineage; preservation
  of whole results needs the same backing reader or an equivalent snapshot
  observation. `Surface.Layer` leaves authority unchanged; registration is
  not an external pin or an availability guarantee. Unregistered local
  handles can become stale. See [rooted collection](arena-prolly-rooted-surface.md).
- **No reuse or generations.** The checked default never refills retired
  indices and requires a fresh owner for a new lifetime. A generational
  alternative must check owner/kind/index/generation on every relevant
  edge, root, and token, preserve live references, and rule out wrapping
  or revival. No reuse policy is implemented here.
- **Eviction or deletion.** Cache eviction drops positive residency only;
  surface collection drops unreachable local slots only. Neither purges
  authoritative bytes. Authoritative deletion needs a separate retention and
  history contract, as would external pin delivery or durable backing.

## Parameterized internal Prolly map

Use `Semantics.Prolly.Block Ref Key Payload` with `LinearOrder Key` and
`Semantics.Prolly.Policy Key` (width, a minimum-width proof and a level/key
bucketer). `Reader.ofSlots` localizes a reference to a typed slot or delegates
an unmapped name; a mapped hole or placeholder fails without falling back.
`Reader.lookup` is the routed seam, parameterized by the policy, root, key and
fuel. Keep `BlockCodec Name Key Payload`, wire encoding, abstract byte-to-name
selection and store validity at the named boundary. Plain keys and tagged
object/blob link keys use the same map machinery, with name identity in the
appropriate tag, not equality of resolved contents.

- **Filesystem:** `Git.Filesystem.DirBlock` specializes to byte-key directory
  components and mode/CID entries, with separate blob reads. The
  [parsed slot fixture](arena-parsed-consumers.md) follows a resident Git
  commit's tree CID through these directory blocks; it does not implement
  filesystem edits, symlink traversal, or Git wire conversion.
- **Arbitrary Git objects:** `Git.Object Key Ref Meta kind` includes blob,
  tree, commit and unresolved references. Keep those kind-indexed carriers
  distinct from the directory specialization. `Git.Arena.Id` distinguishes
  native Git OID algorithms and raw/object CAS lanes; it is not an arena
  lifetime token or evidence of a binding.

Start with local parsed slots, a separate authoritative byte table, explicit
keys and the no-reuse policy. Test ordinary edits, checked publication and
collision rollback before adding optional cache/collection. Exercise the named
Git tree consumer before generalizing the storage backend.
