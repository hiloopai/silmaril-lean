# Mutable arena trait contracts

Import `Silmaril.Semantics.Arena.Traits.Thms`. This is a Lean specification
of two Rust-shaped traits, not a Rust implementation or a borrow-checker
formalization. It adds no requirement to existing arena or Prolly APIs.
See the [language handoff](arena-trait-language-handoff.md) for the combined
operation/law index and Rust, Python, and JavaScript contract sketches.

| Rust-side operation | Lean interface | Observation |
| --- | --- | --- |
| `Arena::read(&self, key)` | `ArenaApi`'s `Mutable.Access.read` field | Hole, occupied reservation, or resident object. |
| `Arena::{reserve, insert, replace, remove}(&mut self, …)` | `ArenaApi.change` and the four named projections | Reserve/insert need a hole; replace/remove need occupancy. Replace drops a local name; remove frees the slot. |
| Optional fresh allocation | `Allocate`, `Allocate.Fresh` | Reserve or install at a fresh key, preserving every other read. |
| `CasArena::get(&self, name)` | `CasArena.get` | `ok none` means absent in the authoritative view. Backend error is not absence. |
| `CasArena::put(&mut self, bytes)` | `CasArena.put` | Select a name and admit the exact bytes without allocating a slot. |
| `CasArena::attach(&mut self, key, name)` | `CasArena.attach` | Serialize the resident object, verify the proposed name, admit its bytes, then attach. |
| Name and reverse lookup | `keyName`, `attachedKeys`, `claimKeys` | All resident aliases by default. Reservations can make claims but do not witness bindings. |

`CasArena.toArena` is an implementation of the ordinary trait on the same
state. `CasArena.Refines.plain_slots` proves its ordinary projection refines the
same slot model. `ArenaApi.raw_refines`, `ArenaApi.dense_refines`, and
`CasArena.model_refines` cover the unbounded slot model, the fixed-size array,
and the authoritative CAS snapshot. Bounds errors on array edits are backend
limitations, not the semantic fault for editing a vacant slot. `Allocate.append`
is checked for the growing array, with no implicit hole reuse.

## Transactions and identity

Each `Step` is a state-passing operation returning a successor only on success.
`Step.Refines` checks the exact model return and successor, or the exact model
semantic failure. A backend failure may preempt the reference operation, so
the relation is a safety claim, not a progress claim. `Step.Refines.bind` composes
these contracts, and `Step.rollback` preserves the original state when a stage
fails. A backend must stage its writes or use a real transaction to refine this
model. Rust's `Result::and_then` alone does not undo side effects.

`putBytes.graph_eq` gives the exact union with a singleton byte binding;
`putBytes.collision_iff` identifies an unequal authoritative byte binding at the
selected name. Repeating the same bytes is allowed. Successful reads of just
published bytes are checked by `CasArena.Refines.put_readback`; it does not
assert the backend cannot fail the read. The oracle is an abstract partial
function `ByteArray → Option Name`. Neither it nor the serializer is assumed
injective; an unavailable oracle choice does not admit a binding.

Plain edits leave the byte table unchanged. `replaceAndAttach` is the checked
stable-key revalidation transaction: either a fresh local attachment is justified
and admitted, preserving all previous byte bindings, or neither edit is
committed. `Cas.Intern` remains an optional separate capability for shared
replacement that may return another key. Its index may be single-valued only
under its explicit exactness invariant; ordinary CAS attachment allows aliases.
An object equality claim additionally needs recovery from serialization.

## Backend boundary

A first backend can use `Vec<Option<Slot>>` and an authoritative byte table
under the same write authority. Check traces of result, affected and unaffected
reads, name claims, and bytes; inject allocation/encoding/read/admission failure.
Keep an old alias live while replacing another. Benchmark allocations, encoder
calls and byte comparisons separately; these are suggested counters, not proven
cost bounds or measured results.

The contract does not model outstanding Rust borrows, raw pointers, async
fetch, durability, persistence, or GC. The slot reader observes an already
accessible state; a cache-only CAS read cannot claim authoritative absence.
Destructive CAS deletion and recycling of public name bindings are not provided.
SQLite, cache and layered blob-key authorities must justify their observational
projection and atomic commit before substituting for the reference snapshot.
Tree codecs and Prolly root/publish policies remain independent.

For the Rust correspondence, see the pinned [borrow operator reference][borrow],
[`Vec::try_reserve`][reserve], [`Option::take`][take], and [`Result::and_then`][result].

[borrow]: https://github.com/rust-lang/reference/blob/86635e30bf861a038dc197d7e16fd09e7e514e7a/src/expressions/operator-expr.md#L61
[reserve]: https://github.com/rust-lang/rust/blob/48a229ceaefd4985c50990b14116b6d856af0985/library/alloc/src/vec/mod.rs#L1535
[take]: https://github.com/rust-lang/rust/blob/48a229ceaefd4985c50990b14116b6d856af0985/library/core/src/option.rs#L1899
[result]: https://github.com/rust-lang/rust/blob/48a229ceaefd4985c50990b14116b6d856af0985/library/core/src/result.rs#L1486

```sh
lake build --wfail +Silmaril.Semantics.Arena.Traits.Examples
make check CHECK_TARGETS='+Silmaril.Semantics.Arena.Traits.Thms +Silmaril.Semantics.Arena.Traits.Examples'
```
