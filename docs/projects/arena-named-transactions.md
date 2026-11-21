# Named reservation and typed publication

`Silmaril.Semantics.Arena.Traits.Publish.{Defs,Thms}` extends the mutable
trait and parsed ingress without changing either API. `Reserve` is an
optional fixed-key capability; `Reserve.model` uses landed `Edit.reserve`
with an explicit name. Plain trait reservation creates anonymous slots, so
named reservation is not derived from it. `reserve_effect` specifies the
entire delta: a hole becomes an occupied name-only slot and the authoritative
byte table is unchanged. A name-only reservation is neither a lock nor a
byte binding; different slots may claim the same name. `keyName` includes
claims, `attachedKeys` excludes placeholders, and an authoritative probe is
separate. An absent block in the authoritative snapshot is not the same as a
local hole, a pending local claim, or unavailable backing.

`Publish.run` is a derived synchronous transaction. `.insert` uses ordinary
fixed-key insertion. `.fulfill` requires an occupied, unresident slot with
the exact claimed name, then stages a plain replacement. Both stage the
ordinary verified attachment on the successor. `run_refines` uses a
`CasArena.Refines` implementation; `run_effect` gives the exact slot frame,
the prior-byte graph union one exact binding, and preservation of valid
attachments. `checked_get` gives exact bytes on a successful backend read;
it does not turn a failed read into absence or guarantee IO availability.
Byte reuse at an existing name with identical bytes is allowed. Reattaching
an already attached exact binding is idempotent in the model; inserting at
an occupied key and re-fulfilling an already resident slot are not.

`Publish.checked` validates the exact source/profile/name/bytes and the
encoding of the submitted typed value before staging writes. A result from
one profile is not automatically accepted by another; revalidation can
succeed if both profiles agree on these inputs. Validation never infers
hash injectivity or equality of typed objects from a digest. `checked_agrees`
gives equality to the trusted transition (up to error injection) on valid
facts. Failed fixed-key allocation, validation, encoding, name selection,
attachment or collision returns the original state via `commit`. The
ordinary nameless parsed path stays unchanged and requires none of this
work. Interning and automatic fresh-key allocation are separate capabilities,
not prerequisites of this transaction. A fresh-key adapter would need a
frame for slots **and** authoritative bytes, not just `Allocate.Fresh`.

The implementation contract is an exclusive pure state transition. A
backend must stage both effects before exposing success; an adapter that
persists the bytes and then returns an error from the slot edit does not
refine this contract. Durable transactions, concurrent visibility, retries
of side effects, and external pinning are not specified here.

```sh
lake build --wfail +Silmaril.Semantics.Arena.Traits.Publish.Examples
make check CHECK_TARGETS='+Silmaril.Semantics.Arena.Traits.Publish.Examples'
```
