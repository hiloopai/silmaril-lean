# Routed queries over parsed arena slots

`Silmaril.Formats.Dasl.Arena.Prolly.Slots.Thms` connects ordinary typed slot
reads to the landed single-layer `Block` and routed query. `Reader.ofSlots`
takes the internal read and localization functions; `Reader.lookup` takes the
existing Prolly policy. This is generic over ref, slot key, ordered map key
and payload, so plain and ordered link keys use the same code. It neither
serializes residents nor computes names. A located vacant or reserved slot
fails as an unreadable block; it does not imply the key is absent. A fallback
is allowed only for an unmapped reference, with a separate proof premise for
any successful fallback result.

`Reader.ofSlots_refines` needs each locally returned block to agree with
the chosen reference reader at its external reference. It does not certify
a caller-chosen localization table or an arbitrary mutation of its rows.
The existing `route_refines` then transports successful results, including
`ok none`, without assuming that siblings are readable. Equality to the
semantic map also needs the existing global rooted representation invariant.

`Silmaril.Formats.Git.Filesystem.Slots.Thms` reuses the existing directory
block, component/entry checks and `locateWith` path traversal. On an agreeing
resident view, a successful child lookup gives the same result on the verified
named-byte route. `lookupChildSlots_sound` obtains map lookup correctness in
any binding reference satisfying the same stored-directory and read premises.
`locateSlots_agrees` compares successful paths; fault equality is not assumed.
The fixture reads a Git commit's tree CID, then follows a parsed directory
branch through tagged storage. Found, successful miss, deferred child and
insufficient fuel are distinct. The fixture is not a serialized Git wire
round trip or proof of a new filesystem writer.

For local-index Prolly, `Reader.ofIndexedSlots_eq` gives reader equality
against an adequately projected indexed snapshot. `Reader.lookup_marked`
preserves routed results, including faults, at every root or node in the
landed marking reachability relation. `Reader.reclaimed_unreadable` checks
that a discarded in-bounds index cannot silently read a different value in
that swept projection. Both results keep the external reader fixed and
require the stated projection of the swept array. They do not authorize
index reuse, prove cross-lineage safety, or sweep authoritative CAS data.

```sh
lake build --wfail +Silmaril.Formats.Git.Filesystem.Slots.Examples
make check CHECK_TARGETS='+Silmaril.Formats.Dasl.Arena.Prolly.Slots.Thms +Silmaril.Formats.Git.Filesystem.Slots.Examples'
```
