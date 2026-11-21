# Typed arena spaces and tagged storage

Import `Silmaril.Semantics.Arena.Traits.Tagged.Thms`. `Spaces` is a
family of independent ordinary arenas, and `Table` is a unified table keyed
by `Σ kind, Key kind`. The table carries each payload and its optional
name at the row's stored kind. A raw read checks that the stored kind
matches the handle kind before exposing either field. A mismatched kind
is an error, not a hole; a reservation retains an explicit occupied slot.
The handle embeds a kind, not a digest, allocation epoch, or store identity.

`equiv` proves exact round trips between separate spaces and unified tables
whose stored tags agree with their keys. `change_pack` proves exact result
and successor agreement for reserve, insert, replace and remove. It also
shows that a successful edit leaves packed tables in the image of `pack`.
`arena_refines` connects each typed projection to the ordinary mutable
trait and `overwrite_other_kind` is the cross-kind frame. An arbitrary raw
table need not satisfy the invariant; `readSlot` and `change` reject a bad
tag at the touched key. No global validation of a function table is claimed.

The Git fixture shares index zero among file bytes, a parsed Prolly directory
node, and a Git commit with typed root/parent fields. Removing one leaves
the other two readable; a displaced blob row is rejected as the wrong kind
by the directory lane. This checks typed storage, not Git graph validity,
filesystem lookup or CAS synchronization. Git and CAS identifiers reuse
the tagged `Git.Arena.Id`, separate from local slot handles; neither row
packing nor ordinary edits derive or authenticate those identifiers.

For an initial backend use separate typed tables; they implement this
contract without an erased row check on reads. A mixed store can implement
the tagged side if it keeps kind in the key and validates the row tag on
untrusted input. Leaving keys separate does not require separate byte
authorities. A shared authoritative CAS table needs its own name-domain
and atomic admission laws. A later index backend must also account for
lineage/generation and retention; the present bridge does not authorize
reuse of a key referenced by a live edge or handle.

```sh
lake build --wfail +Silmaril.Formats.Git.Arena.TaggedExamples
make check CHECK_TARGETS='+Silmaril.Semantics.Arena.Traits.Tagged.Thms +Silmaril.Formats.Git.Arena.TaggedExamples'
```
