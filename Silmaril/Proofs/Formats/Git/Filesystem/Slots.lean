module

public import Silmaril.Formats.Git.Filesystem.Slots.Defs
public import Silmaril.Formats.Git.Filesystem.Routed.Thms
public import Silmaril.Formats.Dasl.Arena.Prolly.Slots.Thms

public section

namespace Silmaril.Proofs.Formats.Git.Filesystem.Slots

open Silmaril.Formats.Git
open Silmaril.Formats.Git.Filesystem
open Silmaril.Formats.Dasl.Arena.Prolly (Reader route_refines)
open Silmaril.Formats.Dasl.Prolly (ByteKey route)
open Silmaril.Semantics.Arena.Mutable (Cell)

variable {Local : Type} {read : Local → Cell DirBlock} {index : Cid → Option Local}
variable {hash : Hash} {store : Store} {fuel : Nat} {root : Cid} {key : ByteKey} {result : Option (Entry Cid)}

theorem lookup_success (agrees : (slotsReader read index).Refines id (dirReader hash store))
    (accepted : lookupChildSlots read index store fuel root key = .ok result) :
    lookupChildRouted hash store fuel root key = .ok result := by
  have hit := checkedChild_ok accepted
  change route (slotsReader read index) policy.width key fuel none root = _ at hit
  have equiv : route (dirReader hash store) policy.width key fuel none root = .ok result :=
    route_refines agrees policy.width fuel key hit
  unfold lookupChildSlots at accepted
  unfold lookupChildRouted
  simpa only [checkedChild, Reader.lookup, hit, equiv] using accepted

end Silmaril.Proofs.Formats.Git.Filesystem.Slots
