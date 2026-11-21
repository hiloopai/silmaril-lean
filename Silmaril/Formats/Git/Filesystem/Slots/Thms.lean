module

public import Silmaril.Formats.Git.Filesystem.Slots.Defs
public import Silmaril.Formats.Git.Filesystem.Routed.Thms
public import Silmaril.Formats.Dasl.Arena.Prolly.Slots.Thms
import Silmaril.Proofs.Formats.Git.Filesystem.Slots

public section

namespace Silmaril.Formats.Git.Filesystem

open Silmaril.Formats.Dasl.Arena.Prolly (Reader)
open Silmaril.Formats.Dasl.Prolly (ByteKey Stored Read)
open Silmaril.Semantics.Arena.Mutable (Cell)

variable {Local : Type} {read : Local → Cell DirBlock} {index : Cid → Option Local}
variable {hash : Hash} {store : Store} {fuel : Nat} {root : Cid} {key : ByteKey} {result : Option (Entry Cid)}

theorem slotsReader_refines
    (resident : ∀ name localKey node, index name = some localKey → read localKey = some (some node) →
      dirReader hash store name = .ok node) :
    (slotsReader read index).Refines id (dirReader hash store) :=
  Reader.ofSlots_refines resident (by intros; contradiction)

/-- Provenance of successful parsed reads is required; mere slot occupancy
or a caller's name-to-key mapping does not certify the block. -/
theorem lookupChildSlots_success (agrees : (slotsReader read index).Refines id (dirReader hash store))
    (accepted : lookupChildSlots read index store fuel root key = .ok result) :
    lookupChildRouted hash store fuel root key = .ok result :=
  Proofs.Formats.Git.Filesystem.Slots.lookup_success agrees accepted

theorem lookupChildSlots_sound {reference : Formats.Dasl.Store Cid}
    {directory : ShallowTree ByteKey Cid} {addressBlock : DirBlock → Cid}
    (stored : Stored dirCodec addressBlock (Semantics.Prolly.build policy directory.ordered) reference)
    (binding : reference.Binding) (reader : Read.Sound (dirRead hash store) reference)
    (agrees : (slotsReader read index).Refines id (dirReader hash store))
    (accepted : lookupChildSlots read index store fuel ((Semantics.Prolly.build policy directory.ordered).rootName addressBlock)
      key = .ok result) : directory.ordered.lookup? key = result :=
  lookupChildRouted_sound stored binding reader (lookupChildSlots_success agrees accepted)

theorem locateSlots_agrees {path : List ByteKey} {expected : Option (Entry Cid)}
    (agrees : (slotsReader read index).Refines id (dirReader hash store))
    (accepted : locateSlots read index store fuel root path = .ok result)
    (routed : locateRouted hash store fuel root path = .ok expected) : result = expected :=
  locateWith_agree (fun {_ _ _ _} first second => Except.ok.inj ((lookupChildSlots_success agrees first).symm.trans second))
    accepted routed

end Silmaril.Formats.Git.Filesystem
