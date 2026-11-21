module

public import Silmaril.Formats.Dasl.Arena.Prolly.Slots.Defs
public import Silmaril.Formats.Git.Filesystem.Routed.Defs

@[expose] public section

namespace Silmaril.Formats.Git.Filesystem

open Silmaril.Formats.Dasl.Arena.Prolly (Reader)
open Silmaril.Formats.Dasl.Prolly (ByteKey)
open Silmaril.Semantics.Arena.Mutable (Cell)

variable {Local : Type}

def slotsReader (read : Local → Cell DirBlock) (locate : Cid → Option Local) : Reader Cid ByteKey (Entry Cid) :=
  Reader.ofSlots read locate (fun name => .error (.missing name))

def lookupChildSlots (read : Local → Cell DirBlock) (locate : Cid → Option Local) (store : Store) (fuel : Nat) :
    ChildLookup := checkedChild store ((slotsReader read locate).lookup policy fuel)

def locateSlots (read : Local → Cell DirBlock) (index : Cid → Option Local) (store : Store) (fuel : Nat) :=
  locateWith (lookupChildSlots read index store fuel)

end Silmaril.Formats.Git.Filesystem
