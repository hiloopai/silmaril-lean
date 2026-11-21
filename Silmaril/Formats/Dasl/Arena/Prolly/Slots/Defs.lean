module

public import Silmaril.Formats.Dasl.Arena.Prolly.Index.Defs
public import Silmaril.Semantics.Arena.Mutable.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.Arena.Prolly

open Silmaril.Semantics.Arena.Mutable (Cell)
open Silmaril.Semantics.Prolly (Block Policy)
open Silmaril.Formats.Dasl.Prolly (Fault route)

variable {Ref Local Key Payload : Type}

/-- A local hit reads a native parsed block. A hole or placeholder is an
unreadable block, not an absent map entry; it never falls back to another
object. The fallback is used only for references not mapped into the arena. -/
def Reader.ofSlots (read : Local → Cell (Block Ref Key Payload)) (locate : Ref → Option Local)
    (fallback : Reader Ref Key Payload) : Reader Ref Key Payload := fun ref =>
  match locate ref with
  | none => fallback ref
  | some key => match read key with
    | some (some block) => .ok block
    | _ => .error (.missing ref)

/-- Specialize by the existing policy and resident reader. Wire codecs and
naming profiles are not parameters of this native read. -/
def Reader.lookup [LinearOrder Key] (read : Reader Ref Key Payload) (policy : Policy Key)
    (fuel : Nat) (root : Ref) (key : Key) : Except (Fault Ref) (Option Payload) :=
  route read policy.width key fuel none root

variable {Name : Type}

/-- A local index is confined to this arena view; external names delegate to
the existing external-reader lane. No index is ever interpreted as a name. -/
def Reader.ofIndexedSlots (read : Nat → Cell (Block (Handle Name) Key Payload))
    (external : Reader Name Key Payload) : Reader (Handle Name) Key Payload :=
  .ofSlots read (fun | .local index => some index | .external _ => none) (Indexed.empty.read external)

end Silmaril.Formats.Dasl.Arena.Prolly
