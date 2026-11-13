module

public import Silmaril.Wasm.Component.Async.Cabi.Defs

@[expose] public section

/-!
# Record updates of ends, by name

Named forms of the record updates `End.copy` (`Silmaril.Wasm.Component.Async.Cabi.Store.copyEnd`)
makes, so that the laws of `Silmaril.Wasm.Component.Async.CabiCopy.Thms` can state the ends a copy
leaves behind.
-/

namespace Silmaril.Wasm.Component.Async.Cabi

/-- The end with another state. -/
def End.withState (x : End) (s : EndState) : End := { x with state := s }

/-- The end with the pending event of `notify(p)`. -/
def End.withPending (x : End) (p : Nat) : End := { x with pending := some p }

/-- The end with another parked buffer. -/
def End.withBuffer (x : End) (b : Option Nat) : End := { x with buffer := b }

/-- The buffer that a copy reads gives as many values as asked: a guest buffer, or a host
buffer holding values for its whole length (every `HostReadableBuffer`). -/
def Buf.ReadOk {α : Type} (b : Buf α) : Prop := b.inst.isSome ∨ b.length ≤ b.src.length

end Silmaril.Wasm.Component.Async.Cabi
