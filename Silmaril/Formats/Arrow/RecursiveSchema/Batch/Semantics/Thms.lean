module

public import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Semantics.Defs
import Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Batch.Semantics.Wire
import Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Batch.Semantics.Visibility

@[expose] public section

namespace Silmaril.Formats.Arrow.RecursiveSchema.Batch.Semantics

/-- The physical tree is aligned with the original schema and layouts, each
region comes from its absolute carrier range, and each node binds its own
bitmap, signed words or List offsets and the visibility of its descendants. -/
theorem decode_wire {limits : Batch.Limits} {schema : Schema} {input : KBytes} {offset : Nat}
    {frame : Frame limits schema input offset} {observed : Observation}
    (read : decode frame = .ok observed) : ObservationWire frame observed :=
  Proofs.Formats.Arrow.RecursiveSchema.Batch.Semantics.decode_wire read

/-- The native entry point certifies the first checked batch in its original carrier. -/
theorem readFirst_wire {limits : Batch.Limits} {input : KBytes} {first : First limits input}
    {observed : Observation} (read : readFirst limits input = .ok (first, observed)) :
    ObservationWire first.batch observed :=
  Proofs.Formats.Arrow.RecursiveSchema.Batch.Semantics.readFirst_wire read

theorem readFirst_layout_error {limits : Batch.Limits} {input : KBytes} {cause : Batch.Error}
    (read : Batch.readFirst limits input = .error cause) :
    readFirst limits input = .error (.layout cause) := by
  simp [readFirst, read, Except.mapError, bind, Except.bind]

/-- The declaration requires a valid bit on each visible slot of a
nonnullable field. Hidden slots still have their own checked physical bits. -/
theorem PresenceWire.required_at {body : KBytes} {node : FieldNode} {buffer : Buffer}
    {visible : Array Bool} {presence : Presence} {index : Nat}
    (wire : PresenceWire body node buffer false visible presence)
    (slot : index < node.length) (reached : presence.visible[index]? = some true) :
    presence.valid[index]? = some true :=
  Proofs.Formats.Arrow.RecursiveSchema.Batch.Semantics.required_at wire slot reached

/-- Each observed List window has its original adjacent signed offset words. -/
theorem PayloadWire.list_window {body : KBytes} {length final : Nat} {buffer : Buffer}
    {offsets : Array Nat} (observed : PayloadWire body length .list (some buffer) (.list offsets))
    (checked : OffsetPrefix (Body.sliceBuffer body buffer) length final)
    {parent : Nat} (bound : parent < length) :
    ∃ lo hi, offsets[parent]? = some lo ∧ offsets[parent + 1]? = some hi ∧
      (Body.sliceBuffer body buffer).readLE (4 * parent) 4 = some lo ∧
      (Body.sliceBuffer body buffer).readLE (4 * (parent + 1)) 4 = some hi ∧ lo ≤ hi ∧ hi ≤ final :=
  Proofs.Formats.Arrow.RecursiveSchema.Batch.Semantics.list_window observed checked bound

/-- Every slot in a List window inherits the presence of its parent slot. -/
theorem listVisibility_window {present : Array Bool} {offsets : Array Nat}
    (initial : offsets[0]?.getD 0 = 0)
    (ordered : ∀ i < present.size, offsets[i]?.getD 0 ≤ offsets[i + 1]?.getD 0)
    {parent child : Nat} (bound : parent < present.size)
    (lower : offsets[parent]?.getD 0 ≤ child) (upper : child < offsets[parent + 1]?.getD 0) :
    (listVisibility present offsets)[child]? = present[parent]? :=
  Proofs.Formats.Arrow.RecursiveSchema.Batch.Semantics.window_visibility initial ordered bound lower upper

/-- The observed endpoint is the original checked child length, including
when the parent array is empty. -/
theorem PayloadWire.list_endpoints {body : KBytes} {length final : Nat} {buffer : Buffer}
    {offsets : Array Nat} (observed : PayloadWire body length .list (some buffer) (.list offsets))
    (checked : OffsetPrefix (Body.sliceBuffer body buffer) length final) :
    offsets[0]? = some 0 ∧ offsets[length]? = some final :=
  Proofs.Formats.Arrow.RecursiveSchema.Batch.Semantics.list_endpoints observed checked

/-- The visibility traversal visits exactly the physical child length
already bound by the layout. -/
theorem PayloadWire.list_visibility_size {body : KBytes} {length final : Nat} {buffer : Buffer}
    {offsets : Array Nat} {present : Array Bool} (size : present.size = length)
    (observed : PayloadWire body length .list (some buffer) (.list offsets))
    (checked : OffsetPrefix (Body.sliceBuffer body buffer) length final) :
    (listVisibility present offsets).size = final :=
  Proofs.Formats.Arrow.RecursiveSchema.Batch.Semantics.list_visibility_size size observed checked

end Silmaril.Formats.Arrow.RecursiveSchema.Batch.Semantics
