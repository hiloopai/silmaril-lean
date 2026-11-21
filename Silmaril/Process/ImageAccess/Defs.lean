module

public import Silmaril.Process.ImageAccess.Contract.Defs
public import Silmaril.Process.Memory

/-!
# Read requests at the instruction / image / process boundary

An instruction issues a request for a whole byte span, without inspecting mappings or
ownership. An image can serve it from mapped memory, hide it under a selected policy, or
delegate it to a process-provided service. The service sees the request, not the processor
state. This is a sequential, read-only snapshot interface, not a loader, scheduler, or
memory model for interference. Image routing (including ownership metadata) is not part
of the processor state or the byte payload.
-/

@[expose] public section

namespace Silmaril.Process.ImageAccess

inductive Outside where
  | unavailable | ub
  deriving DecidableEq, Repr

inductive Route (Service : Type) where
  | mapped
  | hidden (outside : Outside)
  | delegate (service : Service)

/-- Visibility is policy metadata; mapped bytes retain their concrete access permissions. -/
structure Image (Service : Type) where
  memory : Memory
  route : Read → Route Service

def Image.full (memory : Memory) : Image Empty := ⟨memory, fun _ => .mapped⟩

def Image.owned (memory : Memory) (owns : Read → Bool) (outside : Outside) : Image Empty :=
  ⟨memory, fun request => if owns request then .mapped else .hidden outside⟩

/-- The process supplies service answers for its current snapshot. A delegated answer must
cover exactly the requested byte count in range. This check establishes shape only, not
agreement with another image or permission to read in another process. -/
def Image.reader {Service : Type} (image : Image Service) (service : Service → Reader) :
    Reader := fun request =>
  match image.route request with
  | .mapped =>
    let access := match request.kind with | .data => Access.read | .fetch => Access.execute
    match image.memory.readWith access request.address request.size with
    | some bytes => .ok bytes
    | none => .error .fault
  | .hidden .unavailable => .error .unavailable
  | .hidden .ub => .error .ub
  | .delegate tag =>
    match service tag request with
    | .error stop => .error stop
    | .ok bytes =>
      if request.address < addressLimit ∧ request.address + request.size ≤ addressLimit ∧
          bytes.length = request.size then
        .ok bytes
      else .error .unavailable

/-- Interpret an image that has no process services. -/
def Image.localReader (image : Image Empty) : Reader := image.reader (fun tag => nomatch tag)

end Silmaril.Process.ImageAccess
