module

public import Silmaril.Containers.Adapter.Defs

/-! # Experimental checked event views

A codec embeds small events and checks the reverse direction. Unsupported events cause UB;
they are not silently filtered out. Finite execution is executable. `Projects` also describes
infinite runs without pretending that infinitely many hidden events imply progress. -/

@[expose] public section
namespace Silmaril.Containers

structure EventCodec (Small Big : Type) where
  embed : Small → Big
  project : Big → Option Small
  roundtrip : ∀ e, project (embed e) = some e
  sound : ∀ e s, project e = some s → embed s = e

namespace EventCodec
variable {S B : Type}

/-- Keep the accepted prefix when the first unsupported event is encountered. -/
def trace (v : EventCodec S B) : List B → Except (List S) (List S)
  | [] => .ok []
  | e :: es => match v.project e with
    | none => .error []
    | some s => match v.trace es with
      | .ok ss => .ok (s :: ss)
      | .error pre => .error (s :: pre)

/-- A finite run; source UB is retained, and unsupported events introduce UB. -/
def finite (v : EventCodec S B) (t : List B) (stop : Stop) : Beh S :=
  match v.trace t with
  | .ok ss => .done ss stop
  | .error pre => .done pre (.undefined .unmodeled)

/-- Full-run projection: either every event has a small representation, with the same stop,
blocking/divergence/infinite-run kind, or the first unsupported event ends the projected run
in UB. `pre` consists entirely of represented events. -/
def Projects (v : EventCodec S B) (b : Beh B) (s : Beh S) : Prop :=
  b = s.map v.embed ∨ ∃ pre e, b.Prefix (pre.map v.embed ++ [e]) ∧
    v.project e = none ∧ s = .done pre (.undefined .unmodeled)

/-- Semantic confinement: the entire run has a representation, including its outcome. -/
def Confined (v : EventCodec S B) (b : Beh B) : Prop := ∃ s : Beh S, b = s.map v.embed

/-- Read a big model at the small alphabet. This is not a claim that an independently given
small machine simulates the big one; such a claim still needs a run simulation. -/
def restrict (v : EventCodec S B) (M : Model B) : Model S := fun s => M (s.map v.embed)

def expand (v : EventCodec S B) (M : Model S) : Model B :=
  fun b => ∃ s, M s ∧ b = s.map v.embed

end EventCodec

/-- A fixed profile removes unsupported constructors by a checked subtype. These aliases
retain the exact current capability contract (which checks the primary socket). They do not
add POSIX address-family or descriptor-consistency promises. -/
abbrev ProfileEvent (P : Profile) := {e : Ev // P e.cap = true}
abbrev VsockEvent := ProfileEvent Profile.vsockOnly
abbrev TcpEvent := ProfileEvent Profile.tcpOnly
abbrev UdpEvent := ProfileEvent Profile.udpOnly
abbrev NetworkEvent := ProfileEvent Profile.networkOnly

def profileCodec (P : Profile) : EventCodec (ProfileEvent P) Ev where
  embed := Subtype.val
  project e := if h : P e.cap = true then some ⟨e, h⟩ else none
  roundtrip e := by simp [e.property]
  sound e s h := by split at h <;> cases h; rfl

/-- A genuinely separate, small alphabet for stream-only applications. -/
inductive StdioEvent where
  | input (bytes : List UInt8)
  | output (bytes : List UInt8)
  | error (bytes : List UInt8)
  deriving DecidableEq, Repr

def stdioCodec : EventCodec StdioEvent Ev where
  embed
    | .input bs => .stdin bs
    | .output bs => .stdout bs
    | .error bs => .stderr bs
  project
    | .stdin bs => some (.input bs)
    | .stdout bs => some (.output bs)
    | .stderr bs => some (.error bs)
    | _ => none
  roundtrip e := by cases e <;> rfl
  sound e s h := by cases e <;> cases h <;> rfl

end Silmaril.Containers
