module

public import Silmaril.Semantics.Arena.Traits.Parsed.Defs

@[expose] public section

namespace Silmaril.Semantics.Arena.Traits.Publish

variable {Rep Key Name Obj Error : Type}

/-- An optional capability: ordinary reserve can only create anonymous slots.
A named reservation creates a local claim, not a binding or a global lock. -/
abbrev Reserve (Rep Key Name Error : Type) := Key → Name → Step Rep SlotFault Error Unit

def reserveReference [DecidableEq Key] (key : Key) (name : Name) :
    Mutable.Mutation (Cas.State Key Name Obj) SlotFault Unit := fun state =>
  (state.slots.step key (.reserve (some name))).map fun slots => ((), {state with slots})

def Reserve.model [DecidableEq Key] : Reserve (Cas.State Key Name Obj) Key Name Error :=
  fun key name => Step.ofModel (reserveReference key name)

inductive Mode where
  | insert
  | fulfill
  deriving DecidableEq, Repr

inductive Fault (Name : Type) where
  | slot (reason : SlotFault)
  | noReservation
  | notReserved
  | wrongClaim (claimed : Name)
  | attachment (reason : Cas.Fault Name)
  deriving DecidableEq, Repr

def Mode.prepare [DecidableEq Name] (mode : Mode) (cell : Mutable.Cell Obj) (claim : Option Name)
    (obj : Obj) (name : Name) : Except (Fault Name) (Mutable.Change Obj) :=
  match mode with
  | .insert => .ok (.insert obj)
  | .fulfill => match cell, claim with
    | none, _ => .error .noReservation
    | some none, some claimed =>
      if claimed = name then .ok (.replace obj) else .error (.wrongClaim claimed)
    | _, _ => .error .notReserved

/-- The only returned successor includes both the slot edit and verified byte
admission. The intermediate anonymous resident is not observable on failure. -/
def run [DecidableEq Name] (arena : CasArena Rep Key Name Obj Error) (mode : Mode)
    (key : Key) (obj : Obj) (name : Name) : Step Rep (Fault Name) Error Unit := fun state => do
  let operation ← (mode.prepare (arena.toArena.read state key) (arena.keyName state key) obj name).mapError
    Failure.semantic
  (Step.mapSemantic (arena.toArena.change key operation) Fault.slot).bind
    (fun _ => Step.mapSemantic (arena.attach key name) Fault.attachment) state

def reference [DecidableEq Key] [DecidableEq Name] (profile : Cas.Profile Name Obj) (mode : Mode)
    (key : Key) (obj : Obj) (name : Name) : Mutable.Mutation (Cas.State Key Name Obj) (Fault Name) Unit :=
  fun state => do
    let operation ← mode.prepare (Cas.State.plain.read state key) (state.slots.keyName key) obj name
    Mutable.Mutation.bind (fun input => (Cas.State.plain.change key operation input).mapError Fault.slot)
      (fun _ input => (profile.attach key name input).mapError Fault.attachment) state

/-- Gate the caller-supplied value and exact bytes before staging the edit.
Rechecking with a different profile is required; a witness is not portable. -/
abbrev ValueFact (profile : Cas.Profile Name Obj) (source : Parsed.Source Name Error)
    (obj : Obj) (name : Name) (bytes : ByteArray) : Prop :=
  Parsed.Fact profile source name bytes ∧ profile.encode? obj = some bytes

def verifyValue [DecidableEq Name] (profile : Cas.Profile Name Obj) (source : Parsed.Source Name Error)
    (obj : Obj) (name : Name) (bytes : ByteArray) : Except (Parsed.Fault Name Error)
      (PLift (ValueFact profile source obj name bytes)) := do
  let fact ← Parsed.verify profile source name bytes
  if exactBytes : profile.encode? obj = some bytes then .ok ⟨⟨fact.down, exactBytes⟩⟩
  else if (profile.encode? obj).isNone then .error .encodingUnavailable else .error .encodedBytesMismatch

def checked [DecidableEq Name] (arena : CasArena Rep Key Name Obj Error) (source : Parsed.Source Name Error)
    (mode : Mode) (key : Key) (obj : Obj) (name : Name) (bytes : ByteArray) :
    Mutable.Mutation Rep (Parsed.GateError Name Error (Fault Name)) Unit :=
  Parsed.guard (verifyValue arena.profile source obj name bytes) (run arena mode key obj name)

/-- Full observation of the edited slot and byte graph, including the frame. -/
def Effect [DecidableEq Key] (profile : Cas.Profile Name Obj) (before after : Cas.State Key Name Obj)
    (key : Key) (obj : Obj) (name : Name) : Prop :=
  ∃ bytes, profile.Certifies name obj bytes ∧
    after.slots = before.slots.replaceAt key (some ⟨some name, some obj⟩) ∧
    Naming.graph after.blocks = Naming.union (Naming.graph before.blocks) (Naming.listed [(name, bytes)])

end Silmaril.Semantics.Arena.Traits.Publish
