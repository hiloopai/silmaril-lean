module

public import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Defs

@[expose] public section

namespace Silmaril.Wasm.Component.Machine.ReturnFrame.Occurrence

open Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime

variable {E : CoreEngine} {Host : Type}

/-- A segment occurrence, not a continuation value. Equal program closures
can simultaneously occur at different active or saved coordinates. -/
inductive Location where
  | active (activation segment : Nat)
  | saved (slot segment : Nat)
  deriving DecidableEq

/-- The slot at a fixed depth below this segment in the same activation. -/
def Location.below (place : Location) (depth : Nat) : Location :=
  match place with
  | .active activation segment => .active activation (segment + depth)
  | .saved slot segment => .saved slot (segment + depth)

/-- Only control storage is relevant to the lifetime of a saved frame. -/
structure Stacks (E : CoreEngine) (Host : Type) where
  active : List (List (Seg E Host))
  saved : List (Option (List (Seg E Host)))

def segmentStorage (cfg : Config E Host) : Stacks E Host :=
  ⟨cfg.ctl.map Activation.segs, cfg.conts.map (Option.map Activation.segs)⟩

def segmentAt (storage : Stacks E Host) : Location → Option (Seg E Host)
  | .active activation segment => storage.active[activation]?.bind (·[segment]?)
  | .saved slot segment => storage.saved[slot]?.join.bind (·[segment]?)

/-- Scheduler edits projected to segment storage. `clear` is lockdown,
not return; `write` can overwrite a saved slot rather than resume it. -/
inductive Edit (E : CoreEngine) (Host : Type) where
  | same
  | push (frame : Seg E Host)
  | pop
  | exit
  | clear
  | enter
  | write (slot : Nat) (frames : List (Seg E Host))
  | block (slot : Nat)
  | resume (slot : Nat)
  | switch (fromSlot toSlot : Nat)

def savedAt (storage : Stacks E Host) (slot : Nat) : List (Seg E Host) :=
  storage.saved[slot]?.join.getD []

def front (storage : Stacks E Host) : List (Seg E Host) := storage.active.headD []

def Stacks.block (storage : Stacks E Host) (slot : Nat) : Stacks E Host :=
  ⟨storage.active.tail, Config.setSlot storage.saved slot (some (front storage))⟩

def Stacks.resume (storage : Stacks E Host) (slot : Nat) : Stacks E Host :=
  ⟨savedAt storage slot :: storage.active, Config.setSlot storage.saved slot none⟩

def Edit.apply (edit : Edit E Host) (storage : Stacks E Host) : Stacks E Host :=
  match edit with
  | .same => storage
  | .push frame => { storage with active := (frame :: front storage) :: storage.active.tail }
  | .pop => { storage with active := (front storage).tail :: storage.active.tail }
  | .exit => { storage with active := storage.active.tail }
  | .clear => { storage with active := [] }
  | .enter => { storage with active := [[]] }
  | .write slot frames => { storage with saved := Config.setSlot storage.saved slot (some frames) }
  | .block slot => storage.block slot
  | .resume slot => storage.resume slot
  | .switch fromSlot toSlot => (storage.block fromSlot).resume toSlot

def Location.block (slot : Nat) : Location → Option Location
  | .active 0 segment => some (.saved slot segment)
  | .active (activation + 1) segment => some (.active activation segment)
  | .saved current segment => if current = slot then none else some (.saved current segment)

def Location.resume (slot : Nat) : Location → Location
  | .active activation segment => .active (activation + 1) segment
  | .saved current segment => if current = slot then .active 0 segment else .saved current segment

/-- Map an existing coordinate through one scheduler edit. If an edit
discards a frame, a later equal frame cannot revive that occurrence. -/
def Edit.follow (edit : Edit E Host) (place : Location) : Option Location :=
  match edit, place with
  | .push _, .active 0 segment => some (.active 0 (segment + 1))
  | .pop, .active 0 0 => none
  | .pop, .active 0 (segment + 1) => some (.active 0 segment)
  | .exit, .active 0 _ => none
  | .exit, .active (activation + 1) segment => some (.active activation segment)
  | .clear, .active .. | .enter, .active .. => none
  | .write slot _, .saved current _ => if current = slot then none else some place
  | .block slot, _ => place.block slot
  | .resume slot, _ => some (place.resume slot)
  | .switch fromSlot toSlot, _ => (place.block fromSlot).map (Location.resume toSlot)
  | _, _ => some place

/-- The source of a reached segment coordinate. Unoccupied and newly written
coordinates have no predecessor (and therefore cannot carry a mark). -/
abbrev Source (E : CoreEngine) (Host : Type) := Sum Location (Option (Seg E Host))

def Location.beforeBlock (slot : Nat) : Location → Location
  | .active activation segment => .active (activation + 1) segment
  | .saved current segment => if current = slot then .active 0 segment else .saved current segment

def Location.beforeResume (slot : Nat) : Location → Option Location
  | .active 0 segment => some (.saved slot segment)
  | .active (activation + 1) segment => some (.active activation segment)
  | .saved current segment => if current = slot then none else some (.saved current segment)

def Edit.source (edit : Edit E Host) (place : Location) : Source E Host :=
  match edit, place with
  | .push frame, .active 0 0 => .inr (some frame)
  | .push _, .active 0 (segment + 1) => .inl (.active 0 segment)
  | .pop, .active 0 segment => .inl (.active 0 (segment + 1))
  | .exit, .active activation segment => .inl (.active (activation + 1) segment)
  | .clear, .active .. | .enter, .active .. => .inr none
  | .write slot frames, .saved current segment => if current = slot then .inr frames[segment]? else .inl place
  | .block slot, _ => .inl (place.beforeBlock slot)
  | .resume slot, _ => (place.beforeResume slot).elim (.inr none) .inl
  | .switch fromSlot toSlot, _ => (place.beforeResume toSlot).elim (.inr none) (fun source => .inl (source.beforeBlock fromSlot))
  | _, _ => .inl place

def Source.segment (storage : Stacks E Host) : Source E Host → Option (Seg E Host)
  | .inl place => segmentAt storage place
  | .inr fresh => fresh

/-- Older substitutions suffice everywhere except at the single installed
coordinate. This property is indexed by the occurrence, not its closures. -/
def Outside (older : Substitutions E Host) (left right : Stacks E Host) (mark : Option Location) : Prop :=
  ∀ place, some place ≠ mark → ∀ first second,
    segmentAt left place = some first → segmentAt right place = some second → Related.Segment older first second

/-- The only edit that consumes the marked top segment is the actual pop.
Other ways of losing it (lockdown or an overwritten slot) are not returns. -/
def Edit.pops (edit : Edit E Host) (place : Location) : Prop :=
  match edit, place with
  | .pop, .active 0 0 => True
  | _, _ => False

/-- The edit is selected by the actual focus and transition label, never by
comparing continuations or guessing how equal stacks were produced. -/
def transitionEdit (cfg : Config E Host) (label : Label E Host) : Edit E Host :=
  match label with
  | .trap _ => .clear
  | .host _ => .enter
  | .tau =>
    match cfg.ctl with
    | [] => .same
    | act :: _ =>
      match act.focus with
      | .core core resume =>
        match E.status cfg.store.core core with
        | .callout .. => .push (.core core resume)
        | _ => .same
      | .prog (.pure _) => if act.segs.isEmpty then .exit else .pop
      | .prog (.op action next) =>
        match action, next with
        | .call _, resume => .push (.prog resume)
        | .newThread body, _ => .write (ArenaField.threads.alloc cfg.store { task := body.task }).2.idx []
        | .block none, _ => act.thread.elim .same (fun thread => .block thread.idx)
        | .block (some target), _ => act.thread.elim .same (fun thread => .switch thread.idx target.idx)
        | .resumeThread thread, _ => .resume thread.idx
        | _, _ => .same
  | _ => .same

/-- The result of popping the selected program continuation, before its
body executes. An equal continuation elsewhere does not satisfy the location test. -/
def Popped (before after : Config E Host) (label : Label E Host) (place : Location)
    (resume : Continuation E Host) : Prop :=
  place = .active 0 0 ∧ label = .tau ∧ ∃ thread value frames rest,
    before.ctl = ⟨thread, .prog (.pure value), .prog resume :: frames⟩ :: rest ∧
    after = { before with ctl := ⟨thread, .prog (resume value), frames⟩ :: rest }

/-- A finite scheduler prefix throughout which the same installed occurrence
survives. After its first removal no subsequent install can restore this prefix. -/
inductive Prefix (profile : ProfileKind) (ready : HostReady Host) (dispatch : Call E → P E Host (Ret E)) :
    Config E Host → Location → List (Label E Host) → Config E Host → Location → Prop where
  | done (cfg : Config E Host) (place : Location) : Prefix profile ready dispatch cfg place [] cfg place
  | step {before next after : Config E Host} {place middle reached : Location} {label labels} :
      Step profile ready dispatch before label next → (transitionEdit before label).follow place = some middle →
      Prefix profile ready dispatch next middle labels after reached →
      Prefix profile ready dispatch before place (label :: labels) after reached

/-- An execution that carries every slot of the active top frame to its
original location. Intermediate steps need not leave each slot in place. -/
abbrev RetainsActiveSlots (profile : ProfileKind) (ready : HostReady Host) (dispatch : Call E → P E Host (Ret E))
    (before : Config E Host) (labels : List (Label E Host)) (after : Config E Host) : Prop :=
  ∀ depth, Prefix profile ready dispatch before (.active 0 depth) labels after (.active 0 depth)

/-- The older slots survive a prefix ending one slot shallower. This is the
coordinate change at a return, followed by any slot-preserving local work. -/
abbrev RetainsBelowTop (profile : ProfileKind) (ready : HostReady Host) (dispatch : Call E → P E Host (Ret E))
    (before : Config E Host) (labels : List (Label E Host)) (after : Config E Host) : Prop :=
  ∀ depth, Prefix profile ready dispatch before (.active 0 (depth + 1)) labels after (.active 0 depth)

/-- Follow an optional marked occurrence through every actual step. Absence
can only result from an edit removing the mark, and remains absent afterward. -/
inductive Trail (profile : ProfileKind) (ready : HostReady Host) (dispatch : Call E → P E Host (Ret E)) :
    Config E Host → Option Location → List (Label E Host) → Config E Host → Option Location → Prop where
  | done (cfg : Config E Host) (mark : Option Location) : Trail profile ready dispatch cfg mark [] cfg mark
  | step {before next after : Config E Host} {mark reached : Option Location} {label labels} :
      Step profile ready dispatch before label next →
      Trail profile ready dispatch next (mark.bind (transitionEdit before label).follow) labels after reached →
      Trail profile ready dispatch before mark (label :: labels) after reached

end Silmaril.Wasm.Component.Machine.ReturnFrame.Occurrence
