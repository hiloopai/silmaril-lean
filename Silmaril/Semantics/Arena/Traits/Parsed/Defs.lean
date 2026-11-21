module

public import Silmaril.Semantics.Arena.Traits.Defs

@[expose] public section

namespace Silmaril.Semantics.Arena.Traits.Parsed

variable {Rep Key Name Obj Error Semantic Result : Type}

/-- A source observation, not a claim that this source is authoritative.
In particular, a cache miss must be reported as `unavailable`. -/
inductive Observation (Error : Type) where
  | present (bytes : ByteArray)
  | absent
  | unavailable (reason : Error)
  deriving DecidableEq

abbrev Source (Name Error : Type) := Name → Observation Error

def Source.Agrees (source : Source Name Error) (reference : Name → Option ByteArray) : Prop :=
  ∀ name, match source name with
    | .present bytes => reference name = some bytes
    | .absent => reference name = none
    | .unavailable _ => True

def CasArena.probe (arena : CasArena Rep Key Name Obj Error) (state : Rep) : Source Name Error :=
  fun name => match arena.get state name with
    | .ok (some bytes) => .present bytes
    | .ok none => .absent
    | .error reason => .unavailable reason

/-- The trusted boundary is a refinement to an authoritative byte snapshot,
plus the attachment invariant on states the backend exposes as valid. Plain
typed slots need neither an encoder result nor a name. -/
structure Trusted [DecidableEq Key] [DecidableEq Name] (arena : CasArena Rep Key Name Obj Error)
    (observe : Rep → Cas.State Key Name Obj) (ready : Rep → Prop) : Prop where
  refines : arena.Refines observe
  valid : ∀ state, ready state → arena.profile.Valid (observe state)

/-- Proposition-indexed analogue of a verified claim about exact bytes.
The source is the particular observation function and the profile is the
actual policy, not an unchecked source or codec label in the input. -/
structure Fact (profile : Cas.Profile Name Obj) (source : Source Name Error)
    (name : Name) (bytes : ByteArray) : Prop where
  observed : source name = .present bytes
  selected : profile.select? bytes = some name

structure AttachmentFact (arena : CasArena Rep Key Name Obj Error) (source : Source Name Error)
    (state : Rep) (key : Key) (name : Name) (bytes : ByteArray) : Prop where
  fact : Fact arena.profile source name bytes
  resident : ∃ obj, arena.toArena.read state key = some (some obj) ∧ arena.profile.encode? obj = some bytes

inductive Fault (Name Error : Type) where
  | sourceUnavailable (reason : Error)
  | sourceAbsent
  | sourceBytesMismatch
  | nameUnavailable
  | nameMismatch (selected : Name)
  | vacant
  | unresident
  | encodingUnavailable
  | encodedBytesMismatch
  deriving DecidableEq, Repr

/-- No fact is manufactured from a digest. Verify the exact observed bytes
and the selected name; unavailable observations supply no evidence. -/
def verify [DecidableEq Name] (profile : Cas.Profile Name Obj) (source : Source Name Error)
    (name : Name) (bytes : ByteArray) : Except (Fault Name Error) (PLift (Fact profile source name bytes)) :=
  match observed : source name with
  | .unavailable reason => .error (.sourceUnavailable reason)
  | .absent => .error .sourceAbsent
  | .present fetched =>
    if same : fetched = bytes then
      match selected : profile.select? bytes with
      | none => .error .nameUnavailable
      | some actual => if eq : actual = name then .ok ⟨⟨same ▸ observed, eq ▸ selected⟩⟩
                       else .error (.nameMismatch actual)
    else .error .sourceBytesMismatch

/-- Validate the resident typed value by its exact canonical bytes, not by
`DecidableEq Obj`, or by assuming that a name identifies a typed value. -/
def verifyAttachment [DecidableEq Name] (arena : CasArena Rep Key Name Obj Error) (source : Source Name Error)
    (state : Rep) (key : Key) (name : Name) (bytes : ByteArray) :
    Except (Fault Name Error) (PLift (AttachmentFact arena source state key name bytes)) := do
  let fact ← verify arena.profile source name bytes
  match resident : arena.toArena.read state key with
  | none => .error .vacant
  | some none => .error .unresident
  | some (some obj) =>
    match encoded : arena.profile.encode? obj with
    | none => .error .encodingUnavailable
    | some actual => if eq : actual = bytes then .ok ⟨⟨fact.down, obj, resident, eq ▸ encoded⟩⟩
                     else .error .encodedBytesMismatch

abbrev GateError (Name Error Semantic : Type) := Sum (Fault Name Error) (Failure Semantic Error)

def guard {Evidence : Prop} (check : Except (Fault Name Error) (PLift Evidence))
    (edit : Step Rep Semantic Error Result) (state : Rep) : Except (GateError Name Error Semantic) (Result × Rep) :=
  match check with
  | .error fault => .error (.inl fault)
  | .ok _ => (edit state).mapError Sum.inr

/-- Optional ingress over the same backend. Verification stages no writes;
the trusted commit still checks collisions against its own snapshot. -/
def put [DecidableEq Name] (arena : CasArena Rep Key Name Obj Error) (source : Source Name Error)
    (name : Name) (bytes : ByteArray) (state : Rep) : Except (GateError Name Error (PutFault Name)) (Name × Rep) :=
  guard (verify arena.profile source name bytes) (arena.put bytes) state

def attach [DecidableEq Name] (arena : CasArena Rep Key Name Obj Error) (source : Source Name Error)
    (key : Key) (name : Name) (bytes : ByteArray) (state : Rep) : Except (GateError Name Error (Cas.Fault Name)) (Unit × Rep) :=
  guard (verifyAttachment arena source state key name bytes) (arena.attach key name) state

end Silmaril.Semantics.Arena.Traits.Parsed
