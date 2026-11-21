module

public import Silmaril.Semantics.Arena.Cas.Defs

@[expose] public section

namespace Silmaril.Semantics.Arena.Traits

variable {Rep Model Key Name Obj Error Semantic Result Next : Type}

inductive Failure (Semantic Error : Type) where
  | semantic (fault : Semantic)
  | backend (fault : Error)
  deriving DecidableEq, Repr

abbrev Step (Rep Semantic Error Result : Type) := Mutable.Mutation Rep (Failure Semantic Error) Result

namespace Step

def ofModel (edit : Mutable.Mutation Rep Semantic Result) : Step Rep Semantic Error Result :=
  fun state => (edit state).mapError Failure.semantic

def mapSemantic {Other : Type} (edit : Step Rep Semantic Error Result) (rename : Semantic → Other) :
    Step Rep Other Error Result := fun state => (edit state).mapError fun fault =>
  match fault with
  | .semantic value => .semantic (rename value)
  | .backend value => .backend value

/-- Exact successful successors and semantic failures. A backend failure may
preempt either outcome, but cannot provide a successor to commit. -/
def Refines (observe : Rep → Model) (edit : Step Rep Semantic Error Result)
    (spec : Mutable.Mutation Model Semantic Result) : Prop :=
  ∀ state, match edit state with
    | .ok (result, next) => spec (observe state) = .ok (result, observe next)
    | .error (.semantic fault) => spec (observe state) = .error fault
    | .error (.backend _) => True

end Step

abbrev SlotModel := Silmaril.Semantics.Arena.State
abbrev SlotFault := Silmaril.Semantics.Arena.Fault

/-- The landed slot capability with distinct semantic and backend errors. -/
abbrev ArenaApi (Rep Key Obj Error : Type) := Mutable.Access Rep Key Obj (Failure SlotFault Error)

namespace ArenaApi

def reserve (arena : ArenaApi Rep Key Obj Error) (key : Key) : Step Rep SlotFault Error Unit :=
  arena.change key .reserve

def insert (arena : ArenaApi Rep Key Obj Error) (key : Key) (obj : Obj) : Step Rep SlotFault Error Unit :=
  arena.change key (.insert obj)

def replace (arena : ArenaApi Rep Key Obj Error) (key : Key) (obj : Obj) : Step Rep SlotFault Error Unit :=
  arena.change key (.replace obj)

def remove (arena : ArenaApi Rep Key Obj Error) (key : Key) : Step Rep SlotFault Error Unit :=
  arena.change key .remove

def ofAccess (access : Mutable.Access Rep Key Obj SlotFault) : ArenaApi Rep Key Obj Error where
  read := access.read
  change key operation := Step.ofModel (access.change key operation)

def raw [DecidableEq Key] : ArenaApi (SlotModel Key Name Obj) Key Obj Empty := ofAccess Mutable.Access.raw

/-- Bounds failure is a representation restriction, not a semantic hole. -/
def dense (limit : Nat) : ArenaApi (Dense limit Name Obj) Nat Obj SlotFault where
  read := (Mutable.Access.array limit).read
  change key operation state := ((Mutable.Access.array limit).change key operation state).mapError fun fault =>
    match fault with
    | .outOfBounds => .backend fault
    | _ => .semantic fault

def growing : ArenaApi (Mutable.Growing Name Obj) Nat Obj SlotFault where
  read := Mutable.Growing.read
  change key operation state := ((dense state.1).change key operation state.2).map fun (_, slots) =>
    ((), ⟨state.1, slots⟩)

structure Refines [DecidableEq Key] (arena : ArenaApi Rep Key Obj Error) (observe : Rep → SlotModel Key Name Obj) : Prop where
  read_eq : ∀ state key, arena.read state key = Mutable.Access.raw.read (observe state) key
  change_refines : ∀ key operation,
    Step.Refines observe (arena.change key operation) (Mutable.Access.raw.change key operation)

end ArenaApi

/-- Allocation and its frame are optional, independent of the fixed-key API. -/
abbrev Allocate (Rep Key Obj Error : Type) := Option Obj → Step Rep SlotFault Error Key

def Allocate.Fresh (allocate : Allocate Rep Key Obj Error) (arena : ArenaApi Rep Key Obj Error) : Prop :=
  ∀ {payload state key next}, allocate payload state = .ok (key, next) →
    arena.read state key = none ∧ arena.read next key = some payload ∧
      ∀ other, other ≠ key → arena.read next other = arena.read state other

def Allocate.append : Allocate (Mutable.Growing Name Obj) Nat Obj SlotFault := fun payload state =>
  (Mutable.Growing.allocate payload state).mapError Empty.elim

inductive PutFault (Name : Type) where
  | unnamed
  | collision (name : Name)
  deriving DecidableEq, Repr

/-- All raw writes go through the same authoritative admission rule as attachment.
A name chooses a binding, not a new slot. -/
def putBytes [DecidableEq Name] (select? : ByteArray → Option Name) (bytes : ByteArray) :
    Mutable.Mutation (Cas.State Key Name Obj) (PutFault Name) Name := fun state => do
  let some name := select? bytes | .error .unnamed
  let blocks ← (Naming.admit state.blocks [(name, bytes)]).mapError PutFault.collision
  return (name, {state with blocks})

/-- CAS extends the plain API on the same state. Only the authoritative read
may return a definitive miss. Reverse lookup is of all resident aliases. -/
structure CasArena (Rep Key Name Obj Error : Type) where
  toArena : ArenaApi Rep Key Obj Error
  profile : Cas.Profile Name Obj
  get : Rep → Name → Except Error (Option ByteArray)
  keyName : Rep → Key → Option Name
  attachedKeys : Rep → Name → Set Key
  put : ByteArray → Step Rep (PutFault Name) Error Name
  attach : Key → Name → Step Rep (Cas.Fault Name) Error Unit

namespace CasArena

def model [DecidableEq Key] [DecidableEq Name] (profile : Cas.Profile Name Obj) :
    CasArena (Cas.State Key Name Obj) Key Name Obj Empty where
  toArena := ArenaApi.ofAccess Cas.State.plain
  profile := profile
  get state name := .ok (state.blocks name)
  keyName state key := state.slots.keyName key
  attachedKeys := Cas.State.attachedKeys
  put bytes := Step.ofModel (putBytes profile.select? bytes)
  attach key name := Step.ofModel (profile.attach key name)

def claimKeys (arena : CasArena Rep Key Name Obj Error) (state : Rep) (name : Name) : Set Key :=
  {key | arena.keyName state key = some name}

/-- Stage a stable-key edit and revalidation as one commit. A successful
revalidation never removes or changes an older authoritative binding. -/
def replaceAndAttach (arena : CasArena Rep Key Name Obj Error) (key : Key) (obj : Obj) (name : Name) :
    Step Rep (Sum SlotFault (Cas.Fault Name)) Error Unit :=
  (Step.mapSemantic (arena.toArena.change key (.replace obj)) Sum.inl).bind fun _ =>
    Step.mapSemantic (arena.attach key name) Sum.inr

def replaceAndAttachReference [DecidableEq Key] [DecidableEq Name] (profile : Cas.Profile Name Obj)
    (key : Key) (obj : Obj) (name : Name) :
    Mutable.Mutation (Cas.State Key Name Obj) (Sum SlotFault (Cas.Fault Name)) Unit :=
  Mutable.Mutation.bind (fun state => (Cas.State.plain.change key (.replace obj) state).mapError Sum.inl)
    (fun _ state => (profile.attach key name state).mapError Sum.inr)

def putReference [DecidableEq Name] (arena : CasArena Rep Key Name Obj Error) (bytes : ByteArray) :
    Mutable.Mutation (Cas.State Key Name Obj) (PutFault Name) Name := putBytes arena.profile.select? bytes

structure Refines [DecidableEq Key] [DecidableEq Name] (arena : CasArena Rep Key Name Obj Error)
    (observe : Rep → Cas.State Key Name Obj) : Prop where
  plain : ∀ key operation, Step.Refines observe (arena.toArena.change key operation) (Cas.State.plain.change key operation)
  read_eq : ∀ state key, arena.toArena.read state key = Cas.State.plain.read (observe state) key
  get_eq : ∀ state name result, arena.get state name = .ok result → result = (observe state).blocks name
  name_eq : ∀ state key, arena.keyName state key = (observe state).slots.keyName key
  keys_eq : ∀ state name, arena.attachedKeys state name = (observe state).attachedKeys name
  put_refines : ∀ bytes, Step.Refines observe (arena.put bytes) (arena.putReference bytes)
  attach_refines : ∀ key name, Step.Refines observe (arena.attach key name) (arena.profile.attach key name)

end CasArena

end Silmaril.Semantics.Arena.Traits
