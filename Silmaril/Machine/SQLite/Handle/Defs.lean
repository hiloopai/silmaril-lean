module

public import Silmaril.Machine.SQLite.GlobalState.Store.Allocator.Defs
public import Silmaril.Semantics.Resource.Defs

/-! Handle lifetimes for an initialized, sequential SQLite resource profile. -/

@[expose] public section

namespace Silmaril.Machine.SQLite.Handle

open Silmaril.Machine.SQLite.GlobalState

universe u v a l t

/-- An unsuccessful open may return a handle for cleanup. The model exposes
only close on this handle. A ready connection admits new commands. -/
inductive Admission where
  | ready
  | closeOnly
  deriving DecidableEq, Repr

structure Connection (Owner : Type u) where
  owner : Owner
  admission : Admission

structure Dependent (Id Owner : Type u) where
  source : Id
  owner : Owner

structure Backup (Id Owner : Type u) extends Dependent Id Owner where
  destination : Id

/-- Other object kinds retain the caller's payloads, including VFS entries. -/
def Payload (Id Owner : Type u) (Other : ObjectKind → Type u) : ObjectKind → Type u
  | .connection => Connection Owner
  | .statement | .blob => Dependent Id Owner
  | .backup => Backup Id Owner
  | kind => Other kind

/-- A blob entry represents the handle and its private Vdbe as one blocker.
Statement entries represent public statements. A backup's source controls
its contribution to SQLite's busy check. -/
inductive Child (Id Owner : Type u) where
  | statement (entry : Dependent Id Owner)
  | blob (entry : Dependent Id Owner)
  | backup (entry : Backup Id Owner)

inductive ChildKind where
  | statement
  | blob
  | backup
  deriving DecidableEq, Repr

def ChildKind.objectKind : ChildKind → ObjectKind
  | .statement => .statement
  | .blob => .blob
  | .backup => .backup

def Child.kind {Id Owner : Type u} : Child Id Owner → ChildKind
  | .statement _ => .statement
  | .blob _ => .blob
  | .backup _ => .backup

def Child.parent {Id Owner : Type u} : Child Id Owner → Dependent Id Owner
  | .statement entry | .blob entry => entry
  | .backup entry => entry.toDependent

def Child.destination {Id Owner : Type u} : Child Id Owner → Option Id
  | .backup entry => some entry.destination
  | _ => none

def Child.payload {Id Owner : Type u} {Other : ObjectKind → Type u}
    (child : Child Id Owner) : Payload Id Owner Other child.kind.objectKind :=
  match child with
  | .statement entry | .blob entry => entry
  | .backup entry => entry

def Child.object {Id Owner : Type u} {Other : ObjectKind → Type u}
    (child : Child Id Owner) : Object (Payload Id Owner Other) :=
  ⟨child.kind.objectKind, .live, child.payload⟩

variable {Id Owner : Type u} [BEq Id] [Hashable Id] [LawfulBEq Id]
  {Other : ObjectKind → Type u}

abbrev HistoryOf (Id Owner : Type u) [BEq Id] [Hashable Id] (Other : ObjectKind → Type u) :=
  History Id (Payload Id Owner Other)

def ConnectionAt (history : HistoryOf Id Owner Other) (id : Id)
    (state : PresentState) (connection : Connection Owner) : Prop :=
  history.lookup id = some (.present ⟨.connection, state, connection⟩)

def ChildAt (history : HistoryOf Id Owner Other) (id : Id) (child : Child Id Owner) : Prop :=
  history.lookup id = some (.present child.object)

/-- This models the Vdbe list and the source B-tree backup counts in the
selected profile. The destination edge supplies a separate borrow. -/
def Busy (history : HistoryOf Id Owner Other) (db : Id) : Prop :=
  ∃ id child, ChildAt history id child ∧ child.parent.source = db

def DestinationBorrowed (history : HistoryOf Id Owner Other) (db : Id) : Prop :=
  ∃ id child, ChildAt history id child ∧ child.destination = some db

structure Closable (actor : Owner) (history : HistoryOf Id Owner Other)
    (id : Id) (connection : Connection Owner) : Prop where
  present : ConnectionAt history id .live connection
  owned : connection.owner = actor
  available : ¬ DestinationBorrowed history id

def MayCommand (actor : Owner) (history : HistoryOf Id Owner Other) (id : Id) : Prop :=
  Closable actor history id ⟨actor, .ready⟩

/-- A fresh connection token also has no incoming edges in the snapshot. -/
structure Vacant (history : HistoryOf Id Owner Other) (db : Id) : Prop where
  fresh : history.Fresh db
  unblocked : ¬ Busy history db
  unborrowed : ¬ DestinationBorrowed history db

/-- The actor owns the child. The parent's connection need only be available
to release this existing child. A backup requires a separate live destination. -/
structure MayRelease (actor : Owner) (history : HistoryOf Id Owner Other)
    (child : Child Id Owner) : Prop where
  owned : child.parent.owner = actor
  sourceAvailable : ¬ DestinationBorrowed history child.parent.source
  destinationLive : ∀ dst, child.destination = some dst →
    dst ≠ child.parent.source ∧ ∃ owner, ConnectionAt history dst .live ⟨owner, .ready⟩

/-- The registry order is supplied by the caller and every registered ID
references a live VFS entry in the snapshot. -/
structure Registered (registry : List Id) (history : HistoryOf Id Owner Other) : Prop where
  nodup : registry.Nodup
  present : ∀ id ∈ registry, ∃ payload : Other .vfs,
    history.lookup id = some (.present ⟨.vfs, .live, payload⟩)

/-- The zombie cleanup check after a dependent has been released. The
optional token in the observation records actual destruction. -/
inductive Reap (db : Id) : HistoryOf Id Owner Other → Option Id → HistoryOf Id Owner Other → Prop
  | ready {history owner} (present : ConnectionAt history db .live ⟨owner, .ready⟩) :
      Reap db history none history
  | blocked {history owner} (present : ConnectionAt history db .zombie ⟨owner, .ready⟩)
      (busy : Busy history db) : Reap db history none history
  | destroy {history owner} (present : ConnectionAt history db .zombie ⟨owner, .ready⟩)
      (idle : ¬ Busy history db) : Reap db history (some db) (history.free db present)

inductive CloseMode where
  | legacy
  | deferred
  deriving DecidableEq, Repr

inductive PrepareInput where
  | empty
  | statement
  deriving DecidableEq, Repr

/-- Abstract open, prepare and close status. Legacy close has a distinct
`busy` outcome. -/
inductive Status where
  | ok
  | busy
  | error
  deriving DecidableEq, Repr

/-- Abstract a concrete release reply to `ok` for `SQLITE_OK` or `error` for
any other code. Disposal is independent of this status. -/
inductive ReleaseStatus where
  | ok
  | error
  deriving DecidableEq, Repr

inductive Call (Id : Type u) where
  | open
  | prepare (db : Id) (input : PrepareInput)
  | openBlob (db : Id)
  | backupInit (source destination : Id)
  | close (mode : CloseMode) (db : Option Id)
  | release (kind : ChildKind) (id : Option Id)
  | findDefaultVfs
  deriving DecidableEq, Repr

inductive Reply (Id : Type u) where
  | opened (status : Status) (db : Option Id)
  | prepared (status : Status) (stmt : Option Id)
  | created (id : Id)
  | status (status : Status)
  | released (status : ReleaseStatus) (reaped : Option Id)
  | borrowedVfs (id : Option Id)
  deriving DecidableEq, Repr

/-- Resource transitions. Blob and backup creation cover successful calls.
Release observations record zombie destruction separately from the status. -/
inductive Step (actor : Owner) (registry : List Id) :
    Call Id → HistoryOf Id Owner Other → Reply Id → HistoryOf Id Owner Other → Prop
  | openReady {history id} (vacant : Vacant history id) :
      Step actor registry .open history (.opened .ok (some id))
        (history.allocate id .connection ⟨actor, .ready⟩ vacant.fresh)
  | openCloseOnly {history id} (vacant : Vacant history id) :
      Step actor registry .open history (.opened .error (some id))
        (history.allocate id .connection ⟨actor, .closeOnly⟩ vacant.fresh)
  | openNoHandle {history} :
      Step actor registry .open history (.opened .error none) history
  | prepareEmpty {history db} (allowed : MayCommand actor history db) :
      Step actor registry (.prepare db .empty) history (.prepared .ok none) history
  | prepareError {history db input} (allowed : MayCommand actor history db) :
      Step actor registry (.prepare db input) history (.prepared .error none) history
  | prepareStatement {history db id} (allowed : MayCommand actor history db)
      (fresh : history.Fresh id) :
      Step actor registry (.prepare db .statement) history (.prepared .ok (some id))
        (history.allocate id .statement ⟨db, actor⟩ fresh)
  | openBlob {history db id} (allowed : MayCommand actor history db) (fresh : history.Fresh id) :
      Step actor registry (.openBlob db) history (.created id)
        (history.allocate id .blob ⟨db, actor⟩ fresh)
  | backupInit {history source destination id} (sourceAllowed : MayCommand actor history source)
      (destinationAllowed : MayCommand actor history destination) (distinct : source ≠ destination)
      (fresh : history.Fresh id) :
      Step actor registry (.backupInit source destination) history (.created id)
        (history.allocate id .backup ⟨⟨source, actor⟩, destination⟩ fresh)
  | closeNull {history mode} :
      Step actor registry (.close mode none) history (.status .ok) history
  | closeBusy {history db connection} (allowed : Closable actor history db connection)
      (busy : Busy history db) :
      Step actor registry (.close .legacy (some db)) history (.status .busy) history
  | closeZombie {history db connection} (allowed : Closable actor history db connection)
      (busy : Busy history db) :
      Step actor registry (.close .deferred (some db)) history (.status .ok)
        (history.updatePresent db allowed.present .zombie connection)
  | closeDestroy {history db connection mode} (allowed : Closable actor history db connection)
      (idle : ¬ Busy history db) :
      Step actor registry (.close mode (some db)) history (.status .ok)
        (history.free db allowed.present)
  | releaseNull {history kind} :
      Step actor registry (.release kind none) history (.released .ok none) history
  | release {history id child status reaped after} (present : ChildAt history id child)
      (allowed : MayRelease actor history child)
      (reap : Reap child.parent.source (history.free id present) reaped after) :
      Step actor registry (.release child.kind (some id)) history (.released status reaped) after
  | findDefaultVfs {history} (registered : Registered registry history) :
      Step actor registry .findDefaultVfs history (.borrowedVfs registry.head?) history

def writes : Call Id → Reply Id → List Id
  | .open, .opened _ (some id)
  | .prepare .., .prepared _ (some id)
  | .openBlob _, .created id
  | .backupInit .., .created id
  | .close _ (some id), .status .ok => [id]
  | .release _ (some id), .released _ reaped => id :: reaped.toList
  | _, _ => []

variable {AllocId : Type a} [BEq AllocId] [Hashable AllocId]
  {Live : Type l} {Tombstone : Type t}

/-- Lift the object-history relation to the shared tagged store. -/
def contract (actor : Owner) (registry : List Id) :
    Semantics.Resource.Contract (AllocatorStore Id AllocId (Payload Id Owner Other) Live Tombstone)
      (Call Id) (Reply Id) (StoreId Id AllocId) where
  step call before reply after :=
    Step actor registry call before.objectHistory reply after.objectHistory ∧
      after.allocationHistory = before.allocationHistory
  writes call reply := (writes call reply).map StoreId.object

end Silmaril.Machine.SQLite.Handle
