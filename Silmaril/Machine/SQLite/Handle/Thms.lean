module

public import Silmaril.Machine.SQLite.Handle.Defs
public import Silmaril.Semantics.Resource.Thms
import Silmaril.Proofs.Machine.SQLite.Handle.Laws

public section

namespace Silmaril.Machine.SQLite.Handle

open Silmaril.Machine.SQLite.GlobalState

universe u a l t

variable {Id Owner : Type u} [BEq Id] [Hashable Id] [LawfulBEq Id]
  {Other : ObjectKind → Type u} {actor : Owner} {registry : List Id}
  {before after : HistoryOf Id Owner Other} {db id : Id} {reply : Reply Id}

/-- A successful open provides a connection that admits new commands. -/
theorem open_ready (step : Step actor registry .open before (.opened .ok (some db)) after) :
    MayCommand actor after db :=
  Proofs.Machine.SQLite.Handle.open_ready step

/-- An open error can issue an idle handle that admits close for its owner. -/
theorem open_error_close_only
    (step : Step actor registry .open before (.opened .error (some db)) after) :
    Closable actor after db ⟨actor, .closeOnly⟩ ∧ ¬ MayCommand actor after db ∧ ¬ Busy after db :=
  Proofs.Machine.SQLite.Handle.open_error_close_only step

/-- Prepare requires a ready connection belonging to the caller. -/
theorem prepare_requires_command {input : PrepareInput}
    (step : Step actor registry (.prepare db input) before reply after) :
    MayCommand actor before db :=
  Proofs.Machine.SQLite.Handle.prepare_requires_command step

/-- No-SQL input issues no statement token and leaves the object history intact. -/
theorem prepare_empty_post
    (step : Step actor registry (.prepare db .empty) before reply after) :
    after = before ∧ (reply = .prepared .ok none ∨ reply = .prepared .error none) :=
  Proofs.Machine.SQLite.Handle.prepare_empty_post step

/-- Both close modes accept null without changing the history. -/
theorem close_null_iff {mode : CloseMode} :
    Step actor registry (.close mode none) before reply after ↔
      reply = .status .ok ∧ after = before :=
  Proofs.Machine.SQLite.Handle.close_null_iff

/-- Legacy busy close preserves the resource history. -/
theorem close_busy_iff :
    Step actor registry (.close .legacy (some db)) before (.status .busy) after ↔
      after = before ∧ Busy before db ∧ ∃ connection, Closable actor before db connection :=
  Proofs.Machine.SQLite.Handle.close_busy_iff

/-- The caller must leave a borrowed backup destination available until finish. -/
theorem close_borrowed_inapplicable {mode : CloseMode}
    (borrowed : DestinationBorrowed before db) :
    ¬ Step actor registry (.close mode (some db)) before reply after :=
  Proofs.Machine.SQLite.Handle.close_borrowed_inapplicable borrowed

/-- A zombie cannot admit a new command. -/
theorem zombie_no_commands {connection : Connection Owner}
    (zombie : ConnectionAt before db .zombie connection) : ¬ MayCommand actor before db :=
  Proofs.Machine.SQLite.Handle.zombie_no_commands zombie

/-- Deferred close on a busy connection leaves a zombie for existing releases. -/
theorem close_deferred_busy
    (step : Step actor registry (.close .deferred (some db)) before (.status .ok) after)
    (busy : Busy before db) :
    (∃ connection, ConnectionAt after db .zombie connection) ∧ ¬ MayCommand actor after db :=
  Proofs.Machine.SQLite.Handle.close_deferred_busy step busy

/-- Either close mode immediately retires an idle connection. -/
theorem close_idle_destroys {mode : CloseMode}
    (step : Step actor registry (.close mode (some db)) before (.status .ok) after)
    (idle : ¬ Busy before db) : after.lookup db = some (.freed .connection) :=
  Proofs.Machine.SQLite.Handle.close_idle_destroys step idle

/-- An idle zombie is destroyed when the release check reaches it. -/
theorem reap_idle_zombie {owner : Owner} {reaped : Option Id}
    (reap : Reap db before reaped after)
    (zombie : ConnectionAt before db .zombie ⟨owner, .ready⟩) (idle : ¬ Busy before db) :
    reaped = some db ∧ after.lookup db = some (.freed .connection) :=
  Proofs.Machine.SQLite.Handle.reap_idle_zombie reap zombie idle

/-- Release of a non-null handle requires a live child of the right kind and an owner. -/
theorem release_requires_owner {kind : ChildKind}
    (step : Step actor registry (.release kind (some id)) before reply after) :
    ∃ child, ChildAt before id child ∧ child.kind = kind ∧ MayRelease actor before child :=
  Proofs.Machine.SQLite.Handle.release_requires_owner step

/-- Release retires the named handle independently of its SQLite status. -/
theorem release_disposes {kind : ChildKind} {status : ReleaseStatus} {reaped : Option Id}
    (step : Step actor registry (.release kind (some id)) before (.released status reaped) after) :
    after.lookup id = some (.freed kind.objectKind) :=
  Proofs.Machine.SQLite.Handle.release_disposes step

/-- Releasing the last blocker of a zombie can complete with both IDs retired.
The status is independent of disposal. -/
theorem final_dependent_reaps_zombie {child : Child Id Owner} {owner : Owner} {status : ReleaseStatus}
    (present : ChildAt before id child) (allowed : MayRelease actor before child)
    (zombie : ConnectionAt before child.parent.source .zombie ⟨owner, .ready⟩)
    (last : ∀ other entry, ChildAt before other entry → entry.parent.source = child.parent.source →
      other = id) :
    ∃ after, Step actor registry (.release child.kind (some id)) before
      (.released status (some child.parent.source)) after ∧
      after.lookup child.parent.source = some (.freed .connection) ∧
      after.lookup id = some (.freed child.kind.objectKind) :=
  Proofs.Machine.SQLite.Handle.final_dependent_reaps_zombie present allowed zombie last

/-- Finish checks a distinct live destination and preserves it in this profile. -/
theorem backup_finish_destination {backup : Backup Id Owner} {reaped : Option Id}
    (present : ChildAt before id (.backup backup)) (allowed : MayRelease actor before (.backup backup))
    (reap : Reap backup.source (before.free id present) reaped after) :
    ∃ owner, ConnectionAt before backup.destination .live ⟨owner, .ready⟩ ∧
      ConnectionAt after backup.destination .live ⟨owner, .ready⟩ :=
  Proofs.Machine.SQLite.Handle.backup_finish_destination present allowed reap

/-- Object history lookup is stable outside the transition's writes. -/
theorem lookup_frame {call : Call Id} (step : Step actor registry call before reply after) :
    ∀ key, key ∉ writes call reply → after.lookup key = before.lookup key :=
  Proofs.Machine.SQLite.Handle.lookup_frame step

/-- An existing or retired ID cannot become fresh across an admitted operation. -/
theorem fresh_before {call : Call Id} (step : Step actor registry call before reply after)
    (fresh : after.Fresh id) : before.Fresh id :=
  Proofs.Machine.SQLite.Handle.fresh_before step fresh

/-- A tombstone reserves its identity in the object history. -/
theorem stale_not_fresh {kind : ObjectKind} (stale : before.lookup id = some (.freed kind)) :
    ¬ before.Fresh id := by
  simp [History.Fresh, stale]

/-- The private Vdbe for a blob and each backup source contribute to busy. -/
theorem child_blocks_source {child : Child Id Owner} (present : ChildAt before id child) :
    Busy before child.parent.source :=
  ⟨id, child, present, rfl⟩

/-- The borrowed default is the first registered live VFS, with no history edit. -/
theorem find_default_iff :
    Step actor registry .findDefaultVfs before reply after ↔
      Registered registry before ∧ reply = .borrowedVfs registry.head? ∧ after = before :=
  Proofs.Machine.SQLite.Handle.find_default_iff

/-- A non-null default VFS reply refers to a live VFS in the returned state. -/
theorem find_default_live
    (step : Step actor registry .findDefaultVfs before (.borrowedVfs (some id)) after) :
    ∃ payload : Other .vfs, after.lookup id = some (.present ⟨.vfs, .live, payload⟩) :=
  Proofs.Machine.SQLite.Handle.find_default_live step

/-- A registry remains valid when its registered IDs are outside the writes. -/
theorem registered_preserved {call : Call Id} (step : Step actor registry call before reply after)
    (registered : Registered registry before) (outside : ∀ key ∈ registry, key ∉ writes call reply) :
    Registered registry after :=
  Proofs.Machine.SQLite.Handle.registered_preserved step registered outside

variable {AllocId : Type a} [BEq AllocId] [Hashable AllocId] [LawfulBEq AllocId]
  {Live : Type l} {Tombstone : Type t}

/-- The handle contract frames tagged object and allocator lookups outside the writes. -/
theorem frames :
    (contract (Id := Id) (Other := Other) (AllocId := AllocId) (Live := Live)
      (Tombstone := Tombstone) actor registry).Frames AllocatorStore.lookup :=
  Proofs.Machine.SQLite.Handle.frames

end Silmaril.Machine.SQLite.Handle
