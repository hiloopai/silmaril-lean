module

public import Silmaril.Machine.SQLite.Handle.Defs
public import Silmaril.Machine.SQLite.GlobalState.Store.Allocator.Thms

public section

namespace Silmaril.Proofs.Machine.SQLite.Handle

open Silmaril.Machine.SQLite.GlobalState Silmaril.Machine.SQLite.Handle

universe u a l t

variable {Id Owner : Type u} [BEq Id] [Hashable Id] [LawfulBEq Id]
  {Other : ObjectKind → Type u} {actor : Owner} {registry : List Id}
  {before after : HistoryOf Id Owner Other} {db id : Id} {reply : Reply Id}

private def observedKind (entry : Option (HistoryEntry (Payload Id Owner Other))) : Option ObjectKind :=
  (entry.bind HistoryEntry.toObject).map Object.kind

private def observedState (entry : Option (HistoryEntry (Payload Id Owner Other))) : Option PresentState :=
  (entry.bind HistoryEntry.toObject).map Object.state

private def connectionAdmission (entry : Option (HistoryEntry (Payload Id Owner Other))) :
    Option Admission :=
  match entry with
  | some (.present ⟨.connection, _, data⟩) => some data.admission
  | _ => none

private theorem child_after_connection_allocation {connection : Connection Owner}
    (fresh : before.Fresh db) {token : Id} {child : Child Id Owner}
    (present : ChildAt (before.allocate db .connection connection fresh) token child) :
    ChildAt before token child := by
  by_cases equal : token = db
  · subst token
    have conflict := congrArg observedKind ((History.lookup_allocate_self ..).symm.trans present)
    cases child <;> cases conflict
  · exact (History.lookup_allocate_of_ne before equal .connection connection fresh).symm.trans present

private theorem new_connection (vacant : Vacant before db) (admission : Admission) :
    let next := before.allocate db .connection ⟨actor, admission⟩ vacant.fresh
    Closable actor next db ⟨actor, admission⟩ ∧ ¬ Busy next db := by
  refine ⟨⟨History.lookup_allocate_self .., rfl, ?_⟩, ?_⟩
  · rintro ⟨id, child, childPresent, destination⟩
    exact vacant.unborrowed ⟨id, child, child_after_connection_allocation vacant.fresh childPresent,
      destination⟩
  · rintro ⟨id, child, childPresent, source⟩
    exact vacant.unblocked ⟨id, child, child_after_connection_allocation vacant.fresh childPresent,
      source⟩

theorem open_ready (step : Step actor registry .open before (.opened .ok (some db)) after) :
    MayCommand actor after db := by
  cases step with | openReady vacant => exact (new_connection vacant .ready).1

theorem open_error_close_only
    (step : Step actor registry .open before (.opened .error (some db)) after) :
    Closable actor after db ⟨actor, .closeOnly⟩ ∧ ¬ MayCommand actor after db ∧ ¬ Busy after db := by
  cases step with
  | openCloseOnly vacant =>
    obtain ⟨closable, idle⟩ := new_connection (actor := actor) vacant .closeOnly
    refine ⟨closable, ?_, idle⟩
    intro command
    have conflict := congrArg connectionAdmission (closable.present.symm.trans command.present)
    cases conflict

theorem prepare_requires_command {input : PrepareInput}
    (step : Step actor registry (.prepare db input) before reply after) :
    MayCommand actor before db := by
  cases step <;> assumption

theorem prepare_empty_post
    (step : Step actor registry (.prepare db .empty) before reply after) :
    after = before ∧ (reply = .prepared .ok none ∨ reply = .prepared .error none) := by
  cases step with
  | prepareEmpty => exact ⟨rfl, .inl rfl⟩
  | prepareError => exact ⟨rfl, .inr rfl⟩

theorem close_null_iff {mode : CloseMode} :
    Step actor registry (.close mode none) before reply after ↔
      reply = .status .ok ∧ after = before := by
  constructor
  · intro step
    cases step
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact .closeNull

theorem close_busy_iff :
    Step actor registry (.close .legacy (some db)) before (.status .busy) after ↔
      after = before ∧ Busy before db ∧ ∃ connection, Closable actor before db connection := by
  constructor
  · intro step
    cases step with | closeBusy allowed busy => exact ⟨rfl, busy, _, allowed⟩
  · rintro ⟨rfl, busy, _, allowed⟩
    exact .closeBusy allowed busy

theorem close_borrowed_inapplicable {mode : CloseMode}
    (borrowed : DestinationBorrowed before db) :
    ¬ Step actor registry (.close mode (some db)) before reply after := by
  intro step
  cases step with
  | closeBusy allowed _ | closeZombie allowed _ | closeDestroy allowed _ =>
    exact allowed.available borrowed

theorem zombie_no_commands {connection : Connection Owner}
    (zombie : ConnectionAt before db .zombie connection) : ¬ MayCommand actor before db := by
  intro command
  have conflict := congrArg observedState (zombie.symm.trans command.present)
  cases conflict

theorem close_deferred_busy
    (step : Step actor registry (.close .deferred (some db)) before (.status .ok) after)
    (busy : Busy before db) :
    (∃ connection, ConnectionAt after db .zombie connection) ∧ ¬ MayCommand actor after db := by
  cases step with
  | @closeZombie _ _ connection allowed _ =>
    have zombie := History.lookup_updatePresent_self before db allowed.present .zombie connection
    exact ⟨⟨_, zombie⟩, zombie_no_commands zombie⟩
  | closeDestroy _ idle => exact (idle busy).elim

theorem close_idle_destroys {mode : CloseMode}
    (step : Step actor registry (.close mode (some db)) before (.status .ok) after)
    (idle : ¬ Busy before db) : after.lookup db = some (.freed .connection) := by
  cases step with
  | closeZombie _ busy => exact (idle busy).elim
  | closeDestroy allowed _ => exact History.lookup_free_self before db allowed.present

private theorem reap_lookup_frame {reaped : Option Id}
    (reap : Reap db before reaped after) (outside : id ∉ reaped.toList) :
    after.lookup id = before.lookup id := by
  cases reap with
  | ready | blocked => rfl
  | destroy present => exact History.lookup_free_of_ne before (by simpa using outside) present

private theorem reap_lookup_of_ne {reaped : Option Id}
    (reap : Reap db before reaped after) (different : id ≠ db) :
    after.lookup id = before.lookup id := by
  cases reap with
  | ready | blocked => rfl
  | destroy present => exact History.lookup_free_of_ne before different present

private theorem reap_fresh_iff {reaped : Option Id} (reap : Reap db before reaped after) :
    after.Fresh id ↔ before.Fresh id := by
  cases reap with
  | ready | blocked => rfl
  | destroy present => exact History.fresh_free_iff before db id present

theorem reap_idle_zombie {owner : Owner} {reaped : Option Id}
    (reap : Reap db before reaped after)
    (zombie : ConnectionAt before db .zombie ⟨owner, .ready⟩) (idle : ¬ Busy before db) :
    reaped = some db ∧ after.lookup db = some (.freed .connection) := by
  cases reap with
  | ready present =>
    have conflict := congrArg observedState (zombie.symm.trans present)
    cases conflict
  | blocked _ busy => exact (idle busy).elim
  | destroy present => exact ⟨rfl, History.lookup_free_self before db present⟩

private theorem no_busy_after_only_child {child : Child Id Owner} (present : ChildAt before id child)
    (only : ∀ other entry, ChildAt before other entry → entry.parent.source = db → other = id) :
    ¬ Busy (before.free id present) db := by
  rintro ⟨other, entry, childPresent, source⟩
  by_cases equal : other = id
  · subst other
    have conflict := (History.lookup_free_self before id present).symm.trans childPresent
    cases conflict
  · have old := (History.lookup_free_of_ne before equal present).symm.trans childPresent
    exact equal (only other entry old source)

theorem release_requires_owner {kind : ChildKind}
    (step : Step actor registry (.release kind (some id)) before reply after) :
    ∃ child, ChildAt before id child ∧ child.kind = kind ∧ MayRelease actor before child := by
  cases step with
  | release present allowed _ => exact ⟨_, present, rfl, allowed⟩

theorem release_disposes {kind : ChildKind} {status : ReleaseStatus} {reaped : Option Id}
    (step : Step actor registry (.release kind (some id)) before (.released status reaped) after) :
    after.lookup id = some (.freed kind.objectKind) := by
  cases step with
  | @release _ _ child _ _ _ present _ reap =>
    refine (reap_lookup_frame reap ?_).trans (History.lookup_free_self before id present)
    intro member
    cases reap with
    | ready | blocked => simp at member
    | destroy connection =>
      have equal : id = child.parent.source := by simpa using member
      rw [← equal] at connection
      have conflict := (History.lookup_free_self before id present).symm.trans connection
      cases conflict

theorem final_dependent_reaps_zombie {child : Child Id Owner} {owner : Owner} {status : ReleaseStatus}
    (present : ChildAt before id child) (allowed : MayRelease actor before child)
    (zombie : ConnectionAt before child.parent.source .zombie ⟨owner, .ready⟩)
    (last : ∀ other entry, ChildAt before other entry → entry.parent.source = child.parent.source →
      other = id) :
    ∃ after, Step actor registry (.release child.kind (some id)) before
      (.released status (some child.parent.source)) after ∧
      after.lookup child.parent.source = some (.freed .connection) ∧
      after.lookup id = some (.freed child.kind.objectKind) := by
  have different : child.parent.source ≠ id := by
    intro equal
    rw [equal] at zombie
    have conflict := congrArg observedState (zombie.symm.trans present)
    cases conflict
  have stillZombie :=
    (History.lookup_free_of_ne before different present).trans zombie
  have run : Step actor registry (.release child.kind (some id)) before
      (.released status (some child.parent.source))
      ((before.free id present).free child.parent.source stillZombie) :=
    .release present allowed (.destroy stillZombie (no_busy_after_only_child present last))
  exact ⟨_, run, History.lookup_free_self .., release_disposes run⟩

theorem backup_finish_destination {backup : Backup Id Owner} {reaped : Option Id}
    (present : ChildAt before id (.backup backup)) (allowed : MayRelease actor before (.backup backup))
    (reap : Reap backup.source (before.free id present) reaped after) :
    ∃ owner, ConnectionAt before backup.destination .live ⟨owner, .ready⟩ ∧
      ConnectionAt after backup.destination .live ⟨owner, .ready⟩ := by
  obtain ⟨different, owner, destinationLive⟩ := allowed.destinationLive backup.destination rfl
  have outsideChild : backup.destination ≠ id := by
    intro equal
    rw [equal] at destinationLive
    have conflict := congrArg observedKind (present.symm.trans destinationLive)
    cases conflict
  exact ⟨owner, destinationLive, (reap_lookup_of_ne reap different).trans
    ((History.lookup_free_of_ne before outsideChild present).trans destinationLive)⟩

theorem lookup_frame {call : Call Id} (step : Step actor registry call before reply after) :
    ∀ key, key ∉ writes call reply → after.lookup key = before.lookup key := by
  intro key outside
  cases step with
  | openReady vacant | openCloseOnly vacant =>
    exact History.lookup_allocate_of_ne before (by simpa [writes] using outside) _ _ vacant.fresh
  | prepareStatement _ fresh | openBlob _ fresh | backupInit _ _ _ fresh =>
    exact History.lookup_allocate_of_ne before (by simpa [writes] using outside) _ _ fresh
  | closeZombie allowed _ =>
    exact History.lookup_updatePresent_of_ne before (by simpa [writes] using outside)
      allowed.present .zombie _
  | closeDestroy allowed _ =>
    exact History.lookup_free_of_ne before (by simpa [writes] using outside) allowed.present
  | release present _ reap =>
    simp only [writes, List.mem_cons, not_or] at outside
    exact (reap_lookup_frame reap outside.2).trans (History.lookup_free_of_ne before outside.1 present)
  | openNoHandle | prepareEmpty | prepareError | closeNull | closeBusy | releaseNull | findDefaultVfs =>
    rfl

theorem fresh_before {call : Call Id} (step : Step actor registry call before reply after)
    (fresh : after.Fresh id) : before.Fresh id := by
  cases step with
  | openReady vacant | openCloseOnly vacant =>
    exact ((History.fresh_allocate_iff before _ id _ _ vacant.fresh).mp fresh).2
  | prepareStatement _ unused | openBlob _ unused | backupInit _ _ _ unused =>
    exact ((History.fresh_allocate_iff before _ id _ _ unused).mp fresh).2
  | closeZombie allowed _ =>
    exact (History.fresh_updatePresent_iff before _ id allowed.present .zombie _).mp fresh
  | closeDestroy allowed _ =>
    exact (History.fresh_free_iff before _ id allowed.present).mp fresh
  | release present _ reap =>
    exact (History.fresh_free_iff before _ id present).mp ((reap_fresh_iff reap).mp fresh)
  | openNoHandle | prepareEmpty | prepareError | closeNull | closeBusy | releaseNull | findDefaultVfs =>
    exact fresh

theorem find_default_iff :
    Step actor registry .findDefaultVfs before reply after ↔
      Registered registry before ∧ reply = .borrowedVfs registry.head? ∧ after = before := by
  constructor
  · intro step
    cases step with | findDefaultVfs registered => exact ⟨registered, rfl, rfl⟩
  · rintro ⟨registered, rfl, rfl⟩
    exact .findDefaultVfs registered

theorem find_default_live
    (step : Step actor registry .findDefaultVfs before (.borrowedVfs (some id)) after) :
    ∃ payload : Other .vfs, after.lookup id = some (.present ⟨.vfs, .live, payload⟩) := by
  obtain ⟨registered, reply, rfl⟩ := find_default_iff.mp step
  exact registered.present id (List.mem_of_head? (Reply.borrowedVfs.inj reply).symm)

theorem registered_preserved {call : Call Id} (step : Step actor registry call before reply after)
    (registered : Registered registry before) (outside : ∀ key ∈ registry, key ∉ writes call reply) :
    Registered registry after := by
  refine ⟨registered.nodup, ?_⟩
  intro id member
  rw [lookup_frame step id (outside id member)]
  exact registered.present id member

variable {AllocId : Type a} [BEq AllocId] [Hashable AllocId] [LawfulBEq AllocId]
  {Live : Type l} {Tombstone : Type t}

theorem frames :
    (contract (Id := Id) (Other := Other) (AllocId := AllocId) (Live := Live)
      (Tombstone := Tombstone) actor registry).Frames AllocatorStore.lookup := by
  intro call before reply after step key outside
  obtain ⟨historyStep, allocationEq⟩ := step
  cases key with
  | object id =>
    exact congrArg (Option.map (StoreEntry.object (Live := Live) (Tombstone := Tombstone)))
      (lookup_frame historyStep id fun written => outside (List.mem_map_of_mem written))
  | allocation id => simp only [AllocatorStore.lookup, allocationEq]

end Silmaril.Proofs.Machine.SQLite.Handle
