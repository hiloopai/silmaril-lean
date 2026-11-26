module

import Silmaril.Machine.SQLite.Handle.Thms
import Silmaril.Machine.SQLite.Allocator.Thms
import Silmaril.Machine.SQLite.GlobalState.Store.Allocator.Thms

namespace Silmaril.Machine.SQLite.Handle.Checks

open Silmaril.Machine.SQLite.GlobalState Silmaril.Semantics.Resource

private abbrev Other : ObjectKind → Type := fun _ => Unit
private abbrev H := HistoryOf Nat Nat Other
private abbrev World := Allocator.State Nat Nat (Payload Nat Nat Other) Nat Nat

private def actor : Nat := 7
private def registry : List Nat := [9]
private def readyData : Connection Nat := ⟨actor, .ready⟩
private def empty : H := History.empty
private theorem empty_vfs : empty.Fresh 9 := History.lookup_empty 9
private def initial : H := empty.allocate 9 .vfs () empty_vfs

private theorem initial_vfs : initial.lookup 9 = some (.present ⟨.vfs, .live, ()⟩) :=
  History.lookup_allocate_self empty 9 .vfs () empty_vfs

private def seenKind (entry : Option (HistoryEntry (Payload Nat Nat Other))) : Option ObjectKind :=
  (entry.bind HistoryEntry.toObject).map Object.kind

private theorem no_child_after_allocate {history : H} {id : Nat} {kind : ObjectKind}
    {payload : Payload Nat Nat Other kind} (fresh : history.Fresh id)
    (prior : ∀ token child, ¬ ChildAt history token child)
    (nonChild : ∀ k : ChildKind, kind ≠ k.objectKind) (token : Nat) (child : Child Nat Nat) :
    ¬ ChildAt (history.allocate id kind payload fresh) token child := by
  intro present
  by_cases h : token = id
  · subst token
    have mismatch := congrArg seenKind ((History.lookup_allocate_self ..).symm.trans present)
    exact nonChild child.kind (Option.some.inj mismatch)
  · exact prior token child ((History.lookup_allocate_of_ne history h kind payload fresh).symm.trans present)

private theorem no_initial_children (id : Nat) (child : Child Nat Nat) : ¬ ChildAt initial id child :=
  no_child_after_allocate _ (fun token _ present => by
    have impossible := (History.lookup_empty (Payload := Payload Nat Nat Other) token).symm.trans present
    cases impossible) (by intro k; cases k <;> decide) id child

private theorem vacant_of_no_children {history : H} {db : Nat} (fresh : history.Fresh db)
    (prior : ∀ id child, ¬ ChildAt history id child) : Vacant history db :=
  ⟨fresh, fun ⟨id, child, live, _⟩ => prior id child live,
    fun ⟨id, child, live, _⟩ => prior id child live⟩

private theorem initial_fresh {id : Nat} (other : id ≠ 9) : initial.Fresh id :=
  (History.lookup_allocate_of_ne empty other .vfs () empty_vfs).trans (History.lookup_empty id)

private theorem fresh1 : initial.Fresh 1 := initial_fresh (by decide)

private theorem vacant1 : Vacant initial 1 := vacant_of_no_children fresh1 no_initial_children
private def first : H := initial.allocate 1 .connection readyData fresh1

private theorem no_first_children : ∀ token child, ¬ ChildAt first token child :=
  no_child_after_allocate fresh1 no_initial_children (by intro k; cases k <;> decide)

private theorem first_fresh {id : Nat} (notFirst : id ≠ 1) (notVfs : id ≠ 9) : first.Fresh id :=
  (History.lookup_allocate_of_ne initial notFirst .connection readyData fresh1).trans
    (initial_fresh notVfs)

private theorem fresh2 : first.Fresh 2 := first_fresh (by decide) (by decide)

private def before : H := first.allocate 2 .connection readyData fresh2

private theorem no_prior_children : ∀ token child, ¬ ChildAt before token child :=
  no_child_after_allocate fresh2 no_first_children (by intro k; cases k <;> decide)

private theorem ready1 : MayCommand actor before 1 :=
  ⟨(History.lookup_allocate_of_ne first (by decide) .connection readyData fresh2).trans
    (History.lookup_allocate_self ..), rfl,
    fun ⟨id, child, live, _⟩ => no_prior_children id child live⟩

private theorem ready2 : MayCommand actor before 2 :=
  open_ready (.openReady (registry := registry) (vacant_of_no_children fresh2 no_first_children))

private theorem fresh3 : before.Fresh 3 :=
  (History.lookup_allocate_of_ne first (by decide : (3 : Nat) ≠ 2) .connection readyData fresh2).trans
    (first_fresh (by decide) (by decide))

private theorem child_object_inj {left right : Child Nat Nat}
    (same : left.object (Other := Other) = right.object) : left = right := by
  cases left <;> cases right <;> cases same <;> rfl

private theorem identify_child (added : Child Nat Nat) {id : Nat} {entry : Child Nat Nat}
    (present : ChildAt (before.allocate 3 added.kind.objectKind added.payload fresh3) id entry) :
    id = 3 ∧ entry = added := by
  by_cases equal : id = 3
  · subst id
    have same := present.symm.trans (History.lookup_allocate_self ..)
    exact ⟨rfl, child_object_inj (HistoryEntry.present.inj (Option.some.inj same))⟩
  · exact (no_prior_children id entry
      ((History.lookup_allocate_of_ne before equal _ _ fresh3).symm.trans present)).elim

private def closeOnly : H := initial.allocate 1 .connection ⟨actor, .closeOnly⟩ fresh1

example : ∃ after, Step actor registry (.close .legacy (some 1)) closeOnly (.status .ok) after ∧
    after.lookup 1 = some (.freed .connection) ∧
    ¬ MayCommand actor closeOnly 1 := by
  obtain ⟨allowed, denied, idle⟩ :=
    open_error_close_only (.openCloseOnly (registry := registry) vacant1)
  have close : Step actor registry (.close .legacy (some 1)) closeOnly (.status .ok)
      (closeOnly.free 1 allowed.present) := .closeDestroy allowed idle
  exact ⟨_, close, close_idle_destroys close idle, denied⟩

example : Step actor registry (.close .legacy none) before (.status .ok) before := .closeNull

example : Step actor registry (.prepare 1 .empty) before (.prepared .ok none) before :=
  .prepareEmpty ready1

private def statement : Child Nat Nat := .statement ⟨1, actor⟩
private def withStmt : H := before.allocate 3 statement.kind.objectKind statement.payload fresh3
private theorem statement_at : ChildAt withStmt 3 statement := History.lookup_allocate_self ..

example : Step actor registry (.prepare 1 .statement) before (.prepared .ok (some 3)) withStmt :=
  .prepareStatement ready1 fresh3

private theorem statement_closable : Closable actor withStmt 1 readyData := by
  refine ⟨(History.lookup_allocate_of_ne before (by decide) _ _ fresh3).trans ready1.present, rfl, ?_⟩
  rintro ⟨id, child, present, borrowed⟩
  obtain ⟨_, rfl⟩ := identify_child statement present
  cases borrowed

example : Step actor registry (.close .legacy (some 1)) withStmt (.status .busy) withStmt :=
  close_busy_iff.mpr ⟨rfl, child_blocks_source statement_at, _, statement_closable⟩

private def zombie : H := withStmt.updatePresent 1 statement_closable.present .zombie readyData

private theorem defer_close :
    Step actor registry (.close .deferred (some 1)) withStmt (.status .ok) zombie :=
  .closeZombie statement_closable (child_blocks_source statement_at)

private theorem zombie_at : ConnectionAt zombie 1 .zombie readyData :=
  History.lookup_updatePresent_self ..

example (reply : Reply Nat) (after : H) :
    ¬ Step actor registry (.prepare 1 .empty) zombie reply after :=
  fun step => zombie_no_commands zombie_at (prepare_requires_command step)

private theorem zombie_child {id : Nat} {child : Child Nat Nat}
    (present : ChildAt zombie id child) : id = 3 ∧ child = statement := by
  by_cases equal : id = 1
  · subst id
    have mismatch := congrArg seenKind (zombie_at.symm.trans present)
    cases child <;> cases mismatch
  · exact identify_child statement
      ((History.lookup_updatePresent_of_ne withStmt equal statement_closable.present .zombie readyData).symm.trans
        present)

example (reply : Reply Nat) (after : H) :
    ¬ Step 8 registry (.release .statement (some 3)) zombie reply after := by
  intro step
  obtain ⟨_, present, _, allowed⟩ := release_requires_owner step
  obtain ⟨_, rfl⟩ := zombie_child present
  exact (by decide : actor ≠ 8) allowed.owned

private theorem release_statement : ∃ after,
    Step actor registry (.release .statement (some 3)) zombie (.released .error (some 1)) after ∧
    after.lookup 1 = some (.freed .connection) ∧ after.lookup 3 = some (.freed .statement) := by
  have present : ChildAt zombie 3 statement :=
    (History.lookup_updatePresent_of_ne withStmt (by decide) statement_closable.present .zombie readyData).trans
      statement_at
  have allowed : MayRelease actor zombie statement := by
    refine ⟨rfl, ?_, fun _ impossible => by cases impossible⟩
    rintro ⟨id, child, known, borrowed⟩
    obtain ⟨_, rfl⟩ := zombie_child known
    cases borrowed
  exact final_dependent_reaps_zombie present allowed zombie_at fun _ _ known _ => (zombie_child known).1

private def historyWorld (history : H) : World := ⟨history, ∅⟩

private def handles : Contract World (Call Nat) (Reply Nat) (StoreId Nat Nat) :=
  contract actor registry

private def closeThenFinalize := handles.seq handles fun _ _ => .release .statement (some 3)

example : ∃ after : World,
    closeThenFinalize.step (.close .deferred (some 1)) (historyWorld withStmt)
      (.status .ok, .released .error (some 1)) after ∧
    after.lookup (.object 2) = (historyWorld withStmt).lookup (.object 2) ∧
    ¬ after.objectHistory.Fresh 1 := by
  obtain ⟨result, finalized, retired, _⟩ := release_statement
  have two : closeThenFinalize.step (.close .deferred (some 1)) (historyWorld withStmt)
      (.status .ok, .released .error (some 1)) (historyWorld result) :=
    ⟨historyWorld zombie, ⟨defer_close, rfl⟩, ⟨finalized, rfl⟩⟩
  have bothFrame : closeThenFinalize.Frames AllocatorStore.lookup := Contract.seq_frames frames frames
  exact ⟨_, two, bothFrame two (.object 2) (by decide), stale_not_fresh retired⟩

private def blob : Child Nat Nat := .blob ⟨1, actor⟩
private def withBlob : H := before.allocate 3 blob.kind.objectKind blob.payload fresh3

example : Step actor registry (.openBlob 1) before (.created 3) withBlob ∧ Busy withBlob 1 :=
  ⟨.openBlob ready1 fresh3, child_blocks_source (child := blob) (History.lookup_allocate_self ..)⟩

private def backup : Backup Nat Nat := ⟨⟨1, actor⟩, 2⟩
private def withBackup : H :=
  before.allocate 3 (Child.backup backup).kind.objectKind (Child.backup backup).payload fresh3
private theorem backup_at : ChildAt withBackup 3 (.backup backup) := History.lookup_allocate_self ..

private theorem destination_borrowed : DestinationBorrowed withBackup 2 :=
  ⟨3, .backup backup, backup_at, rfl⟩

example : Step actor registry (.backupInit 1 2) before (.created 3) withBackup ∧ Busy withBackup 1 ∧
    ¬ Busy withBackup 2 := by
  refine ⟨.backupInit ready1 ready2 (by decide) fresh3, child_blocks_source backup_at, ?_⟩
  rintro ⟨id, child, present, source⟩
  obtain ⟨_, rfl⟩ := identify_child (.backup backup) present
  exact (by decide : (1 : Nat) ≠ 2) source

example (mode : CloseMode) (result : Reply Nat) (after : H) :
    ¬ Step actor registry (.close mode (some 2)) withBackup result after :=
  close_borrowed_inapplicable destination_borrowed

example (status : ReleaseStatus) :
    ∃ after owner, Step actor registry (.release .backup (some 3)) withBackup
      (.released status none) after ∧ ConnectionAt after 2 .live ⟨owner, .ready⟩ ∧
      after.lookup 3 = some (.freed .backup) := by
  have destination : ConnectionAt withBackup 2 .live readyData :=
    (History.lookup_allocate_of_ne before (by decide) _ _ fresh3).trans ready2.present
  have allowed : MayRelease actor withBackup (.backup backup) := by
    refine ⟨rfl, ?_, ?_⟩
    · rintro ⟨id, child, known, borrow⟩
      obtain ⟨_, rfl⟩ := identify_child (.backup backup) known
      have impossible : (2 : Nat) = 1 := Option.some.inj borrow
      exact (by decide : (2 : Nat) ≠ 1) impossible
    · intro dst found
      have same : 2 = dst := Option.some.inj found
      subst dst
      exact ⟨by decide, actor, destination⟩
  have src : ConnectionAt (withBackup.free 3 backup_at) 1 .live readyData :=
    (History.lookup_free_of_ne withBackup (by decide) backup_at).trans
      ((History.lookup_allocate_of_ne before (by decide) _ _ fresh3).trans ready1.present)
  obtain ⟨owner, _, liveAfter⟩ := backup_finish_destination backup_at allowed (.ready src)
  have finish : Step actor registry (.release .backup (some 3)) withBackup
      (.released status none) (withBackup.free 3 backup_at) :=
    .release backup_at allowed (.ready src)
  exact ⟨_, owner, finish, liveAfter, release_disposes finish⟩

private theorem registry_valid : Registered registry initial := by
  refine ⟨by decide, ?_⟩
  intro id member
  have equal : id = 9 := by simpa [registry] using member
  subst id
  exact ⟨(), initial_vfs⟩

private def allocator : Allocator.Scope Nat Nat := ⟨0, actor, 64, by decide⟩
private def block : Allocator.Block Nat Nat := allocator.block 4 8 (by decide) (by decide)
private def allocated : World := (historyWorld initial).writeAllocation 9 (.live block)
private def borrowThenMalloc := handles.seq (Allocator.contract allocator) fun _ _ => .malloc 4

example : borrowThenMalloc.step .findDefaultVfs (historyWorld initial)
      (.borrowedVfs (some 9), .pointer (some 9)) allocated ∧
    allocated.lookup (.object 9) = some (.object (.present ⟨.vfs, .live, ()⟩)) := by
  have find : Step actor registry .findDefaultVfs initial (.borrowedVfs (some 9)) initial :=
    .findDefaultVfs registry_valid
  have alloc : Allocator.Step allocator (.malloc 4) (historyWorld initial) (.pointer (some 9)) allocated :=
    .mallocSuccess (by decide) (by decide) (by decide) (AllocationHistory.lookup_empty 9)
  have two : borrowThenMalloc.step .findDefaultVfs (historyWorld initial)
      (.borrowedVfs (some 9), .pointer (some 9)) allocated :=
    ⟨historyWorld initial, ⟨find, rfl⟩, alloc⟩
  have bothFrame : borrowThenMalloc.Frames AllocatorStore.lookup :=
    Contract.seq_frames frames Allocator.frames
  refine ⟨two, (bothFrame two (.object 9) (by decide)).trans ?_⟩
  exact congrArg (Option.map (StoreEntry.object (Live := Allocator.Block Nat Nat) (Tombstone := Unit)))
    initial_vfs

#print axioms open_ready
#print axioms open_error_close_only
#print axioms prepare_requires_command
#print axioms prepare_empty_post
#print axioms close_null_iff
#print axioms close_busy_iff
#print axioms close_borrowed_inapplicable
#print axioms zombie_no_commands
#print axioms close_deferred_busy
#print axioms close_idle_destroys
#print axioms reap_idle_zombie
#print axioms release_requires_owner
#print axioms release_disposes
#print axioms final_dependent_reaps_zombie
#print axioms backup_finish_destination
#print axioms lookup_frame
#print axioms fresh_before
#print axioms stale_not_fresh
#print axioms child_blocks_source
#print axioms find_default_iff
#print axioms find_default_live
#print axioms registered_preserved
#print axioms frames

end Silmaril.Machine.SQLite.Handle.Checks
