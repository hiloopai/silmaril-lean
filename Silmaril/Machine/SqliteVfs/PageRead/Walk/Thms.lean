module

public import Silmaril.Machine.SqliteVfs.PageRead.Walk.Defs
import Silmaril.Proofs.Machine.SqliteVfs.PageRead.Walk.Trace

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.PageRead.Walk

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

/-- When a selector finds no next page, the walk retains the current result, backing, cache and trace. -/
theorem walk_unselected {State : Type} (handler : Handler State) (slot : SlotId)
    (current : Position State) (select : Selector) (rest : List Selector) (bytes : Bytes)
    (accepted : current.observed.result = .ok bytes)
    (unselected : select current.page bytes = none) :
    walk handler slot current (select :: rest) = current :=
  Silmaril.Proofs.Machine.SqliteVfs.PageRead.Walk.walk_unselected
    handler slot current select rest bytes accepted unselected

/-- A selected step records a valid suffix beginning from the current file. -/
theorem advance_trace {State : Type} (handler : Handler State) (slot : SlotId)
    (current next : Position State) (select : Selector)
    (advanced : advance handler slot current select = some next) :
    Trace.Valid handler current.observed.file next.observed.trace next.observed.file :=
  Silmaril.Proofs.Machine.SqliteVfs.PageRead.Walk.advance_trace
    handler slot current next select advanced

/-- A finite walk preserves trace validity for its actual result and file state. -/
theorem walk_trace {State : Type} (handler : Handler State) (slot : SlotId)
    (start : State) (current : Position State) (selectors : List Selector)
    (valid : Trace.Valid handler start current.observed.trace current.observed.file) :
    let last := walk handler slot current selectors
    Trace.Valid handler start last.observed.trace last.observed.file :=
  Silmaril.Proofs.Machine.SqliteVfs.PageRead.Walk.walk_trace
    handler slot start current selectors valid

/-- A full read-only walk reuses one owned slot, preserves the backing and records the exact ordered read list. -/
theorem walk_readOnly (capacity : Nat) (file : FileState) (cache : Cache) (slot : SlotId)
    (page : Page) (selectors : List Selector) (pages : List Page)
    (owned : cache slot = some .vacant) (full : FullRead file page)
    (plan : ReadPlan file page selectors pages) :
    let initial : Position FileState := ⟨page, fill (readOnly capacity) file cache slot page⟩
    let last := pages.getLastD page
    walk (readOnly capacity) slot initial selectors =
      ⟨last, ⟨.ok (buffer file last), file, cache.install slot last (buffer file last),
        (page :: pages).map (readExchange file)⟩⟩ :=
  Silmaril.Proofs.Machine.SqliteVfs.PageRead.Walk.walk_readOnly
    capacity file cache slot page selectors pages owned full plan

/-- The exact read list of a covered walk is valid on its unchanged snapshot. -/
theorem walk_readOnly_trace (capacity : Nat) (file : FileState) (cache : Cache)
    (slot : SlotId) (page : Page) (selectors : List Selector) (pages : List Page)
    (owned : cache slot = some .vacant) (full : FullRead file page)
    (plan : ReadPlan file page selectors pages) :
    Trace.Valid (readOnly capacity) file ((page :: pages).map (readExchange file)) file :=
  Silmaril.Proofs.Machine.SqliteVfs.PageRead.Walk.walk_readOnly_trace
    capacity file cache slot page selectors pages owned full plan

end Silmaril.Machine.SqliteVfs.PageRead.Walk
