module

public import Silmaril.Machine.SqliteVfs.PageRead.Walk.Defs
import Silmaril.Machine.SqliteVfs.PageRead.Release.Thms
import Silmaril.Machine.SqliteVfs.PageRead.Thms

@[expose] public section

namespace Silmaril.Proofs.Machine.SqliteVfs.PageRead.Walk

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.Walk

theorem walk_unselected {State : Type} (handler : Handler State) (slot : SlotId)
    (current : Position State) (select : Selector) (rest : List Selector) (bytes : Bytes)
    (accepted : current.observed.result = .ok bytes)
    (unselected : select current.page bytes = none) :
    walk handler slot current (select :: rest) = current := by
  simp [walk, advance, accepted, unselected]

theorem advance_trace {State : Type} (handler : Handler State) (slot : SlotId)
    (current next : Position State) (select : Selector)
    (advanced : advance handler slot current select = some next) :
    Trace.Valid handler current.observed.file next.observed.trace next.observed.file := by
  cases result : current.observed.result with
  | error reason => simp [advance, result] at advanced
  | ok bytes =>
    cases selected : select current.page bytes with
    | none => simp [advance, result, selected] at advanced
    | some page =>
      cases release : Release.release current.observed.cache slot current.page with
      | error reason => simp [advance, result, selected, release] at advanced
      | ok released =>
        simp [advance, result, selected, release] at advanced
        subst next
        exact fill_trace handler current.observed.file released slot page

private theorem append_valid {State : Type} {handler : Handler State} {a b c : State}
    {first second : Trace} (head : Trace.Valid handler a first b)
    (tail : Trace.Valid handler b second c) : Trace.Valid handler a (first ++ second) c := by
  induction head with
  | nil => exact tail
  | cons step _ ih => exact .cons step (ih tail)

theorem walk_trace {State : Type} (handler : Handler State) (slot : SlotId)
    (start : State) (current : Position State) (selectors : List Selector)
    (valid : Trace.Valid handler start current.observed.trace current.observed.file) :
    let last := walk handler slot current selectors
    Trace.Valid handler start last.observed.trace last.observed.file := by
  induction selectors generalizing start current with
  | nil => exact valid
  | cons select rest ih =>
    cases step : advance handler slot current select with
    | none => simpa only [walk, step] using valid
    | some next =>
      have suffix := ih current.observed.file next (advance_trace handler slot current next select step)
      simpa only [walk, step] using append_valid valid suffix

theorem walk_readOnly (capacity : Nat) (file : FileState) (cache : Cache) (slot : SlotId)
    (page : Page) (selectors : List Selector) (pages : List Page)
    (owned : cache slot = some .vacant) (full : FullRead file page)
    (plan : ReadPlan file page selectors pages) :
    let initial : Position FileState := ⟨page, fill (readOnly capacity) file cache slot page⟩
    let last := pages.getLastD page
    walk (readOnly capacity) slot initial selectors =
      ⟨last, ⟨.ok (buffer file last), file, cache.install slot last (buffer file last),
        (page :: pages).map (readExchange file)⟩⟩ := by
  induction plan with
  | nil current =>
    obtain ⟨admitted, live, complete⟩ := full
    have filled := readOnly_fill capacity file cache slot current owned admitted live
    simp [walk, buffer, readExchange, complete] at filled ⊢
    exact filled
  | @cons current next select rest pages selected nextFull tail ih =>
    have nextPlan := ih nextFull
    obtain ⟨admitted, live, complete⟩ := full
    obtain ⟨nextAdmitted, nextLive, nextComplete⟩ := nextFull
    obtain ⟨firstFill, released, _, _⟩ :=
      Release.readOnly_release_and_refill capacity file cache slot current next owned
        admitted nextAdmitted live nextLive complete nextComplete
    let first : Position FileState := ⟨current, fill (readOnly capacity) file cache slot current⟩
    let second : Position FileState := ⟨next, fill (readOnly capacity) file cache slot next⟩
    have step : advance (readOnly capacity) slot first select = some second := by
      have accepted : (fill (readOnly capacity) file cache slot current).result =
          .ok (buffer file current) :=
        congrArg Outcome.result firstFill
      have unchanged : (fill (readOnly capacity) file cache slot current).file = file :=
        congrArg Outcome.file firstFill
      simp [advance, accepted, selected, first, second, unchanged, released]
    change walk (readOnly capacity) slot first (select :: rest) = _
    change walk (readOnly capacity) slot second rest = _ at nextPlan
    have firstTrace : first.observed.trace = [readExchange file current] :=
      congrArg Outcome.trace firstFill
    simp only [walk, step, nextPlan, firstTrace, List.getLastD_cons, List.map_cons, List.singleton_append]

theorem walk_readOnly_trace (capacity : Nat) (file : FileState) (cache : Cache)
    (slot : SlotId) (page : Page) (selectors : List Selector) (pages : List Page)
    (owned : cache slot = some .vacant) (full : FullRead file page)
    (plan : ReadPlan file page selectors pages) :
    Trace.Valid (readOnly capacity) file ((page :: pages).map (readExchange file)) file := by
  have valid := walk_trace (readOnly capacity) slot file
    ⟨page, fill (readOnly capacity) file cache slot page⟩ selectors
    (fill_trace (readOnly capacity) file cache slot page)
  dsimp only at valid
  rw [walk_readOnly capacity file cache slot page selectors pages owned full plan] at valid
  exact valid

end Silmaril.Proofs.Machine.SqliteVfs.PageRead.Walk
