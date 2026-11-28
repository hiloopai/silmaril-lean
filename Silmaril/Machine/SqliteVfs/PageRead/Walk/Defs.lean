module

public import Silmaril.Machine.SqliteVfs.PageRead.Release.Defs

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.PageRead.Walk

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

abbrev Selector := Page → Bytes → Option Page

structure Position (State : Type) where
  page : Page
  observed : Outcome State

/-- A selector consumes the accepted bytes before the current slot is
released. A selected read uses the actual file and released cache. -/
def advance {State : Type} (handler : Handler State) (slot : SlotId)
    (current : Position State) (select : Selector) : Option (Position State) := do
  let .ok bytes := current.observed.result | none
  let page ← select current.page bytes
  let .ok released := Release.release current.observed.cache slot current.page | none
  pure ⟨page, fill handler current.observed.file released slot page⟩

/-- Run the finite selector list, keeping the previous prefix if no further
read is attempted and the raw exchange and state of any attempted read. -/
def walk {State : Type} (handler : Handler State) (slot : SlotId)
    (current : Position State) : List Selector → Position State
  | [] => current
  | select :: rest =>
    match advance handler slot current select with
    | none => current
    | some next =>
      let last := walk handler slot next rest
      ⟨last.page, { last.observed with trace := current.observed.trace ++ last.observed.trace }⟩

def FullRead (file : FileState) (page : Page) : Prop :=
  page.Admitted ∧ (file.mode page.handle).isNone = false ∧
    page.offset + page.size ≤ file.bytes.length

def buffer (file : FileState) (page : Page) : Bytes :=
  readBytes file.bytes page.offset page.size

def readExchange (file : FileState) (page : Page) : Exchange :=
  ⟨page.request, .ok (buffer file page)⟩

/-- Per-hop selection from the current page's exact snapshot buffer and
admission, liveness and full-presence premises for the selected read. -/
inductive ReadPlan (file : FileState) : Page → List Selector → List Page → Prop where
  | nil (page : Page) : ReadPlan file page [] []
  | cons {page next : Page} {select : Selector} {rest : List Selector} {pages : List Page} :
      select page (buffer file page) = some next → FullRead file next →
      ReadPlan file next rest pages → ReadPlan file page (select :: rest) (next :: pages)

end Silmaril.Machine.SqliteVfs.PageRead.Walk
