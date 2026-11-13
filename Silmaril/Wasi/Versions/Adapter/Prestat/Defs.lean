module

public import Silmaril.Wasi.Versions.Adapter.Defs

@[expose] public section

/-!
# The adapter with `fd_prestat_get` and `fd_prestat_dir_name`

A related variant of the adapter slice of `Silmaril.Wasi.Versions.Adapter`, adding the two preview1
functions by which a program finds its preopened directories (`specs/wasi/adapter/lib.rs`,
`fd_prestat_get` and `fd_prestat_dir_name`):

* `fd_prestat_get(fd)`: for a preopen, `ok(prestat::dir { pr_name_len })` with the UTF-8 length
  of its name; otherwise `errno::badf`;
* `fd_prestat_dir_name(fd, path_len)`: for a preopen whose name fits in `path_len` bytes,
  `ok` with its name (the bytes the adapter writes); `errno::nametoolong` when it does not fit;
  otherwise `errno::badf`.

Both create the descriptor table first (`State::with`, `descriptors()`).

## Lifted shapes

Arguments: `u32 fd` (and `u32 path_len`); the output pointers are dropped. Payloads:
`variant 0 (u32 pr_name_len)` (the `prestat` union, tag `dir = 0`) and the name as a string.

## State and the names of preopens

The adapter's `Descriptors` keeps each preopen's name (`preopen_name_len` in its `File`, the path
in a side buffer). The state `PSt` extends `ASt` by `names`: the descriptors that are preopens,
with their names from `get-directories`. `watch` runs a program of the adapter and records the
answer of `get-directories` (called once, when the table is created, for the preopens at
`3, 4, …`); a successful `fd_close` removes the descriptor from `names` (`closeNames`), so that a
descriptor reused by `path_open` is not a preopen. The answers also check that the entry is open
in the table; with `closeNames` this check never fails for a name in `names`.

`bodyP` answers the two functions and runs `body` for all others; `adapterP` is the component.
`Silmaril.Wasi.Versions.Adapter.Prestat.Thms`: `adapterP_sat`, `adapterP_model`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.Adapter

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)

/-- The state of the adapter with preopen names. -/
structure PSt where
  /-- The adapter's state. -/
  a : ASt
  /-- The preopens: descriptor and name. -/
  names : List (Nat × Val)

/-- The initial state. -/
def PSt.init : PSt := ⟨ASt.init, []⟩

/-- A program of the extended adapter. -/
abbrev PProg : Type := SProg PSt imports

/-- The names of the preopens `ps`, from descriptor `i` on. -/
def namesFrom : Nat → List Val → List (Nat × Val)
  | _, [] => []
  | i, .record [_, nm] :: t => (i, nm) :: namesFrom (i + 1) t
  | i, _ :: t => namesFrom (i + 1) t

/-- The names of the preopens of a `get-directories` answer (descriptors `3, 4, …`). -/
def namesOf : Option (List Val) → List (Nat × Val)
  | some [.record ps] => namesFrom 3 ps
  | _ => []

/-- Run a program of the adapter, recording the answer of `get-directories`. -/
def watch : SProg ASt imports → List (Nat × Val) → PProg
  | .pure (s, r), w => .pure (⟨s, w⟩, r)
  | .call m k, w => .call m fun n => watch (k n) (if m.1.1 = getDirs then namesOf n else w)

/-- The table is created (as `withTable`), recording the preopens' names. -/
def ensureTable (st : PSt) : PProg :=
  watch (withTable st.a fun s _ => .pure (s, none)) st.names

/-- The name of the preopen `fd`, if any. -/
def lookupName (fd : BitVec 32) (w : List (Nat × Val)) : Option Val :=
  (w.find? (·.1 == fd.toNat)).map (·.2)

/-- A closed table entry. -/
def isClosedD : Desc → Bool
  | .closed => true
  | _ => false

/-- The UTF-8 length of a name. -/
def nameLen (nm : Val) : Nat := ((charsOf nm).map Char.utf8Size).sum

/-- The name of an open preopen `fd`. -/
def preopenName (st : PSt) (fd : BitVec 32) : Option Val :=
  match st.a.table with
  | some t => if isClosedD (getD t fd) then none else lookupName fd st.names
  | none => none

/-- **`fd_prestat_get`**, once the table exists. -/
def prestatGet (st : PSt) : List Val → PProg
  | [.u32 fd] =>
    match preopenName st fd with
    | some nm => .pure (st, P1.okAns (some (.variant 0 (some (.u32 (BitVec.ofNat 32 (nameLen nm)))))))
    | none => .pure (st, P1.errAns P1.eBadf)
  | _ => .pure (st, P1.errAns P1.eInval)

/-- `errno::nametoolong`. -/
def eNametoolong : Nat := P1.errno "nametoolong"

/-- **`fd_prestat_dir_name`**, once the table exists. -/
def prestatDirName (st : PSt) : List Val → PProg
  | [.u32 fd, .u32 len] =>
    match preopenName st fd with
    | some nm =>
      if nameLen nm ≤ len.toNat then .pure (st, P1.okAns (some nm))
      else .pure (st, P1.errAns eNametoolong)
    | none => .pure (st, P1.errAns P1.eBadf)
  | _ => .pure (st, P1.errAns P1.eInval)

/-- A successful `fd_close(fd)` removes `fd` from the preopens. -/
def closeNames (st : PSt) (n : String) (a : List Val) (r : Option (List Val)) : PSt :=
  match n == "fd_close", a, r with
  | true, [.u32 fd], some [.variant 0 none] => { st with names := st.names.filter (·.1 != fd.toNat) }
  | _, _, _ => st

/-- **The adapter with `fd_prestat_get` and `fd_prestat_dir_name`.** -/
def bodyP : SBody PSt imports P1.imports := fun st q =>
  if q.1.1.fn = "fd_prestat_get" then (ensureTable st).bind fun x => prestatGet x.1 q.2
  else if q.1.1.fn = "fd_prestat_dir_name" then
    (ensureTable st).bind fun x => prestatDirName x.1 q.2
  else (watch (body st.a q) st.names).bind fun x => .pure (closeNames x.1 q.1.1.fn q.2 x.2, x.2)

/-- **The adapter component with preopens.** -/
def adapterP : Strategy (nsig imports) (nsig P1.imports) := ofSBody bodyP PSt.init

end Silmaril.Wasi.Versions.Adapter
