module

public import Silmaril.Wasi.Versions.FsMore.Defs
public import Silmaril.Wasi.Versions.P3.Defs

@[expose] public section

/-!
# The 0.3 `read-directory` stream: a loose theory and a host

In 0.3 (`vendor/wasi/0.3.2/filesystem/types.wit`)

```
read-directory: func() -> tuple<stream<directory-entry>, future<result<_, error-code>>>;
```

"This always returns a new stream which starts at the beginning of the directory. Multiple
streams may be active on the same directory, and they do not interfere with each other." The
entries are read with the Component Model built-in `stream.read(stream, count)`, answered with
the packed copy result and the items (as `P3.fsReadTh3` reads bytes). `FsMore.fsTh3` leaves
this function unconstrained: its tuple answer never matches the 0.2 clause.

* **The theory** `dir3Th T` extends `FsMore.fsTh3 T` (its state and checks are kept as the
  first component; `dir3Th_fs` below says the first component evolves exactly as in
  `fsTh3`): a `read-directory` of a descriptor at a directory of the tree queues the
  directory's existing entries with their kinds (`FsMore.entriesOf`, the same entries as the
  0.2 `read-directory`) on the stream's readable end. A `stream.read` on such a stream that
  completes with `k` items needs `k` entries to be pending and the items to be the next `k`;
  one that reports the stream dropped needs none pending. Blocked and cancelled reads are not
  constrained, nor is the future.
* **The host** `dir3Impl T pre` is `FsMore.fsImpl3 T pre` with `read-directory` answering a
  fresh pair of handles and `stream.read` on a directory stream delivering one entry at a time,
  and `DROPPED` when none is left.

As in `FsMore`, the order of the entries is the order of the directory's names in `T` (the
tree is a parameter, so this is the order the file system lists them in); `.` and `..` are
never names of `T`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.FsDir3

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasm.Component.Async (CopyResult packCopy)
open Silmaril.Wasi.Versions.Net (gated)
open Silmaril.Wasi.Versions.FsMore
open Silmaril.Wasi.Versions.P3 (natV natOf copyOf cStreamRead)

/-! ## Values -/

/-- A `directory-entry { type, name }` value. -/
def entV (e : Comp × Nat) : Val := .record [.variant e.2 none, strC e.1]

/-- The entry of a `directory-entry` value. -/
def entOf : Val → Option (Comp × Nat)
  | .record [.variant k none, nm] => (charsV nm).map fun n => (n, k)
  | _ => none

/-- The entries of a list of `directory-entry` values. -/
def entsOf : Val → Option (List (Comp × Nat))
  | .record es => es.mapM entOf
  | _ => none

/-- The value of `k` in an association list keyed by numbers. -/
def nlook {α : Type} (k : Nat) (l : List (Nat × α)) : Option α :=
  (l.find? (·.1 == k)).map (·.2)

/-! ## The theory -/

/-- The state: the `FsMore` state, and the pending entries of each directory stream. -/
structure D3St where
  fs : FsSt := {}
  strs : List (Nat × List (Comp × Nat)) := []

/-- The pending entries of the stream read in `a`. -/
def pendingOf (q : D3St) (a : List Val) : Option (List (Comp × Nat)) :=
  match a with
  | rv :: _ => (natOf rv).bind (nlook · q.strs)
  | [] => none

/-- The next stream table. -/
def strsNext (T : Tree) (q : D3St) : WEv → List (Nat × List (Comp × Nat))
  | .imp f a r =>
    if f = v3.readDir then
      (match selfPath q.fs a, r with
       | some p, some [.record [rv, _]] =>
         (match natOf rv, nodeAt T q.fs p with
          | some r', some (.dir ns) => (r', entriesOf v3 T q.fs p ns) :: q.strs
          | _, _ => q.strs)
       | _, _ => q.strs)
    else if f = cStreamRead then
      (match a, r with
       | rv :: _, some [pv, _] =>
         (match natOf rv, (natOf pv).bind copyOf with
          | some r', some (some (.completed, k)) =>
            (match nlook r' q.strs with
             | some l => (r', l.drop k) :: q.strs
             | none => q.strs)
          | _, _ => q.strs)
       | _, _ => q.strs)
    else q.strs
  | _ => q.strs

/-- The next state. -/
def d3Next (T : Tree) (q : D3St) (e : WEv) : D3St := ⟨fsNext v3 T q.fs e, strsNext T q e⟩

/-- The check of a `stream.read` answer on a stream with the pending entries `l`. -/
def drChk (l : List (Comp × Nat)) : Option (List Val) → Bool
  | some [pv, items] =>
    (match (natOf pv).bind copyOf with
     | some (some (.completed, k)) => decide (k ≤ l.length) && entsOf items == some (l.take k)
     | some (some (.dropped, _)) => l.isEmpty
     | _ => true)
  | _ => true

/-- The check of the directory streams. -/
def dirOk (q : D3St) : WEv → Bool
  | .imp f a r =>
    if f = cStreamRead then
      (match pendingOf q a with
       | some l => drChk l r
       | none => true)
    else true
  | _ => true

/-- The check: `FsMore`'s, and the directory streams. -/
def d3Ok (T : Tree) (q : D3St) (e : WEv) : Bool := FsMore.fsOk v3 T q.fs e && dirOk q e

/-- **The 0.3 filesystem theory with the `read-directory` stream**, over the tree `T`. -/
def dir3Th (T : Tree) : Protocol D3St WEv := gated {} (d3Next T) (d3Ok T)

/-! ## The host -/

/-- The state after the answers `p`. -/
def d3State (T : Tree) (p : List WEv) : D3St := p.foldl (d3Next T) {}

/-- The answer of a `stream.read` with the pending entries `l`, asking for `n` items: one
entry (none if `n = 0`), or `DROPPED` when none is left. -/
def readA (l : List (Comp × Nat)) (n : Option Nat) : Option (List Val) :=
  if l.isEmpty then some [natV (packCopy .dropped 0), .record []]
  else
    let k := if n = some 0 then 0 else 1
    some [natV (packCopy .completed k), .record ((l.take k).map entV)]

/-- **The concrete host**: `FsMore.fsImpl3` with the `read-directory` stream. -/
def dir3Impl (T : Tree) (pre : List Comp) : Impl := fun p f a =>
  let q := d3State T p
  if f = v3.readDir then some [.record [natV (2 * p.length + 1), natV (2 * p.length + 2)]]
  else if f = cStreamRead then
    (match pendingOf q a with
     | some l => readA l (a[1]?.bind natOf)
     | none => none)
  else fsImpl3 T pre p f a

end Silmaril.Wasi.Versions.FsDir3
