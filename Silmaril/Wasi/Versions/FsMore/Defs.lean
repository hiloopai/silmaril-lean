module

public import Silmaril.Wasi.Versions.Net.Defs

@[expose] public section

/-!
# `wasi:filesystem` beyond the read slice: a loose theory and a host, for 0.2 and 0.3

The earlier filesystem results cover reading (`P3OverP2.fsRead2`, `P3.fsReadTh3`) and the result
shapes of `open-at`/`read`/`write` (`Theory.fsTyped`). This module adds a behavioural theory of
the descriptor functions that look at the file system: `get-directories`, `open-at`, `stat`,
`stat-at`, `get-type`, and in 0.2 also `read`, `write`, `read-directory` and
`directory-entry-stream.read-directory-entry` (checked against
`specs/wasi/0.2.12/filesystem/{types,preopens}.wit`, `specs/wasi/v0.2.9/…` has the same
functions, and `specs/wasi/0.3.2/filesystem/types.wit`).

## The model

* **A tree** `T : Tree` says which paths (lists of components, a component a list of chars) are
  files (with contents) and directories (with the names of their children). Nothing relates a
  directory's names to the paths below it; the theory reads both as given.
* **The theory state** `FsSt`: the path of each descriptor the theory has seen opened, the
  pending entries of each directory-entry stream, and an overlay of the contents written so far.
  `nodeAt T q p` is the overlay over `T`.
* **One theory for both versions** `fsThV V T`, parametric in the version data `V : FsVer` (the
  interface names, the case numbers of `directory`, `regular-file` and `no-entry` in that
  version's `descriptor-type` and `error-code`). `fsTh2 T := fsThV v2 T` and
  `fsTh3 T := fsThV v3 T`. The 0.3 functions are `async` and are observed sync-lowered, as in
  `Udp`; their results have the 0.2 shapes. 0.3 has no `read`, `write`, `read-directory-entry`
  and its `read-directory` returns a stream: the 0.2-only clauses never fire on 0.3 events.

## The checks (gated: only these answers are constrained)

* `get-directories`: every preopen named `n` is a directory `[n]` of `T`; the descriptors are
  recorded at `[n]`.
* `open-at(self, path-flags, path, open-flags, flags)` on a known descriptor, with a relative
  path without `..` and without the `create` flag: `ok(d)` needs the path to exist (and to be a
  directory when the `directory` flag is set), and records `d`; `error(no-entry)` needs it to be
  absent. With `create`, or `..`, nothing is checked and nothing recorded.
* `stat`, `stat-at`, `get-type` on a known path: an `ok` answer needs the node to exist, its
  `type` to be the node's kind and, for a file, its `size` to be the current content length.
* `read(self, length, offset)` (0.2) on a file: `ok((data, eof))` needs `data` to be the
  contents from `offset`, at most `length` bytes, and `eof` only at the end.
* `write(self, buffer, offset)` (0.2) on a file: `ok(n)` needs `n ≤ |buffer|`, and the first `n`
  bytes are written at `offset` in the overlay (extending with zeros).
* `read-directory(self)` (0.2): `ok(s)` needs a directory; `s` is recorded with the directory's
  entries that exist, with their kinds. `read-directory-entry(s)`: `ok(some({type, name}))` is
  the next pending entry, `ok(none)` needs none pending.

Errors other than `no-entry` of `open-at`, traps, ill-shaped answers and other functions are not
constrained.

## The host

`fsImplV V T pre` answers from the theory state of the answers so far: fresh handles (the
position in the trace), the preopens `pre` that are directories of `T`, the node's kind and size,
the contents, the full buffer written, the directory's entries one by one, `error(no-entry)` for
absent paths and `error(bad-descriptor)` for unknown descriptors.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.FsMore

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.Net (gated lookup selfH)

/-! ## Trees -/

/-- A path component. -/
abbrev Comp : Type := List Char

/-- A path: its components from a preopen's name. -/
abbrev Path : Type := List Comp

/-- A node of the tree: a file with its contents, or a directory with the names of its
children. -/
inductive Node where
  | file (bs : List (BitVec 8))
  | dir (names : List Comp)

/-- A file system tree. -/
abbrev Tree : Type := Path → Option Node

/-! ## Versions -/

/-- What differs between the 0.2 and 0.3 functions of this slice. -/
structure FsVer where
  /-- `wasi:filesystem/types` with the version suffix. -/
  types : String
  /-- `wasi:filesystem/preopens` with the version suffix. -/
  preopens : String
  /-- The case of `descriptor-type.directory`. -/
  dirK : Nat
  /-- The case of `descriptor-type.regular-file`. -/
  fileK : Nat
  /-- The case of `error-code.no-entry`. -/
  noEntry : Nat
  /-- The case of `error-code.bad-descriptor`. -/
  badDesc : Nat
  /-- The case of `error-code.not-directory`. -/
  notDir : Nat

/-- WASI 0.2 (`specs/wasi/0.2.12/filesystem/types.wit`: `enum descriptor-type { unknown,
block-device, character-device, directory, fifo, symbolic-link, regular-file, socket }`,
`enum error-code { access, would-block, already, bad-descriptor, …, no-entry (20), … }`). -/
def v2 : FsVer := ⟨"wasi:filesystem/types", "wasi:filesystem/preopens", 3, 6, 20, 3, 24⟩

/-- WASI 0.3 (`specs/wasi/0.3.2/filesystem/types.wit`: `variant descriptor-type {
block-device, character-device, directory, fifo, symbolic-link, regular-file, socket,
other(option<string>) }`, `variant error-code { access, already, bad-descriptor, …,
no-entry (19), … }`). -/
def v3 : FsVer :=
  ⟨"wasi:filesystem/types@0.3.2", "wasi:filesystem/preopens@0.3.2", 2, 5, 19, 2, 23⟩

def FsVer.getDirs (V : FsVer) : FnName := ⟨V.preopens, "get-directories"⟩
def FsVer.openAt (V : FsVer) : FnName := ⟨V.types, "[method]descriptor.open-at"⟩
def FsVer.stat (V : FsVer) : FnName := ⟨V.types, "[method]descriptor.stat"⟩
def FsVer.statAt (V : FsVer) : FnName := ⟨V.types, "[method]descriptor.stat-at"⟩
def FsVer.getType (V : FsVer) : FnName := ⟨V.types, "[method]descriptor.get-type"⟩
def FsVer.read (V : FsVer) : FnName := ⟨V.types, "[method]descriptor.read"⟩
def FsVer.write (V : FsVer) : FnName := ⟨V.types, "[method]descriptor.write"⟩
def FsVer.readDir (V : FsVer) : FnName := ⟨V.types, "[method]descriptor.read-directory"⟩
def FsVer.readEntry (V : FsVer) : FnName :=
  ⟨V.types, "[method]directory-entry-stream.read-directory-entry"⟩

/-- The kind of a node in version `V`. -/
def kindOf (V : FsVer) : Node → Nat
  | .file _ => V.fileK
  | .dir _ => V.dirK

/-! ## Values -/

/-- The characters of a string value. -/
def charsV : Val → Option (List Char)
  | .record vs => vs.mapM fun | .char c => some c | _ => none
  | _ => none

/-- The bytes of a `list<u8>` value. -/
def u8sV : Val → Option (List (BitVec 8))
  | .record vs => vs.mapM fun | .u8 b => some b | _ => none
  | _ => none

/-- A string value. -/
def strC (n : Comp) : Val := .record (n.map .char)

/-- A `list<u8>` value. -/
def u8sC (bs : List (BitVec 8)) : Val := .record (bs.map .u8)

/-- Split at `/` (structural, so that the kernel evaluates it). -/
def splitSlash : List Char → List Comp
  | [] => [[]]
  | c :: cs => match splitSlash cs with
    | [] => [[c]]
    | w :: ws => if c = '/' then [] :: w :: ws else (c :: w) :: ws

/-- The components of a relative path; `none` when it is absolute or has a `..`. -/
def relPath (cs : List Char) : Option Path :=
  if cs.head? = some '/' then none
  else
    let ps := (splitSlash cs).filter fun c => c ≠ [] ∧ c ≠ ['.']
    if ['.', '.'] ∈ ps then none else some ps

/-- The `create` flag of `open-flags` (a record of booleans). -/
def createSet : List Val → Bool
  | _ :: _ :: _ :: .record (.bool true :: _) :: _ => true
  | _ => false

/-- The `directory` flag of `open-flags`. -/
def dirSet : List Val → Bool
  | _ :: _ :: _ :: .record (_ :: .bool true :: _) :: _ => true
  | _ => false

/-- An `ok` answer. -/
def isOkAns : Option (List Val) → Bool
  | some [.variant 0 _] => true
  | _ => false

/-! ## The state -/

/-- The theory state. -/
structure FsSt where
  /-- The path of each descriptor seen opened. -/
  descs : List (BitVec 32 × Path) := []
  /-- The pending entries (name, kind) of each directory-entry stream. -/
  ents : List (BitVec 32 × List (Comp × Nat)) := []
  /-- The contents written so far. -/
  over : List (Path × List (BitVec 8)) := []

/-- The node at `p`: written contents over the tree. -/
def nodeAt (T : Tree) (q : FsSt) (p : Path) : Option Node :=
  match q.over.lookup p with
  | some bs => some (.file bs)
  | none => T p

/-- The path of the descriptor in the first argument. -/
def selfPath (q : FsSt) : List Val → Option Path
  | .u32 s :: _ => lookup s q.descs
  | _ => none

/-- The path named by `(self, path-flags, path, …)`. -/
def atPath (q : FsSt) : List Val → Option Path
  | .u32 s :: _ :: pv :: _ => do
    let p ← lookup s q.descs
    let cs ← charsV pv
    let r ← relPath cs
    pure (p ++ r)
  | _ => none

/-- The entries of the directory at `p` with names `ns` that exist, with their kinds. -/
def entriesOf (V : FsVer) (T : Tree) (q : FsSt) (p : Path) (ns : List Comp) : List (Comp × Nat) :=
  ns.filterMap fun n => (nodeAt T q (p ++ [n])).map fun m => (n, kindOf V m)

/-- `bs` with `ys` written at `off` (zeros fill a gap). -/
def writeAt (bs : List (BitVec 8)) (off : Nat) (ys : List (BitVec 8)) : List (BitVec 8) :=
  bs.take off ++ List.replicate (off - bs.length) 0 ++ ys ++ bs.drop (off + ys.length)

/-- The preopens of an answer of `get-directories`. -/
def preopensOf : Option (List Val) → List (BitVec 32 × Comp)
  | some [.record es] => es.filterMap fun
    | .record [.u32 h, nm] => (charsV nm).map fun n => (h, n)
    | _ => none
  | _ => []

/-! ## The checks -/

/-- A directory node. -/
def isDir : Option Node → Bool
  | some (.dir _) => true
  | _ => false

/-- The size check of `stat`. -/
def sizeOk : Node → BitVec 64 → Bool
  | .file bs, sz => sz == BitVec.ofNat 64 bs.length
  | .dir _, _ => true

/-- The check of a `stat`/`stat-at` answer for the node `o`. -/
def statChk (V : FsVer) : Option Node → Option (List Val) → Bool
  | none, r => !isOkAns r
  | some n, some [.variant 0 (some (.record (.variant k none :: _ :: .u64 sz :: _)))] =>
    k == kindOf V n && sizeOk n sz
  | some _, _ => true

/-- The check of a `get-type` answer for the node `o`. -/
def typeChk (V : FsVer) : Option Node → Option (List Val) → Bool
  | none, r => !isOkAns r
  | some n, some [.variant 0 (some (.variant k none))] => k == kindOf V n
  | some _, _ => true

/-- The check of an `open-at` answer for the node `o`. -/
def openChk (V : FsVer) (dirF : Bool) (o : Option Node) : Option (List Val) → Bool
  | some [.variant 0 (some (.u32 _))] => o.isSome && (!dirF || isDir o)
  | some [.variant 1 (some (.variant k none))] => k != V.noEntry || o.isNone
  | _ => true

/-- The check of a `read(length, offset)` answer for the node `o`. -/
def readChk (len off : Nat) : Option Node → Option (List Val) → Bool
  | some (.file bs), some [.variant 0 (some (.record [v, .bool eof]))] =>
    match u8sV v with
    | some xs => xs.length ≤ len && xs == (bs.drop off).take xs.length &&
        (!eof || bs.length ≤ off + xs.length)
    | none => false
  | some (.file _), _ => true
  | _, r => !isOkAns r

/-- The check of a `write(buffer, offset)` answer for the node `o`. -/
def writeChk (buf : Val) : Option Node → Option (List Val) → Bool
  | some (.file _), some [.variant 0 (some (.u64 n))] =>
    match u8sV buf with
    | some xs => n.toNat ≤ xs.length
    | none => true
  | some (.file _), _ => true
  | _, r => !isOkAns r

/-- The check of a `read-directory` answer for the node `o`. -/
def readDirChk (o : Option Node) (r : Option (List Val)) : Bool := isDir o || !isOkAns r

/-- The check of a `read-directory-entry` answer for the pending entries `l`. -/
def entryChk : List (Comp × Nat) → Option (List Val) → Bool
  | (n, k) :: _, some [.variant 0 (some (.variant 1 (some (.record [.variant k' none, nm]))))] =>
    k' == k && charsV nm == some n
  | [], some [.variant 0 (some (.variant 1 _))] => false
  | _ :: _, some [.variant 0 (some (.variant 0 none))] => false
  | _, _ => true

/-- The length and offset arguments of `read(self, length, offset)`. -/
def lenOff : List Val → Nat × Nat
  | _ :: .u64 l :: .u64 o :: _ => (l.toNat, o.toNat)
  | _ => (0, 0)

/-- The buffer and offset arguments of `write(self, buffer, offset)`. -/
def bufOff : List Val → Val × Nat
  | _ :: b :: .u64 o :: _ => (b, o.toNat)
  | _ => (.record [], 0)

/-- The check of every answer. -/
def fsOk (V : FsVer) (T : Tree) (q : FsSt) : WEv → Bool
  | .imp f a r =>
    if f = V.getDirs then
      (preopensOf r).all fun x => isDir (T [x.2])
    else if f = V.openAt then
      (match atPath q a with
       | some p => createSet a || openChk V (dirSet a) (nodeAt T q p) r
       | none => true)
    else if f = V.stat then
      (match selfPath q a with
       | some p => statChk V (nodeAt T q p) r
       | none => true)
    else if f = V.statAt then
      (match atPath q a with
       | some p => statChk V (nodeAt T q p) r
       | none => true)
    else if f = V.getType then
      (match selfPath q a with
       | some p => typeChk V (nodeAt T q p) r
       | none => true)
    else if f = V.read then
      (match selfPath q a with
       | some p => readChk (lenOff a).1 (lenOff a).2 (nodeAt T q p) r
       | none => true)
    else if f = V.write then
      (match selfPath q a with
       | some p => writeChk (bufOff a).1 (nodeAt T q p) r
       | none => true)
    else if f = V.readDir then
      (match selfPath q a with
       | some p => readDirChk (nodeAt T q p) r
       | none => true)
    else if f = V.readEntry then
      (match a with
       | .u32 s :: _ => (match lookup s q.ents with
         | some l => entryChk l r
         | none => true)
       | _ => true)
    else true
  | _ => true

/-! ## The state update -/

/-- The next state. -/
def fsNext (V : FsVer) (T : Tree) (q : FsSt) : WEv → FsSt
  | .imp f a r =>
    if f = V.getDirs then
      { q with descs := (preopensOf r).map (fun x => (x.1, [x.2])) ++ q.descs }
    else if f = V.openAt then
      (match atPath q a, r with
       | some p, some [.variant 0 (some (.u32 d))] =>
         if createSet a then q else { q with descs := (d, p) :: q.descs }
       | _, _ => q)
    else if f = V.write then
      (match selfPath q a, r with
       | some p, some [.variant 0 (some (.u64 n))] =>
         (match nodeAt T q p, u8sV (bufOff a).1 with
          | some (.file bs), some xs =>
            { q with over := (p, writeAt bs (bufOff a).2 (xs.take n.toNat)) :: q.over }
          | _, _ => q)
       | _, _ => q)
    else if f = V.readDir then
      (match selfPath q a, r with
       | some p, some [.variant 0 (some (.u32 s))] =>
         (match nodeAt T q p with
          | some (.dir ns) => { q with ents := (s, entriesOf V T q p ns) :: q.ents }
          | _ => q)
       | _, _ => q)
    else if f = V.readEntry then
      (match a, r with
       | .u32 s :: _, some [.variant 0 (some (.variant 1 _))] =>
         (match lookup s q.ents with
          | some l => { q with ents := (s, l.drop 1) :: q.ents }
          | none => q)
       | _, _ => q)
    else q
  | _ => q

/-- **The loose filesystem theory** of version `V` over the tree `T`. -/
def fsThV (V : FsVer) (T : Tree) : Protocol FsSt WEv := gated {} (fsNext V T) (fsOk V T)

/-- **The 0.2 theory.** -/
abbrev fsTh2 (T : Tree) : Protocol FsSt WEv := fsThV v2 T
/-- **The 0.3 theory** (sync-lowered `async` functions). -/
abbrev fsTh3 (T : Tree) : Protocol FsSt WEv := fsThV v3 T

/-! ## The host -/

/-- The state of the theory after the answers `p`. -/
def fsState (V : FsVer) (T : Tree) (p : List WEv) : FsSt := p.foldl (fsNext V T) {}

/-- `ok(v)`, `error(case k)`. -/
def okA (v : Val) : Option (List Val) := some [.variant 0 (some v)]
def errA (k : Nat) : Option (List Val) := some [.variant 1 (some (.variant k none))]

/-- `none` as an `option`. -/
def noneV : Val := .variant 0 none

/-- The `descriptor-stat` of a node. -/
def statV (V : FsVer) : Node → Val
  | .file bs => .record [.variant (kindOf V (.file bs)) none, .u64 1, .u64 (BitVec.ofNat 64 bs.length),
      noneV, noneV, noneV]
  | .dir ns => .record [.variant (kindOf V (.dir ns)) none, .u64 1, .u64 0, noneV, noneV, noneV]

/-- The answer of `stat` for the node `o`. -/
def statA (V : FsVer) : Option Node → Option (List Val)
  | some n => okA (statV V n)
  | none => errA V.noEntry

/-- The answer of `get-type` for the node `o`. -/
def typeA (V : FsVer) : Option Node → Option (List Val)
  | some n => okA (.variant (kindOf V n) none)
  | none => errA V.noEntry

/-- The answer of `open-at`: a fresh handle `h` when the node exists (and is a directory if
asked), `error(no-entry)` when it does not, `error(not-directory)` when it is not a directory
but one was asked for. -/
def openA (V : FsVer) (h : BitVec 32) (dirF : Bool) : Option Node → Option (List Val)
  | none => errA V.noEntry
  | some n => if !dirF || isDir (some n) then okA (.u32 h) else errA V.notDir

/-- The answer of `read(length, offset)`. -/
def readA (V : FsVer) (len off : Nat) : Option Node → Option (List Val)
  | some (.file bs) =>
    let xs := (bs.drop off).take len
    okA (.record [u8sC xs, .bool (decide (bs.length ≤ off + xs.length))])
  | _ => errA V.badDesc

/-- The answer of `write(buffer, offset)`: the whole buffer. -/
def writeA (V : FsVer) (buf : Val) : Option Node → Option (List Val)
  | some (.file _) => okA (.u64 (BitVec.ofNat 64 ((u8sV buf).getD []).length))
  | _ => errA V.badDesc

/-- The answer of `read-directory-entry` for the pending entries. -/
def entryA : List (Comp × Nat) → Option (List Val)
  | (n, k) :: _ => okA (.variant 1 (some (.record [.variant k none, strC n])))
  | [] => okA (.variant 0 none)

/-- The preopens `ns`, numbered from `b`. -/
def numbered : Nat → List Comp → List Val
  | _, [] => []
  | b, n :: ns => .record [.u32 (BitVec.ofNat 32 b), strC n] :: numbered (b + 1) ns

/-- The answer of `get-directories`: the preopens of `pre` that are directories, with handles
numbered from `base`. -/
def dirsA (T : Tree) (base : Nat) (pre : List Comp) : Option (List Val) :=
  some [.record (numbered base (pre.filter fun n => isDir (T [n])))]

/-- **The concrete filesystem host** of version `V`, tree `T` and preopen names `pre`. -/
def fsImplV (V : FsVer) (T : Tree) (pre : List Comp) : Impl := fun p f a =>
  let q := fsState V T p
  let h : BitVec 32 := BitVec.ofNat 32 p.length
  if f = V.getDirs then dirsA T p.length pre
  else if f = V.openAt then
    (match atPath q a with
     | some pa => openA V h (dirSet a) (nodeAt T q pa)
     | none => errA V.badDesc)
  else if f = V.stat then
    (match selfPath q a with
     | some pa => statA V (nodeAt T q pa)
     | none => errA V.badDesc)
  else if f = V.statAt then
    (match atPath q a with
     | some pa => statA V (nodeAt T q pa)
     | none => errA V.badDesc)
  else if f = V.getType then
    (match selfPath q a with
     | some pa => typeA V (nodeAt T q pa)
     | none => errA V.badDesc)
  else if f = V.read then
    (match selfPath q a with
     | some pa => readA V (lenOff a).1 (lenOff a).2 (nodeAt T q pa)
     | none => errA V.badDesc)
  else if f = V.write then
    (match selfPath q a with
     | some pa => writeA V (bufOff a).1 (nodeAt T q pa)
     | none => errA V.badDesc)
  else if f = V.readDir then
    (match selfPath q a with
     | some pa => if isDir (nodeAt T q pa) then okA (.u32 h) else errA V.badDesc
     | none => errA V.badDesc)
  else if f = V.readEntry then
    (match a with
     | .u32 s :: _ => (match lookup s q.ents with
       | some l => entryA l
       | none => errA V.badDesc)
     | _ => errA V.badDesc)
  else none

/-- The 0.2 host. -/
abbrev fsImpl2 (T : Tree) (pre : List Comp) : Impl := fsImplV v2 T pre
/-- The 0.3 host. -/
abbrev fsImpl3 (T : Tree) (pre : List Comp) : Impl := fsImplV v3 T pre

end Silmaril.Wasi.Versions.FsMore
