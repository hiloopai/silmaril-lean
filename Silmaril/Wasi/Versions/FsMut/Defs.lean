module

public import Silmaril.Wasi.Versions.FsMore.Defs

@[expose] public section

/-!
# `wasi:filesystem` mutations: create, links, rename, remove, timestamps (0.2 and 0.3)

`Silmaril.Wasi.Versions.FsMore` reads a fixed tree. This module is a second theory of the same
descriptor functions in which the tree **changes**: `create-directory-at`, `open-at` with the
`create` flag, `remove-directory-at`, `unlink-file-at`, `rename-at`, `link-at`, `symlink-at`,
`readlink-at`, and `set-times-at` (checked against `specs/wasi/0.2.12/filesystem/types.wit`,
the same functions in `specs/wasi/v0.2.9`, and `specs/wasi/0.3.2/filesystem/types.wit`, where
they are `async` and observed sync-lowered with the 0.2 result shapes). It is a related variant
of `FsMore.fsThV`, not an extension of it: it does not model contents, reads, writes or
directory streams.

## The model

* **The view** `view : Path → Option MNode`: what is at each path now. It starts as the tree
  `T` (files, directories) and records symbolic links (`MNode.sym`) created by `symlink-at`.
  A rename moves a whole subtree; removing a directory removes its subtree.
* **Symbolic links are not resolved.** A path one of whose prefixes is a symbolic link (or, for
  the functions that may follow a final link, the path itself) is not checked. A *mutation*
  through such a path sets `lost`: from then on the view is not trusted and nothing is checked.
* Absolute paths and paths with `..` are not checked (as in `FsMore`).

## The checks (gated: only `ok` answers are constrained)

| function | an `ok` answer needs |
|---|---|
| `get-directories` | every preopen `n` is a directory `[n]` in the view |
| `open-at` without `create` | the node exists (a directory if `directory` is set) |
| `open-at` with `create` | the node exists or its parent is a directory; a file is created |
| `stat-at`, `set-times-at` | the node exists |
| `create-directory-at` | the node is absent and its parent is a directory |
| `remove-directory-at` | a directory |
| `unlink-file-at` | a node that is not a directory |
| `rename-at` | the old node exists and the new path is not strictly below it |
| `link-at` | the old node is a file and the new path is absent (the WIT: `no-entry` if the old path does not exist, `exist` if the new path exists, `not-permitted` if the old path is not a file) |
| `symlink-at` | the new path is absent and the contents do not start with `/` (the WIT: `not-permitted`) |
| `readlink-at` | a symbolic link, and the answer is its contents |

What is not checked: errors (only the explicit `link-at`/`symlink-at` sentences are conditions on
`ok`), that a removed directory is empty (`not-empty`), timestamps beyond existence
(`set-times` on a descriptor is not constrained at all: POSIX allows it on an unlinked open
file, and the WIT does not say that a timestamp set is read back), permissions and flags other
than `create` and `directory`.

## The host

`mutImplV V T pre` answers each of these functions with `ok` exactly when the condition of the
table holds in the view of the answers so far (a fresh handle for `open-at`, the contents for
`readlink-at`), and `error(no-entry)` otherwise; `get-directories` answers the preopens of `pre`
that are directories.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.FsMut

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.Net (gated lookup)
open Silmaril.Wasi.Versions.FsMore

/-! ## Names -/

def _root_.Silmaril.Wasi.Versions.FsMore.FsVer.createDir (V : FsVer) : FnName :=
  ⟨V.types, "[method]descriptor.create-directory-at"⟩
def _root_.Silmaril.Wasi.Versions.FsMore.FsVer.removeDir (V : FsVer) : FnName :=
  ⟨V.types, "[method]descriptor.remove-directory-at"⟩
def _root_.Silmaril.Wasi.Versions.FsMore.FsVer.unlink (V : FsVer) : FnName :=
  ⟨V.types, "[method]descriptor.unlink-file-at"⟩
def _root_.Silmaril.Wasi.Versions.FsMore.FsVer.rename (V : FsVer) : FnName :=
  ⟨V.types, "[method]descriptor.rename-at"⟩
def _root_.Silmaril.Wasi.Versions.FsMore.FsVer.linkAt (V : FsVer) : FnName :=
  ⟨V.types, "[method]descriptor.link-at"⟩
def _root_.Silmaril.Wasi.Versions.FsMore.FsVer.symlink (V : FsVer) : FnName :=
  ⟨V.types, "[method]descriptor.symlink-at"⟩
def _root_.Silmaril.Wasi.Versions.FsMore.FsVer.readlink (V : FsVer) : FnName :=
  ⟨V.types, "[method]descriptor.readlink-at"⟩
def _root_.Silmaril.Wasi.Versions.FsMore.FsVer.setTimesAt (V : FsVer) : FnName :=
  ⟨V.types, "[method]descriptor.set-times-at"⟩

/-! ## The view -/

/-- What is at a path: a file, a directory, or a symbolic link with its contents. -/
inductive MNode where
  | file
  | dir
  | sym (target : List Char)

/-- The view of a tree node. -/
def ofNode : Node → MNode
  | .file _ => .file
  | .dir _ => .dir

/-- The view of the tree `T`. -/
def viewOf (T : Tree) : Path → Option MNode := fun p => (T p).map ofNode

def isDirM : Option MNode → Bool
  | some .dir => true
  | _ => false

def isFileM : Option MNode → Bool
  | some .file => true
  | _ => false

def isSymM : Option MNode → Bool
  | some (.sym _) => true
  | _ => false

/-- A proper prefix of `p` is a symbolic link. -/
def linky (v : Path → Option MNode) (p : Path) : Bool :=
  (List.range p.length).any fun i => isSymM (v (p.take i))

/-- `p` or a proper prefix of it is a symbolic link. -/
def linky' (v : Path → Option MNode) (p : Path) : Bool := linky v p || isSymM (v p)

/-- The parent of `p` is a directory. -/
def parentDir (v : Path → Option MNode) (p : Path) : Bool := isDirM (v p.dropLast)

/-- Set the node at `p`. -/
def upd (v : Path → Option MNode) (p : Path) (o : Option MNode) : Path → Option MNode :=
  fun x => if x = p then o else v x

/-- Remove the subtree at `p`. -/
def rmTree (v : Path → Option MNode) (p : Path) : Path → Option MNode :=
  fun x => if p.isPrefixOf x then none else v x

/-- Move the subtree at `o` to `n`. -/
def mvTree (v : Path → Option MNode) (o n : Path) : Path → Option MNode :=
  fun x => if n.isPrefixOf x then v (o ++ x.drop n.length)
    else if o.isPrefixOf x then none else v x

/-! ## The state -/

/-- The theory state. -/
structure MSt where
  /-- The path of each descriptor seen opened. -/
  descs : List (BitVec 32 × Path)
  /-- The view. -/
  view : Path → Option MNode
  /-- A mutation went through a symbolic link: the view is not trusted. -/
  lost : Bool := false

/-- The path named by the descriptor `d` and the string `pv`. -/
def resolve (q : MSt) : Option Val → Option Val → Option Path
  | some (.u32 s), some pv => do
    let b ← lookup s q.descs
    let cs ← charsV pv
    let r ← relPath cs
    pure (b ++ r)
  | _, _ => none

/-- The path of the self descriptor and the string argument `i`. -/
def at_ (q : MSt) (a : List Val) (i : Nat) : Option Path := resolve q a[0]? a[i]?

/-- The paths of `rename-at(self, old-path, new-descriptor, new-path)`. -/
def renPaths (q : MSt) (a : List Val) : Option (Path × Path) := do
  pure (← resolve q a[0]? a[1]?, ← resolve q a[2]? a[3]?)

/-- The paths of `link-at(self, old-path-flags, old-path, new-descriptor, new-path)`. -/
def linkPaths (q : MSt) (a : List Val) : Option (Path × Path) := do
  pure (← resolve q a[0]? a[2]?, ← resolve q a[3]? a[4]?)

/-- The contents and the path of `symlink-at(self, old-path, new-path)`. -/
def symArgs (q : MSt) (a : List Val) : Option (List Char × Path) := do
  pure (← a[1]?.bind charsV, ← resolve q a[0]? a[2]?)

/-! ## The conditions -/

/-- The condition an `ok` answer needs, for the functions of the table other than
`get-directories` and `readlink-at`; `none`: not checked. -/
def cond (V : FsVer) (q : MSt) (f : FnName) (a : List Val) : Option Bool :=
  if q.lost then none
  else if f = V.openAt then
    (at_ q a 2).bind fun p =>
      if linky' q.view p then none
      else if createSet a then some ((q.view p).isSome || parentDir q.view p)
      else some ((q.view p).isSome && (!dirSet a || isDirM (q.view p)))
  else if f = V.statAt ∨ f = V.setTimesAt then
    (at_ q a 2).bind fun p => if linky' q.view p then none else some (q.view p).isSome
  else if f = V.createDir then
    (at_ q a 1).bind fun p =>
      if linky q.view p then none else some ((q.view p).isNone && parentDir q.view p)
  else if f = V.removeDir then
    (at_ q a 1).bind fun p => if linky q.view p then none else some (isDirM (q.view p))
  else if f = V.unlink then
    (at_ q a 1).bind fun p =>
      if linky q.view p then none else some ((q.view p).isSome && !isDirM (q.view p))
  else if f = V.rename then
    (renPaths q a).bind fun (o, n) =>
      if linky q.view o || linky q.view n then none
      else some ((q.view o).isSome && (o == n || !o.isPrefixOf n))
  else if f = V.linkAt then
    (linkPaths q a).bind fun (o, n) =>
      if linky' q.view o || linky q.view n then none
      else some (isFileM (q.view o) && (q.view n).isNone)
  else if f = V.symlink then
    (symArgs q a).bind fun (t, n) =>
      if linky q.view n then none
      else some ((q.view n).isNone && t.head? != some '/')
  else none

/-- An `ok` answer needs `c`. -/
def okNeeds (c : Bool) (r : Option (List Val)) : Bool := !isOkAns r || c

/-- The check of a `readlink-at` answer for the node `o`. -/
def rlChk (o : Option MNode) : Option (List Val) → Bool
  | some [.variant 0 (some s)] =>
    (match o with
     | some (.sym t) => charsV s == some t
     | _ => false)
  | _ => true

/-- The check of every answer. -/
def mutOk (V : FsVer) (q : MSt) : WEv → Bool
  | .imp f a r =>
    if f = V.getDirs then
      q.lost || (preopensOf r).all fun x => isDirM (q.view [x.2])
    else if f = V.readlink then
      (match at_ q a 1 with
       | some p => q.lost || linky q.view p || rlChk (q.view p) r
       | none => true)
    else
      (match cond V q f a with
       | some c => okNeeds c r
       | none => true)
  | _ => true

/-! ## The state update -/

/-- Apply a mutation at the paths `ps`: through a symbolic link the view is lost. -/
def mutate (q : MSt) (ps : List Path) (g : (Path → Option MNode) → Path → Option MNode) : MSt :=
  if ps.any (linky q.view) then { q with lost := true } else { q with view := g q.view }

/-- The next state. -/
def mutNext (V : FsVer) (q : MSt) : WEv → MSt
  | .imp f a r =>
    if f = V.getDirs then
      { q with descs := (preopensOf r).map (fun x => (x.1, [x.2])) ++ q.descs }
    else if isOkAns r then
      if f = V.openAt then
        (match at_ q a 2, r with
         | some p, some [.variant 0 (some (.u32 d))] =>
           let q' := { q with descs := (d, p) :: q.descs }
           if createSet a && (q.view p).isNone then mutate q' [p] (upd · p (some .file)) else q'
         | _, _ => q)
      else if f = V.createDir then
        (match at_ q a 1 with
         | some p => mutate q [p] (upd · p (some .dir))
         | none => q)
      else if f = V.removeDir then
        (match at_ q a 1 with
         | some p => mutate q [p] (rmTree · p)
         | none => q)
      else if f = V.unlink then
        (match at_ q a 1 with
         | some p => mutate q [p] (upd · p none)
         | none => q)
      else if f = V.rename then
        (match renPaths q a with
         | some (o, n) => mutate q [o, n] (mvTree · o n)
         | none => q)
      else if f = V.linkAt then
        (match linkPaths q a with
         | some (o, n) => mutate q [o, n] fun v => upd v n (v o)
         | none => q)
      else if f = V.symlink then
        (match symArgs q a with
         | some (t, n) => mutate q [n] (upd · n (some (.sym t)))
         | none => q)
      else q
    else q
  | _ => q

/-- The initial state over the tree `T`. -/
def mutInit (T : Tree) : MSt := ⟨[], viewOf T, false⟩

/-- **The filesystem mutation theory** of version `V` over the initial tree `T`. -/
def mutThV (V : FsVer) (T : Tree) : Protocol MSt WEv := gated (mutInit T) (mutNext V) (mutOk V)

abbrev mutTh2 (T : Tree) : Protocol MSt WEv := mutThV v2 T
abbrev mutTh3 (T : Tree) : Protocol MSt WEv := mutThV v3 T

/-! ## The host -/

/-- The state after the answers `p`. -/
def mutState (V : FsVer) (T : Tree) (p : List WEv) : MSt := p.foldl (mutNext V) (mutInit T)

/-- The unit `ok`. -/
def okU : Option (List Val) := some [.variant 0 none]

/-- The answer of `readlink-at` for the node `o`. -/
def rlA (V : FsVer) : Option MNode → Option (List Val)
  | some (.sym t) => okA (strC t)
  | _ => errA V.noEntry

/-- The answer for a condition: `ok` (a handle `h` for `open-at`) or `error(no-entry)`. -/
def condA (V : FsVer) (f : FnName) (h : BitVec 32) : Option Bool → Option (List Val)
  | some true => if f = V.openAt then okA (.u32 h) else okU
  | _ => errA V.noEntry

/-- The functions answered from `cond`. -/
def condFns (V : FsVer) : List FnName :=
  [V.openAt, V.statAt, V.setTimesAt, V.createDir, V.removeDir, V.unlink, V.rename, V.linkAt,
   V.symlink]

/-- **The concrete mutation host** of version `V`, tree `T` and preopen names `pre`. -/
def mutImplV (V : FsVer) (T : Tree) (pre : List Comp) : Impl := fun p f a =>
  let q := mutState V T p
  if f = V.getDirs then
    some [.record (numbered p.length (pre.filter fun n => isDirM (q.view [n])))]
  else if f = V.readlink then
    (match at_ q a 1 with
     | some pa => rlA V (q.view pa)
     | none => errA V.noEntry)
  else if f ∈ condFns V then condA V f (BitVec.ofNat 32 p.length) (cond V q f a)
  else none

abbrev mutImpl2 (T : Tree) (pre : List Comp) : Impl := mutImplV v2 T pre
abbrev mutImpl3 (T : Tree) (pre : List Comp) : Impl := mutImplV v3 T pre

end Silmaril.Wasi.Versions.FsMut
