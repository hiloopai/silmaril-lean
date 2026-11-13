module

public import Silmaril.Servers.WasiExamples.Defs
public import Silmaril.Servers.State.OwnedFs.Defs
public import Silmaril.Wasi.Versions.FsMore.Defs

@[expose] public section

/-!
# A file-backed `wasi:http` store: state model (b) run as a WASI component

See `docs/projects/http-servers.md` (section "State models"). State model (b)
(`Silmaril.Servers.State.OwnedFs`) keeps the server's state in files, in the file model of the
CLI work (`Silmaril.Cli.Fs`: rooted paths to contents). This module runs that model as a
component of the `wasi:http` proxy world that also imports `wasi:filesystem` 0.2, and reads it
back as a server of `Silmaril.Servers.State`.

## Files as a `wasi:filesystem` tree

`treeOf pre fs` is the tree of `Silmaril.Wasi.Versions.FsMore` (paths of components, the first
component a preopen's name) that the files `fs` give: each preopen of `pre` is a directory and
each file `⟨root, rel⟩` (with `rel` not empty) is a file node at `root :: rel`. Directories other
than the preopens are not represented (`FsMore` checks the existence of the node a path names,
not of its parents). `toPath`/`ofPath` translate rooted paths.

## The host

`storeHost root q fs` serves one call of `handle` for the request `q` with the files `fs` under
the one preopen `root`:

* the `wasi:http` imports are answered by the reference host `refHost q`;
* the **read-only** `wasi:filesystem` calls (`get-directories`, `open-at` without `create`,
  `read`, `stat`, …) are answered by **the `FsMore` host** `fsImplV v2 (treeOf [root] fs') [root]`
  of the files `fs'` as they are at that point of the call, so its answers satisfy the
  `FsMore` theory of the 0.2 filesystem functions (`fsImplV_ok`);
* the **mutating** calls (`mutating`): `open-at` with `create` (and `truncate`), `write` and
  `unlink-file-at`, change the files (`mutAns`, `mutUpd`): `open-at` with `create` makes the
  file if it is absent and empties it with `truncate`, `write(d, buf, off)` writes at the
  offset (`writeAt`) through a descriptor opened by `open-at`, `unlink-file-at` removes a file
  (`error(no-entry)` when there is none). Descriptors are fresh positions in the list of the
  filesystem calls so far (numbered apart from the `wasi:http` handles).

`replay root fs u` is the state after the filesystem calls of `u` (`fsEvents`), so the files
after a call are `(replay root fs u).files`.

## The component

`storeBody` (exports `handle`, imports the proxy slice and `getDirs`, `open-at`, `read`,
`write`, `unlink-file-at`) keeps the representation of target `t` in the file `keyName` of its
path-with-query (`k` and the octets in hexadecimal, or `n` for no path) under the preopen:

* `GET`, `HEAD`: `get-directories`, `open-at`, then `read` of the whole file: `200` with the
  contents (none for `HEAD`), or `404` for `error(no-entry)`;
* `PUT`: read the request body as `echo` does, then `open-at` without `create` (does the file
  exist?), `open-at` with `create` and `truncate`, `write` of the body: `204` if it existed, else
  `201`; a body of `2^64 - 1` octets or more is answered `413` (a `read` length is a `u64`);
* `DELETE`: `unlink-file-at`: `204`, or `404` for `error(no-entry)`;
* `OPTIONS`: `204`; `POST`, `CONNECT`, `TRACE`, `PATCH`: `405`; other methods: `501`.

Every unexpected answer gives `500`. The responses carry no header fields, since the reading of
`Silmaril.Servers.WasiHttp` does not observe them.

## The component read as a server

`storeHandler root`: in files `fs`, request `q` is answered `resp` with files `fs'` when the
complete run of `handle` over `storeHost root q fs` makes the response `resp` (`respOf`) and
leaves the files `fs'`. The files are host state, so they survive a fresh instance per request.
`wasiStore root fs₀` is the server (`Silmaril.Servers.State.Server.closed`): nobody else
edits the files.

The specification it is compared with (`Thms`): `fileStore (keyFile root) fs₀` of state model
(b), read without header fields (`noFields`, `Atomic.mapResp`), for requests whose content is
shorter than `2^64 - 1` octets (`Atomic.guard`, `smallReq`).

A Silmaril addition.
-/

namespace Silmaril.Servers.WasiFs

open Silmaril.Games Silmaril.Wasi Silmaril.Servers.WasiHttp Silmaril.Servers.WasiExamples
open Silmaril.Servers.State Silmaril.Servers.State.OwnedFs
open Silmaril.Wasm.Component (Val)
open Silmaril.Net.Http (Request Response Method Target)
open Silmaril.Cli (Fs FPath)
open Silmaril.Wasi.Versions.FsMore (Tree Node Comp strC u8sC u8sV charsV relPath createSet okA
  errA fsImplV fsState v2)

/-! ## Files as a `wasi:filesystem` tree -/

/-- The `FsMore` path of a rooted path. -/
def toPath (p : FPath) : Versions.FsMore.Path := p.root.toList :: p.rel.map String.toList

/-- The rooted path of an `FsMore` path. -/
def ofPath : Versions.FsMore.Path → Option FPath
  | [] => none
  | n :: rest => some ⟨String.ofList n, rest.map String.ofList⟩

/-- **The tree of the files `fs` under the preopens `pre`.** -/
def treeOf (pre : List String) (fs : Fs) : Tree
  | [] => none
  | [n] => if String.ofList n ∈ pre then some (.dir []) else none
  | n :: m :: rest =>
    (fs ⟨String.ofList n, (m :: rest).map String.ofList⟩).map fun c => .file (c.map UInt8.toBitVec)

/-! ## Function names -/

/-- `wasi:filesystem/types.[method]descriptor.unlink-file-at`. -/
def unlinkAt : FnName := ⟨"wasi:filesystem/types", "[method]descriptor.unlink-file-at"⟩

/-- The filesystem imports of the store. -/
def fsList : List FnName := [getDirs, openAt, fdRead, fdWrite, unlinkAt]

/-- The imports of the store: the proxy slice and the filesystem imports. -/
def storeList : List FnName := proxyList ++ fsList

/-- The imports of the store. -/
def storeImports : Set FnName := {f | f ∈ storeList}

/-- **The store's world**: the proxy slice and `wasi:filesystem`, exporting `handle`. -/
def storeWorld : World := ⟨storeImports, proxyWorld.exports⟩

/-! ## The host -/

/-- The `truncate` flag of `open-flags` (`create`, `directory`, `exclusive`, `truncate`). -/
def truncSet : List Val → Bool
  | _ :: _ :: _ :: .record (_ :: _ :: _ :: .bool true :: _) :: _ => true
  | _ => false

/-- The calls that change the files. -/
def mutating (f : FnName) (a : List Val) : Bool :=
  (decide (f = openAt) && createSet a) || decide (f = fdWrite) || decide (f = unlinkAt)

/-- The state of the files host: the files, the `FsMore` state of the calls so far (for the
descriptors of the preopens and of `open-at` without `create`), and the descriptors opened with
`create`. -/
structure FSt where
  /-- The files. -/
  files : Fs
  /-- The `FsMore` state. -/
  q : Versions.FsMore.FsSt := {}
  /-- The descriptors opened with `create`, with their paths. -/
  descs : List (BitVec 32 × Versions.FsMore.Path) := []

/-- The path of the descriptor in the first argument. -/
def FSt.self (st : FSt) : List Val → Option Versions.FsMore.Path
  | .u32 d :: _ => (Versions.Net.lookup d (st.descs ++ st.q.descs))
  | _ => none

/-- The path named by `(self, path)` for `unlink-file-at`. -/
def FSt.at2 (st : FSt) : List Val → Option FPath
  | .u32 d :: pv :: _ => do
    let p ← Versions.Net.lookup d st.q.descs
    let cs ← charsV pv
    let r ← relPath cs
    ofPath (p ++ r)
  | _ => none

/-- The rooted path named by the arguments of `open-at`. -/
def FSt.atOpen (st : FSt) (a : List Val) : Option Versions.FsMore.Path :=
  Versions.FsMore.atPath st.q a

/-- The bytes of a file, octets. -/
def bitsOf (c : List UInt8) : List (BitVec 8) := c.map UInt8.toBitVec

/-- `c` with `ys` written at `off` (zeros fill a gap). -/
def writeAtU (c : List UInt8) (off : Nat) (ys : List UInt8) : List UInt8 :=
  c.take off ++ List.replicate (off - c.length) 0 ++ ys ++ c.drop (off + ys.length)

/-- The buffer and offset of `write(self, buffer, offset)`. -/
def bufArgs : List Val → Option (List UInt8 × Nat)
  | _ :: b :: .u64 o :: _ => (u8sV b).map fun xs => (xs.map UInt8.ofBitVec, o.toNat)
  | _ => none

/-- **The answer of a mutating call**, with `h` the fresh descriptor. -/
def mutAns (st : FSt) (h : BitVec 32) (f : FnName) (a : List Val) : Option (List Val) :=
  if f = openAt then
    match (st.atOpen a).bind ofPath with
    | some _ => okA (.u32 h)
    | none => errA v2.badDesc
  else if f = fdWrite then
    match (st.self a).bind ofPath, bufArgs a with
    | some _, some (xs, _) => okA (.u64 (BitVec.ofNat 64 xs.length))
    | _, _ => errA v2.badDesc
  else
    match st.at2 a with
    | some p => if (st.files p).isSome then some [.variant 0 none] else errA v2.noEntry
    | none => errA v2.badDesc

/-- **The effect of a mutating call** answered `r`. -/
def mutUpd (st : FSt) (f : FnName) (a : List Val) (r : Option (List Val)) : FSt :=
  if f = openAt then
    match st.atOpen a, r with
    | some p, some [.variant 0 (some (.u32 d))] =>
      match ofPath p with
      | some fp =>
        { st with
          files := if truncSet a || (st.files fp).isNone then st.files.set fp (some []) else st.files
          descs := (d, p) :: st.descs }
      | none => st
    | _, _ => st
  else if f = fdWrite then
    match (st.self a).bind ofPath, bufArgs a with
    | some fp, some (xs, off) =>
      { st with files := st.files.set fp (some (writeAtU ((st.files fp).getD []) off xs)) }
    | _, _ => st
  else
    match st.at2 a, r with
    | some p, some [.variant 0 none] => { st with files := st.files.set p none }
    | _, _ => st

/-- **One filesystem call** of the host (`root`: the preopen). -/
def fstep (root : String) (st : FSt) : WEv → FSt
  | e@(.imp f a r) =>
    let st' := if mutating f a then mutUpd st f a r else st
    { st' with q := Versions.FsMore.fsNext v2 (treeOf [root] st.files) st.q e }
  | _ => st

/-- A filesystem call. -/
def isFsEv : WEv → Bool
  | .imp f _ _ => decide (f ∈ fsList)
  | _ => false

/-- The filesystem calls of an event list. -/
def fsEvents (u : List WEv) : List WEv := u.filter isFsEv

/-- **The state after the filesystem calls** of `u`, from the files `fs`. -/
def replay (root : String) (fs : Fs) (u : List WEv) : FSt :=
  (fsEvents u).foldl (fstep root) ⟨fs, {}, []⟩

/-- **The host of the store** for the request `q` and the files `fs` under the preopen `root`. -/
def storeHost (root : String) (q : Request) (fs : Fs) : Impl := fun past f a =>
  if f ∈ fsList then
    let u := fsEvents past
    let st := replay root fs past
    if mutating f a then mutAns st (BitVec.ofNat 32 u.length) f a
    else fsImplV v2 (treeOf [root] st.files) [root.toList] u f a
  else refHost q past f a

/-! ## The component -/

/-- A hexadecimal digit. -/
def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- The file name of a path-with-query: `k` and its octets in hexadecimal, or `n`. -/
def keyName : Option (List UInt8) → Comp
  | none => ['n']
  | some p => 'k' :: p.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

/-- **The file of a target** under the preopen `root`. -/
def keyFile (root : String) (t : Target) : FPath :=
  ⟨root, [String.ofList (keyName t.pathWithQuery)]⟩

/-- An import call of the store. -/
def sop (f : FnName) (hf : f ∈ storeList := by simp [storeList, proxyList, fsList]) (a : List Val) :
    (nsig storeImports).Op :=
  (⟨f, hf⟩, a)

/-- The proxy slice is part of the store's imports. -/
theorem proxy_sub : proxyImports ⊆ storeImports := fun _ h => List.mem_append_left _ h

/-- A program over the proxy slice, as a program of the store. -/
def widen : BProg proxyImports → BProg storeImports
  | .pure r => .pure r
  | .call m k => .call (⟨m.1.1, proxy_sub m.1.2⟩, m.2) fun n => widen (k n)

/-- Answer the outparam `o` with `resp` (`answer`). -/
def answerS (o : BitVec 32) (resp : Response) : BProg storeImports := widen (answer o resp)

/-- What the store does with a method. -/
inductive Kind where
  | get | head | put | delete | options | notAllowed | other
  deriving DecidableEq

/-- The kind of a method. -/
def kindOf : Method → Kind
  | .get => .get
  | .head => .head
  | .put => .put
  | .delete => .delete
  | .options => .options
  | .post | .connect | .trace | .patch => .notAllowed
  | .other _ => .other

/-- The kind of the answer of `method()` (`none`: not a method). -/
def kindAns : Option (List Val) → Option Kind
  | some [.variant 0 none] => some .get
  | some [.variant 1 none] => some .head
  | some [.variant 2 none] => some .notAllowed
  | some [.variant 3 none] => some .put
  | some [.variant 4 none] => some .delete
  | some [.variant 5 none] => some .notAllowed
  | some [.variant 6 none] => some .options
  | some [.variant 7 none] => some .notAllowed
  | some [.variant 8 none] => some .notAllowed
  | some [.variant 9 (some _)] => some .other
  | _ => none

/-- The preopen descriptor of an answer of `get-directories` (its first entry). -/
def preOf : Option (List Val) → BitVec 32
  | some [.record (.record [.u32 h, _] :: _)] => h
  | _ => 0

/-- The arguments of `open-at(d, {}, name, {create, truncate}, {read, write})`. -/
def openArgs (d : BitVec 32) (name : Comp) (create : Bool) : List Val :=
  [.u32 d, .record [.bool false], strC name,
    .record [.bool create, .bool false, .bool false, .bool create], .record [.bool true, .bool create]]

/-- The length of every `read` of a file: the largest `u64`. -/
def maxRead : Nat := 2 ^ 64 - 1

/-- The contents in an answer of `read`. -/
def readData : Option (List Val) → Option (List UInt8)
  | some [.variant 0 (some (.record [v, .bool _]))] => (u8sV v).map (List.map UInt8.ofBitVec)
  | _ => none

/-- An `ok(d)` answer of `open-at`. -/
def openFd : Option (List Val) → Option (BitVec 32)
  | some [.variant 0 (some (.u32 d))] => some d
  | _ => none

/-- An `error(no-entry)` answer. -/
def isNoEntry : Option (List Val) → Bool
  | some [.variant 1 (some (.variant 20 none))] => true
  | _ => false

/-- `GET` and `HEAD` (`head`): open the file and read it whole. -/
def getPath (o : BitVec 32) (name : Comp) (head : Bool) : BProg storeImports :=
  .call (sop getDirs (a := [])) fun nd =>
  .call (sop openAt (a := openArgs (preOf nd) name false)) fun no =>
  match openFd no with
  | some fd =>
    .call (sop fdRead (a := [.u32 fd, .u64 (BitVec.ofNat 64 maxRead), .u64 0])) fun nr =>
    match readData nr with
    | some c => answerS o (Response.simple 200 (if head then [] else c))
    | none => answerS o failResp
  | none => if isNoEntry no then answerS o (Response.simple 404 []) else answerS o failResp

/-- `PUT` of the contents `c`: create (and truncate) the file and write `c`. -/
def putFile (o : BitVec 32) (name : Comp) (c : List UInt8) : BProg storeImports :=
  if maxRead ≤ c.length then answerS o (Response.simple 413 []) else
  .call (sop getDirs (a := [])) fun nd =>
  .call (sop openAt (a := openArgs (preOf nd) name false)) fun no =>
  .call (sop openAt (a := openArgs (preOf nd) name true)) fun nc =>
  match openFd nc with
  | some fd =>
    .call (sop fdWrite (a := [.u32 fd, u8sC (bitsOf c), .u64 0])) fun nw =>
    match nw with
    | some [.variant 0 (some (.u64 _))] =>
      answerS o (Response.simple (if (openFd no).isSome then 204 else 201) [])
    | _ => answerS o failResp
  | none => answerS o failResp

/-- Read the stream `s` at most `n` times after `acc`, then continue with the contents. -/
def readBody (o s : BitVec 32) (k : List UInt8 → BProg storeImports) :
    Nat → List UInt8 → BProg storeImports
  | 0, _ => answerS o failResp
  | n + 1, acc => .call (sop inRead (a := [.u32 s, .u64 readLen])) fun
    | some [.variant 0 (some bs)] => readBody o s k n (acc ++ (bytesOf bs).map UInt8.ofBitVec)
    | some [.variant 1 (some (.variant 1 none))] => k acc
    | _ => answerS o failResp

/-- `PUT`: read the request body, then `putFile`. -/
def putPath (o r : BitVec 32) (name : Comp) : BProg storeImports :=
  .call (sop reqConsume (a := [.u32 r])) fun
  | some [.variant 0 (some (.u32 b))] => .call (sop inStream (a := [.u32 b])) fun
    | some [.variant 0 (some (.u32 s))] => readBody o s (putFile o name) echoFuel []
    | _ => answerS o failResp
  | _ => answerS o failResp

/-- `DELETE`: unlink the file. -/
def delPath (o : BitVec 32) (name : Comp) : BProg storeImports :=
  .call (sop getDirs (a := [])) fun nd =>
  .call (sop unlinkAt (a := [.u32 (preOf nd), strC name])) fun nu =>
  match nu with
  | some [.variant 0 none] => answerS o (Response.simple 204 [])
  | _ => if isNoEntry nu then answerS o (Response.simple 404 []) else answerS o failResp

/-- **The file-backed store component.** -/
def storeBody : Body storeImports storeWorld.exports := fun q =>
  .call (sop reqMethod (a := [.u32 (reqOf q.2)])) fun nm =>
  .call (sop reqPath (a := [.u32 (reqOf q.2)])) fun np =>
  match kindAns nm with
  | some .get => getPath (outOf q.2) (keyName (pathOf np)) false
  | some .head => getPath (outOf q.2) (keyName (pathOf np)) true
  | some .put => putPath (outOf q.2) (reqOf q.2) (keyName (pathOf np))
  | some .delete => delPath (outOf q.2) (keyName (pathOf np))
  | some .options => answerS (outOf q.2) (Response.simple 204 [])
  | some .notAllowed => answerS (outOf q.2) (Response.simple 405 [])
  | some .other => answerS (outOf q.2) (Response.simple 501 [])
  | none => answerS (outOf q.2) failResp

/-! ## The component read as a server -/

/-- The events of the run of `handle(0, 1)` for the request `q` with the files `fs`. -/
def runStore (root : String) (fs : Fs) (q : Request) : List WEv :=
  (Calls.runP (storeHost root q fs) [] (storeBody handleQ)).1

/-- **The store component as an atomic handler**: the response of a complete run of `handle`
over the host, and the files it leaves. -/
def storeHandler (root : String) : Atomic Fs Request Response := fun fs q resp fs' =>
  respOf 1 (runStore root fs q) = some resp ∧ fs' = (replay root fs (runStore root fs q)).files

/-- **The store component as a server** over files nobody else edits. -/
def wasiStore (root : String) (fs₀ : Fs) : Server Request Response :=
  Server.closed (storeHandler root) fs₀

/-! ## The specification -/

/-- A response without header fields or trailers. -/
def noFields (s : Response) : Response := Response.simple s.status s.content

/-- The handler `A` with its responses read through `g`. -/
def _root_.Silmaril.Servers.State.Atomic.mapResp {σ Req Resp : Type} (g : Resp → Resp)
    (A : Atomic σ Req Resp) : Atomic σ Req Resp :=
  fun s r resp s' => ∃ x, A s r x s' ∧ resp = g x

/-- The handler `A` on the requests satisfying `P` only (other requests are never answered). -/
def _root_.Silmaril.Servers.State.Atomic.guard {σ Req Resp : Type} (P : Req → Prop)
    (A : Atomic σ Req Resp) : Atomic σ Req Resp :=
  fun s r resp s' => P r ∧ A s r resp s'

/-- Requests whose content is shorter than `2^64 - 1` octets. -/
def smallReq (r : Request) : Prop := r.content.length < maxRead

/-- Files shorter than `2^64 - 1` octets. -/
def Small (fs : Fs) : Prop := ∀ p c, fs p = some c → c.length < maxRead

/-- **The specification**: `fileStoreStep (keyFile root)` without header fields, and `413` for
a `PUT` whose content is too long for a `read`. -/
def specStep (root : String) (fs : Fs) (r : Request) : Response × Fs :=
  if kindOf r.method = .put ∧ maxRead ≤ r.content.length then (Response.simple 413 [], fs)
  else (noFields (fileStoreStep (keyFile root) fs r).1, (fileStoreStep (keyFile root) fs r).2)

/-- **The specification server** (the `fileStore` of state model (b), without header fields,
`413` for a `PUT` too long to read back). -/
def specStore (root : String) (fs₀ : Fs) : Server Request Response :=
  Server.closed (Atomic.ofFun (specStep root)) fs₀

/-- **`fileStore` without header fields, on short requests**. -/
def fileStoreNF (root : String) (fs₀ : Fs) : Server Request Response :=
  Server.closed ((Atomic.ofFun (fileStoreStep (keyFile root))).mapResp noFields |>.guard smallReq) fs₀

/-- The store component on short requests. -/
def wasiStoreSmall (root : String) (fs₀ : Fs) : Server Request Response :=
  Server.closed ((storeHandler root).guard smallReq) fs₀

end Silmaril.Servers.WasiFs
