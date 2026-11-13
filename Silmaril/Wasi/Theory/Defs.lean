module

public import Silmaril.Wasi.Host.Defs
public import Silmaril.Wasm.Resource.Handle.Defs

@[expose] public section

/-!
# WASI theories: `wasi:clocks`, `wasi:cli/stdout`, a `wasi:filesystem` slice

The functions, worlds, theories and concrete hosts of three small WASI slices.

## Value encodings

`Silmaril.Wasm.Component.Val` has no lists, strings or handles: `list<u8>` is encoded as a record of
`u8`s (`bytesV`), `string` as a record of `char`s (`strV`), handles (`own`/`borrow`) as their
`u32` table index, `result<T, E>` as the variant cases `0` (`ok`) and `1` (`error`). The
arguments of a function are the flattened WIT parameters (a method takes `self` first).

## Functions and worlds

* `wasi:clocks/monotonic-clock.now : func() -> instant` (`clockNow`).
* `wasi:cli/stdout.get-stdout : func() -> own<output-stream>`,
  `wasi:io/streams.[method]output-stream.blocking-write-and-flush(self, contents: list<u8>) ->
  result<_, stream-error>` and `[resource-drop]output-stream` (`getStdout`, `streamWrite`,
  `streamDrop`).
* `wasi:filesystem/preopens.get-directories : func() -> list<tuple<own<descriptor>, string>>`,
  and from `wasi:filesystem/types` the descriptor methods `open-at(self, path) ->
  result<own<descriptor>, error-code>` (the path and open flags are dropped from this slice),
  `write(self, buffer, offset) -> result<filesize, error-code>`,
  `read(self, length, offset) -> result<tuple<list<u8>, bool>, error-code>` and
  `[resource-drop]descriptor`.
* `clocksWorld`, `stdoutWorld`, `fsWorld` (with the export `wasi:cli/run.run`, or for the
  clock example `example:clock/check.check`), and `cliWorld`, their union.

## Theories (axioms on the host's answers)

* `clockTh`: `now` answers a `u64` instant, never smaller than the previous one (monotonicity).
* `stdoutTyped`, `fsTyped`: the answers have the WIT result types (`pointwise` protocols).

## Guarantees (on the component's events)

* `stdoutHandles`, `fsHandles`: the client handle protocol of `Silmaril.Wasm.Resource.Handle`
  (`handleProto _ .client`): an output stream or descriptor is used or dropped only while live.
  Allocations are the host's answers (`get-stdout`, `get-directories`, `open-at`), uses and
  drops the component's requests. A host handing out a live handle again is an environment
  fault, after which everything is accepted.
* `retTrue`: every export call returns `true`.

## Concrete hosts

`clockImpl` (a saturating tick counter), `stdoutImpl` (fresh stream handles, writes succeed),
`fsImpl` (one preopened directory `/`, fresh descriptors, a write reports its length, a read
returns the bytes written so far through that descriptor).

A Silmaril addition.
-/

namespace Silmaril.Wasi

open Silmaril.Games
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol HEv handleProto Role)

/-! ## Encodings -/

/-- `list<u8>`. -/
def bytesV (b : List (BitVec 8)) : Val := .record (b.map .u8)

/-- `string`. -/
def strV (s : String) : Val := .record (s.toList.map .char)

/-- `ok(v)`. -/
def okV (v : Option Val) : Val := .variant 0 v

/-- `error(v)`. -/
def errV (v : Option Val) : Val := .variant 1 v

/-! ## Functions -/

/-- `wasi:clocks/monotonic-clock.now`. -/
def clockNow : FnName := ⟨"wasi:clocks/monotonic-clock", "now"⟩
/-- `wasi:cli/stdout.get-stdout`. -/
def getStdout : FnName := ⟨"wasi:cli/stdout", "get-stdout"⟩
/-- `wasi:io/streams.[method]output-stream.blocking-write-and-flush`. -/
def streamWrite : FnName := ⟨"wasi:io/streams", "[method]output-stream.blocking-write-and-flush"⟩
/-- `wasi:io/streams.[resource-drop]output-stream`. -/
def streamDrop : FnName := ⟨"wasi:io/streams", "[resource-drop]output-stream"⟩
/-- `wasi:filesystem/preopens.get-directories`. -/
def getDirs : FnName := ⟨"wasi:filesystem/preopens", "get-directories"⟩
/-- `wasi:filesystem/types.[method]descriptor.open-at`. -/
def openAt : FnName := ⟨"wasi:filesystem/types", "[method]descriptor.open-at"⟩
/-- `wasi:filesystem/types.[method]descriptor.write`. -/
def fdWrite : FnName := ⟨"wasi:filesystem/types", "[method]descriptor.write"⟩
/-- `wasi:filesystem/types.[method]descriptor.read`. -/
def fdRead : FnName := ⟨"wasi:filesystem/types", "[method]descriptor.read"⟩
/-- `wasi:filesystem/types.[resource-drop]descriptor`. -/
def fdDrop : FnName := ⟨"wasi:filesystem/types", "[resource-drop]descriptor"⟩
/-- `wasi:cli/run.run`. -/
def cliRun : FnName := ⟨"wasi:cli/run", "run"⟩
/-- `example:clock/check.check`, an example export returning `bool`. -/
def clockCheck : FnName := ⟨"example:clock/check", "check"⟩

/-! ## Worlds -/

/-- The clock slice. -/
def clocksWorld : World := ⟨{clockNow}, {clockCheck}⟩
/-- The stdout slice. -/
def stdoutWorld : World := ⟨{getStdout, streamWrite, streamDrop}, {cliRun}⟩
/-- The filesystem slice. -/
def fsWorld : World := ⟨{getDirs, openAt, fdWrite, fdRead, fdDrop}, {cliRun}⟩
/-- The union of the three slices. -/
def cliWorld : World := (clocksWorld.union stdoutWorld).union fsWorld

/-! ## Protocol helpers -/

/-- A protocol checking every event on its own. -/
def pointwise (ok : WEv → Bool) : Protocol Unit WEv := ⟨(), fun _ e => if ok e then some () else none⟩

/-- The protocol accepting everything (no assumption). -/
def topP : Protocol Unit WEv := pointwise fun _ => true

/-- A protocol read through a classifier producing several events per event. -/
def comapList {S E E' : Type} (g : E' → List E) (p : Protocol S E) : Protocol S E' :=
  ⟨p.init, fun q e => p.run q (g e)⟩

/-! ## The clock theory -/

/-- An answer of `now` after the instant `last`. -/
def nowStep (last : Option (BitVec 64)) : Option (List Val) → Option (Option (BitVec 64))
  | some [.u64 x] => if last.all fun l => decide (l ≤ x) then some (some x) else none
  | _ => none

/-- One step of the clock theory: the last instant answered, if any. -/
def clockStep (last : Option (BitVec 64)) : WEv → Option (Option (BitVec 64))
  | .imp f _ r => if f = clockNow then nowStep last r else some last
  | _ => some last

/-- **The monotonic clock theory**: `now` answers `u64` instants that never decrease. -/
def clockTh : Protocol (Option (BitVec 64)) WEv := ⟨none, clockStep⟩

/-! ## Typing theories -/

/-- The answers of the stdout slice are well typed (other functions are unconstrained). -/
def stdoutOk : WEv → Bool
  | .imp f _ r =>
    if f = getStdout then (match r with | some [.u32 _] => true | _ => false)
    else if f = streamWrite then
      (match r with | some [.variant 0 none] => true | some [.variant 1 (some _)] => true
                    | _ => false)
    else if f = streamDrop then (match r with | some [] => true | _ => false)
    else true
  | _ => true

/-- **The stdout typing theory.** -/
def stdoutTyped : Protocol Unit WEv := pointwise stdoutOk

/-- A preopen entry `(own<descriptor>, string)`. -/
def preopenOk : Val → Bool
  | .record [.u32 _, _] => true
  | _ => false

/-- The answers of the filesystem slice are well typed. -/
def fsOk : WEv → Bool
  | .imp f _ r =>
    if f = getDirs then (match r with | some [.record ds] => ds.all preopenOk | _ => false)
    else if f = openAt then
      (match r with | some [.variant 0 (some (.u32 _))] => true
                    | some [.variant 1 (some _)] => true | _ => false)
    else if f = fdWrite then
      (match r with | some [.variant 0 (some (.u64 _))] => true
                    | some [.variant 1 (some _)] => true | _ => false)
    else if f = fdRead then
      (match r with | some [.variant 0 (some (.record [.record _, .bool _]))] => true
                    | some [.variant 1 (some _)] => true | _ => false)
    else if f = fdDrop then (match r with | some [] => true | _ => false)
    else true
  | _ => true

/-- **The filesystem typing theory.** -/
def fsTyped : Protocol Unit WEv := pointwise fsOk

/-! ## Handle guarantees -/

/-- Output-stream handle events: `get-stdout` allocates, a write uses, a drop frees. -/
def stdoutHEv : WEv → HEv (BitVec 32)
  | .imp f _ (some [.u32 h]) => if f = getStdout then .alloc h else .skip
  | .req f (.u32 h :: _) =>
    if f = streamWrite then .use h else if f = streamDrop then .free h else .skip
  | _ => .skip

/-- **Stream handles are used and dropped only while live.** -/
def stdoutHandles : Protocol (Option (List (BitVec 32))) WEv :=
  (handleProto (BitVec 32) .client).comap stdoutHEv

/-- The descriptor of a preopen entry. -/
def preopenFd : Val → Option (HEv (BitVec 32))
  | .record [.u32 h, _] => some (.alloc h)
  | _ => none

/-- Descriptor handle events: `get-directories` and `open-at` allocate, the methods use, a drop
frees. -/
def fsHEv : WEv → List (HEv (BitVec 32))
  | .imp f _ (some [.record ds]) => if f = getDirs then ds.filterMap preopenFd else []
  | .imp f _ (some [.variant 0 (some (.u32 h))]) => if f = openAt then [.alloc h] else []
  | .req f (.u32 h :: _) =>
    if f = openAt ∨ f = fdWrite ∨ f = fdRead then [.use h] else if f = fdDrop then [.free h]
    else []
  | _ => []

/-- **Descriptors are used and dropped only while live.** -/
def fsHandles : Protocol (Option (List (BitVec 32))) WEv :=
  comapList fsHEv (handleProto (BitVec 32) .client)

/-! ## A client-side guarantee -/

/-- Every export call returns `true`. -/
def retTrueStep : Unit → WEv → Option Unit
  | _, .ret _ _ (some [.bool true]) => some ()
  | _, .ret .. => none
  | _, _ => some ()

/-- **Every export call returns `true`.** -/
def retTrue : Protocol Unit WEv := ⟨(), retTrueStep⟩

/-! ## Concrete hosts -/

/-- The largest `u64`. -/
def u64Max : Nat := 2 ^ 64 - 1

/-- **A tick clock**: `now` answers the number of answers given so far (saturating). -/
def clockImpl : Impl := fun p f _ =>
  if f = clockNow then some [.u64 (BitVec.ofNat 64 (min p.length u64Max))] else none

/-- **A stdout host**: fresh stream handles; writes and drops succeed. -/
def stdoutImpl : Impl := fun p f _ =>
  if f = getStdout then some [.u32 (BitVec.ofNat 32 p.length)]
  else if f = streamWrite then some [okV none]
  else if f = streamDrop then some []
  else none

/-- The bytes of an encoded `list<u8>`. -/
def bytesOf : Val → List (BitVec 8)
  | .record vs => vs.filterMap fun | .u8 b => some b | _ => none
  | _ => []

/-- The bytes written so far through the descriptor `fd`. -/
def writtenTo (fd : BitVec 32) : List WEv → List (BitVec 8)
  | [] => []
  | .imp f (.u32 d :: buf :: _) (some [.variant 0 _]) :: t =>
    (if f = fdWrite ∧ d = fd then bytesOf buf else []) ++ writtenTo fd t
  | _ :: t => writtenTo fd t

/-- **A filesystem host**: one preopened directory `/` (descriptor `0`), `open-at` gives a
fresh descriptor, a write succeeds and reports its length, a read returns everything written
through that descriptor (and end of file). -/
def fsImpl : Impl := fun p f a =>
  if f = getDirs then some [.record [.record [.u32 0, strV "/"]]]
  else if f = openAt then some [okV (some (.u32 (BitVec.ofNat 32 (p.length + 1))))]
  else if f = fdWrite then
    (match a with
     | _ :: buf :: _ => some [okV (some (.u64 (BitVec.ofNat 64 (bytesOf buf).length)))]
     | _ => some [errV (some (.variant 0 none))])
  else if f = fdRead then
    (match a with
     | .u32 d :: _ => some [okV (some (.record [bytesV (writtenTo d p), .bool true]))]
     | _ => some [errV (some (.variant 0 none))])
  else if f = fdDrop then some []
  else none

end Silmaril.Wasi
