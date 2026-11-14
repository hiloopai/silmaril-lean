module

public import Silmaril.Wasi.Versions.WitImport.PickRest.Defs
public import Silmaril.Wasi.Versions.HttpBody.Defs
public import Silmaril.Wasi.Versions.Http3.Defs
public import Silmaril.Wasi.Versions.P3.Defs

@[expose] public section

/-!
# WASI 0.3 `wasi:http` response bodies: streams and futures

Extends the 0.3 outgoing HTTP slice of `Silmaril.Wasi.Versions.Http3` (`httpTh3 W`) with the
response body, checked against `vendor/wasi/0.3.2/http/types.wit`:

* `[static]response.consume-body(this: response, res: future<result<_, error-code>>)
  -> tuple<stream<u8>, future<result<option<trailers>, error-code>>>` (`consumeBody3`);
* `[method]fields.copy-all() -> list<tuple<field-name, field-value>>` (`copyAll3`);
* the Component Model built-ins `stream.read` and `future.read` (`P3.cStreamRead`,
  `P3.cFutureRead`, imported from `$root` as in `Silmaril.Wasi.Versions.P3`), whose store model is
  `Silmaril.Wasm.Component.Async`: `stream.read(r, n) -> [packed, items]` with `packed` the
  `BLOCKED` code or `result | count << 4` (`P3.copyOf`), `future.read(f) -> [packed, value]` or
  `[BLOCKED]`.

The body is a `stream<u8>` and the trailers a `future`, both handed out by `consume-body`; the
web is a body web `B : BWeb` as in 0.2 (`Silmaril.Wasi.Versions.HttpBody`).

## The theory `body3Th B`

Gated, with the 0.3 HTTP state as `base` (moved by `http3Next`) and, per readable end of a body
stream, its request and the number of bytes delivered; per trailer future and trailer resource,
its request. Every handle handed out is recorded (`none` when untracked). The check is `http3Ok B.web` on the base and:

* `stream.read(r, n)` of a body stream: `BLOCKED`; `COMPLETED c` with `c ≤ n` and the items the
  next `c` bytes of the body (zero-length copies included, unlike the original `P3.fsReadTh3`,
  which `host3` refutes); `DROPPED 0` only when the whole body was delivered; or a trap;
* `future.read(f)` of a trailer future: blocked; `ok(t)` with `t` present exactly when the
  response has trailers; `error(_)` (the transfer failed); or a trap;
* `copy-all` of a trailer resource: the response's trailers.

## Concrete host

`body3Impl B`: as `httpImpl3 B.web` for the outgoing slice; each read delivers the next
`min n 2^27 remaining` bytes (so that the packed count fits in a `u32`, the bound that
`host3` lacks, `P3OverP2.Bounds`), `DROPPED 0` at the end; trailer futures are ready.

**Not modelled**: `request.new` with a body stream, `response.new`, headers, the `res` future
argument of `consume-body` (an argument the theory does not read), `stream.cancel-read` and
waitable sets on body streams.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasm.Component.Async (packCopy CopyResult)

/-- `wasi:http/types@0.3.2.[static]response.consume-body`. -/
def consumeBody3 : FnName := ⟨"wasi:http/types@0.3.2", "[static]response.consume-body"⟩
/-- `wasi:http/types@0.3.2.[method]fields.copy-all`. -/
def copyAll3 : FnName := ⟨"wasi:http/types@0.3.2", "[method]fields.copy-all"⟩

/-- The body functions of the 0.3 slice: the WIT functions **read from the vendored WIT**
(`http3T` with the keys `WitImport.body3Keys`) and two `canon` built-ins, which are not WIT
functions and stay hand-written. Proofs that need the members rewrite with `bodyFns3_eq`. -/
def bodyFns3 : Set FnName :=
  {f | f ∈ WitImport.pick (WitImport.names WitImport.http3T) WitImport.body3Keys ++
    [P3.cStreamRead, P3.cFutureRead]}

/-- **The imported body functions with the built-ins are the hand-written ones.** -/
theorem bodyFns3_eq : bodyFns3 = {consumeBody3, copyAll3, P3.cStreamRead, P3.cFutureRead} := by
  ext f
  show f ∈ WitImport.pick (WitImport.names WitImport.http3T) WitImport.body3Keys ++
    [P3.cStreamRead, P3.cFutureRead] ↔ _
  rw [(show (WitImport.pick (WitImport.names WitImport.http3T) WitImport.body3Keys ++
    [P3.cStreamRead, P3.cFutureRead]).Perm [consumeBody3, copyAll3, P3.cStreamRead, P3.cFutureRead] by
      decide +kernel).mem_iff]
  simp

/-- The 0.3 HTTP functions with bodies. -/
def httpBody3Fns : Set FnName := http3Fns ∪ bodyFns3

/-- A body function, as a test. -/
def isBodyFn3 (f : FnName) : Bool :=
  f == consumeBody3 || f == copyAll3 || f == P3.cStreamRead || f == P3.cFutureRead

/-- The state of the 0.3 body theory. -/
structure Body3St where
  /-- The state of the 0.3 outgoing HTTP theory. -/
  base : Http3St := {}
  /-- The request of each body stream and the number of bytes it delivered. -/
  streams : List (BitVec 32 × Option ((Val × Val) × Nat)) := []
  /-- The request of each trailer future. -/
  futs : List (BitVec 32 × Option (Val × Val)) := []
  /-- The request of each trailer resource. -/
  trs : List (BitVec 32 × Option (Val × Val)) := []

/-- The decoded packed code of a copy. -/
def copy3 (pv : BitVec 32) : Option (Option (CopyResult × Nat)) := P3.copyOf pv.toNat

/-- The number of items a `stream.read` answer completed. -/
def completed3 : Option (List Val) → Option Nat
  | some [.u32 pv, _] =>
    match copy3 pv with
    | some (some (.completed, c)) => some c
    | _ => none
  | _ => none

/-- The trailer handle of a `future.read` answer `ok(some(t))`. -/
def trHandle3 : Option (List Val) → Option (BitVec 32)
  | some [_, .variant 0 (some (.variant 1 (some (.u32 t))))] => some t
  | _ => none

/-- The body part of the next state. -/
def body3Step (q : Body3St) (e : WEv) : Body3St :=
  match e with
  | .imp f (.u32 h :: _) r =>
    if f = consumeBody3 then
      match r with
      | some [.record [.u32 rd, .u32 fu]] =>
        { q with streams := (rd, (lookup h q.base.resps).map (·, 0)) :: q.streams,
                 futs := (fu, lookup h q.base.resps) :: q.futs }
      | _ => q
    else if f = P3.cStreamRead then
      match lookup h q.streams, completed3 r with
      | some (some (k, n)), some c => { q with streams := (h, some (k, n + c)) :: q.streams }
      | _, _ => q
    else if f = P3.cFutureRead then
      match trHandle3 r with
      | some t => { q with trs := (t, (lookup h q.futs).join) :: q.trs }
      | none => q
    else q
  | _ => q

/-- **The next state.** -/
def body3Next (q : Body3St) (e : WEv) : Body3St :=
  { body3Step q e with base := http3Next q.base e }

/-- A `stream.read(r, n)` answer for the remaining bytes `rest`. -/
def read3Ok (rest : List (BitVec 8)) (n : Nat) : Option (List Val) → Bool
  | none => true
  | some [.u32 pv, items] =>
    match copy3 pv, items with
    | some none, _ => true
    | some (some (.completed, c)), .record vs =>
      decide (c ≤ n) && (match u8sOf vs with
        | some bs => decide (bs = rest.take c) && decide (bs.length = c)
        | none => false)
    | some (some (.dropped, 0)), _ => rest.isEmpty
    | _, _ => false
  | _ => false

/-- A `future.read` answer for the trailers `tr`. -/
def fut3Ok (tr : Option Fields) : Option (List Val) → Bool
  | none => true
  | some [_] => true
  | some [_, .variant 0 (some (.variant 0 none))] => tr.isNone
  | some [_, .variant 0 (some (.variant 1 (some (.u32 _))))] => tr.isSome
  | some [_, .variant 1 (some (.variant _ _))] => true
  | _ => false

/-- The `u32` count argument of `stream.read`. -/
def count3 (a : List Val) : Nat :=
  match a with
  | _ :: .u32 n :: _ => n.toNat
  | _ => 0

/-- The body part of the check. -/
def body3Check (B : BWeb) (q : Body3St) (e : WEv) : Bool :=
  match e with
  | .imp f (.u32 h :: a) r =>
    if f = P3.cStreamRead then
      match lookup h q.streams with
      | some (some (k, n)) => read3Ok ((B.body k).drop n) (count3 (.u32 h :: a)) r
      | _ => true
    else if f = P3.cFutureRead then
      match lookup h q.futs with
      | some (some k) => match B k.1 k.2 with
        | .resp _ => fut3Ok (B.trailers k) r
        | .error _ => true
      | _ => true
    else if f = copyAll3 then
      match lookup h q.trs with
      | some (some k) => entriesOk (B.trailers k) r
      | _ => true
    else true
  | _ => true

/-- The check of an answer against the body web `B`. -/
def body3Ok (B : BWeb) (q : Body3St) (e : WEv) : Bool := http3Ok B.web q.base e && body3Check B q e

/-- **The 0.3 HTTP theory with response bodies** of the body web `B`. -/
def body3Th (B : BWeb) : Protocol Body3St WEv := gated {} body3Next (body3Ok B)

/-! ## The concrete host -/

/-- The state after the answers `p`. -/
def body3State (p : List WEv) : Body3St := p.foldl body3Next {}

/-- The largest chunk of one read of the concrete host (`2^27`). -/
def chunk3 : Nat := 2 ^ 27

/-- The answer of `stream.read` of at most `n` items from `rest`. -/
def read3Ans (rest : List (BitVec 8)) (n : Nat) : Option (List Val) :=
  if rest.isEmpty then some [P3.natV (packCopy .dropped 0), bytesV []]
  else
    some [P3.natV (packCopy .completed (rest.take (min n chunk3)).length),
      bytesV (rest.take (min n chunk3))]

/-- The answer of `future.read` for the trailers `tr`. -/
def fut3Ans (t : BitVec 32) : Option Fields → Option (List Val)
  | none => some [P3.natV 0, okV (some noneV)]
  | some _ => some [P3.natV 0, okV (some (.variant 1 (some (.u32 t))))]

/-- The body functions of the concrete host. -/
def body3Ans (B : BWeb) (p : List WEv) (f : FnName) (a : List Val) : Option (List Val) :=
  if f = consumeBody3 then
    some [.record [P3.natV (2 * p.length), P3.natV (2 * p.length + 1)]]
  else if f = P3.cStreamRead then
    match lookup (selfH a) (body3State p).streams with
    | some (some (k, n)) => read3Ans ((B.body k).drop n) (count3 a)
    | _ => some [P3.natV (packCopy .dropped 0), bytesV []]
  else if f = P3.cFutureRead then
    match lookup (selfH a) (body3State p).futs with
    | some (some k) => fut3Ans (freshH p) (B.trailers k)
    | _ => some [P3.natV 0, errV (some (.variant 0 none))]
  else
    match lookup (selfH a) (body3State p).trs with
    | some (some k) => some [fieldsV ((B.trailers k).getD [])]
    | _ => some [fieldsV []]

/-- **The concrete 0.3 HTTP host with bodies** of the body web `B`. -/
def body3Impl (B : BWeb) : Impl := fun p f a =>
  if isBodyFn3 f then body3Ans B p f a else httpImpl3 B.web p f a

end Silmaril.Wasi.Versions.Net
