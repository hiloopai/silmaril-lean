module

public import Silmaril.Wasi.Versions.HttpBodyOver.Defs

@[expose] public section

/-!
# HTTP with response bodies across versions: 0.2 over 0.3 (buffering)

**`httpB2Over3 rounds`** imports the 0.3 HTTP functions with bodies (`httpBody3Fns`) and
exports the 0.2 ones (`httpBodyImports`). It is the converse of `httpB3Over2`
(`Silmaril.Wasi.Versions.HttpBodyOver`) and extends `http2Over3` (`Silmaril.Wasi.Versions.HttpOver`)
with the response body.

* `set-authority` / `set-path-with-query` call the 0.3 setter with the same arguments.
* `handle(r, _)` does the whole 0.3 response protocol within the call: the async `send(r)`
  observed sync-lowered; on `ok(rs)`: `get-status-code(rs)`, then
  `consume-body(rs, 0)` (the `res` future argument is a placeholder handle `0`: `future.new`
  is not modelled, and the theory does not read the argument), then `stream.read(rd, 65536)`
  until `DROPPED` (`BLOCKED` answers retried; at most `rounds` reads, `readAll3`), then
  `future.read(fu)` while it answers `BLOCKED` (at most `rounds` times, `pollFut3`) and, for
  trailers, `copy-all(t)`. It stores the inner result, the status, the body bytes and the
  trailer outcome (`TrInfo`) under a fresh 0.2 future `f` and answers `ok(f)`. On `error(code)`
  of `send` it stores the error. Any other answer (a trap, rounds running out, an ill-typed
  answer) is a trap.
* `future-incoming-response.get(f)` answers the stored inner result (`some(err)` once
  retrieved); retrieving `ok(rs)` records the stored status, body and trailers for `rs`.
* `incoming-response.status(rs)` answers the recorded status (`200` for an unknown handle).
* `consume(rs)` hands out a fresh body handle `b` with the recorded body of `rs`;
  `stream(b)` a fresh stream `s` whose buffer is the body; `read` / `blocking-read(s, len)`
  answer from the buffer as `bodyImpl` does (`readAns`: the next at most `len` bytes,
  `error(closed)` at the end); `finish(b)` a fresh trailer future with the trailer outcome of
  `b`; `future-trailers.get` the outcome (`some(ok(ok(none)))`, `some(ok(ok(some(t))))` with
  a fresh trailer handle `t`, or `some(ok(error(code)))`); `entries(t)` the buffered
  `copy-all` answer. No import call. An unknown handle is a trap.

As for `httpB3Over2`, buffering is the simplest correct strategy: all 0.3 calls of a response
happen within `handle`, so no other call can reuse a 0.3 handle in between. The cost is that
`handle` reads the whole body before it returns; a streaming adapter is not covered.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (packCopy CopyResult)

/-! ## Imports -/

/-- An outgoing 0.3 function is a 0.3 function with bodies. -/
theorem http3Fns_subB : http3Fns ⊆ httpBody3Fns := Set.subset_union_left

/-- `send` as a 0.3 import with bodies. -/
def jSend : {f // f ∈ httpBody3Fns} := ⟨send3, http3Fns_subB iSend3.2⟩
/-- `set-authority` as a 0.3 import with bodies. -/
def jSetAuth : {f // f ∈ httpBody3Fns} := ⟨setAuth3, http3Fns_subB iSetAuth3.2⟩
/-- `set-path-with-query` as a 0.3 import with bodies. -/
def jSetPath : {f // f ∈ httpBody3Fns} := ⟨setPath3, http3Fns_subB iSetPath3.2⟩
/-- `get-status-code` as a 0.3 import with bodies. -/
def jStatus : {f // f ∈ httpBody3Fns} := ⟨getStatus3, http3Fns_subB iStatus3.2⟩
/-- `consume-body` as a 0.3 import. -/
def jConsume : {f // f ∈ httpBody3Fns} := ⟨consumeBody3, Or.inr (by simp [bodyFns3_eq])⟩
/-- `stream.read` as a 0.3 import. -/
def jRead : {f // f ∈ httpBody3Fns} := ⟨P3.cStreamRead, Or.inr (by simp [bodyFns3_eq])⟩
/-- `future.read` as a 0.3 import. -/
def jFut : {f // f ∈ httpBody3Fns} := ⟨P3.cFutureRead, Or.inr (by simp [bodyFns3_eq])⟩
/-- `copy-all` as a 0.3 import. -/
def jCopy : {f // f ∈ httpBody3Fns} := ⟨copyAll3, Or.inr (by simp [bodyFns3_eq])⟩

/-! ## The component -/

/-- What `handle` buffers for a response: the status, the body bytes, the trailer outcome. -/
abbrev RInfo : Type := BitVec 16 × List (BitVec 8) × TrInfo

/-- The state of `httpB2Over3`. -/
structure B2St where
  /-- Per 0.2 future: the stored inner result and response info (`none`: already retrieved). -/
  pend : List (BitVec 32 × Option (Val × RInfo)) := []
  /-- Per response handle: the recorded info. -/
  resp : List (BitVec 32 × RInfo) := []
  /-- Per incoming-body handle: the body bytes and trailer outcome. -/
  bodies : List (BitVec 32 × (List (BitVec 8) × TrInfo)) := []
  /-- Per input stream: the remaining bytes. -/
  bufs : List (BitVec 32 × List (BitVec 8)) := []
  /-- Per trailer future: the trailer outcome. -/
  ftr : List (BitVec 32 × TrInfo) := []
  /-- Per trailer handle: the buffered `copy-all` answer. -/
  trv : List (BitVec 32 × Option (List Val)) := []
  /-- The next fresh handle. -/
  next : Nat := 0

/-- The program run by `httpB2Over3`. -/
abbrev BProg2 : Type := SProg B2St httpBody3Fns

/-- The fresh handle of the state. -/
def B2St.fresh (st : B2St) : BitVec 32 := BitVec.ofNat 32 st.next

/-- The read length of `readAll3`. -/
def readLen3 : Nat := 65536

/-- A trap. -/
def trapB (st : B2St) : BProg2 := .pure (st, none)

/-- Read the stream `rd` until `DROPPED`, at most `k` times; `acc` holds the bytes so far. -/
def readAll3 (st : B2St) (rd : BitVec 32) (kont : List (BitVec 8) → BProg2) :
    Nat → List (BitVec 8) → BProg2
  | 0, _ => trapB st
  | k + 1, acc => .call (jRead, [.u32 rd, P3.natV readLen3]) fun r =>
    match r with
    | some [.u32 pv, .record vs] =>
      match copy3 pv with
      | some none => readAll3 st rd kont k acc
      | some (some (.completed, _)) =>
        match u8sOf vs with
        | some bs => readAll3 st rd kont k (acc ++ bs)
        | none => trapB st
      | some (some (.dropped, 0)) => kont acc
      | _ => trapB st
    | _ => trapB st

/-- Poll the trailer future `fu` while it answers `BLOCKED`, at most `k` times. -/
def pollFut3 (st : B2St) (fu : BitVec 32) (kont : TrInfo → BProg2) : Nat → BProg2
  | 0 => trapB st
  | k + 1 => .call (jFut, [.u32 fu]) fun r =>
    match r with
    | some [_] => pollFut3 st fu kont k
    | some [_, .variant 0 (some (.variant 0 none))] => kont .noTr
    | some [_, .variant 0 (some (.variant 1 (some (.u32 t))))] =>
      .call (jCopy, [.u32 t]) fun r₂ => kont (.tr r₂)
    | some [_, .variant 1 (some (.variant c p))] => kont (.err (.variant c p))
    | _ => trapB st

/-- Store `x` for a fresh 0.2 future and answer `ok(f)`. -/
def storeFutB (st : B2St) (x : Val × RInfo) : B2St × Option (List Val) :=
  ({ st with pend := (st.fresh, some x) :: st.pend, next := st.next + 1 },
   some [okV (some (.u32 st.fresh))])

/-- After `get-status-code(rs)` answered `s`: the body and the trailers. -/
def bodyOfProg (rounds : Nat) (st : B2St) (rs : BitVec 32) (s : BitVec 16) : BProg2 :=
  .call (jConsume, [.u32 rs, .u32 0]) fun r =>
    match r with
    | some [.record [.u32 rd, .u32 fu]] =>
      readAll3 st rd (fun bytes =>
        pollFut3 st fu (fun i => .pure (storeFutB st (okV (some (.u32 rs)), s, bytes, i))) rounds)
        rounds []
    | _ => trapB st

/-- After `send` answered `ok(rs)`: the status, then the body. -/
def afterSendB (rounds : Nat) (st : B2St) (rs : BitVec 32) : BProg2 :=
  .call (jStatus, [.u32 rs]) fun r =>
    match r with
    | some [.u16 s] => bodyOfProg rounds st rs s
    | _ => trapB st

/-- The program of `handle(r, _)` for the request `r`. -/
def sendProgB (rounds : Nat) (st : B2St) (r : BitVec 32) : BProg2 :=
  .call (jSend, [.u32 r]) fun r₁ =>
    match r₁ with
    | some [.variant 0 (some (.u32 rs))] => afterSendB rounds st rs
    | some [.variant 1 (some (.variant k p))] =>
      .pure (storeFutB st (errV (some (.variant k p)), 0, [], .noTr))
    | _ => trapB st

/-- The program of `handle(r, _)`. -/
def handleProgB (rounds : Nat) (st : B2St) (a : List Val) : BProg2 :=
  match a with
  | .u32 r :: _ => sendProgB rounds st r
  | _ => trapB st

/-- The info of a retrieved inner result `ok(rs)`, recorded for `rs`. -/
def recResp (x : Val) (i : RInfo) (l : List (BitVec 32 × RInfo)) : List (BitVec 32 × RInfo) :=
  match x with
  | .variant 0 (some (.u32 rs)) => (rs, i) :: l
  | _ => l

/-- The result of `get(f)` (no import call). -/
def getResB (st : B2St) (a : List Val) : B2St × Option (List Val) :=
  match a with
  | .u32 fu :: _ =>
    match lookup fu st.pend with
    | some (some (x, i)) =>
      ({ st with pend := (fu, none) :: st.pend, resp := recResp x i st.resp },
       some [.variant 1 (some (.variant 0 (some x)))])
    | _ => (st, some [gotV])
  | _ => (st, some [gotV])

/-- The result of `status(rs)` (no import call). -/
def statusResB (st : B2St) (a : List Val) : B2St × Option (List Val) :=
  (st, some [.u16 ((lookup (selfH a) st.resp).map (·.1) |>.getD 200)])

/-- The result of `consume(rs)`. -/
def consumeResB (st : B2St) (a : List Val) : B2St × Option (List Val) :=
  match a with
  | .u32 rs :: _ =>
    match lookup rs st.resp with
    | some (_, bytes, i) =>
      ({ st with bodies := (st.fresh, (bytes, i)) :: st.bodies, next := st.next + 1 },
       some [okV (some (.u32 st.fresh))])
    | none => (st, none)
  | _ => (st, none)

/-- The result of `stream(b)`. -/
def streamResB (st : B2St) (a : List Val) : B2St × Option (List Val) :=
  match a with
  | .u32 b :: _ =>
    match lookup b st.bodies with
    | some (bytes, _) =>
      ({ st with bufs := (st.fresh, bytes) :: st.bufs, next := st.next + 1 },
       some [okV (some (.u32 st.fresh))])
    | none => (st, none)
  | _ => (st, none)

/-- The result of `read` / `blocking-read(s, len)`. -/
def readResB (st : B2St) (a : List Val) : B2St × Option (List Val) :=
  match a with
  | .u32 s :: _ =>
    match lookup s st.bufs with
    | some rest =>
      ({ st with bufs := (s, rest.drop (rest.take (readLen a)).length) :: st.bufs },
       readAns rest (readLen a))
    | none => (st, none)
  | _ => (st, none)

/-- The result of `finish(b)`. -/
def finishResB (st : B2St) (a : List Val) : B2St × Option (List Val) :=
  match a with
  | .u32 b :: _ =>
    match lookup b st.bodies with
    | some (_, i) =>
      ({ st with ftr := (st.fresh, i) :: st.ftr, next := st.next + 1 }, some [.u32 st.fresh])
    | none => (st, none)
  | _ => (st, none)

/-- The result of `future-trailers.get(ft)`. -/
def trGetResB (st : B2St) (a : List Val) : B2St × Option (List Val) :=
  match a with
  | .u32 ft :: _ =>
    match lookup ft st.ftr with
    | some .noTr => (st, some [.variant 1 (some (okV (some (okV (some noneV)))))])
    | some (.tr ans) =>
      ({ st with trv := (st.fresh, ans) :: st.trv, next := st.next + 1 },
       some [.variant 1 (some (okV (some (okV (some (.variant 1 (some (.u32 st.fresh))))))))])
    | some (.err v) => (st, some [.variant 1 (some (okV (some (errV (some v)))))])
    | none => (st, none)
  | _ => (st, none)

/-- The result of `entries(t)`. -/
def entriesResB (st : B2St) (a : List Val) : B2St × Option (List Val) :=
  match a with
  | .u32 t :: _ =>
    match lookup t st.trv with
    | some ans => (st, ans)
    | none => (st, none)
  | _ => (st, none)

/-- The result of a 0.2 body function (no import call). -/
def bodyRes2 (st : B2St) (f : FnName) (a : List Val) : B2St × Option (List Val) :=
  if f = consume2 then consumeResB st a
  else if f = bodyStream2 then streamResB st a
  else if isReadFn f then readResB st a
  else if f = bodyFinish2 then finishResB st a
  else if f = trGet2 then trGetResB st a
  else entriesResB st a

/-- **HTTP with bodies, 0.2 over 0.3.** -/
def httpB2Over3 (rounds : Nat) : SBody B2St httpBody3Fns httpBodyImports := fun st q =>
  if q.1.1 = setAuthority then .call (jSetAuth, q.2) fun r => .pure (st, r)
  else if q.1.1 = setPath then .call (jSetPath, q.2) fun r => .pure (st, r)
  else if q.1.1 = httpHandle then handleProgB rounds st q.2
  else if q.1.1 = futGet then .pure (getResB st q.2)
  else if q.1.1 = respStatus then .pure (statusResB st q.2)
  else .pure (bodyRes2 st q.1.1 q.2)

/-! ## The invariant -/

/-- Recorded response info that matches the body web for a request of key `k`. -/
def RespOk (B : BWeb) (k : Val × Val) (v : RInfo) : Prop :=
  B.web k.1 k.2 = .status v.1 ∧ v.2.1 = B.body k ∧ InfoOk B k v.2.2

/-- A buffered body and trailer outcome that match the body web for a request of key `k`. -/
def BodyOk (B : BWeb) (k : Val × Val) (v : List (BitVec 8) × TrInfo) : Prop :=
  v.1 = B.body k ∧ InfoOk B k v.2

/-- A stored result for a request of key `k`: it matches the web, and a response comes with
info that matches the body web. -/
def PendB (B : BWeb) (k : Val × Val) (x : Val × RInfo) : Prop :=
  outcomeOk (B.web k.1 k.2) x.1 = true ∧ ∀ rs, x.1 = .variant 0 (some (.u32 rs)) → RespOk B k x.2

/-- **The invariant of `httpB2Over3`** over the body web `B`: the 0.2 and 0.3 states agree on
the requests; every stored result is for a tied 0.2 future and matches the web; every response,
body, body stream, trailer future and trailer resource the 0.2 theory tracks has buffered data
that matches the body web. The body part of the 0.3 state is not constrained. -/
def JB2 (B : BWeb) (st : B2St) (q3 : Body3St) (q2 : BodySt) : Prop :=
  q2.base.auth = q3.base.auth ∧ q2.base.path = q3.base.path ∧
  (∀ fu x, lookup fu st.pend = some (some x) → ∃ k, lookup fu q2.base.futs = some k ∧ PendB B k x) ∧
  (∀ rs k, lookup rs q2.base.resps = some k → ∃ v, lookup rs st.resp = some v ∧ RespOk B k v) ∧
  (∀ b k, lookup b q2.bodies = some (some k) → ∃ v, lookup b st.bodies = some v ∧ BodyOk B k v) ∧
  (∀ s k n, lookup s q2.streams = some (some (k, n)) → lookup s st.bufs = some ((B.body k).drop n)) ∧
  (∀ ft k, lookup ft q2.ftr = some (some k) → ∃ i, lookup ft st.ftr = some i ∧ InfoOk B k i) ∧
  (∀ t k, lookup t q2.trs = some (some k) →
    ∃ ans, lookup t st.trv = some ans ∧ entriesOk (B.trailers k) ans = true)

/-- The postcondition of the program of `handle(a)` from the 0.2 state `q2`: its answer is
accepted by the 0.2 theory with bodies, and `JB2` holds after it. -/
def PostH (B : BWeb) (q2 : BodySt) (a : List Val) : B2St × Option (List Val) → Body3St → Prop :=
  fun x q3' => ∃ q2', (bodyTh B).step q2 (.imp httpHandle a x.2) = some q2' ∧ JB2 B x.1 q3' q2'

end Silmaril.Wasi.Versions.Net
