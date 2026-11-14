module

public import Silmaril.Wasi.Versions.P2OverP3.World.Defs
public import Silmaril.Wasi.Versions.Stateful.Defs

@[expose] public section

/-!
# WASI 0.2 over 0.3: the component

`p2OverP3 cap` is a stateful component (`Silmaril.Wasi.Versions.Stateful`) of the world
`p2OverP3World`: it imports WASI 0.3 with the Component Model async built-ins and exports the
WASI 0.2 `wasi:io`, `wasi:cli` and `wasi:clocks` functions of the slice `Silmaril.Wasi.Versions.P2`.
`cap` is the size of the buffer of an output stream (`p2OverP3 4096` is the default).

## Resources

* **An output stream** (`OutS`) wraps a WASI 0.3 `stream<u8>` writable end `w` and the
  `future<result<_, error-code>>` that `write-via-stream` returned for its readable end
  (`get-stdout`/`get-stderr`: `stream.new`, then `write-via-stream(r)`). It buffers the bytes
  the guest wrote and the reader has not taken yet (`buf`, at most `cap` after every
  `check-write` permit is respected), and remembers whether a `stream.write` of the buffer is in
  flight (`BLOCKED`) and whether the reader is gone (`DROPPED`, or an ill-typed answer).
* **An input stream** (`InS`) wraps the readable end and future of `stdin.read-via-stream`.
* **A pollable** (`PollK`) is the waitable of an output stream's writable end, an input stream,
  or a monotonic deadline (`subscribe-instant`/`subscribe-duration`; WASI 0.3 has no pollables).
* **The waitable set** is created at the first wait (`waitable-set.new`).

The component also keeps the 0.2 stream state of the `wasi:io` theory (`St.io : IoSt`, updated
by `ioUpd` with each of its own answers): which streams it reported closed and the permit of
the last `check-write`, as a 0.2 implementation must (a `write` beyond the permit traps, a closed
stream answers `error(closed)`).

## Functions

* `check-write`: start writing the buffer (`stream.write`, non-blocking), then report the free
  room `cap - |buf|` (a **conservative budget**: `0` while the reader has not taken the buffer).
* `write`/`write-zeroes`: trap beyond the permit; append to the buffer and start writing it.
* `blocking-write-and-flush`/`blocking-write-zeroes-and-flush` (trap beyond 4096 bytes),
  `blocking-flush`: append, then drive the buffer to the reader: `stream.write`; while a copy is
  in flight, `waitable.join` the writable end and `waitable-set.wait`; at most `rounds` rounds.
* `flush`: start writing the buffer. `splice`/`blocking-splice`: move nothing (`ok(0)`).
* `read`/`skip`: one `stream.read`; `blocking-read`/`blocking-skip`: `stream.read`, and while
  it is `BLOCKED` (or returns no bytes), wait on the readable end and read again (this encoding
  carries the items of a read in its answer, not in guest memory, so a read that completes
  after blocking is observed by the next `stream.read`).
* `subscribe`: a pollable of the stream. `pollable.ready`: an output stream's pollable is ready
  when no copy is in flight (after starting one, if the buffer is not empty); a deadline is
  ready when `now` has passed it; an input stream's pollable is always ready. `poll`/`block`:
  the ready pollables; if none, wait: on the in-flight writable ends with `waitable-set.wait`,
  or else on the first deadline with `monotonic-clock.wait-for` (an `async func`,
  **sync-lowered**: one blocking call, faithful by `Silmaril.Wasm.Component.Async.syncRun_result`);
  at most `rounds` rounds, then `poll` answers index `0` (a spurious wake-up).
* `wasi:cli`: `get-stdout`/`get-stderr`/`get-stdin` as above; `environment`, `terminal-*`,
  `exit` forwarded to WASI 0.3. `wasi:clocks`: `monotonic-clock.now`/`resolution` forwarded,
  `wall-clock` from `system-clock` (an `instant` with negative seconds is read as `0`).
  Answers of these functions are **lifted** at their WIT type (`cliFix`: the identity on
  well-typed answers, a fixed well-typed answer otherwise), as the canonical ABI's lifting does.
  `monotonic-clock.now` is forwarded unchanged (`cliOk` does not constrain it).

## Simplifications (stated, not hidden)

* A `BLOCKED` `stream.read` of `read` is not tracked (no `stream.cancel-read`).
* `rounds = 64` bounds every wait loop; a `blocking-*` call that has not finished then fails
  with `error(closed)` (blocking calls), `ok([])` (`blocking-read`) or a spurious index (`poll`).
* `splice` is not implemented (it moves nothing, which the WIT allows: "may return fewer").
* Events of `waitable-set.wait` other than `stream-write` (code `3`) are ignored.
* Input pollables are always ready (this is the **eager variant**, `eager_inp_ready`); the
  extension `Silmaril.Wasi.Versions.P2OverP3.Fs` probes them with zero-length reads.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.P2OverP3

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (CopyResult)
open Silmaril.Wasi.Versions.P3
open Silmaril.Wasi.Versions.P2

/-! ## State -/

/-- An output stream: a WASI 0.3 writable end and the future of `write-via-stream`. -/
structure OutS where
  /-- The writable end. -/
  w : Val
  /-- The future of `write-via-stream`. -/
  fut : Val
  /-- The bytes not yet taken by the reader. -/
  buf : List (BitVec 8) := []
  /-- A `stream.write` of the buffer is in flight. -/
  inflight : Bool := false
  /-- The reader is gone (or an answer was ill-typed). -/
  err : Bool := false

/-- An input stream: a WASI 0.3 readable end and its future. -/
structure InS where
  /-- The readable end. -/
  r : Val
  /-- The future of `read-via-stream`. -/
  fut : Val
  /-- The writer dropped the stream (end of file). -/
  eof : Bool := false

/-- What a pollable waits for. -/
inductive PollK where
  /-- The writable end of an output stream. -/
  | out (h : BitVec 32)
  /-- An input stream. -/
  | inp (h : BitVec 32)
  /-- A monotonic deadline. -/
  | timer (d : Nat)

/-- The implementation state. -/
structure ISt where
  /-- The next 0.2 handle. -/
  next : Nat := 0
  /-- Output streams. -/
  outs : List (BitVec 32 × OutS) := []
  /-- Input streams. -/
  ins : List (BitVec 32 × InS) := []
  /-- Pollables. -/
  polls : List (BitVec 32 × PollK) := []
  /-- The waitable set, once created. -/
  ws : Option Val := none

/-- The state of the component: the 0.2 stream state of its own answers, and the
implementation state. -/
structure St where
  /-- The `wasi:io` state of the answers given so far. -/
  io : IoSt
  /-- The implementation state. -/
  impl : ISt

/-- The initial state. -/
def St.init : St := ⟨ioInit, {}⟩

/-- Look a handle up. -/
def look {α : Type} (l : List (BitVec 32 × α)) (h : BitVec 32) : Option α :=
  (l.find? fun x => decide (x.1 = h)).map (·.2)

/-- A fresh 0.2 handle. -/
def ISt.fresh (st : ISt) : ISt × BitVec 32 := ({ st with next := st.next + 1 }, BitVec.ofNat 32 st.next)

/-- Update an output stream. -/
def ISt.setOut (st : ISt) (h : BitVec 32) (o : OutS) : ISt := { st with outs := (h, o) :: st.outs }

/-- Update an input stream. -/
def ISt.setIn (st : ISt) (h : BitVec 32) (i : InS) : ISt := { st with ins := (h, i) :: st.ins }

/-! ## Answers -/

/-- `error(closed)`. -/
def errAns : Option (List Val) := some [errClosed]
/-- `ok`. -/
def okUnit : Option (List Val) := some [okV none]
/-- `ok(n)` (`u64`). -/
def okN (n : Nat) : Option (List Val) := some [okV (some (.u64 (BitVec.ofNat 64 n)))]
/-- `ok(bytes)`. -/
def okBytes (bs : List (BitVec 8)) : Option (List Val) := some [okV (some (bytesV bs))]

/-- Wait loops run at most this many rounds. -/
def rounds : Nat := 64

/-! ## Writing -/

/-- The copy result in the answer of `stream.write`. -/
def copyAns : Option (List Val) → Option (Option (CopyResult × Nat))
  | some [pv] => natOf pv >>= copyOf
  | _ => none

/-- The output stream after a copy result of its buffer. -/
def onCopy (o : OutS) : Option (Option (CopyResult × Nat)) → OutS
  | some none => { o with inflight := true }
  | some (some (.completed, k)) => { o with buf := o.buf.drop k, inflight := false }
  | some (some (.dropped, k)) => { o with buf := o.buf.drop k, inflight := false, err := true }
  | _ => { o with inflight := false, err := true }

/-- Start writing the buffer, unless a copy is in flight, the reader is gone, or it is empty. -/
def pump (o : OutS) : Pg OutS :=
  if o.inflight || o.err || o.buf.isEmpty then .pure o
  else .call (opStreamWrite o.w o.buf) fun r => .pure (onCopy o (copyAns r))

/-- The state after an event of `waitable-set.wait`: a `stream-write` event (code `3`) of an
in-flight writable end completes its copy. -/
def onEvent (st : ISt) : Option (List Val) → ISt
  | some [cv, iv, pv] =>
    if natOf cv = some 3 then
      { st with outs := st.outs.map fun x =>
          if x.2.inflight && decide (natOf x.2.w = natOf iv) then (x.1, onCopy x.2 (natOf pv >>= copyOf))
          else x }
    else st
  | _ => st

/-- The waitable set, created at the first use. -/
def ensureWs (st : ISt) : Pg (ISt × Val) :=
  match st.ws with
  | some s => .pure (st, s)
  | none => .call opWsNew fun
    | some [s] => .pure ({ st with ws := some s }, s)
    | _ => .pure (st, natV 0)

/-- Join the waitables `ws` to the set `s`, then continue. -/
def joinAll {A : Type} (s : Val) : List Val → Pg A → Pg A
  | [], k => k
  | w :: ws, k => .call (opJoin w s) fun _ => joinAll s ws k

/-- Wait for an event of one of the waitables `ws`. -/
def waitOn (st : ISt) (ws : List Val) : Pg ISt :=
  (ensureWs st).bind fun x => joinAll x.2 ws (.call (opWait x.2) fun r => .pure (onEvent x.1 r))

/-- Drive the buffer of the output stream `h` to the reader, at most `n` rounds. -/
def flushLoop : Nat → BitVec 32 → ISt → Pg ISt
  | 0, _, st => .pure st
  | n + 1, h, st =>
    match look st.outs h with
    | none => .pure st
    | some o =>
      if o.err || (o.buf.isEmpty && !o.inflight) then .pure st
      else (pump o).bind fun o' =>
        if o'.inflight then (waitOn (st.setOut h o') [o'.w]).bind (flushLoop n h)
        else flushLoop n h (st.setOut h o')

/-- The answer of a blocking flush: `ok` when everything was taken. -/
def flushed (st : ISt) (h : BitVec 32) : Option (List Val) :=
  match look st.outs h with
  | some o => if !o.err && o.buf.isEmpty && !o.inflight then okUnit else errAns
  | none => errAns

/-- `check-write`. -/
def cwP (cap : Nat) (s : St) (a : List Val) : Pg (ISt × Option (List Val)) :=
  let h := selfOf a
  if s.io.closed h then .pure (s.impl, errAns) else
  match look s.impl.outs h with
  | none => .pure (s.impl, errAns)
  | some o => (pump o).bind fun o' =>
    .pure (s.impl.setOut h o', if o'.err then errAns else okN (cap - o'.buf.length))

/-- `write`/`write-zeroes` of the bytes `bs`. -/
def writeP (s : St) (a : List Val) (bs : List (BitVec 8)) : Pg (ISt × Option (List Val)) :=
  let h := selfOf a
  if s.io.permit h < bs.length then .pure (s.impl, none) else
  if s.io.closed h then .pure (s.impl, errAns) else
  match look s.impl.outs h with
  | none => .pure (s.impl, errAns)
  | some o =>
    if o.err then .pure (s.impl, errAns)
    else (pump { o with buf := o.buf ++ bs }).bind fun o' =>
      .pure (s.impl.setOut h o', if o'.err then errAns else okUnit)

/-- `blocking-write-and-flush`/`blocking-write-zeroes-and-flush` of the bytes `bs`. -/
def bwfP (s : St) (a : List Val) (bs : List (BitVec 8)) : Pg (ISt × Option (List Val)) :=
  let h := selfOf a
  if s.io.closed h then .pure (s.impl, errAns) else
  if 4096 < bs.length then .pure (s.impl, none) else
  match look s.impl.outs h with
  | none => .pure (s.impl, errAns)
  | some o =>
    if o.err then .pure (s.impl, errAns)
    else (flushLoop rounds h (s.impl.setOut h { o with buf := o.buf ++ bs })).bind fun st =>
      .pure (st, flushed st h)

/-- `flush`. -/
def flushP (s : St) (a : List Val) : Pg (ISt × Option (List Val)) :=
  let h := selfOf a
  if s.io.closed h then .pure (s.impl, errAns) else
  match look s.impl.outs h with
  | none => .pure (s.impl, errAns)
  | some o => (pump o).bind fun o' =>
    .pure (s.impl.setOut h o', if o'.err then errAns else okUnit)

/-- `blocking-flush`. -/
def bflushP (s : St) (a : List Val) : Pg (ISt × Option (List Val)) :=
  let h := selfOf a
  if s.io.closed h then .pure (s.impl, errAns) else
  (flushLoop rounds h s.impl).bind fun st => .pure (st, flushed st h)

/-- `splice`/`blocking-splice`: nothing is moved. -/
def spliceP (s : St) (a : List Val) : Pg (ISt × Option (List Val)) :=
  .pure (s.impl, if s.io.closed (selfOf a) then errAns else okN 0)

/-! ## Reading -/

/-- The result of one `stream.read`. -/
inductive RdRes where
  | data (bs : List (BitVec 8))
  | eof
  | blocked

/-- One `stream.read` of at most `len` items. -/
def readStep (st : ISt) (h : BitVec 32) (i : InS) (len : Nat) : Pg (ISt × RdRes) :=
  .call (opStreamRead i.r len) fun
    | some [pv, items] =>
      match natOf pv >>= copyOf with
      | some (some (.completed, _)) => .pure (st, .data (bytesOf items))
      | some (some (.dropped, _)) => .pure (st.setIn h { i with eof := true }, .eof)
      | _ => .pure (st, .blocked)
    | _ => .pure (st, .blocked)

/-- Read until some bytes arrive, the stream ends, or `n` rounds have passed. -/
def readLoop : Nat → ISt → BitVec 32 → InS → Nat → Pg (ISt × RdRes)
  | 0, st, _, _, _ => .pure (st, .blocked)
  | n + 1, st, h, i, len => (readStep st h i len).bind fun x =>
    match x.2 with
    | .eof => .pure x
    | .data bs => if bs.isEmpty && 0 < len then (waitOn x.1 [i.r]).bind fun st' => readLoop n st' h i len
                  else .pure x
    | .blocked => (waitOn x.1 [i.r]).bind fun st' => readLoop n st' h i len

/-- The answer of a read (`skip`: the count) of at most `len` bytes. -/
def rdAns (skip : Bool) (len : Nat) : RdRes → Option (List Val)
  | .data bs => if skip then okN (min len bs.length) else okBytes (bs.take len)
  | .eof => errAns
  | .blocked => if skip then okN 0 else okBytes []

/-- `read`, `blocking-read`, `skip`, `blocking-skip`. -/
def readP (s : St) (a : List Val) (blocking skip : Bool) : Pg (ISt × Option (List Val)) :=
  let h := selfOf a
  let len := lenOf a
  if s.io.closed h then .pure (s.impl, errAns) else
  match look s.impl.ins h with
  | none => .pure (s.impl, errAns)
  | some i =>
    if i.eof then .pure (s.impl, errAns)
    else ((if blocking then readLoop rounds s.impl h i len else readStep s.impl h i len)).bind
      fun x => .pure (x.1, rdAns skip len x.2)

/-! ## Pollables -/

/-- `subscribe`: a pollable for the stream. -/
def subP (s : St) (a : List Val) (k : BitVec 32 → PollK) : Pg (ISt × Option (List Val)) :=
  let x := s.impl.fresh
  .pure ({ x.1 with polls := (x.2, k (selfOf a)) :: x.1.polls }, some [.u32 x.2])

/-- Whether the pollable `p` is ready now (starting a write of a non-empty buffer). -/
def readyNow (st : ISt) (p : BitVec 32) : Pg (ISt × Bool) :=
  match look st.polls p with
  | some (.out h) =>
    match look st.outs h with
    | some o => (pump o).bind fun o' => .pure (st.setOut h o', !o'.inflight)
    | none => .pure (st, true)
  | some (.timer d) => .call opNow fun
    | some [.u64 x] => .pure (st, decide (d ≤ x.toNat))
    | _ => .pure (st, true)
  | _ => .pure (st, true)

/-- The indices of the ready pollables among the indexed list. -/
def readyList (st : ISt) : List (Nat × BitVec 32) → Pg (ISt × List Nat)
  | [] => .pure (st, [])
  | (i, p) :: ps => (readyNow st p).bind fun x => (readyList x.1 ps).bind fun y =>
    .pure (y.1, if x.2 then i :: y.2 else y.2)

/-- The indexed pollables. -/
def indexed (ps : List (BitVec 32)) : List (Nat × BitVec 32) := (List.range ps.length).zip ps

/-- The in-flight writable ends among the pollables. -/
def inflightEnds (st : ISt) (ps : List (BitVec 32)) : List Val :=
  ps.filterMap fun p => match look st.polls p with
    | some (.out h) => (look st.outs h).bind fun o => if o.inflight then some o.w else none
    | _ => none

/-- The deadlines among the pollables. -/
def deadlines (st : ISt) (ps : List (BitVec 32)) : List Nat :=
  ps.filterMap fun p => match look st.polls p with
    | some (.timer d) => some d
    | _ => none

/-- The instant of a `now` answer (`d` if ill-typed). -/
def nowOr (d : Nat) : Option (List Val) → Nat
  | some [.u64 x] => x.toNat
  | _ => d

/-- Wait until one of the pollables is ready, at most `n` rounds: on the in-flight writable ends
with `waitable-set.wait`, or else on the first deadline with the sync-lowered `wait-for`. -/
def pollLoop : Nat → ISt → List (BitVec 32) → Pg (ISt × List Nat)
  | 0, st, ps => readyList st (indexed ps)
  | n + 1, st, ps => (readyList st (indexed ps)).bind fun x =>
    if !x.2.isEmpty then .pure x
    else match inflightEnds x.1 ps, deadlines x.1 ps with
      | w :: ws, _ => (waitOn x.1 (w :: ws)).bind fun st' => pollLoop n st' ps
      | [], d :: _ => .call opNow fun r => .call (opWaitFor (d - nowOr d r)) fun _ => pollLoop n x.1 ps
      | [], [] => .pure x

/-- The handles of a `list<borrow<pollable>>`. -/
def handlesOf (ps : List Val) : List (BitVec 32) :=
  ps.map fun | .u32 p => p | _ => 0

/-- The answer of `poll` over `n` pollables: the ready indices, or index `0`. -/
def pollAnsOf (n : Nat) (is : List Nat) : Val :=
  match is.filter (· < n) with
  | [] => .record [natV 0]
  | js => .record (js.map natV)

/-- `pollable.ready`. -/
def readyP (s : St) (a : List Val) : Pg (ISt × Option (List Val)) :=
  (readyNow s.impl (selfOf a)).bind fun x => .pure (x.1, some [.bool x.2])

/-- `pollable.block`. -/
def blockP (s : St) (a : List Val) : Pg (ISt × Option (List Val)) :=
  (pollLoop rounds s.impl [selfOf a]).bind fun x => .pure (x.1, some [])

/-- `poll`. -/
def pollP (s : St) (a : List Val) : Pg (ISt × Option (List Val)) :=
  match a with
  | [.record ps] =>
    if ps.isEmpty then .pure (s.impl, none)
    else (pollLoop rounds s.impl (handlesOf ps)).bind fun x =>
      .pure (x.1, some [pollAnsOf ps.length x.2])
  | _ => .pure (s.impl, some [.record []])

/-- `[resource-drop]pollable`. -/
def pdropP (s : St) (a : List Val) : Pg (ISt × Option (List Val)) :=
  .pure ({ s.impl with polls := s.impl.polls.filter fun x => !decide (x.1 = selfOf a) }, some [])

/-! ## `wasi:cli`, `wasi:clocks` and drops -/

/-- A new output stream over `write-via-stream` (`stdout` or `stderr`). -/
def newOut (st : ISt) (wvs : Val → IOp) : Pg (ISt × Option (List Val)) :=
  .call opStreamNew fun
    | some [rv, wv] => .call (wvs rv) fun r =>
      let x := st.fresh
      match r with
      | some [f] => .pure (x.1.setOut x.2 { w := wv, fut := f }, some [.u32 x.2])
      | _ => .pure (x.1.setOut x.2 { w := wv, fut := natV 0, err := true }, some [.u32 x.2])
    | _ =>
      let x := st.fresh
      .pure (x.1.setOut x.2 { w := natV 0, fut := natV 0, err := true }, some [.u32 x.2])

/-- A new input stream over `stdin.read-via-stream`. -/
def newIn (st : ISt) : Pg (ISt × Option (List Val)) :=
  .call opStdin fun r =>
    let x := st.fresh
    match r with
    | some [.record [rv, fv]] => .pure (x.1.setIn x.2 { r := rv, fut := fv }, some [.u32 x.2])
    | _ => .pure (x.1.setIn x.2 { r := natV 0, fut := natV 0, eof := true }, some [.u32 x.2])

/-- `[resource-drop]output-stream`: drive the buffer, then drop the writable end and the future. -/
def dropOut (st : ISt) (h : BitVec 32) : Pg (ISt × Option (List Val)) :=
  match look st.outs h with
  | some o => (flushLoop rounds h st).bind fun st' =>
    .call (opDropW o.w) fun _ => .call (opFutDropR o.fut) fun _ =>
      .pure ({ st' with outs := st'.outs.filter fun x => !decide (x.1 = h) }, some [])
  | none => .pure (st, some [])

/-- `[resource-drop]input-stream`: drop the readable end and the future. -/
def dropIn (st : ISt) (h : BitVec 32) : Pg (ISt × Option (List Val)) :=
  match look st.ins h with
  | some i => .call (opDropR i.r) fun _ => .call (opFutDropR i.fut) fun _ =>
      .pure ({ st with ins := st.ins.filter fun x => !decide (x.1 = h) }, some [])
  | none => .pure (st, some [])

/-- A WASI 0.3 `instant` as a WASI 0.2 `datetime` (negative seconds as `0`). -/
def ofInstant : Option (List Val) → Option (List Val)
  | some [.record [.s64 s, .u32 ns]] => some [.record [.u64 (if s.msb then 0 else s), .u32 ns]]
  | r => r

/-- A WASI 0.3 `duration` (nanoseconds) as a WASI 0.2 `datetime`. -/
def ofDuration : Option (List Val) → Option (List Val)
  | some [.u64 d] =>
    some [.record [.u64 (BitVec.ofNat 64 (d.toNat / 1000000000)),
      .u32 (BitVec.ofNat 32 (d.toNat % 1000000000))]]
  | r => r

/-- Forward a call to a further WASI 0.3 function, converting its answer. -/
def fwd (st : ISt) (f : FnName) (hf : f ∈ extra3) (a : List Val)
    (conv : Option (List Val) → Option (List Val) := id) : Pg (ISt × Option (List Val)) :=
  .call (opExtra f hf a) fun r => .pure (st, conv r)

/-- The first `u64` argument. -/
def arg64 : List Val → Nat
  | .u64 n :: _ => n.toNat
  | _ => 0

/-- The functions `ioOp` classifies as `other`. -/
def otherP (st : ISt) (f : FnName) (a : List Val) : Pg (ISt × Option (List Val)) :=
  if f = getStdout then newOut st opStdout
  else if f = getStderr then newOut st opStderr
  else if f = getStdin then newIn st
  else if f = clockNow then .call opNow fun r => .pure (st, r)
  else if f = monoRes then fwd st monoRes3 (by simp [extra3]) []
  else if f = monoSubInstant then
    let x := st.fresh
    .pure ({ x.1 with polls := (x.2, .timer (arg64 a)) :: x.1.polls }, some [.u32 x.2])
  else if f = monoSubDuration then .call opNow fun r =>
    let x := st.fresh
    .pure ({ x.1 with polls := (x.2, .timer (nowOr 0 r + arg64 a)) :: x.1.polls },
      some [.u32 x.2])
  else if f = wallNow then fwd st sysNow3 (by simp [extra3]) [] ofInstant
  else if f = wallRes then fwd st sysRes3 (by simp [extra3]) [] ofDuration
  else if f = getEnv then fwd st getEnv3 (by simp [extra3]) []
  else if f = getArgs then fwd st getArgs3 (by simp [extra3]) []
  else if f = initialCwd then fwd st cwd3 (by simp [extra3]) []
  else if f = getTermStdin then fwd st termStdin3 (by simp [extra3]) []
  else if f = getTermStdout then fwd st termStdout3 (by simp [extra3]) []
  else if f = getTermStderr then fwd st termStderr3 (by simp [extra3]) []
  else if f = cliExit then fwd st exit3 (by simp [extra3]) a fun _ => none
  else if f = osDrop then dropOut st (selfOf a)
  else if f = isDrop then dropIn st (selfOf a)
  else if f = errDebug then .pure (st, some [strV "stream error"])
  else .pure (st, some [])

/-- The fixed well-typed answer of a `wasi:cli`/`wasi:clocks` function (same case split as
`cliOk`). -/
def cliDflt (f : FnName) : Option (List Val) :=
  if f = cliExit then none
  else if f = getEnv then some [.record []]
  else if f = getArgs then some [.record []]
  else if f = initialCwd then some [.variant 0 none]
  else if f = getStdin ∨ f = getStdout ∨ f = getStderr ∨ f = monoSubInstant ∨
      f = monoSubDuration then some [.u32 0]
  else if f = getTermStdin ∨ f = getTermStdout ∨ f = getTermStderr then some [.variant 0 none]
  else if f = monoRes then some [.u64 0]
  else if f = wallNow ∨ f = wallRes then some [.record [.u64 0, .u32 0]]
  else if f = fdReadStream ∨ f = fdWriteStream ∨ f = fdAppendStream then some [errV (some (.u32 0))]
  else if f = fdGetType then some [errV (some (.u32 0))]
  else if f = streamDrop then some []
  else some []

/-- **Lifting at the WIT type**: the identity on well-typed answers. -/
def cliFix (f : FnName) (r : Option (List Val)) : Option (List Val) :=
  if cliOk f r then r else cliDflt f

/-! ## The component -/

/-- The program of an export call. -/
def prog (cap : Nat) (s : St) (f : FnName) (a : List Val) : Pg (ISt × Option (List Val)) :=
  match ioOp f with
  | .checkWrite => cwP cap s a
  | .write => writeP s a (contentsOf a)
  | .writeZeroes => writeP s a (List.replicate (lenOf a) 0)
  | .bwf => bwfP s a (contentsOf a)
  | .bwzf => bwfP s a (List.replicate (lenOf a) 0)
  | .flush => flushP s a
  | .bflush => bflushP s a
  | .splice | .bsplice => spliceP s a
  | .oSubscribe => subP s a .out
  | .iSubscribe => subP s a .inp
  | .read => readP s a false false
  | .bread => readP s a true false
  | .skip => readP s a false true
  | .bskip => readP s a true true
  | .ready => readyP s a
  | .block => blockP s a
  | .poll => pollP s a
  | .pDrop => pdropP s a
  | .other => (otherP s.impl f a).bind fun x => .pure (x.1, cliFix f x.2)

/-- The body: run the program, and record the answer in the 0.2 stream state. -/
def body (cap : Nat) : SBody St imp3 exp2 := fun s q =>
  (prog cap s q.1.1 q.2).bind fun x => .pure (⟨ioUpd s.io (ioOp q.1.1) q.2 x.2, x.1⟩, x.2)

/-- **WASI 0.2 over WASI 0.3**, with output buffers of `cap` bytes. -/
def p2OverP3 (cap : Nat) : Strategy (nsig imp3) (nsig exp2) := ofSBody (body cap) St.init

end Silmaril.Wasi.Versions.P2OverP3
