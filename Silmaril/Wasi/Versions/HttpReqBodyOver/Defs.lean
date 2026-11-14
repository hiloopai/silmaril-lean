module

public import Silmaril.Wasi.Versions.HttpReqBody.Defs
public import Silmaril.Wasi.Versions.HttpOver.Defs

@[expose] public section

/-!
# Outgoing request bodies, 0.3 over 0.2 (`req3Over2`)

`req3Over2 rounds` imports the 0.2 slice with outgoing bodies (`req2Fns`) and exports the 0.3
one (`req3Fns`). It buffers: the 0.3 body is written into the component's own streams, and the
0.2 body is written in one go when the request is sent.

* **State**: the adapter keeps its own copy of the 0.3 theory state (`Req3St`, updated with
  `req3Next` on every answer it gives) and a counter for fresh handles.
* `stream.new` answers fresh `(2n, 2n + 1)`; `stream.write(w, buf)` completes
  `min |buf| chunk3` items; `stream.drop-writable` answers; `request.new` answers a fresh
  `(2n, 2n + 1)`; `set-authority` and `set-path-with-query` answer `ok`. None calls the 0.2 host.
* `send(r)` with a finished body `bs` (the 0.3 state's `done r`; otherwise it traps): 0.2
  `set-authority(r, authority)`, `set-path-with-query(r, path)`, `outgoing-request.body(r)` →
  `b`, `outgoing-body.write(b)` → `s`, `blocking-write-and-flush(s, bs)`,
  `outgoing-body.finish(b, none)`, `handle(r, none)` → `f`, then `future-incoming-response.get(f)`
  while it answers `none` (at most `rounds` times); it answers the inner result (as
  `http3Over2`). Any unexpected answer traps.
* `get-status-code(rs)` is forwarded to 0.2 `incoming-response.status(rs)`.

The 0.3 request handle is used as the 0.2 request handle (as in `http3Over2`); the adapter's
fresh handles are not checked against the host's.

**Not covered**: the trailers argument of `request.new`; bodies larger than one
`blocking-write-and-flush` accepts (a host may trap); `check-write`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (packCopy)

/-! ## Imports -/

/-- `set-authority` as a 0.2 import with bodies. -/
def kSetAuth : {f // f ∈ req2Fns} := ⟨setAuthority, Or.inl (by simp [httpImports_eq])⟩
/-- `set-path-with-query` as a 0.2 import with bodies. -/
def kSetPath : {f // f ∈ req2Fns} := ⟨setPath, Or.inl (by simp [httpImports_eq])⟩
/-- `handle` as a 0.2 import with bodies. -/
def kHandle : {f // f ∈ req2Fns} := ⟨httpHandle, Or.inl (by simp [httpImports_eq])⟩
/-- `future-incoming-response.get` as a 0.2 import with bodies. -/
def kGet : {f // f ∈ req2Fns} := ⟨futGet, Or.inl (by simp [httpImports_eq])⟩
/-- `incoming-response.status` as a 0.2 import with bodies. -/
def kStatus : {f // f ∈ req2Fns} := ⟨respStatus, Or.inl (by simp [httpImports_eq])⟩
/-- `outgoing-request.body` as a 0.2 import. -/
def kBody : {f // f ∈ req2Fns} := ⟨outReqBody2, by rw [req2Fns_eq]; exact Or.inr (by simp)⟩
/-- `outgoing-body.write` as a 0.2 import. -/
def kWrite : {f // f ∈ req2Fns} := ⟨outBodyWrite2, by rw [req2Fns_eq]; exact Or.inr (by simp)⟩
/-- `outgoing-body.finish` as a 0.2 import. -/
def kFinish : {f // f ∈ req2Fns} := ⟨outBodyFinish2, by rw [req2Fns_eq]; exact Or.inr (by simp)⟩
/-- `blocking-write-and-flush` as a 0.2 import. -/
def kBwf : {f // f ∈ req2Fns} := ⟨P2.osBwf, by rw [req2Fns_eq]; exact Or.inr (by simp)⟩

/-! ## The program of `send` -/

/-- Poll `get(f)` while it answers `none`, at most `k` times; answer the inner result. -/
def pollGetB : Nat → BitVec 32 → Prog (nsig req2Fns) (Option (List Val))
  | 0, _ => .pure none
  | k + 1, fu => .call (kGet, [.u32 fu]) fun r =>
    if isPending r then pollGetB k fu else .pure (sendOf2 r)

/-- After `finish`: `handle(r, none)` and poll. -/
def sendB4 (rounds : Nat) (rq : BitVec 32) : Prog (nsig req2Fns) (Option (List Val)) :=
  .call (kHandle, [.u32 rq, noneV]) fun r =>
    match okHandle r with
    | some fu => pollGetB rounds fu
    | none => .pure none

/-- After `write`: write the body, finish it, send. -/
def sendB3 (rounds : Nat) (rq b st : BitVec 32) (bs : List (BitVec 8)) :
    Prog (nsig req2Fns) (Option (List Val)) :=
  .call (kBwf, [.u32 st, bytesV bs]) fun r =>
    if isOkU r then
      .call (kFinish, [.u32 b, noneV]) fun r' =>
        if isOkU r' then sendB4 rounds rq else .pure none
    else .pure none

/-- After the setters: take the body and its stream. -/
def sendB2 (rounds : Nat) (rq : BitVec 32) (bs : List (BitVec 8)) :
    Prog (nsig req2Fns) (Option (List Val)) :=
  .call (kBody, [.u32 rq]) fun r =>
    match okHandle r with
    | some b => .call (kWrite, [.u32 b]) fun r' =>
      match okHandle r' with
      | some st => sendB3 rounds rq b st bs
      | none => .pure none
    | none => .pure none

/-- The program of `send(r)` over 0.2, from the adapter's copy `s` of the 0.3 state. -/
def sendB (rounds : Nat) (s : Req3St) (a : List Val) : Prog (nsig req2Fns) (Option (List Val)) :=
  match a with
  | .u32 rq :: _ =>
    match s.done rq with
    | some bs =>
      .call (kSetAuth, [.u32 rq, (s.key rq).1]) fun r =>
        if isOkU r then
          .call (kSetPath, [.u32 rq, (s.key rq).2]) fun r' =>
            if isOkU r' then sendB2 rounds rq bs else .pure none
        else .pure none
    | none => .pure none
  | _ => .pure none

/-! ## The adapter -/

/-- The answer of an export served without the host. -/
def localAns (n : Nat) (f : FnName) (a : List Val) : Option (List Val) :=
  if f = P3.cStreamNew then some [P3.natV (2 * n), P3.natV (2 * n + 1)]
  else if f = P3.cStreamWrite then
    match a with
    | _ :: buf :: _ => some [P3.natV (packCopy .completed (min ((valOf buf).getD []).length chunk3))]
    | _ => some [P3.natV (packCopy .completed 0)]
  else if f = P3.cStreamDropW then some []
  else if f = reqNew3 then some [.record [P3.natV (2 * n), P3.natV (2 * n + 1)]]
  else if f = setAuth3 ∨ f = setPath3 then some [okV none]
  else none

/-- The program of an export call, before the state update. -/
def req3Prog (rounds : Nat) (s : Req3St × Nat) (f : FnName) (a : List Val) :
    Prog (nsig req2Fns) (Option (List Val)) :=
  if f = send3 then sendB rounds s.1 a
  else if f = getStatus3 then .call (kStatus, a) fun r => .pure r
  else .pure (localAns s.2 f a)

/-- **Outgoing request bodies, 0.3 over 0.2.** -/
def req3Over2 (rounds : Nat) : SBody (Req3St × Nat) req2Fns req3Fns := fun s q =>
  (req3Prog rounds s q.1.1 q.2).bind fun x => .pure ((req3Next s.1 (.imp q.1.1 q.2 x), s.2 + 1), x)

/-- The invariant of `req3Over2`: the adapter's copy is the 0.3 theory state, and the two
theories record the same responses. -/
def JR3 (s : Req3St × Nat) (q2 : Req2St) (q3 : Req3St) : Prop := s.1 = q3 ∧ q2.resps = q3.resps

end Silmaril.Wasi.Versions.Net
