module

public import Silmaril.Wasi.Versions.Http3.Defs
public import Silmaril.Wasi.Versions.Stateful.Defs

@[expose] public section

/-!
# Outgoing HTTP across versions: 0.3 over 0.2 and 0.2 over 0.3

Two components between the 0.2 outgoing HTTP slice (`Net.httpImports`, theory `httpTh W`) and
the 0.3 one (`http3Fns`, theory `httpTh3 W`), for the same web `W`. The `error-code` variant of
`wasi:http/types` has the same 39 cases in the same order in `specs/wasi/0.2.12/http/types.wit`
and `specs/wasi/0.3.2/http/types.wit` (checked with `diff` on the case lists, 2026-11-09), so
codes pass unchanged.

**`http3Over2 rounds`** (relation (b)): imports 0.2, exports 0.3, no state.

* `set-authority` / `set-path-with-query` call the 0.2 setter with the same arguments and return
  its answer (both are `result` without payloads).
* `send(r)` calls `handle(r, none)`; on `ok(f)` it polls `future-incoming-response.get(f)`
  while the answer is `none` (not ready), at most `rounds` times (`pollGet`), and returns
  `ok(response)` or `error(code)` from `some(ok(_))`. It traps when the rounds run out, when
  `handle` does not answer `ok(f)` (its errors are not outcomes of the web), on `some(err)`
  and on ill-typed answers. As for TCP (`Net3.Over`), the poll loop does not `subscribe`/`block`.
* `get-status-code(r)` calls `incoming-response.status(r)` and returns its answer.

**`http2Over3`** (relation (c)): imports 0.3, exports 0.2. Its state `HSt` keeps, per 0.2
future, the 0.2 inner result and the status (`pend`), and per response handle the status it
had when its future was retrieved (`stat`).

* `handle(r, _)` calls the async `send(r)` **sync-lowered**; on `ok(rs)` it calls
  `get-status-code(rs)` at once and stores `(ok(rs), status)`; on `error(k)` it stores
  `error(k)`; it answers `ok(f)` with a fresh future `f`. A trap of `send` or an ill-typed answer
  is a trap.
* `get(f)` answers the stored result once (`some(ok(_))`, then `some(err)`); retrieving
  `ok(rs)` records the stored status for `rs`.
* `status(rs)` answers the recorded status (`200` for an unknown handle; no import call).
* The setters are forwarded as above.

Storing the status when the response arrives, instead of forwarding `status` later, makes the
component correct for 0.3 hosts that reuse a response handle for a later request: the 0.3
theory reads the status of the newest response with that handle.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)

/-! ## Shared helpers -/

/-- The list of requests after a setter call `a` answered `r` (the same in both versions). -/
def setUpd (a : List Val) (r : Option (List Val)) (l : List (BitVec 32 × Val)) :
    List (BitVec 32 × Val) :=
  match a, r with
  | .u32 h :: v :: _, some [.variant 0 none] => (h, v) :: l
  | _, _ => l

/-- The authority and path of the request `r` in a 0.2 theory state. -/
def HttpSt.key (q : HttpSt) (r : BitVec 32) : Val × Val :=
  ((lookup r q.auth).getD noneV, (lookup r q.path).getD noneV)

/-! ## 0.3 over 0.2 -/

/-- `handle` as a 0.2 import. -/
def iHandle : {f // f ∈ httpImports} := ⟨httpHandle, by simp [httpImports_eq]⟩
/-- `set-authority` as a 0.2 import. -/
def iSetAuth : {f // f ∈ httpImports} := ⟨setAuthority, by simp [httpImports_eq]⟩
/-- `set-path-with-query` as a 0.2 import. -/
def iSetPath : {f // f ∈ httpImports} := ⟨setPath, by simp [httpImports_eq]⟩
/-- `future-incoming-response.get` as a 0.2 import. -/
def iFutGet : {f // f ∈ httpImports} := ⟨futGet, by simp [httpImports_eq]⟩
/-- `incoming-response.status` as a 0.2 import. -/
def iStatus : {f // f ∈ httpImports} := ⟨respStatus, by simp [httpImports_eq]⟩

/-- A 0.2 `get` answer `none`: not ready yet. -/
def isPending : Option (List Val) → Bool
  | some [.variant 0 none] => true
  | _ => false

/-- The 0.3 `send` answer of a 0.2 `get` answer (`none`: a trap). -/
def sendOf2 : Option (List Val) → Option (List Val)
  | some [.variant 1 (some (.variant 0 (some (.variant 0 (some (.u32 rs))))))] =>
    some [okV (some (.u32 rs))]
  | some [.variant 1 (some (.variant 0 (some (.variant 1 (some (.variant k p))))))] =>
    some [errV (some (.variant k p))]
  | _ => none

/-- Poll `get(f)` while it answers `none`, at most `k` times. -/
def pollGet : Nat → BitVec 32 → SProg Unit httpImports
  | 0, _ => .pure ((), none)
  | k + 1, fu => .call (iFutGet, [.u32 fu]) fun r =>
    if isPending r then pollGet k fu else .pure ((), sendOf2 r)

/-- The program of `send(r)`. -/
def send3Prog (rounds : Nat) (a : List Val) : SProg Unit httpImports :=
  match a with
  | .u32 r :: _ =>
    .call (iHandle, [.u32 r, noneV]) fun r₁ =>
      match r₁ with
      | some [.variant 0 (some (.u32 fu))] => pollGet rounds fu
      | _ => .pure ((), none)
  | _ => .pure ((), none)

/-- **Outgoing HTTP 0.3 over 0.2.** -/
def http3Over2 (rounds : Nat) : SBody Unit httpImports http3Fns := fun _ q =>
  if q.1.1 = setAuth3 then .call (iSetAuth, q.2) fun r => .pure ((), r)
  else if q.1.1 = setPath3 then .call (iSetPath, q.2) fun r => .pure ((), r)
  else if q.1.1 = send3 then send3Prog rounds q.2
  else .call (iStatus, q.2) fun r => .pure ((), r)

/-- The invariant of `http3Over2`: the 0.2 and 0.3 theory states agree on the requests and on
the responses. -/
def JH3 (_ : Unit) (q2 : HttpSt) (q3 : Http3St) : Prop :=
  q2.auth = q3.auth ∧ q2.path = q3.path ∧ q2.resps = q3.resps

/-! ## 0.2 over 0.3 -/

/-- `send` as a 0.3 import. -/
def iSend3 : {f // f ∈ http3Fns} := ⟨send3, by simp [http3Fns_eq]⟩
/-- `set-authority` as a 0.3 import. -/
def iSetAuth3 : {f // f ∈ http3Fns} := ⟨setAuth3, by simp [http3Fns_eq]⟩
/-- `set-path-with-query` as a 0.3 import. -/
def iSetPath3 : {f // f ∈ http3Fns} := ⟨setPath3, by simp [http3Fns_eq]⟩
/-- `get-status-code` as a 0.3 import. -/
def iStatus3 : {f // f ∈ http3Fns} := ⟨getStatus3, by simp [http3Fns_eq]⟩

/-- The state of `http2Over3`. -/
structure HSt where
  /-- Per future: the stored inner result and status (`none`: already retrieved). -/
  pend : List (BitVec 32 × Option (Val × BitVec 16)) := []
  /-- Per response: the status. -/
  stat : List (BitVec 32 × BitVec 16) := []
  /-- The next future handle. -/
  next : Nat := 0

/-- Store `x` for a fresh future and answer `ok(f)`. -/
def storeFut (st : HSt) (x : Val × BitVec 16) : HSt × Option (List Val) :=
  ({ st with pend := (BitVec.ofNat 32 st.next, some x) :: st.pend, next := st.next + 1 },
   some [okV (some (.u32 (BitVec.ofNat 32 st.next)))])

/-- After `send` answered `ok(rs)`: read the status. -/
def afterSend (st : HSt) (rs : BitVec 32) : SProg HSt http3Fns :=
  .call (iStatus3, [.u32 rs]) fun r =>
    match r with
    | some [.u16 s] => .pure (storeFut st (okV (some (.u32 rs)), s))
    | _ => .pure (st, none)

/-- The program of `handle(r, _)`. -/
def handleProg (st : HSt) (a : List Val) : SProg HSt http3Fns :=
  match a with
  | .u32 r :: _ =>
    .call (iSend3, [.u32 r]) fun r₁ =>
      match r₁ with
      | some [.variant 0 (some (.u32 rs))] => afterSend st rs
      | some [.variant 1 (some (.variant k p))] => .pure (storeFut st (errV (some (.variant k p)), 0))
      | _ => .pure (st, none)
  | _ => .pure (st, none)

/-- `some(err)`: the result was already retrieved. -/
def gotV : Val := .variant 1 (some (.variant 1 none))

/-- The status of a retrieved inner result `ok(rs)`, recorded for `rs`. -/
def recStat (x : Val) (s : BitVec 16) (l : List (BitVec 32 × BitVec 16)) :
    List (BitVec 32 × BitVec 16) :=
  match x with
  | .variant 0 (some (.u32 rs)) => (rs, s) :: l
  | _ => l

/-- The result of `get(f)` (no import call). -/
def getRes (st : HSt) (a : List Val) : HSt × Option (List Val) :=
  match a with
  | .u32 fu :: _ =>
    match lookup fu st.pend with
    | some (some (x, s)) =>
      ({ st with pend := (fu, none) :: st.pend, stat := recStat x s st.stat },
       some [.variant 1 (some (.variant 0 (some x)))])
    | _ => (st, some [gotV])
  | _ => (st, some [gotV])

/-- The result of `status(rs)` (no import call). -/
def statusRes (st : HSt) (a : List Val) : HSt × Option (List Val) :=
  match a with
  | .u32 rs :: _ => (st, some [.u16 ((lookup rs st.stat).getD 200)])
  | _ => (st, some [.u16 200])

/-- **Outgoing HTTP 0.2 over 0.3.** -/
def http2Over3 : SBody HSt http3Fns httpImports := fun st q =>
  if q.1.1 = setAuthority then .call (iSetAuth3, q.2) fun r => .pure (st, r)
  else if q.1.1 = setPath then .call (iSetPath3, q.2) fun r => .pure (st, r)
  else if q.1.1 = httpHandle then handleProg st q.2
  else if q.1.1 = futGet then .pure (getRes st q.2)
  else .pure (statusRes st q.2)

/-- A stored result for a request of key `k`: it matches the web, and a response comes with
the web's status. -/
def PendOk (W : Web) (k : Val × Val) (x : Val × BitVec 16) : Prop :=
  outcomeOk (W k.1 k.2) x.1 = true ∧ ∀ rs, x.1 = .variant 0 (some (.u32 rs)) → W k.1 k.2 = .status x.2

/-- **The invariant of `http2Over3`** over the web `W`: the 0.2 and 0.3 states agree on the
requests; every stored result is for a tied 0.2 future and matches the web; every response of
the 0.2 theory has a recorded status, which is the web's. -/
def JH2 (W : Web) (st : HSt) (q3 : Http3St) (q2 : HttpSt) : Prop :=
  q2.auth = q3.auth ∧ q2.path = q3.path ∧
  (∀ fu x, lookup fu st.pend = some (some x) → ∃ k, lookup fu q2.futs = some k ∧ PendOk W k x) ∧
  (∀ rs k, lookup rs q2.resps = some k →
    ∃ s, lookup rs st.stat = some s ∧ statusOk W k (some [.u16 s]) = true)

end Silmaril.Wasi.Versions.Net
