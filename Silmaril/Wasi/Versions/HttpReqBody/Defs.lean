module

public import Silmaril.Wasi.Versions.WitImport.PickRest.Defs
public import Silmaril.Wasi.Versions.HttpFields.Defs

@[expose] public section

/-!
# WASI `wasi:http` outgoing request bodies, 0.2 and 0.3, as theories

The outgoing slices of `Silmaril.Wasi.Versions.Net` and `Silmaril.Wasi.Versions.Http3` send requests
whose outcome depends on the authority and the path only (`Web`). Here the outcome may also
depend on the request body: a **request-body web** `Q : QWeb` answers a request (authority,
path-with-query, body bytes) with a status or an `error-code`. `QWeb.ofWeb W` ignores the body.

## 0.2 (`req2Th Q`)

Checked against `vendor/wasi/0.2.12/http/types.wit` and `vendor/wasi/0.2.12/io/streams.wit`:

* `[method]outgoing-request.body() -> result<outgoing-body>` (`outReqBody2`);
* `[method]outgoing-body.write() -> result<output-stream>` (`outBodyWrite2`);
* `wasi:io/streams` `[method]output-stream.write(contents)` and
  `blocking-write-and-flush(contents) -> result<_, stream-error>` (`P2.osWrite`, `P2.osBwf`)
  on such a stream;
* `[static]outgoing-body.finish(this, trailers) -> result<_, error-code>` (`outBodyFinish2`);
* with `set-authority`, `set-path-with-query`, `handle`, `future-incoming-response.get` and
  `incoming-response.status` as in `httpTh`.

The state records the body of each request, the body of each output stream, the bytes each body
accepted (writes answered `ok`; nothing after `finish`) and whether it was finished, and per
future and per response its request key and body. **The check**: `get` answered
`some(ok(x))` for a request whose body was finished with the bytes `bs` matches `Q` at
`(authority, path, bs)`; `status` of such a response is `Q`'s status. A request whose body is
not finished (or was never obtained) is unconstrained.

## 0.3 (`req3Th Q`)

Checked against `vendor/wasi/0.3.2/http/types.wit`:
`[static]request.new(headers, contents: option<stream<u8>>, trailers, options)
-> tuple<request, future<result<_, error-code>>>` (`reqNew3`), with the Component Model
built-ins `stream.new`, `stream.write` and `stream.drop-writable` (`P3.cStreamNew`,
`P3.cStreamWrite`, `P3.cStreamDropW`) on the body stream, and `set-authority`,
`set-path-with-query`, `send`, `get-status-code` as in `httpTh3`. `stream.new` answers the
readable and the writable end; `stream.write(w, buf)` answered with the packed count `c` has
written the first `c` bytes of `buf`; `drop-writable(w)` finishes the body. A request made with
`contents = none` has the empty body. **The check**: `send(r)` answered (not trapping) for a
request whose body is finished with `bs` matches `Q` at `(authority, path, bs)`;
`get-status-code` likewise.

## Concrete hosts

`req2Impl Q`, `req3Impl Q`: every call succeeds with fresh handles (a 0.3 `stream.write`
accepts the whole buffer, at most `2^27` bytes); `get` / `send` answer `Q`'s outcome for the
bytes written so far, `status` / `get-status-code` `Q`'s status.

**Not modelled**: headers of the request (`fields`, `Silmaril.Wasi.Versions.HttpFields`, is a
separate slice), the trailers argument of `finish` / `request.new`, the transmission future of
`request.new`, `check-write`, the rule that the output stream must be dropped before `finish`,
early responses (the web reads the whole body). The adapters between the two versions for
outgoing bodies are not covered.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-! ## Request-body webs -/

/-- A request-body web: the outcome of a request for an authority, a path-with-query and a body. -/
abbrev QWeb : Type := Val → Val → List (BitVec 8) → HttpOutcome

/-- The request-body web of a web: the body is ignored. -/
def QWeb.ofWeb (W : Web) : QWeb := fun a p _ => W a p

/-- The web of a request-body web at a fixed body. -/
def QWeb.at (Q : QWeb) (bs : List (BitVec 8)) : Web := fun a p => Q a p bs

/-! ## 0.2 -/

/-- `wasi:http/types.[method]outgoing-request.body`. -/
def outReqBody2 : FnName := ⟨"wasi:http/types", "[method]outgoing-request.body"⟩
/-- `wasi:http/types.[method]outgoing-body.write`. -/
def outBodyWrite2 : FnName := ⟨"wasi:http/types", "[method]outgoing-body.write"⟩
/-- `wasi:http/types.[static]outgoing-body.finish`. -/
def outBodyFinish2 : FnName := ⟨"wasi:http/types", "[static]outgoing-body.finish"⟩

/-- The 0.2 functions with outgoing bodies: `httpImports` and the body functions **read from
the vendored WIT** (`http2T` and `io2T` with the keys `WitImport.req2Keys`; `req2Fns_eq`). -/
def req2Fns : Set FnName :=
  httpImports ∪ {f | f ∈ WitImport.pick (WitImport.names WitImport.http2T ++
    WitImport.names WitImport.io2T) WitImport.req2Keys}

/-- **The imported outgoing-body functions are the hand-written ones.** -/
theorem req2Fns_eq :
    req2Fns = httpImports ∪ {outReqBody2, outBodyWrite2, outBodyFinish2, P2.osWrite, P2.osBwf} := by
  unfold req2Fns
  congr 1
  ext f
  show f ∈ WitImport.pick (WitImport.names WitImport.http2T ++ WitImport.names WitImport.io2T)
    WitImport.req2Keys ↔ _
  rw [(show (WitImport.pick (WitImport.names WitImport.http2T ++ WitImport.names WitImport.io2T)
    WitImport.req2Keys).Perm [outReqBody2, outBodyWrite2, outBodyFinish2, P2.osWrite, P2.osBwf] by
      decide +kernel).mem_iff]
  simp

/-- A write to an output stream. -/
def isWriteFn (f : FnName) : Bool := f == P2.osWrite || f == P2.osBwf

/-- The state of the 0.2 theory with outgoing bodies. -/
structure Req2St where
  /-- Authorities set on requests. -/
  auth : List (BitVec 32 × Val) := []
  /-- Paths set on requests. -/
  path : List (BitVec 32 × Val) := []
  /-- The body of each request. -/
  rbody : List (BitVec 32 × BitVec 32) := []
  /-- The body of each output stream. -/
  sbody : List (BitVec 32 × BitVec 32) := []
  /-- The bytes each body accepted, and whether it was finished. -/
  written : List (BitVec 32 × (List (BitVec 8) × Bool)) := []
  /-- The request key and body of each future. -/
  futs : List (BitVec 32 × ((Val × Val) × Option (BitVec 32))) := []
  /-- The request key and finished body (if any) of each response. -/
  resps : List (BitVec 32 × ((Val × Val) × Option (List (BitVec 8)))) := []

/-- The authority and path of the request `r`. -/
def Req2St.key (q : Req2St) (r : BitVec 32) : Val × Val :=
  ((lookup r q.auth).getD noneV, (lookup r q.path).getD noneV)

/-- The finished bytes of a body, if it is finished. -/
def Req2St.done (q : Req2St) : Option (BitVec 32) → Option (List (BitVec 8))
  | some b =>
    match lookup b q.written with
    | some (bs, true) => some bs
    | _ => none
  | none => none

/-- `result` without payload: `ok`. -/
def isOkU : Option (List Val) → Bool
  | some [.variant 0 none] => true
  | _ => false

/-- The next state after a write of `c` to the stream `s`. -/
def writeNext (q : Req2St) (s : BitVec 32) (c : Val) : Req2St :=
  match lookup s q.sbody with
  | some b =>
    match lookup b q.written, valOf c with
    | some (bs, false), some cs => { q with written := (b, (bs ++ cs, false)) :: q.written }
    | _, _ => q
  | none => q

/-- **The next state** (independent of the web). -/
def req2Next (q : Req2St) (e : WEv) : Req2St :=
  match e with
  | .imp f (.u32 h :: rest) r =>
    if f = setAuthority then
      (match rest with
       | v :: _ => if isOkU r then { q with auth := (h, v) :: q.auth } else q
       | [] => q)
    else if f = setPath then
      (match rest with
       | v :: _ => if isOkU r then { q with path := (h, v) :: q.path } else q
       | [] => q)
    else if f = outReqBody2 then
      (match okHandle r with
       | some b => { q with rbody := (h, b) :: q.rbody, written := (b, ([], false)) :: q.written }
       | none => q)
    else if f = outBodyWrite2 then
      (match okHandle r with
       | some s => { q with sbody := (s, h) :: q.sbody }
       | none => q)
    else if isWriteFn f then
      (match rest with
       | c :: _ => if isOkU r then writeNext q h c else q
       | [] => q)
    else if f = outBodyFinish2 then
      (match lookup h q.written with
       | some (bs, _) => if isOkU r then { q with written := (h, (bs, true)) :: q.written } else q
       | none => q)
    else if f = httpHandle then
      (match okHandle r with
       | some fu => { q with futs := (fu, (q.key h, lookup h q.rbody)) :: q.futs }
       | none => q)
    else if f = futGet then
      (match r, lookup h q.futs with
       | some [.variant 1 (some (.variant 0 (some (.variant 0 (some (.u32 rs))))))], some (k, ob) =>
         { q with resps := (rs, (k, q.done ob)) :: q.resps }
       | _, _ => q)
    else q
  | _ => q

/-- **The check** of an answer against the request-body web `Q`. -/
def req2Ok (Q : QWeb) (q : Req2St) (e : WEv) : Bool :=
  match e with
  | .imp f (.u32 h :: _) r =>
    if f = futGet then
      (match r, lookup h q.futs with
       | some [.variant 1 (some (.variant 0 (some x)))], some (k, ob) =>
         match q.done ob with
         | some bs => outcomeOk (Q k.1 k.2 bs) x
         | none => true
       | _, _ => true)
    else if f = respStatus then
      (match lookup h q.resps with
       | some (k, some bs) => statusOk (Q.at bs) k r
       | _ => true)
    else true
  | _ => true

/-- **The 0.2 HTTP theory with outgoing bodies** of the request-body web `Q`. -/
def req2Th (Q : QWeb) : Protocol Req2St WEv := gated {} req2Next (req2Ok Q)

/-- The state after the answers `p`. -/
def req2State (p : List WEv) : Req2St := p.foldl req2Next {}

/-- **The concrete 0.2 host with outgoing bodies** of `Q`. -/
def req2Impl (Q : QWeb) : Impl := fun p f a =>
  let q := req2State p
  let n := p.length
  if f = setAuthority ∨ f = setPath ∨ isWriteFn f = true ∨ f = outBodyFinish2 then some [okV none]
  else if f = outReqBody2 ∨ f = outBodyWrite2 ∨ f = httpHandle then
    some [okV (some (.u32 (BitVec.ofNat 32 n)))]
  else if f = futGet then
    match lookup (selfH a) q.futs with
    | some (k, ob) => some [.variant 1 (some (okV (some (outcomeV n (Q k.1 k.2 ((q.done ob).getD []))))))]
    | none => some [gotV]
  else if f = respStatus then
    match lookup (selfH a) q.resps with
    | some (k, some bs) => statusAns (Q.at bs) k
    | _ => some [.u16 200]
  else none

/-! ## 0.3 -/

/-- `wasi:http/types@0.3.2.[static]request.new`. -/
def reqNew3 : FnName := ⟨"wasi:http/types@0.3.2", "[static]request.new"⟩

/-- The 0.3 functions with outgoing bodies: `http3Fns`, `request.new` **read from the vendored
WIT** (`http3T` with the keys `WitImport.req3Keys`), and three `canon` built-ins, which are not
WIT functions and stay hand-written (`req3Fns_eq`). -/
def req3Fns : Set FnName :=
  http3Fns ∪ {f | f ∈ WitImport.pick (WitImport.names WitImport.http3T) WitImport.req3Keys ++
    [P3.cStreamNew, P3.cStreamWrite, P3.cStreamDropW]}

/-- **The imported `request.new` with the built-ins is the hand-written set.** -/
theorem req3Fns_eq :
    req3Fns = http3Fns ∪ {reqNew3, P3.cStreamNew, P3.cStreamWrite, P3.cStreamDropW} := by
  unfold req3Fns
  congr 1
  ext f
  show f ∈ WitImport.pick (WitImport.names WitImport.http3T) WitImport.req3Keys ++
    [P3.cStreamNew, P3.cStreamWrite, P3.cStreamDropW] ↔ _
  rw [(show (WitImport.pick (WitImport.names WitImport.http3T) WitImport.req3Keys ++
    [P3.cStreamNew, P3.cStreamWrite, P3.cStreamDropW]).Perm
      [reqNew3, P3.cStreamNew, P3.cStreamWrite, P3.cStreamDropW] by decide +kernel).mem_iff]
  simp

/-- The state of the 0.3 theory with outgoing bodies. -/
structure Req3St where
  /-- Authorities set on requests. -/
  auth : List (BitVec 32 × Val) := []
  /-- Paths set on requests. -/
  path : List (BitVec 32 × Val) := []
  /-- The readable end of each writable end. -/
  pairs : List (BitVec 32 × BitVec 32) := []
  /-- The bytes written to each readable end, and whether the writer dropped it. -/
  written : List (BitVec 32 × (List (BitVec 8) × Bool)) := []
  /-- The body stream of each request (`none`: no body). -/
  reqs : List (BitVec 32 × Option (BitVec 32)) := []
  /-- The request key and finished body (if any) of each response. -/
  resps : List (BitVec 32 × ((Val × Val) × Option (List (BitVec 8)))) := []

/-- The authority and path of the request `r`. -/
def Req3St.key (q : Req3St) (r : BitVec 32) : Val × Val :=
  ((lookup r q.auth).getD noneV, (lookup r q.path).getD noneV)

/-- The finished body of the request `r`, if it is finished. -/
def Req3St.done (q : Req3St) (r : BitVec 32) : Option (List (BitVec 8)) :=
  match lookup r q.reqs with
  | some none => some []
  | some (some rd) =>
    match lookup rd q.written with
    | some (bs, true) => some bs
    | _ => none
  | none => none

/-- The body stream of a `contents` argument (`some none`: no body). -/
def contentsOf : Val → Option (Option (BitVec 32))
  | .variant 0 none => some none
  | .variant 1 (some (.u32 rd)) => some (some rd)
  | _ => none

/-- The count of a packed copy answer. -/
def countOf3 : Option (List Val) → Option Nat
  | some [.u32 pv] =>
    match copy3 pv with
    | some (some (_, c)) => some c
    | _ => none
  | _ => none

/-- **The next state** (independent of the web). -/
def req3Next (q : Req3St) (e : WEv) : Req3St :=
  match e with
  | .imp f a r =>
    if f = P3.cStreamNew then
      (match r with
       | some [.u32 rd, .u32 wr] => { q with pairs := (wr, rd) :: q.pairs, written := (rd, ([], false)) :: q.written }
       | _ => q)
    else if f = P3.cStreamWrite then
      (match a, countOf3 r with
       | .u32 w :: buf :: _, some c =>
         match lookup w q.pairs with
         | some rd =>
           match lookup rd q.written, valOf buf with
           | some (bs, false), some cs => { q with written := (rd, (bs ++ cs.take c, false)) :: q.written }
           | _, _ => q
         | none => q
       | _, _ => q)
    else if f = P3.cStreamDropW then
      (match a with
       | .u32 w :: _ =>
         match lookup w q.pairs with
         | some rd =>
           match lookup rd q.written with
           | some (bs, _) => { q with written := (rd, (bs, true)) :: q.written }
           | none => q
         | none => q
       | _ => q)
    else if f = reqNew3 then
      (match a, r with
       | _ :: cv :: _, some [.record [.u32 rq, _]] =>
         match contentsOf cv with
         | some o => { q with reqs := (rq, o) :: q.reqs }
         | none => q
       | _, _ => q)
    else if f = setAuth3 then
      (match a with
       | .u32 h :: v :: _ => if isOkU r then { q with auth := (h, v) :: q.auth } else q
       | _ => q)
    else if f = setPath3 then
      (match a with
       | .u32 h :: v :: _ => if isOkU r then { q with path := (h, v) :: q.path } else q
       | _ => q)
    else if f = send3 then
      (match a, r with
       | .u32 h :: _, some [.variant 0 (some (.u32 rs))] =>
         { q with resps := (rs, (q.key h, q.done h)) :: q.resps }
       | _, _ => q)
    else q
  | _ => q

/-- **The check** of an answer against the request-body web `Q`. -/
def req3Ok (Q : QWeb) (q : Req3St) (e : WEv) : Bool :=
  match e with
  | .imp f (.u32 h :: _) r =>
    if f = send3 then
      (match r, q.done h with
       | some _, some bs => sendOk (Q (q.key h).1 (q.key h).2 bs) r
       | _, _ => true)
    else if f = getStatus3 then
      (match lookup h q.resps with
       | some (k, some bs) => statusOk (Q.at bs) k r
       | _ => true)
    else true
  | _ => true

/-- **The 0.3 HTTP theory with outgoing bodies** of the request-body web `Q`. -/
def req3Th (Q : QWeb) : Protocol Req3St WEv := gated {} req3Next (req3Ok Q)

/-- The state after the answers `p`. -/
def req3State (p : List WEv) : Req3St := p.foldl req3Next {}

/-- **The concrete 0.3 host with outgoing bodies** of `Q`. -/
def req3Impl (Q : QWeb) : Impl := fun p f a =>
  let q := req3State p
  let n := p.length
  if f = P3.cStreamNew then some [P3.natV (2 * n), P3.natV (2 * n + 1)]
  else if f = P3.cStreamWrite then
    (match a with
     | _ :: buf :: _ =>
       some [P3.natV (Silmaril.Wasm.Component.Async.packCopy .completed
         (min ((valOf buf).getD []).length chunk3))]
     | _ => some [P3.natV (Silmaril.Wasm.Component.Async.packCopy .completed 0)])
  else if f = P3.cStreamDropW then some []
  else if f = reqNew3 then some [.record [P3.natV (2 * n), P3.natV (2 * n + 1)]]
  else if f = setAuth3 ∨ f = setPath3 then some [okV none]
  else if f = send3 then
    match a with
    | .u32 r :: _ => sendAns n (Q (q.key r).1 (q.key r).2 ((q.done r).getD []))
    | _ => none
  else if f = getStatus3 then
    match lookup (selfH a) q.resps with
    | some (k, some bs) => statusAns (Q.at bs) k
    | _ => some [.u16 200]
  else none

end Silmaril.Wasi.Versions.Net
