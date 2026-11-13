module

public import Silmaril.Wasi.Versions.HttpReqBodyOver.Defs

@[expose] public section

/-!
# Outgoing request bodies, 0.2 over 0.3 (`req2Over3`)

`req2Over3 rounds` imports the 0.3 slice with outgoing bodies (`req3Fns`) and exports the 0.2
one (`req2Fns`). It keeps its own copy of the 0.2 theory state (`Req2St`, updated with
`req2Next` on every answer it gives) and a counter for fresh handles, and does the 0.3 exchange
**when the 0.2 future is read**, which is when the 0.2 theory checks the outcome (the body it
checks is the one finished by then):

* `set-authority`, `set-path-with-query`, `output-stream.write`, `blocking-write-and-flush`,
  `outgoing-body.finish` answer `ok`; `outgoing-request.body`, `outgoing-body.write`, `handle`
  answer `ok` of a fresh handle. None calls the 0.3 host.
* `future-incoming-response.get(f)` of a future of the request key `k` whose body `bs` is
  finished (in the adapter's copy; otherwise it traps): `stream.new` → `(rd, wr)`, then
  `stream.write(wr, rest)` until the whole body is written (at most `rounds` writes),
  `stream.drop-writable(wr)`, `request.new(0, some(rd), 0, none)` → `rq` (the headers and the
  trailers future are placeholder handles: `fields` and `future.new` are not in the slice, and
  the theory does not read them), `set-authority(rq, k.1)`, `set-path-with-query(rq, k.2)`,
  `send(rq)`; the answer `v` of `send` is returned as `some(ok(v))`. Each `get` does the
  exchange again (the 0.2 theory checks every `get`).
* `incoming-response.status(rs)` is forwarded to 0.3 `get-status-code(rs)`.

Any unexpected answer traps.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)

/-! ## Imports -/

/-- `stream.new` as a 0.3 import with bodies. -/
def mStreamNew : {f // f ∈ req3Fns} := ⟨P3.cStreamNew, by rw [req3Fns_eq]; exact Or.inr (by simp)⟩
/-- `stream.write` as a 0.3 import with bodies. -/
def mStreamWrite : {f // f ∈ req3Fns} :=
  ⟨P3.cStreamWrite, by rw [req3Fns_eq]; exact Or.inr (by simp)⟩
/-- `stream.drop-writable` as a 0.3 import with bodies. -/
def mStreamDropW : {f // f ∈ req3Fns} :=
  ⟨P3.cStreamDropW, by rw [req3Fns_eq]; exact Or.inr (by simp)⟩
/-- `request.new` as a 0.3 import. -/
def mReqNew : {f // f ∈ req3Fns} := ⟨reqNew3, by rw [req3Fns_eq]; exact Or.inr (by simp)⟩
/-- `set-authority` as a 0.3 import with bodies. -/
def mSetAuth3 : {f // f ∈ req3Fns} := ⟨setAuth3, Or.inl (by simp [http3Fns_eq])⟩
/-- `set-path-with-query` as a 0.3 import with bodies. -/
def mSetPath3 : {f // f ∈ req3Fns} := ⟨setPath3, Or.inl (by simp [http3Fns_eq])⟩
/-- `send` as a 0.3 import with bodies. -/
def mSend3 : {f // f ∈ req3Fns} := ⟨send3, Or.inl (by simp [http3Fns_eq])⟩
/-- `get-status-code` as a 0.3 import with bodies. -/
def mStatus3 : {f // f ∈ req3Fns} := ⟨getStatus3, Or.inl (by simp [http3Fns_eq])⟩

/-! ## The exchange -/

/-- Write `rest` to `wr`, at most `n` writes; `true` when everything is written. -/
def bodyWLoop : Nat → BitVec 32 → List (BitVec 8) → Prog (nsig req3Fns) Bool
  | _, _, [] => .pure true
  | 0, _, _ :: _ => .pure false
  | n + 1, wr, b :: bs => .call (mStreamWrite, [.u32 wr, bytesV (b :: bs)]) fun r =>
    match countOf3 r with
    | some c => bodyWLoop n wr ((b :: bs).drop c)
    | none => .pure false

/-- The 0.2 `get` answer of a 0.3 `send` answer. -/
def wrapGet : Option (List Val) → Option (List Val)
  | some [v] => some [.variant 1 (some (.variant 0 (some v)))]
  | _ => none

/-- After the body: make the request, set its key, send. -/
def reqXchg2 (rd : BitVec 32) (k : Val × Val) : Prog (nsig req3Fns) (Option (List Val)) :=
  .call (mReqNew, [.u32 0, .variant 1 (some (.u32 rd)), .u32 0, noneV]) fun r =>
    match r with
    | some [.record [.u32 rq, _]] =>
      .call (mSetAuth3, [.u32 rq, k.1]) fun r₁ =>
        if isOkU r₁ then
          .call (mSetPath3, [.u32 rq, k.2]) fun r₂ =>
            if isOkU r₂ then .call (mSend3, [.u32 rq]) fun x => .pure (wrapGet x)
            else .pure none
        else .pure none
    | _ => .pure none

/-- After `stream.new`: write the body, drop the writer, then the request. -/
def reqXchg1 (rounds : Nat) (rd wr : BitVec 32) (k : Val × Val) (bs : List (BitVec 8)) :
    Prog (nsig req3Fns) (Option (List Val)) :=
  (bodyWLoop rounds wr bs).bind fun ok =>
    if ok then .call (mStreamDropW, [.u32 wr]) fun _ => reqXchg2 rd k else .pure none

/-- The exchange of the request of key `k` with the body `bs`. -/
def reqXchg (rounds : Nat) (k : Val × Val) (bs : List (BitVec 8)) :
    Prog (nsig req3Fns) (Option (List Val)) :=
  .call (mStreamNew, []) fun r =>
    match r with
    | some [.u32 rd, .u32 wr] => reqXchg1 rounds rd wr k bs
    | _ => .pure none

/-- The program of `get(f)`, from the adapter's copy `s` of the 0.2 state. -/
def getProg (rounds : Nat) (s : Req2St) (a : List Val) : Prog (nsig req3Fns) (Option (List Val)) :=
  match a with
  | .u32 fu :: _ =>
    match lookup fu s.futs with
    | some (k, ob) =>
      match s.done ob with
      | some bs => reqXchg rounds k bs
      | none => .pure none
    | none => .pure none
  | _ => .pure none

/-! ## The adapter -/

/-- The answer of an export served without the host. -/
def localAns2 (n : Nat) (f : FnName) : Option (List Val) :=
  if f = outReqBody2 ∨ f = outBodyWrite2 ∨ f = httpHandle then
    some [okV (some (.u32 (BitVec.ofNat 32 n)))]
  else some [okV none]

/-- The program of an export call, before the state update. -/
def req2Prog (rounds : Nat) (s : Req2St × Nat) (f : FnName) (a : List Val) :
    Prog (nsig req3Fns) (Option (List Val)) :=
  if f = futGet then getProg rounds s.1 a
  else if f = respStatus then .call (mStatus3, a) fun r => .pure r
  else .pure (localAns2 s.2 f)

/-- **Outgoing request bodies, 0.2 over 0.3.** -/
def req2Over3 (rounds : Nat) : SBody (Req2St × Nat) req3Fns req2Fns := fun s q =>
  (req2Prog rounds s q.1.1 q.2).bind fun x => .pure ((req2Next s.1 (.imp q.1.1 q.2 x), s.2 + 1), x)

/-- The invariant of `req2Over3`: the adapter's copy is the 0.2 theory state, and the two
theories record the same responses. -/
def JR2 (s : Req2St × Nat) (q3 : Req3St) (q2 : Req2St) : Prop := s.1 = q2 ∧ q3.resps = q2.resps

end Silmaril.Wasi.Versions.Net
