module

public import Silmaril.Wasi.Versions.Net3.Defs
public import Silmaril.Wasi.Versions.Stateful.Defs

@[expose] public section

/-!
# TCP connect across versions: 0.3 over 0.2 and 0.2 over 0.3

Two components between the 0.2 TCP connect slice (`Net.tcpImports`, theory `tcpTh`) and the 0.3
one (`tcp3Fns`, theory `tcpTh3`).

**`tcp3Over2 rounds`** (relation (b)): imports 0.2, exports 0.3.

* `create(family)` calls `create-tcp-socket(family)`; the socket handle is passed through, an
  error code is translated (`e2to3`).
* `connect(s, addr)` calls `instance-network()`, then `start-connect(s, network, addr)`; on
  `ok` it polls `finish-connect(s)` while the answer is `would-block`, at most `rounds` times
  (`poll3`), and returns the outcome with its code translated (`outcome3`). A real component
  would `subscribe` and `block` on the socket's pollable between polls; the 0.2 theory
  `tcpTh` does not relate pollables to `finish-connect`, so blocking is left out. It traps when
  the rounds run out, when `start-connect` fails (its errors are not outcomes of the network),
  and on ill-typed answers.

**`tcp2Over3`** (relation (c)): imports 0.3, exports 0.2. Its state `CSt` keeps the outcome of
each started connect (`pend`, the 0.2 answer of `finish-connect`) and a counter for stream
handles.

* `instance-network()` answers the handle `0` (0.3 has no network resource).
* `create-tcp-socket(family)` calls `create(family)`, translating error codes (`e3to2`).
* `start-connect(s, network, addr)` calls the async `connect(s, addr)` **sync-lowered**: the
  0.2 call blocks until the 0.3 outcome is known, stores the 0.2 answer of `finish-connect`
  (`fin2`: `ok` with two fresh stream handles, or the translated error) and answers `ok`; a trap
  of `connect` (or an ill-typed answer) is a trap.
* `finish-connect(s)` answers the stored outcome once and forgets it; without one it answers
  `error(not-in-progress)`.

The input and output streams of a connection are fresh handles only: their reads and writes
(0.3 `send`/`receive`) are not part of this slice.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)

/-! ## 0.3 over 0.2 -/

/-- `instance-network` as a 0.2 import. -/
def iNet : {f // f ∈ tcpImports} := ⟨instanceNetwork, by simp [tcpImports_eq]⟩
/-- `create-tcp-socket` as a 0.2 import. -/
def iCreate : {f // f ∈ tcpImports} := ⟨createTcp, by simp [tcpImports_eq]⟩
/-- `start-connect` as a 0.2 import. -/
def iStart : {f // f ∈ tcpImports} := ⟨startConnect, by simp [tcpImports_eq]⟩
/-- `finish-connect` as a 0.2 import. -/
def iFinish : {f // f ∈ tcpImports} := ⟨finishConnect, by simp [tcpImports_eq]⟩

/-- The 0.3 answer of a 0.2 `finish-connect` answer. -/
def outcome3 : Option (List Val) → Option (List Val)
  | some [.variant 0 (some (.record [.u32 _, .u32 _]))] => some [okV none]
  | some [.variant 1 (some (.variant k none))] => some [errV (some (ecV3 (e2to3 k)))]
  | _ => none

/-- The 0.3 answer of a 0.2 `create-tcp-socket` answer. -/
def createAns3 : Option (List Val) → Option (List Val)
  | some [.variant 0 (some h)] => some [okV (some h)]
  | some [.variant 1 (some (.variant k _))] => some [errV (some (ecV3 (e2to3 k)))]
  | _ => none

/-- Poll `finish-connect(s)` while it answers `would-block`, at most `k` times. -/
def poll3 : Nat → BitVec 32 → SProg Unit tcpImports
  | 0, _ => .pure ((), none)
  | k + 1, s => .call (iFinish, [.u32 s]) fun r =>
    if isWouldBlock r then poll3 k s else .pure ((), outcome3 r)

/-- The program of `connect(s, addr)`. -/
def connect3Prog (rounds : Nat) (a : List Val) : SProg Unit tcpImports :=
  match a with
  | .u32 s :: addr :: _ =>
    .call (iNet, []) fun r =>
      match r with
      | some [nv] =>
        .call (iStart, [.u32 s, nv, addr]) fun r₂ =>
          match r₂ with
          | some [.variant 0 none] => poll3 rounds s
          | _ => .pure ((), none)
      | _ => .pure ((), none)
  | _ => .pure ((), none)

/-- **TCP connect 0.3 over 0.2.** -/
def tcp3Over2 (rounds : Nat) : SBody Unit tcpImports tcp3Fns := fun _ q =>
  if q.1.1 = create3 then .call (iCreate, q.2) fun r => .pure ((), createAns3 r)
  else connect3Prog rounds q.2

/-! ## 0.2 over 0.3 -/

/-- `create` as a 0.3 import. -/
def iCreate3 : {f // f ∈ tcp3Fns} := ⟨create3, by simp [tcp3Fns_eq]⟩
/-- `connect` as a 0.3 import. -/
def iConnect3 : {f // f ∈ tcp3Fns} := ⟨connect3, by simp [tcp3Fns_eq]⟩

/-- The state of `tcp2Over3`: the stored `finish-connect` answers, and the next stream handle. -/
structure CSt where
  /-- The 0.2 answer of `finish-connect`, by socket. -/
  pend : List (BitVec 32 × Option (List Val)) := []
  /-- The next stream handle. -/
  next : Nat := 0

/-- 0.2 `error-code.invalid-argument` (`eInvalidArg_wit`: the WIT case number of the name). -/
abbrev eInvalidArg : Nat := 3

/-- The literal is the case number of `invalid-argument` in the 0.2 `error-code` of the WIT. -/
theorem eInvalidArg_wit : eInvalidArg = WitImport.caseIdx codes2 "invalid-argument" := by
  decide +kernel

/-- The 0.2 `finish-connect` answer of a 0.3 `connect` answer (`none`: not a 0.3 answer). -/
def fin2 (n : Nat) : Option (List Val) → Option (Option (List Val))
  | some [.variant 0 none] => some (connectAns n none)
  | some [.variant 1 (some (.variant k _))] => some (errAnsN (e3to2 k))
  | _ => none

/-- The 0.2 answer of a 0.3 `create` answer. -/
def createAns2 : Option (List Val) → Option (List Val)
  | some [.variant 0 (some h)] => some [okV (some h)]
  | some [.variant 1 (some (.variant k _))] => some [errV (some (.variant (e3to2 k) none))]
  | _ => none

/-- The program of `start-connect`. -/
def startProg (st : CSt) (a : List Val) : SProg CSt tcp3Fns :=
  match a with
  | .u32 s :: _ :: addr :: _ =>
    .call (iConnect3, [.u32 s, addr]) fun r =>
      match fin2 st.next r with
      | some fin => .pure ({ pend := (s, fin) :: st.pend, next := st.next + 2 }, some [okV none])
      | none => .pure (st, none)
  | _ => .pure (st, errAnsN eInvalidArg)

/-- The result of `finish-connect` (no import call). -/
def finishRes (st : CSt) (a : List Val) : CSt × Option (List Val) :=
  match a with
  | .u32 s :: _ =>
    match lookup s st.pend with
    | some fin => ({ st with pend := st.pend.filter (·.1 != s) }, fin)
    | none => (st, errAnsN eNotInProgress)
  | _ => (st, errAnsN eNotInProgress)

/-- **TCP connect 0.2 over 0.3.** -/
def tcp2Over3 : SBody CSt tcp3Fns tcpImports := fun st q =>
  if q.1.1 = instanceNetwork then .pure (st, some [.u32 0])
  else if q.1.1 = createTcp then .call (iCreate3, q.2) fun r => .pure (st, createAns2 r)
  else if q.1.1 = startConnect then startProg st q.2
  else .pure (finishRes st q.2)

/-- **The invariant of `tcp2Over3`** over the network `N3`: every socket pending in the 0.2
theory state `qG` has a stored answer, which is the network's outcome; no stored answer is
`would-block`. -/
def J2 (N3 : Network) (st : CSt) (_ : Unit) (qG : TcpSt) : Prop :=
  (∀ s addr, lookup s qG = some addr →
    ∃ fin, lookup s st.pend = some fin ∧ connectOk (net2of3 N3 addr) fin = true) ∧
  (∀ s fin, lookup s st.pend = some fin → isWouldBlock fin = false)

end Silmaril.Wasi.Versions.Net
