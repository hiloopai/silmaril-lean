module

public import Silmaril.Wasi.Versions.Accept3.Defs
public import Silmaril.Wasi.Versions.Net3.Defs
public import Silmaril.Wasi.Versions.Stateful.Defs

@[expose] public section

/-!
# Accept across versions: the 0.3 `listen` stream over the 0.2 `accept`

A component that exports the 0.3 listen/accept slice of `Silmaril.Wasi.Versions.Accept3`
(`bind`, `listen`, `stream.read` on the listening stream, `get-remote-address`) and imports the
0.2 one of `Silmaril.Wasi.Versions.NetMore` (`start-bind`, `accept`, `remote-address`). It is
relation (b) for accept: over a host of the 0.2 theory `acceptTh P` it is a model of the 0.3
theory `acc3Th P`, for the same peers (`Accept3Over.Thms.acc3Over2_model`).

* `bind(s, addr)` calls `start-bind(s, network, addr)` with the network handle `0` and passes
  the answer, an error code translated by `Net.e2to3` (as `Net3.Over`); on a socket that is
  already listening it answers `error(invalid-state)` without calling (0.2 would allow the
  rebind, 0.3 says "The socket is already bound").
* `listen(s)` answers `ok(stream s)` (the stream handle is the socket handle) and records `s`
  as listening when it was bound.
* `stream.read(st, n)` on a listening stream calls `accept(st)` once: `ok((c, in, out))` is
  one socket `c`, `COMPLETED 1`; any other answer is `BLOCKED` (nothing to accept now). On a
  stream that is not listening it answers `BLOCKED` without calling.
* `get-remote-address(c)` calls `remote-address(c)` and passes the answer, an error code
  translated.

A real adapter would also call `finish-bind`, `start-listen` and `finish-listen`, and would
wait on the socket's pollable instead of answering `BLOCKED`; `acceptTh` does not constrain
those functions, so they are left out (as `Net3.Over` leaves out blocking). The input and
output streams of an accepted connection are dropped.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.Accept3Over

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasi.Versions (SBody SProg)
open Silmaril.Wasi.Versions.Net
open Silmaril.Wasi.Versions.Accept3
open Silmaril.Wasi.Versions.P3 (natV cStreamRead)

/-- The 0.2 accept functions imported. -/
def acc2I : Set FnName := {tcpBind, tcpAccept, tcpRemote}

/-- The 0.3 listen/accept functions exported. -/
def acc3X : Set FnName := {tcpBind3, tcpListen3, cStreamRead, tcpRemote3}

def iBind : {f // f ∈ acc2I} := ⟨tcpBind, by simp [acc2I]⟩
def iAccept : {f // f ∈ acc2I} := ⟨tcpAccept, by simp [acc2I]⟩
def iRemote : {f // f ∈ acc2I} := ⟨tcpRemote, by simp [acc2I]⟩

/-- The adapter's state: the sockets it bound and the sockets listening (bound when listened). -/
structure ASt where
  bound : List (BitVec 32) := []
  lst : List (BitVec 32) := []

/-- The 0.3 answer of a 0.2 unit answer (`start-bind`). -/
def unitAns3 : Option (List Val) → Option (List Val)
  | some [.variant 0 none] => some [okV none]
  | some [.variant 1 (some (.variant k _))] => some [errV (some (ecV3 (e2to3 k)))]
  | _ => none

/-- The 0.3 answer of a 0.2 `remote-address` answer. -/
def addrAns3 : Option (List Val) → Option (List Val)
  | some [.variant 0 (some a)] => some [okV (some a)]
  | some [.variant 1 (some (.variant k _))] => some [errV (some (ecV3 (e2to3 k)))]
  | _ => none

/-- `BLOCKED`, nothing read. -/
def blockedA : Option (List Val) := some [natV Silmaril.Wasm.Component.Async.blocked, .record []]

/-- The `stream.read` answer of a 0.2 `accept` answer. -/
def readAns3 : Option (List Val) → Option (List Val)
  | some [.variant 0 (some (.record [.u32 c, _, _]))] => some [completed1, .record [.u32 c]]
  | some _ => blockedA
  | none => none

/-- A unit `ok`. -/
def isOkU : Option (List Val) → Bool
  | some [.variant 0 none] => true
  | _ => false

/-- The adapter's state after the 0.2 answer `r` of `start-bind(s, …)`. -/
def bindNext (A : ASt) (s : BitVec 32) (r : Option (List Val)) : ASt :=
  if isOkU r then { A with bound := s :: A.bound } else A

/-- The program of `bind(s, addr)`. -/
def bindProg (A : ASt) (a : List Val) : SProg ASt acc2I :=
  match a with
  | .u32 s :: addr :: _ =>
    if s ∈ A.lst then .pure (A, some [errV (some (ecV3 eInvalidState3'))])
    else .call (iBind, [.u32 s, .u32 0, addr]) fun r => .pure (bindNext A s r, unitAns3 r)
  | _ => .pure (A, none)

/-- The result of `listen(s)` (no import call). -/
def listenRes (A : ASt) (a : List Val) : ASt × Option (List Val) :=
  match a with
  | .u32 s :: _ =>
    (if s ∈ A.bound then { A with lst := s :: A.lst } else A, some [okV (some (.u32 s))])
  | _ => (A, none)

/-- The program of `stream.read(st, n)`. -/
def readProg (A : ASt) (a : List Val) : SProg ASt acc2I :=
  match a with
  | .u32 st :: _ =>
    if st ∈ A.lst then .call (iAccept, [.u32 st]) fun r => .pure (A, readAns3 r)
    else .pure (A, blockedA)
  | _ => .pure (A, none)

/-- The program of `get-remote-address(c)`. -/
def remoteProg (A : ASt) (a : List Val) : SProg ASt acc2I :=
  match a with
  | .u32 c :: _ => .call (iRemote, [.u32 c]) fun r => .pure (A, addrAns3 r)
  | _ => .pure (A, none)

/-- **The 0.3 listen/accept slice over the 0.2 accept.** -/
def acc3Over2 : SBody ASt acc2I acc3X := fun A q =>
  if q.1.1 = tcpBind3 then bindProg A q.2
  else if q.1.1 = tcpListen3 then .pure (listenRes A q.2)
  else if q.1.1 = cStreamRead then readProg A q.2
  else remoteProg A q.2

/-- **The invariant**: the bound sockets agree; the adapter's listening sockets are those of
the 0.3 state, each listening at the address it is bound to in 0.2; every socket accepted in
the 0.3 state is accepted at the same address in the 0.2 state. -/
def JA (A : ASt) (qT : AccSt) (qG : Acc3St) : Prop :=
  qG.bound = qT.bound ∧
  (∀ s, s ∈ A.bound ↔ (lookup s qG.bound).isSome) ∧
  (∀ st, st ∈ A.lst ↔ (lookup st qG.lst).isSome) ∧
  (∀ st addr, lookup st qG.lst = some addr → lookup st qT.bound = some addr) ∧
  (∀ c addr, lookup c qG.acc = some addr → lookup c qT.acc = some addr)

end Silmaril.Wasi.Versions.Accept3Over
