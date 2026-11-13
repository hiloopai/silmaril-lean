module

public import Silmaril.Wasi.Versions.Udp.Defs
public import Silmaril.Wasi.Versions.Net3.Over.Defs

@[expose] public section

/-!
# UDP receive across versions: 0.3 over 0.2 and 0.2 over 0.3

Two components between the 0.2 UDP slice (`udpImports`, theory `udpTh U`) and the 0.3 one
(`udp3Fns`, theory `udpTh3 U`), for the same inbox `U` (a 0.3 datagram
`tuple<list<u8>, ip-socket-address>` and a 0.2 `incoming-datagram` record are the same `Val`).

**`udp3Over2 rounds`** (relation (b)): imports 0.2, exports 0.3. Its state is the list of
**poisoned** sockets: those whose 0.2 `start-bind` succeeded but whose `finish-bind` failed, so
that the 0.2 theory records a binding that 0.3 does not.

* `create(family)` calls `create-udp-socket(family)` (error codes translated, `e2to3`).
* `bind(s, addr)` calls `instance-network()`, `start-bind(s, network, addr)` and, when that
  succeeds, `finish-bind(s)`; it answers `ok` when both succeed, the translated error
  otherwise, and poisons `s` when `finish-bind` fails. It traps on a poisoned socket.
* `receive(s)` calls `stream(s, none)`, then polls `receive(i, 1)` on the incoming stream `i`
  while it answers an empty list, at most `rounds` times, and answers the first datagram. A
  real component would `subscribe` and `block` on the stream's pollable between polls; the 0.2
  theory does not relate pollables to `receive`. It traps on a poisoned socket, when the rounds
  run out, and on ill-typed answers.
* `send` traps (0.2 `outgoing-datagram-stream` is not part of the slice).

**`udp2Over3`** (relation (c)): imports 0.3, exports 0.2. The incoming stream of a socket has
the socket's handle (`stream(s, _)` answers `ok(tuple<s, s>)`). Its state `USt` keeps each
binding with a **generation** (a counter), and the generation of each stream: a stream is tied
to the binding current when it was created, while 0.3 `receive` reads the socket's current
binding, so `receive` on a stream whose binding has since changed answers
`error(invalid-state)` instead of calling 0.3.

* `instance-network()` answers `0`; `create-udp-socket(family)` calls `create(family)`.
* `start-bind(s, network, addr)` calls `bind(s, addr)`; `finish-bind(s)` answers `ok`.
* `stream(s, _)` on a bound socket records the stream and answers `ok(tuple<s, s>)`, else
  `error(invalid-state)`.
* `receive(i, _)` on a stream of the current binding calls `receive(i)` (sync-lowered) and
  answers the datagram as a one-element list.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)

/-! ## Answers -/

/-- `ok(_)`. -/
def isOkUnit : Option (List Val) → Bool
  | some [.variant 0 none] => true
  | _ => false

/-- The incoming stream handle of a 0.2 `stream` answer. -/
def streamIn : Option (List Val) → Option (BitVec 32)
  | some [.variant 0 (some (.record [.u32 i, _]))] => some i
  | _ => none

/-- An empty 0.2 `receive` answer. -/
def isEmptyRecv : Option (List Val) → Bool
  | some [.variant 0 (some (.record []))] => true
  | _ => false

/-- The 0.3 error answer of a 0.2 error answer (a trap otherwise). -/
def errOf3 : Option (List Val) → Option (List Val)
  | some [.variant 1 (some (.variant k _))] => some [errV (some (ecV3 (e2to3 k)))]
  | _ => none

/-- The 0.3 `receive` answer of a 0.2 `receive` answer: the first datagram. -/
def recv3of2 : Option (List Val) → Option (List Val)
  | some [.variant 0 (some (.record (d :: _)))] => some [okV (some d)]
  | r => errOf3 r

/-- The 0.2 error answer of a 0.3 error answer (a trap otherwise). -/
def errOf2 : Option (List Val) → Option (List Val)
  | some [.variant 1 (some (.variant k _))] => errAnsN (e3to2 k)
  | _ => none

/-- The 0.2 `receive` answer of a 0.3 `receive` answer: a one-element list. -/
def recv2of3 : Option (List Val) → Option (List Val)
  | some [.variant 0 (some d)] => some [okV (some (.record [d]))]
  | r => errOf2 r

/-! ## 0.3 over 0.2 -/

/-- `instance-network` as a 0.2 import. -/
def uNet : {f // f ∈ udpImports} := ⟨instanceNetwork, by simp [udpImports_eq]⟩
/-- `create-udp-socket` as a 0.2 import. -/
def uCreate : {f // f ∈ udpImports} := ⟨createUdp, by simp [udpImports_eq]⟩
/-- `start-bind` as a 0.2 import. -/
def uBind : {f // f ∈ udpImports} := ⟨udpBind, by simp [udpImports_eq]⟩
/-- `finish-bind` as a 0.2 import. -/
def uFinish : {f // f ∈ udpImports} := ⟨udpFinishBind, by simp [udpImports_eq]⟩
/-- `stream` as a 0.2 import. -/
def uStream : {f // f ∈ udpImports} := ⟨udpStream, by simp [udpImports_eq]⟩
/-- `receive` as a 0.2 import. -/
def uRecv : {f // f ∈ udpImports} := ⟨udpReceive, by simp [udpImports_eq]⟩

/-- The state of `udp3Over2`: the poisoned sockets. -/
abbrev PSt : Type := List (BitVec 32)

/-- Poll `receive(i, 1)` while it answers an empty list, at most `k` times. -/
def pollU (st : PSt) : Nat → BitVec 32 → SProg PSt udpImports
  | 0, _ => .pure (st, none)
  | k + 1, i => .call (uRecv, [.u32 i, .u64 1]) fun r =>
    if isEmptyRecv r then pollU st k i else .pure (st, recv3of2 r)

/-- The program of `bind(s, addr)`. -/
def bind3Prog (st : PSt) (a : List Val) : SProg PSt udpImports :=
  match a with
  | .u32 s :: addr :: _ =>
    if s ∈ st then .pure (st, none) else
    .call (uNet, []) fun r₀ =>
      match r₀ with
      | some [nv] =>
        .call (uBind, [.u32 s, nv, addr]) fun r₁ =>
          if isOkUnit r₁ then
            .call (uFinish, [.u32 s]) fun r₂ =>
              if isOkUnit r₂ then .pure (st, some [okV none]) else .pure (s :: st, errOf3 r₂)
          else .pure (st, errOf3 r₁)
      | _ => .pure (st, none)
  | _ => .pure (st, none)

/-- The program of `receive(s)`. -/
def recv3Prog (rounds : Nat) (st : PSt) (a : List Val) : SProg PSt udpImports :=
  match a with
  | .u32 s :: _ =>
    if s ∈ st then .pure (st, none) else
    .call (uStream, [.u32 s, .variant 0 none]) fun r =>
      match streamIn r with
      | some i => pollU st rounds i
      | none => .pure (st, errOf3 r)
  | _ => .pure (st, none)

/-- **UDP receive 0.3 over 0.2.** -/
def udp3Over2 (rounds : Nat) : SBody PSt udpImports udp3Fns := fun st q =>
  if q.1.1 = udpCreate3 then .call (uCreate, q.2) fun r => .pure (st, createAns3 r)
  else if q.1.1 = udpBind3 then bind3Prog st q.2
  else if q.1.1 = udpReceive3 then recv3Prog rounds st q.2
  else .pure (st, none)

/-- **The invariant of `udp3Over2`**: an unpoisoned socket bound in the 0.3 theory state `qG`
is bound to the same address in the 0.2 theory state `qT`. -/
def JU3 (st : PSt) (qT : UdpSt) (qG : Udp3St) : Prop :=
  ∀ s a, s ∉ st → lookup s qG = some a → lookup s qT.bound = some a

/-! ## 0.2 over 0.3 -/

/-- `create` as a 0.3 import. -/
def vCreate : {f // f ∈ udp3Fns} := ⟨udpCreate3, by simp [udp3Fns_eq]⟩
/-- `bind` as a 0.3 import. -/
def vBind : {f // f ∈ udp3Fns} := ⟨udpBind3, by simp [udp3Fns_eq]⟩
/-- `receive` as a 0.3 import. -/
def vRecv : {f // f ∈ udp3Fns} := ⟨udpReceive3, by simp [udp3Fns_eq]⟩

/-- The state of `udp2Over3`: bindings with their generation, the generation of each stream,
and the next generation. -/
structure USt where
  /-- The binding of each socket, with its generation. -/
  bnd : List (BitVec 32 × (Val × Nat)) := []
  /-- The generation of the binding each stream was created under. -/
  strm : List (BitVec 32 × Nat) := []
  /-- The next generation. -/
  ctr : Nat := 0

/-- The program of `start-bind(s, network, addr)`. -/
def bind2Prog (st : USt) (a : List Val) : SProg USt udp3Fns :=
  match a with
  | .u32 s :: _ :: addr :: _ =>
    .call (vBind, [.u32 s, addr]) fun r =>
      if isOkUnit r then
        .pure ({ st with bnd := (s, (addr, st.ctr)) :: st.bnd, ctr := st.ctr + 1 }, some [okV none])
      else .pure (st, errOf2 r)
  | _ => .pure (st, errAnsN eInvalidArg)

/-- The result of `stream(s, _)` (no import call). -/
def stream2Res (st : USt) (a : List Val) : USt × Option (List Val) :=
  match a with
  | .u32 s :: _ =>
    match lookup s st.bnd with
    | some (_, g) => ({ st with strm := (s, g) :: st.strm }, some [okV (some (.record [.u32 s, .u32 s]))])
    | none => (st, errAnsN eInvalidState)
  | _ => (st, errAnsN eInvalidArg)

/-- The stream `i` was created under the current binding of its socket. -/
def current (st : USt) (i : BitVec 32) : Bool :=
  match lookup i st.strm, lookup i st.bnd with
  | some g, some (_, g') => g' == g
  | _, _ => false

/-- The program of `receive(i, _)`. -/
def recv2Prog (st : USt) (a : List Val) : SProg USt udp3Fns :=
  match a with
  | .u32 i :: _ =>
    if current st i then .call (vRecv, [.u32 i]) fun r => .pure (st, recv2of3 r)
    else .pure (st, errAnsN eInvalidState)
  | _ => .pure (st, errAnsN eInvalidArg)

/-- **UDP receive 0.2 over 0.3.** -/
def udp2Over3 : SBody USt udp3Fns udpImports := fun st q =>
  if q.1.1 = instanceNetwork then .pure (st, some [.u32 0])
  else if q.1.1 = createUdp then .call (vCreate, q.2) fun r => .pure (st, createAns2 r)
  else if q.1.1 = udpBind then bind2Prog st q.2
  else if q.1.1 = udpFinishBind then .pure (st, some [okV none])
  else if q.1.1 = udpStream then .pure (stream2Res st q.2)
  else recv2Prog st q.2

/-- **The invariant of `udp2Over3`**: both theory states agree with the bindings of the state;
a stream tied to an address in the 0.2 theory state has a generation, and if the socket's
current binding has that generation its address is the stream's; generations are below the
counter. -/
def JU2 (st : USt) (qT : Udp3St) (qG : UdpSt) : Prop :=
  (∀ s, lookup s qG.bound = (lookup s st.bnd).map (·.1)) ∧
  (∀ s, lookup s qT = (lookup s st.bnd).map (·.1)) ∧
  (∀ i a, lookup i qG.ins = some a → ∃ g, lookup i st.strm = some g ∧
    ∀ a' g', lookup i st.bnd = some (a', g') → g' = g → a' = a) ∧
  (∀ i g, lookup i st.strm = some g → g < st.ctr) ∧
  (∀ s a g, lookup s st.bnd = some (a, g) → g < st.ctr)

end Silmaril.Wasi.Versions.Net
